module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesForms
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap
open CFSG.RankThree.OrthogonalInvolutions (commSpace fixSpace mem_commSpace mem_fixSpace
  sub_mem_commSpace finrank_commSpace_add_finrank_fixSpace map_add_eq)

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]

abbrev OGroup (Q : QuadraticForm (ZMod 3) V) : Type :=
  ↥(TauCeti.QuadraticMap.orthogonalGroup Q)

variable {Q : QuadraticForm (ZMod 3) V}

abbrev commSp (t : OGroup Q) : Submodule (ZMod 3) V :=
  commSpace (t : V ≃ₗ[ZMod 3] V)

abbrev fixSp (t : OGroup Q) : Submodule (ZMod 3) V :=
  fixSpace (t : V ≃ₗ[ZMod 3] V)

private theorem aux_coe_mul_self {t : OGroup Q} (htt : t * t = 1) :
    (t : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V) = 1 := by
  simpa using congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V)) htt

private theorem aux_apply_apply {t : OGroup Q} (htt : t * t = 1) (v : V) :
    (t : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) v) = v := by
  rw [← LinearEquiv.mul_apply, aux_coe_mul_self htt, LinearEquiv.coe_one, id]

private theorem aux_radical_restrict_polar {W : Submodule (ZMod 3) V} {x : W}
    (hx : x ∈ (Q.restrict W).radical) (y : W) :
    QuadraticMap.polar Q (x : V) (y : V) = 0 := by
  have hx1 : Q (x : V) = 0 := (QuadraticMap.mem_radical_iff'.mp hx).1
  have hkey : Q ((x : V) + (y : V)) = Q (y : V) := (QuadraticMap.mem_radical_iff'.mp hx).2 y
  rw [map_add_eq Q (x : V) (y : V), hx1, zero_add] at hkey
  have h : Q (y : V) + QuadraticMap.polar Q (x : V) (y : V) = Q (y : V) + 0 := by
    rw [hkey, add_zero]
  exact add_left_cancel h

theorem mem_commSp_iff {t : OGroup Q} (htt : t * t = 1) {v : V} :
    v ∈ commSp t ↔ (t : V ≃ₗ[ZMod 3] V) v = -v := by
  rw [commSp, mem_commSpace]
  constructor
  · rintro ⟨w, rfl⟩
    rw [map_sub, aux_apply_apply htt w, neg_sub]
  · intro hv
    refine ⟨v, ?_⟩
    rw [hv]
    have h2 : (-1 - 1 : ZMod 3) = 1 := by decide
    calc -v - v = (-1 : ZMod 3) • v - (1 : ZMod 3) • v := by simp
      _ = ((-1 : ZMod 3) - 1) • v := by rw [sub_smul]
      _ = (1 : ZMod 3) • v := by rw [h2]
      _ = v := one_smul _ _

theorem mem_fixSp_iff {t : OGroup Q} {v : V} :
    v ∈ fixSp t ↔ (t : V ≃ₗ[ZMod 3] V) v = v := by
  rw [fixSp]
  exact mem_fixSpace

theorem isCompl_fixSp_commSp {t : OGroup Q} (htt : t * t = 1) : IsCompl (fixSp t) (commSp t) := by
  refine ⟨disjoint_iff.mpr ?_, codisjoint_iff.mpr ?_⟩
  · rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    rw [Submodule.mem_bot]
    have h1 : (t : V ≃ₗ[ZMod 3] V) v = v := (mem_fixSp_iff).mp hv.1
    have h2 : (t : V ≃ₗ[ZMod 3] V) v = -v := (mem_commSp_iff htt).mp hv.2
    have h3 : v = -v := h1.symm.trans h2
    have h4 : (2 : ZMod 3) • v = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp h3
    exact (isUnit_of_invertible (2 : ZMod 3)).smul_eq_zero.mp h4
  · rw [eq_top_iff]
    intro v _
    refine Submodule.mem_sup.mpr
      ⟨(2 : ZMod 3) • (v + (t : V ≃ₗ[ZMod 3] V) v), ?_,
       (2 : ZMod 3) • (v - (t : V ≃ₗ[ZMod 3] V) v), ?_, ?_⟩
    · rw [mem_fixSp_iff, map_smul, map_add, aux_apply_apply htt v, add_comm]
    · rw [mem_commSp_iff htt, map_smul, map_sub, aux_apply_apply htt v, ← smul_neg, neg_sub]
    · rw [← smul_add]
      have hsum : (v + (t : V ≃ₗ[ZMod 3] V) v) + (v - (t : V ≃ₗ[ZMod 3] V) v) =
          (2 : ZMod 3) • v := by
        rw [two_smul]; abel
      rw [hsum, smul_smul]
      have h4 : (2 : ZMod 3) * 2 = 1 := by decide
      rw [h4, one_smul]

theorem polar_fixSp_commSp {t : OGroup Q} (htt : t * t = 1) {v w : V} (hv : v ∈ fixSp t)
    (hw : w ∈ commSp t) : QuadraticMap.polar Q v w = 0 := by
  have hv' : (t : V ≃ₗ[ZMod 3] V) v = v := (mem_fixSp_iff).mp hv
  have hw' : (t : V ≃ₗ[ZMod 3] V) w = -w := (mem_commSp_iff htt).mp hw
  have hp : QuadraticMap.polar Q v w = -QuadraticMap.polar Q v w := by
    calc QuadraticMap.polar Q v w =
          QuadraticMap.polar Q ((t : V ≃ₗ[ZMod 3] V) v) ((t : V ≃ₗ[ZMod 3] V) w) :=
          (TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup t.2 v w).symm
      _ = QuadraticMap.polar Q v (-w) := by rw [hv', hw']
      _ = -QuadraticMap.polar Q v w := by simp
  have h2 : (2 : ZMod 3) * QuadraticMap.polar Q v w = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp hp
  exact (mul_eq_zero.mp h2).resolve_left (by decide : (2 : ZMod 3) ≠ 0)

theorem map_add_of_fixSp_commSp {t : OGroup Q} (htt : t * t = 1) {v w : V} (hv : v ∈ fixSp t)
    (hw : w ∈ commSp t) : Q (v + w) = Q v + Q w := by
  rw [map_add_eq Q v w, polar_fixSp_commSp htt hv hw, add_zero]

theorem commSp_eq_orthogonal_fixSp (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    commSp t = LinearMap.BilinForm.orthogonal Q.polarBilin (fixSp t) := by
  have hB : Q.polarBilin.Nondegenerate := (QuadraticMap.nondegenerate_polar_iff).mpr hQ
  apply le_antisymm
  · intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    simpa using polar_fixSp_commSp htt hv hw
  · intro x hx
    have hx' : x ∈ fixSp t ⊔ commSp t := by
      rw [(isCompl_fixSp_commSp htt).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx'
    have hb_orth : b ∈ LinearMap.BilinForm.orthogonal Q.polarBilin (fixSp t) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro v hv
      simpa using polar_fixSp_commSp htt hv hb
    have ha_orth : a ∈ LinearMap.BilinForm.orthogonal Q.polarBilin (fixSp t) := by
      have := sub_mem hx hb_orth
      simpa using this
    have ha_zero : a = 0 := by
      refine hB.1 a fun y => ?_
      have hy : y ∈ fixSp t ⊔ commSp t := by
        rw [(isCompl_fixSp_commSp htt).sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
      have h1 : QuadraticMap.polar Q a c = 0 := by
        have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp ha_orth) c hc
        rw [QuadraticMap.polarBilin_apply_apply] at h
        exact (QuadraticMap.polar_comm Q c a).symm.trans h
      have h2 : QuadraticMap.polar Q a d = 0 := polar_fixSp_commSp htt ha hd
      show QuadraticMap.polar Q a (c + d) = 0
      rw [QuadraticMap.polar_add_right, h1, h2, add_zero]
    rw [ha_zero, zero_add]
    exact hb

theorem nondegenerate_restrict_fixSp (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    (Q.restrict (fixSp t)).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro x hx
  apply Subtype.ext
  have hx1 : Q (x : V) = 0 := (QuadraticMap.mem_radical_iff'.mp hx).1
  have hxpol : ∀ y : fixSp t, QuadraticMap.polar Q (x : V) (y : V) = 0 :=
    fun y => aux_radical_restrict_polar hx y
  have hrad : (x : V) ∈ Q.radical := by
    rw [QuadraticMap.mem_radical_iff']
    refine ⟨hx1, fun y => ?_⟩
    have hy : y ∈ fixSp t ⊔ commSp t := by
      rw [(isCompl_fixSp_commSp htt).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
    have hpc : QuadraticMap.polar Q (x : V) c = 0 := hxpol ⟨c, hc⟩
    have hpd : QuadraticMap.polar Q (x : V) d = 0 := polar_fixSp_commSp htt x.2 hd
    show Q ((x : V) + (c + d)) = Q (c + d)
    rw [map_add_eq Q (x : V) (c + d), hx1, zero_add, QuadraticMap.polar_add_right]
    simp only [hpc, hpd, add_zero]
  rw [hQ.radical_eq_bot, Submodule.mem_bot] at hrad
  exact hrad

theorem nondegenerate_restrict_commSp (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    (Q.restrict (commSp t)).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro x hx
  apply Subtype.ext
  have hx1 : Q (x : V) = 0 := (QuadraticMap.mem_radical_iff'.mp hx).1
  have hxpol : ∀ y : commSp t, QuadraticMap.polar Q (x : V) (y : V) = 0 :=
    fun y => aux_radical_restrict_polar hx y
  have hrad : (x : V) ∈ Q.radical := by
    rw [QuadraticMap.mem_radical_iff']
    refine ⟨hx1, fun y => ?_⟩
    have hy : y ∈ fixSp t ⊔ commSp t := by
      rw [(isCompl_fixSp_commSp htt).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
    have hpc : QuadraticMap.polar Q (x : V) c = 0 := by
      rw [QuadraticMap.polar_comm]
      exact polar_fixSp_commSp htt hc x.2
    have hpd : QuadraticMap.polar Q (x : V) d = 0 := hxpol ⟨d, hd⟩
    show Q ((x : V) + (c + d)) = Q (c + d)
    rw [map_add_eq Q (x : V) (c + d), hx1, zero_add, QuadraticMap.polar_add_right]
    simp only [hpc, hpd, add_zero]
  rw [hQ.radical_eq_bot, Submodule.mem_bot] at hrad
  exact hrad

theorem finrank_fixSp_add_finrank_commSp (t : OGroup Q) :
    Module.finrank (ZMod 3) (fixSp t) + Module.finrank (ZMod 3) (commSp t) =
      Module.finrank (ZMod 3) V := by
  rw [fixSp, commSp, add_comm, finrank_commSpace_add_finrank_fixSpace]

theorem quadSign_eq_fixSp_commSp (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    quadSign Q = quadSign (Q.restrict (fixSp t)) * quadSign (Q.restrict (commSp t)) *
      (-1) ^ (Module.finrank (ZMod 3) (fixSp t) * Module.finrank (ZMod 3) (commSp t)) := by
  have hcomm := commSp_eq_orthogonal_fixSp hQ htt
  have hcompl :
      IsCompl (fixSp t) (LinearMap.BilinForm.orthogonal Q.polarBilin (fixSp t)) := by
    rw [← hcomm]
    exact isCompl_fixSp_commSp htt
  have hiso : Q.Equivalent ((Q.restrict (fixSp t)).prod (Q.restrict (commSp t))) := by
    rw [hcomm]
    exact ⟨(QuadraticMap.IsometryEquiv.prodRestrictOrthogonal Q (fixSp t) hcompl).symm⟩
  calc quadSign Q = quadSign ((Q.restrict (fixSp t)).prod (Q.restrict (commSp t))) :=
        quadSign_congr hQ hiso
    _ = quadSign (Q.restrict (fixSp t)) * quadSign (Q.restrict (commSp t)) *
          (-1) ^ (Module.finrank (ZMod 3) (fixSp t) * Module.finrank (ZMod 3) (commSp t)) :=
        quadSign_prod (nondegenerate_restrict_fixSp hQ htt) (nondegenerate_restrict_commSp hQ htt)

theorem commSp_conj (g t : OGroup Q) :
    commSp (g * t * g⁻¹) = (commSp t).map (g : V →ₗ[ZMod 3] V) := by
  simpa [commSp] using
    CFSG.RankThree.OrthogonalInvolutions.commSpace_conj (g : V ≃ₗ[ZMod 3] V) (t : V ≃ₗ[ZMod 3] V)

theorem equivalent_restrict_commSp_conj (g t : OGroup Q) :
    (Q.restrict (commSp t)).Equivalent (Q.restrict (commSp (g * t * g⁻¹))) := by
  refine ⟨(g : V ≃ₗ[ZMod 3] V).ofSubmodules (commSp t) (commSp (g * t * g⁻¹))
    (commSp_conj g t).symm, ?_⟩
  intro x
  change Q ((g : V ≃ₗ[ZMod 3] V) (x : V)) = Q (x : V)
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup g.2 (x : V)

theorem exists_involution_of_commSp (hQ : Q.Nondegenerate) {N : Submodule (ZMod 3) V}
    (hN : (Q.restrict N).Nondegenerate) : ∃ t : OGroup Q, t * t = 1 ∧ commSp t = N := by
  let P : Submodule (ZMod 3) V := LinearMap.BilinForm.orthogonal Q.polarBilin N
  have hcompl : IsCompl N P := hN.isCompl_orthogonal
  set d : (N × P) ≃ₗ[ZMod 3] V := Submodule.prodEquivOfIsCompl N P hcompl with hd
  set t₁ : V ≃ₗ[ZMod 3] V :=
    d.symm.trans
      (((LinearEquiv.neg (ZMod 3) : N ≃ₗ[ZMod 3] N).prodCongr
        (LinearEquiv.refl (ZMod 3) P)).trans d)
    with ht
  have hdapply : ∀ (a : N) (b : P), d (a, b) = (a : V) + (b : V) := by
    intro a b
    rw [hd, Submodule.coe_prodEquivOfIsCompl']
  have htapply : ∀ (a : N) (b : P), t₁ (d (a, b)) = d (-a, b) := by
    intro a b
    rw [ht, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply,
      LinearEquiv.prodCongr_apply, LinearEquiv.neg_apply, LinearEquiv.refl_apply]
  have hQd : ∀ (a : N) (b : P), Q (d (a, b)) = Q (a : V) + Q (b : V) := by
    intro a b
    rw [hd, Submodule.coe_prodEquivOfIsCompl', map_add_eq Q (a : V) (b : V)]
    have hpol : QuadraticMap.polar Q (a : V) (b : V) = 0 := by
      rw [← QuadraticMap.polarBilin_apply_apply]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp b.2) a a.2
    rw [hpol, add_zero]
  have htO : t₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    set x : N × P := d.symm v with hx
    obtain ⟨a, b⟩ := x
    have hv : v = d (a, b) := by
      rw [hx]
      exact (d.apply_symm_apply v).symm
    rw [hv, htapply, hQd, hQd]
    simp
  have htt₁ : t₁ * t₁ = 1 := by
    ext v
    set x : N × P := d.symm v with hx
    obtain ⟨a, b⟩ := x
    have hv : v = d (a, b) := by
      rw [hx]
      exact (d.apply_symm_apply v).symm
    rw [LinearEquiv.mul_apply, hv, htapply, htapply, neg_neg]
    simp
  have htt : (⟨t₁, htO⟩ : OGroup Q) * ⟨t₁, htO⟩ = 1 := Subtype.ext htt₁
  have hcomm : commSp (⟨t₁, htO⟩ : OGroup Q) = N := by
    ext v
    rw [mem_commSp_iff htt]
    change t₁ v = -v ↔ v ∈ N
    constructor
    · intro hv
      set x : N × P := d.symm v with hx
      obtain ⟨a, b⟩ := x
      have hv' : v = d (a, b) := by
        rw [hx]
        exact (d.apply_symm_apply v).symm
      rw [hv', htapply] at hv
      have hdneg : -d (a, b) = d (-a, -b) :=
        (LinearMap.map_neg (d : (N × P) →ₗ[ZMod 3] V) (a, b)).symm
      have hpair : (-a, b) = (-a, -b) := d.injective (hv.trans hdneg)
      have hb : b = -b := by simpa using congrArg Prod.snd hpair
      have hb0 : b = 0 := by
        have h2 : (2 : ZMod 3) • b = 0 := by
          rw [two_smul]
          exact eq_neg_iff_add_eq_zero.mp hb
        exact (isUnit_of_invertible (2 : ZMod 3)).smul_eq_zero.mp h2
      have hdv : v = (a : V) := by
        rw [hv', hb0, hdapply]
        simp
      rw [hdv]
      exact a.2
    · intro hv
      set x : N × P := d.symm v with hx
      obtain ⟨a, b⟩ := x
      have hv' : v = d (a, b) := by
        rw [hx]
        exact (d.apply_symm_apply v).symm
      have hbN : (b : V) ∈ N := by
        have hbv : (b : V) = v - (a : V) := by
          rw [hv', hdapply]
          abel
        rw [hbv]
        exact N.sub_mem hv a.2
      have hb0 : (b : V) = 0 :=
        Submodule.disjoint_def.mp hcompl.disjoint (b : V) hbN b.2
      have hb0' : b = 0 := Subtype.ext hb0
      have key : t₁ (d (a, b)) = -(d (a, b)) := by
        rw [htapply, hb0', hdapply]
        rw [hdapply]
        simp
      rw [hv']
      exact key
  exact ⟨⟨t₁, htO⟩, htt, hcomm⟩

theorem eq_of_commSp_eq (hQ : Q.Nondegenerate) {s t : OGroup Q} (hs : s * s = 1)
    (ht : t * t = 1) (h : commSp s = commSp t) : s = t := by
  have hB : Q.polarBilin.Nondegenerate := (QuadraticMap.nondegenerate_polar_iff).mpr hQ
  have hBsymm : Q.polarBilin.IsRefl := Q.isSymm_polarBilin.isRefl
  have horth : LinearMap.BilinForm.orthogonal Q.polarBilin (fixSp s) =
      LinearMap.BilinForm.orthogonal Q.polarBilin (fixSp t) := by
    rw [← commSp_eq_orthogonal_fixSp hQ hs, ← commSp_eq_orthogonal_fixSp hQ ht, h]
  have hfix : fixSp s = fixSp t := by
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hB hBsymm (fixSp s),
      ← LinearMap.BilinForm.orthogonal_orthogonal hB hBsymm (fixSp t), horth]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hx : x ∈ fixSp s ⊔ commSp s := by
    rw [(isCompl_fixSp_commSp hs).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  have ha' : a ∈ fixSp t := hfix ▸ ha
  have hb' : b ∈ commSp t := h ▸ hb
  have hsa : (s : V ≃ₗ[ZMod 3] V) a = a := (mem_fixSp_iff).mp ha
  have hta : (t : V ≃ₗ[ZMod 3] V) a = a := (mem_fixSp_iff).mp ha'
  have hsb : (s : V ≃ₗ[ZMod 3] V) b = -b := (mem_commSp_iff hs).mp hb
  have htb : (t : V ≃ₗ[ZMod 3] V) b = -b := (mem_commSp_iff ht).mp hb'
  rw [map_add, map_add, hsa, hta, hsb, htb]

theorem commSp_eq_bot_iff {t : OGroup Q} (htt : t * t = 1) : commSp t = ⊥ ↔ t = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hmem : (t : V ≃ₗ[ZMod 3] V) v - v ∈ commSp t :=
      sub_mem_commSpace (t : V ≃ₗ[ZMod 3] V) v
    rw [h, Submodule.mem_bot, sub_eq_zero] at hmem
    simpa using hmem
  · intro h
    rw [h, commSp, commSpace, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨y, hy⟩ := hx
    simpa using hy.symm

end CFSG.OddStandard.SmallF3.Omega
