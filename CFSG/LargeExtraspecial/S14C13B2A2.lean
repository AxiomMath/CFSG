module

public import CFSG.LargeExtraspecial.S14C13B2Data
public import CFSG.LargeExtraspecial.S14C13B2Flag
public import CFSG.LargeExtraspecial.S14C13B2Rank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)


variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem commSpace_t_eq_Vt (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) :
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t := by
  ext w
  rw [mem_commSpace]
  constructor
  · rintro ⟨v, rfl⟩
    rw [← coe_chi_apply_mk H C ht ht1 hVQ v]
    exact (chi H C ht ht1 hVQ (Submodule.Quotient.mk v)).2
  · intro hw
    obtain ⟨m, hm⟩ := (chi H C ht ht1 hVQ).surjective ⟨w, hw⟩
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    exact ⟨v, by rw [← coe_chi_apply_mk H C ht ht1 hVQ v, hm]⟩

section Ranks

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {d : S.O} (hdR : d ∈ Rbar S g t)

noncomputable abbrev subOne (d : S.O) : S.Qt →ₗ[ZMod 2] S.Qt :=
  ((d : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1

theorem subOne_apply (d : S.O) (v : S.Qt) :
    subOne d v = (d : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v :=
  rfl

include H ht1 hdR in
theorem finrank_flag_le :
    finrank (ZMod 2) ((Vt S g t).map (subOne d)) +
      finrank (ZMod 2) (((Wt S g t).map (subOne d)).map (Vt S g t).mkQ) +
      finrank (ZMod 2) (((⊤ : Submodule (ZMod 2) S.Qt).map (subOne d)).map (Wt S g t).mkQ) ≤
      finrank (ZMod 2) (commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have hVW := Vt_le_Wt H ht1 (S := S) (g := g)
  have hVφ : (Vt S g t).map (subOne d) ≤ Vt S g t := by
    rintro _ ⟨v, hv, rfl⟩
    exact sub_mem (apply_mem_Vt_of_mem_Rbar H.conj_mem hdR hv) hv
  have hWφ : (Wt S g t).map (subOne d) ≤ Wt S g t := by
    rintro _ ⟨v, hv, rfl⟩
    exact sub_mem (apply_mem_Wt H hdR hv) hv
  have h1 := finrank_map_add_finrank_map_mkQ_le (subOne d) hVW hVφ
  have h2 := finrank_map_add_finrank_map_mkQ_le (subOne d) (le_top : Wt S g t ≤ ⊤) hWφ
  have h3 : (⊤ : Submodule (ZMod 2) S.Qt).map (subOne d) =
      commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt) := Submodule.map_top _
  rw [h3] at h2 ⊢
  omega

theorem finrank_Vt_subOne (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    finrank (ZMod 2) ((Vt S g t).map (subOne d)) =
      finrank (ZMod 2) (commSpace (resV haQ t ⟨d, hdR⟩)) := by
  have hEq : (Vt S g t).map (subOne d) =
      (commSpace (resV haQ t ⟨d, hdR⟩)).map (Vt S g t).subtype := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨resV haQ t ⟨d, hdR⟩ ⟨v, hv⟩ - ⟨v, hv⟩, sub_mem_commSpace _ _, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hm
      exact ⟨v, v.2, rfl⟩
  exact (congrArg (fun U : Submodule (ZMod 2) S.Qt => finrank (ZMod 2) U) hEq).trans
    (Submodule.finrank_map_subtype_eq _ _)

include H C ht ht1 hVQ in
theorem finrank_QW_subOne :
    finrank (ZMod 2) (((⊤ : Submodule (ZMod 2) S.Qt).map (subOne d)).map (Wt S g t).mkQ) =
      finrank (ZMod 2) (commSpace (resV H.conj_mem t ⟨d, hdR⟩)) := by
  set χ := chi H C ht ht1 hVQ
  have hchi : ∀ v, χ ((Wt S g t).mkQ (subOne d v)) =
      resV H.conj_mem t ⟨d, hdR⟩ (χ (Submodule.Quotient.mk v)) - χ (Submodule.Quotient.mk v) := by
    intro v
    have e : χ (Submodule.Quotient.mk ((d : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) =
        resV H.conj_mem t ⟨d, hdR⟩ (χ (Submodule.Quotient.mk v)) :=
      chi_equivariant H C ht ht1 hVQ ⟨d, hdR⟩ v
    rw [subOne_apply, map_sub, map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply, e]
  have hEq : (((⊤ : Submodule (ZMod 2) S.Qt).map (subOne d)).map (Wt S g t).mkQ).map
      χ.toLinearMap = commSpace (resV H.conj_mem t ⟨d, hdR⟩) := by
    ext w
    constructor
    · rintro ⟨_, ⟨_, ⟨v, -, rfl⟩, rfl⟩, rfl⟩
      exact ⟨χ (Submodule.Quotient.mk v), (hchi v).symm⟩
    · rintro ⟨m, rfl⟩
      obtain ⟨m', rfl⟩ := χ.surjective m
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m'
      exact ⟨(Wt S g t).mkQ (subOne d v), ⟨subOne d v, ⟨v, Submodule.mem_top, rfl⟩, rfl⟩,
        hchi v⟩
  rw [← hEq, LinearEquiv.finrank_map_eq]

theorem finrank_WV_subOne {X : Type*} [Group X]
    (ρ : X →* (↥((Wt S g t).map (Vt S g t).mkQ) ≃ₗ[ZMod 2] ↥((Wt S g t).map (Vt S g t).mkQ)))
    (e : X) (hρ : ∀ w (hw : w ∈ Wt S g t), ((ρ e (secMk (Vt S g t) hw) :
      ↥((Wt S g t).map (Vt S g t).mkQ)) : S.Qt ⧸ Vt S g t) =
        (Vt S g t).mkQ ((d : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) :
    finrank (ZMod 2) (((Wt S g t).map (subOne d)).map (Vt S g t).mkQ) =
      finrank (ZMod 2) (commSpace (ρ e)) := by
  have hEq : ((Wt S g t).map (subOne d)).map (Vt S g t).mkQ =
      (commSpace (ρ e)).map ((Wt S g t).map (Vt S g t).mkQ).subtype := by
    ext w
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨ρ e (secMk (Vt S g t) hv) - secMk (Vt S g t) hv, sub_mem_commSpace _ _, ?_⟩
      rw [Submodule.subtype_apply, Submodule.coe_sub, hρ v hv, coe_secMk, subOne_apply,
        map_sub]
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨n, rfl⟩ := mem_commSpace.mp hm
      obtain ⟨v, hv, rfl⟩ := exists_secMk (Vt S g t) n
      refine ⟨subOne d v, ⟨v, hv, rfl⟩, ?_⟩
      rw [Submodule.subtype_apply, Submodule.coe_sub, hρ v hv, coe_secMk, subOne_apply,
        map_sub]
  exact (congrArg (fun U : Submodule (ZMod 2) (S.Qt ⧸ Vt S g t) => finrank (ZMod 2) U)
    hEq).trans (Submodule.finrank_map_subtype_eq _ _)

end Ranks

theorem finrank_commSpace_conj_eq (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {d k : S.O}
    (hdk : d = k * t * k⁻¹) :
    finrank (ZMod 2) (commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt)) = finrank (ZMod 2) (Vt S g t) := by
  have hdk' : (d : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (k : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ := by
    rw [hdk]; rfl
  rw [hdk', finrank_commSpace_conj, commSpace_t_eq_Vt H C ht ht1 hVQ]

theorem isTypeA_resV_of_conj {t : S.O} (hCE : CentralExtInput.{0}) (hSt : Stage S g t)
    (hocc : Config.omegaPlus8b.Occurs S g t) (D : B2Data S g hSt.mem) {d : S.O}
    (hdL : d ∈ S.Lbar g) (hdN : d ∉ Nbar S g t) {k : S.O} (hdk : d = k * t * k⁻¹) :
    IsTypeA D.Q (resV hSt.hyp4.conj_mem t ⟨d, Lbar_le_Rbar hSt.mem hdL⟩) 2 := by
  have H := hSt.hyp4
  have ht := hSt.mem
  have hdR : d ∈ Rbar S g t := Lbar_le_Rbar ht hdL
  set x := resV H.conj_mem t ⟨d, hdR⟩ with hxdef
  have hxL : x ∈ pointRadical D.Q (aV ht) := by
    rw [← D.hE]; exact ⟨d, hdL, fun v => rfl⟩
  have hxΩ : x ∈ omegaGroup D.Q D.hQ := by
    rw [← D.hX]; exact ⟨d, hdR, fun v => rfl⟩
  have hx1 : x ≠ 1 := fun h => hdN ((resV_eq_one_iff H.conj_mem ⟨d, hdR⟩).mp h)
  by_contra hA
  obtain ⟨ρ, hρ, hc⟩ := D.exists_wv hCE hSt hocc
  have hb0 := commSpace_eq_fixOf_of_not_isTypeA ρ (m := 4) (by norm_num) (by rw [D.hdim])
    (D.Q_aV H) (D.Q_bV H) D.hab hc ⟨x, hxΩ⟩ hxL hx1 hA
  have h16 := two_mul_finrank_fixOf_eq ρ (m := 4) (by norm_num) (by rw [D.hdim])
    (aV_ne_zero H ht) (D.Q_aV H) (D.Q_bV H) D.hab hc
  rw [D.finrank_wv hSt hocc] at h16
  have hWV := finrank_WV_subOne ρ ⟨x, hxΩ⟩ (d := d)
    (fun w hw => hρ ⟨x, hxΩ⟩ ⟨d, hdR⟩ rfl w hw)
  rw [hb0.2] at hWV
  obtain ⟨u, hau, hxu⟩ := (mem_pointRadical_iff D.hQ (aV_ne_zero H ht) (D.Q_aV H)).mp hxL
  have hli : LinearIndependent (ZMod 2) ![aV ht, u] := by
    rw [linearIndependent_pair_iff]
    refine ⟨aV_ne_zero H ht, fun hu => hx1 ?_, fun hu => hx1 ?_⟩
    · rw [hxu, hu, CFSG.ClassicalGroups.Orthogonal.eichler_zero_right]
    · rw [hxu, ← hu]
      exact (eichler_eq_one_iff D.hQ (aV_ne_zero H ht) (D.Q_aV H)
        (polar_self_eq_zero D.Q _)).mpr (Submodule.mem_span_singleton_self _)
  have hx2 : finrank (ZMod 2) (commSpace x) = 2 := by
    rw [hxu, commSpace_eichler D.hQ (D.Q_aV H) hau hli, finrank_span_pair hli]
  have hV := finrank_Vt_subOne hdR H.conj_mem (S := S) (g := g) (t := t)
  have hQW := finrank_QW_subOne H hSt.cons ht hSt.ne_one D.hVQ hdR
  have hflag := finrank_flag_le H hSt.ne_one hdR (S := S) (g := g)
  have hconj := finrank_commSpace_conj_eq H hSt.cons ht hSt.ne_one D.hVQ hdk
  rw [D.hdim] at hconj
  rw [← hxdef] at hV hQW
  omega

end CFSG.LargeExtraspecial.S14
