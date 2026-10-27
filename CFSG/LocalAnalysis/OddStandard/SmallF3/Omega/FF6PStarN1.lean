module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSTypes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private def ffOutFF6PStarN1_supp (v : Fin 5 → ZMod 2) : Finset (Fin 5) :=
  Finset.univ.filter fun i => v i ≠ 0

private theorem ffOutFF6PStarN1_ffVecT (fr : PFrame Q (Option (Fin 5)) ffC)
    (v : Fin 5 → ZMod 2) :
    ffVecT fr v = fr.signChange (ffOpt (ffOutFF6PStarN1_supp v)) := rfl

private lemma ffOutFF6PStarN1_zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

private theorem ffOutFF6PStarN1_isEvenVec_iff_even_supp (v : Fin 5 → ZMod 2) :
    IsEvenVec v ↔ Even (ffOutFF6PStarN1_supp v).card := by
  unfold IsEvenVec ffOutFF6PStarN1_supp
  have h1 : (∑ i, v i) = ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), v i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : v i = 0 <;> simp [h]
  rw [h1]
  have h2 : (∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), v i)
      = ∑ _i ∈ Finset.univ.filter (fun i => v i ≠ 0), (1 : ZMod 2) :=
    Finset.sum_congr rfl fun i hi =>
      ffOutFF6PStarN1_zmod2_eq_one_of_ne_zero (Finset.mem_filter.mp hi).2
  rw [h2, Finset.sum_const, nsmul_eq_mul, mul_one, ZMod.natCast_eq_zero_iff_even]

private theorem ffOutFF6PStarN1_ffVecT_mem_omega (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    ffVecT fr v ∈ omegaGroup hQ := by
  apply ffB0p_le_omega hQ fr
  rw [ffOutFF6PStarN1_ffVecT, mem_ffB0p_iff_ffOpt]
  exact ⟨ffOutFF6PStarN1_supp v,
    (ffOutFF6PStarN1_isEvenVec_iff_even_supp v).mp hv, rfl⟩

private theorem ffOutFF6PStarN1_supp_permVec (σ : Equiv.Perm (Fin 5))
    (v : Fin 5 → ZMod 2) :
    ffOutFF6PStarN1_supp (permVec σ v) = ffAct σ (ffOutFF6PStarN1_supp v) := by
  ext i
  rw [ffAct, Finset.mem_map]
  constructor
  · intro hi
    exact ⟨σ.symm i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simpa [permVec, Function.comp_apply] using (Finset.mem_filter.mp hi).2⟩,
      Equiv.apply_symm_apply σ i⟩
  · rintro ⟨j, hj, hji⟩
    have hsymm : σ.symm i = j := (Equiv.symm_apply_eq σ).mpr hji.symm
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [permVec, Function.comp_apply, hsymm]
    exact (Finset.mem_filter.mp hj).2

private theorem ffOutFF6PStarN1_isEvenVec_permVec (σ : Equiv.Perm (Fin 5))
    (v : Fin 5 → ZMod 2) : IsEvenVec (permVec σ v) ↔ IsEvenVec v := by
  rw [ffOutFF6PStarN1_isEvenVec_iff_even_supp, ffOutFF6PStarN1_isEvenVec_iff_even_supp,
    ffOutFF6PStarN1_supp_permVec, ffAct_card]

private theorem ffOutFF6PStarN1_isEvenVec_add {v w : Fin 5 → ZMod 2}
    (hv : IsEvenVec v) (hw : IsEvenVec w) : IsEvenVec (v + w) := by
  unfold IsEvenVec at hv hw ⊢
  simp only [Pi.add_apply, Finset.sum_add_distrib, hv, hw, add_zero]

private theorem ffOutFF6PStarN1_mem_omega_of_mem_ffN0p (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) {g : OGroup Q} (hg : g ∈ ffN0p hQ fr) :
    g ∈ omegaGroup hQ := by
  rw [ffN0p, Subgroup.mem_inf] at hg
  exact hg.1

theorem ff6p_star_normalizer_act (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (fr : PFrame Q (Option (Fin 5)) ffC) {n : ↥(omegaProj hQ)}
    (hn : n ∈ Subgroup.normalizer
      ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ))) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ (J : Finset (Fin 5)) (b b' : ↥(omegaProj hQ)), Even J.card →
      (b : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J)) →
      (b' : ProjOrth Q) = toProj Q (fr.signChange (ffOpt (ffAct σ J))) → n * b * n⁻¹ = b' := by
  have hπ : piOrth Q ∉ omegaGroup hQ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  obtain ⟨g, hgN0, hgn⟩ := ff6p_star_normalizer hQ (by omega) hπ fr hn
  refine ⟨ffN0Rho hQ fr ⟨(g : OGroup Q), hgN0⟩, ?_⟩
  intro J b b' _ hb hb'
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hb, hb', hgn, coe_omegaToProj]
  simp only [← map_mul, ← map_inv]
  rw [ffN0p_conj_signChange hQ fr hgN0 J]

theorem ff6p_star_exists_normalizer (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (fr : PFrame Q (Option (Fin 5)) ffC) (σ : Equiv.Perm (Fin 5)) :
    ∃ n ∈ Subgroup.normalizer
        ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ)),
      ∀ (J : Finset (Fin 5)) (b b' : ↥(omegaProj hQ)), Even J.card →
        (b : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J)) →
        (b' : ProjOrth Q) = toProj Q (fr.signChange (ffOpt (ffAct σ J))) → n * b * n⁻¹ = b' := by
  have hπ : piOrth Q ∉ omegaGroup hQ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  let g : ↥(omegaGroup hQ) := ⟨ffHat fr σ, ffHat_mem_omega hQ fr σ⟩
  have hgN0 : (g : OGroup Q) ∈ ffN0p hQ fr := ffHat_mem_ffN0p hQ fr σ
  refine ⟨omegaToProj hQ g, ff6p_mem_normalizer_of_N0 hQ hπ fr hgN0, ?_⟩
  intro J b b' _ hb hb'
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hb, hb', coe_omegaToProj]
  simp only [← map_mul, ← map_inv]
  rw [ffHat_conj_signChange_ffOpt fr σ J]

theorem ff6p_star_quotEquivTo (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (fr : PFrame Q (Option (Fin 5)) ffC) :
    QuotEquivTo (Subgroup.normalizer
      ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ))) (ffB1p hQ fr)
      (Equiv.Perm (Fin 5)) := by
  have hπ : piOrth Q ∉ omegaGroup hQ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  let N : Subgroup ↥(omegaProj hQ) := Subgroup.normalizer
    ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ))
  let f : ↥(ffN0p hQ fr) →* ↥N :=
    MonoidHom.mk' (fun x => ⟨omegaToProj hQ
        ⟨(x : OGroup Q), ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr x.2⟩,
        ff6p_mem_normalizer_of_N0 hQ hπ fr x.2⟩)
      (fun a b => by
        apply Subtype.ext
        change omegaToProj hQ ⟨((a * b : ↥(ffN0p hQ fr)) : OGroup Q),
            ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr (a * b).2⟩ =
          omegaToProj hQ ⟨(a : OGroup Q),
            ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr a.2⟩ *
            omegaToProj hQ ⟨(b : OGroup Q),
              ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr b.2⟩
        rw [show (⟨((a * b : ↥(ffN0p hQ fr)) : OGroup Q),
              ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr (a * b).2⟩ :
                ↥(omegaGroup hQ)) =
            ⟨(a : OGroup Q), ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr a.2⟩ *
              ⟨(b : OGroup Q), ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr b.2⟩
          from Subtype.ext rfl,
          map_mul])
  have hf_apply : ∀ x : ↥(ffN0p hQ fr),
      ((f x : ↥N) : ↥(omegaProj hQ)) =
        omegaToProj hQ ⟨(x : OGroup Q),
          ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr x.2⟩ := fun x => rfl
  have hinj : Function.Injective f := by
    intro a b hab
    have h : omegaToProj hQ ⟨(a : OGroup Q),
          ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr a.2⟩ =
        omegaToProj hQ ⟨(b : OGroup Q),
          ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr b.2⟩ := by
      rw [← hf_apply a, ← hf_apply b, hab]
    have h2' := omegaToProj_injective_of_not_mem hQ hπ h
    exact Subtype.ext (congrArg (fun z : ↥(omegaGroup hQ) => (z : OGroup Q)) h2')
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, hgN0, hgy⟩ := ff6p_star_normalizer hQ (by omega) hπ fr y.2
    refine ⟨⟨(g : OGroup Q), hgN0⟩, ?_⟩
    apply Subtype.ext
    rw [hf_apply]
    rw [show (⟨(g : OGroup Q),
        ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr hgN0⟩ : ↥(omegaGroup hQ)) = g from
      Subtype.ext rfl]
    exact hgy.symm
  let e : ↥(ffN0p hQ fr) ≃* ↥N := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have he_apply : ∀ x, e x = f x := fun x => rfl
  refine ⟨(ffN0Rho hQ fr).comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro σ
    obtain ⟨x, hx⟩ := ffN0Rho_surjective hQ fr σ
    refine ⟨e x, ?_⟩
    change ffN0Rho hQ fr (e.symm (e x)) = σ
    rw [e.symm_apply_apply]
    exact hx
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hy : e.symm x ∈ (ffB0p fr).subgroupOf (ffN0p hQ fr) := by
        rw [← ffN0Rho_ker hQ fr, MonoidHom.mem_ker]
        exact hx
      rw [Subgroup.mem_subgroupOf] at hy
      change (x : ↥(omegaProj hQ)) ∈ ffStar hQ (ffB0p fr)
      rw [mem_ffStar_iff]
      refine ⟨⟨((e.symm x : ↥(ffN0p hQ fr)) : OGroup Q),
        ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr (e.symm x).2⟩, hy, ?_⟩
      rw [← hf_apply (e.symm x), ← he_apply (e.symm x)]
      exact congrArg (fun z : ↥N => (z : ↥(omegaProj hQ))) (e.apply_symm_apply x)
    · intro hx
      change ffN0Rho hQ fr (e.symm x) = 1
      rw [← MonoidHom.mem_ker, ffN0Rho_ker, Subgroup.mem_subgroupOf]
      change (x : ↥(omegaProj hQ)) ∈ ffStar hQ (ffB0p fr) at hx
      rw [mem_ffStar_iff] at hx
      obtain ⟨g, hgB0, hgx⟩ := hx
      have hthis : (⟨((e.symm x : ↥(ffN0p hQ fr)) : OGroup Q),
          ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr (e.symm x).2⟩ :
            ↥(omegaGroup hQ)) = g := by
        apply omegaToProj_injective_of_not_mem hQ hπ
        rw [← hf_apply (e.symm x), ← he_apply (e.symm x)]
        exact (congrArg (fun z : ↥N => (z : ↥(omegaProj hQ)))
          (e.apply_symm_apply x)).trans hgx.symm
      have hval : ((e.symm x : ↥(ffN0p hQ fr)) : OGroup Q) = (g : OGroup Q) :=
        congrArg (fun z : ↥(omegaGroup hQ) => (z : OGroup Q)) hthis
      rw [hval]
      exact hgB0

theorem ff6p_star_centralizer (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (fr : PFrame Q (Option (Fin 5)) ffC) {n : ↥(omegaProj hQ)}
    (hc : ∀ b ∈ ffB1p hQ fr, n * b = b * n) : n ∈ ffB1p hQ fr := by
  have hz : ∀ b ∈ ffB1p hQ fr,
      ffOmegaToSim hQ n * ffOmegaToSim hQ b = ffOmegaToSim hQ b * ffOmegaToSim hQ n := by
    intro b hb
    rw [← map_mul, hc b hb, map_mul]
  rcases ff6p_cent_sim_cases hQ (by omega) fr hz with ⟨b, hb, hzb⟩ | ⟨b, hb, hzb⟩
  · have hnb : n = b := ffOmegaToSim_injective hQ (by rw [hzb])
    rw [hnb]; exact hb
  · exfalso
    apply ffTs_not_simInOmegaStar hQ hdim fr
    refine ⟨n * b⁻¹, (n * b⁻¹).2, ?_⟩
    change ffOmegaToSim hQ (n * b⁻¹) = ffTs fr
    have hffts : ffTs fr = ffOmegaToSim hQ (n * b⁻¹) := by
      rw [map_mul, map_inv]
      rw [hzb]
      group
    exact hffts.symm

theorem ff6p_star_permModule (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (fr : PFrame Q (Option (Fin 5)) ffC) :
    ∃ κ : (Fin 5 → ZMod 2) → ↥(omegaProj hQ),
      IsPermModuleVia IsEvenVec κ (ffB1p hQ fr)
        (Subgroup.normalizer
          ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ))) ⊤ := by
  classical
  have hπ : piOrth Q ∉ omegaGroup hQ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hN0 := ff6p_N0_permModule hQ fr
  let κ : (Fin 5 → ZMod 2) → ↥(omegaProj hQ) := fun v =>
    if hv : IsEvenVec v then
      omegaToProj hQ ⟨ffVecT fr v, ffOutFF6PStarN1_ffVecT_mem_omega hQ fr hv⟩
    else 1
  have hκ : ∀ v (hv : IsEvenVec v), κ v =
      omegaToProj hQ ⟨ffVecT fr v, ffOutFF6PStarN1_ffVecT_mem_omega hQ fr hv⟩ :=
    fun v hv => by dsimp only [κ]; exact dif_pos hv
  refine ⟨κ, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v w hv hw
    rw [hκ (v+w) (ffOutFF6PStarN1_isEvenVec_add hv hw), hκ v hv, hκ w hw, ← map_mul]
    exact congrArg (omegaToProj hQ) (Subtype.ext (hN0.1 v w hv hw))
  · intro v w hv hw hvw
    apply hN0.2.1 v w hv hw
    have h : omegaToProj hQ ⟨ffVecT fr v, ffOutFF6PStarN1_ffVecT_mem_omega hQ fr hv⟩ =
        omegaToProj hQ ⟨ffVecT fr w, ffOutFF6PStarN1_ffVecT_mem_omega hQ fr hw⟩ := by
      rw [← hκ v hv, ← hκ w hw]; exact hvw
    exact congrArg (fun z : ↥(omegaGroup hQ) => (z : OGroup Q))
      (omegaToProj_injective_of_not_mem hQ hπ h)
  · intro x
    rw [show ffB1p hQ fr = ffStar hQ (ffB0p fr) from rfl, mem_ffStar_iff]
    constructor
    · rintro ⟨g, hgB0, hgx⟩
      obtain ⟨v, hv, hvv⟩ := (hN0.2.2.1 (g : OGroup Q)).mp hgB0
      refine ⟨v, hv, ?_⟩
      rw [hκ v hv]
      rw [show (⟨ffVecT fr v, ffOutFF6PStarN1_ffVecT_mem_omega hQ fr hv⟩ :
          ↥(omegaGroup hQ)) = g from Subtype.ext hvv]
      exact hgx
    · rintro ⟨v, hv, hvx⟩
      refine ⟨⟨ffVecT fr v, ffOutFF6PStarN1_ffVecT_mem_omega hQ fr hv⟩,
        (hN0.2.2.1 (ffVecT fr v)).mpr ⟨v, hv, rfl⟩, ?_⟩
      rw [hκ v hv] at hvx
      exact hvx
  · intro h hh
    obtain ⟨g, hgN0, hgh⟩ := ff6p_star_normalizer hQ (by omega) hπ fr hh
    obtain ⟨σ, -, hσ⟩ := hN0.2.2.2.1 (g : OGroup Q) hgN0
    refine ⟨σ, Subgroup.mem_top σ, fun v hv => ?_⟩
    have hperm : IsEvenVec (permVec σ v) :=
      (ffOutFF6PStarN1_isEvenVec_permVec σ v).mpr hv
    rw [hκ v hv, hκ (permVec σ v) hperm, hgh]
    rw [show omegaToProj hQ g *
        omegaToProj hQ ⟨ffVecT fr v, ffOutFF6PStarN1_ffVecT_mem_omega hQ fr hv⟩ *
        (omegaToProj hQ g)⁻¹ =
        omegaToProj hQ (g * ⟨ffVecT fr v, ffOutFF6PStarN1_ffVecT_mem_omega hQ fr hv⟩ * g⁻¹)
      from by simp only [map_mul, map_inv]]
    apply congrArg (omegaToProj hQ)
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hσ v hv
  · intro σ _
    obtain ⟨h0, hh0, hσ⟩ := hN0.2.2.2.2 σ (Subgroup.mem_top σ)
    let h0' : ↥(omegaGroup hQ) :=
      ⟨h0, ffOutFF6PStarN1_mem_omega_of_mem_ffN0p hQ fr hh0⟩
    refine ⟨omegaToProj hQ h0', ff6p_mem_normalizer_of_N0 hQ hπ fr hh0, fun v hv => ?_⟩
    have hperm : IsEvenVec (permVec σ v) :=
      (ffOutFF6PStarN1_isEvenVec_permVec σ v).mpr hv
    rw [hκ v hv, hκ (permVec σ v) hperm]
    rw [show omegaToProj hQ h0' *
        omegaToProj hQ ⟨ffVecT fr v, ffOutFF6PStarN1_ffVecT_mem_omega hQ fr hv⟩ *
        (omegaToProj hQ h0')⁻¹ =
        omegaToProj hQ (h0' *
          ⟨ffVecT fr v, ffOutFF6PStarN1_ffVecT_mem_omega hQ fr hv⟩ * h0'⁻¹)
      from by simp only [map_mul, map_inv]]
    apply congrArg (omegaToProj hQ)
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hσ v hv

end CFSG.OddStandard.SmallF3.Omega
