module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthModelTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmCases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpAsmAnalysis

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient_apply_mk)
open scoped Classical

theorem exists_special_sesqSUConj_eq {ℓ f : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    {M : Type} [AddCommGroup M] [Module E M] [FiniteDimensional E M]
    {hE : UnitaryFieldData ℓ f E} {B : M →ₛₗ[hE.bar] M →ₗ[E] E}
    (hBs : B.IsSymm) (hBl : B.SeparatingLeft) (hdim : Module.finrank E M = 2)
    (g : ↥(sesqUnitaryGroup B)) :
    ∃ s : ↥(sesqSpecialUnitaryGroup B),
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.sesqSUConj g =
        CFSG.LocalAnalysis.GLTheoremA.KD264Lie.sesqSUConj
          ⟨s, sesqSpecialUnitaryGroup_le B s.2⟩ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hE.prime⟩
  haveI : Finite M := Module.finite_of_finite E
  let G : LinearMap.GeneralLinearGroup E M := g
  have hG : G ∈ sesqUnitaryGroup B := g.2
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hBs hBl
  have hdetnorm : hE.norm (LinearMap.det (G : M →ₗ[E] M)) = 1 :=
    CFSG.LinearGroups.norm_det_of_isometry (φ := (G : M →ₗ[E] M)) hE e
      (CFSG.LinearGroups.mem_orthonormalFrames.mpr he) (mem_sesqUnitaryGroup.mp hG)
  have hdetnorm' : LinearMap.det (G : M →ₗ[E] M) *
      hE.bar (LinearMap.det (G : M →ₗ[E] M)) = 1 := hdetnorm
  have hne : LinearMap.det (G : M →ₗ[E] M) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdetnorm'
    exact zero_ne_one hdetnorm'
  let u : Eˣ := Units.mk0 (LinearMap.det (G : M →ₗ[E] M)) hne
  have hucoe : (u : E) = LinearMap.det (G : M →ₗ[E] M) := rfl
  have hℓ : ℓ = 2 := CharP.eq E hE.charP inferInstance
  have hodd : Odd (Nat.card Eˣ) := by
    rw [Nat.card_units, hE.card, hℓ]
    have heven : Even (2 ^ (2 * f)) :=
      Nat.even_pow.mpr ⟨even_two, by have := hE.one_le; omega⟩
    exact Nat.Even.sub_odd (Nat.one_le_pow (2 * f) 2 (by norm_num)) heven odd_one
  have hcop : Nat.Coprime (Nat.card Eˣ) 2 := Nat.coprime_two_right.mpr hodd
  obtain ⟨ρ, hρ⟩ := (powCoprime hcop).surjective u
  have hρ' : ρ ^ 2 = u := by simpa using hρ
  have hρcoe : (ρ : E) ^ 2 = LinearMap.det (G : M →ₗ[E] M) := by
    rw [← Units.val_pow_eq_pow_val, hρ', hucoe]
  have hρnorm : (ρ : E) * hE.bar (ρ : E) = 1 := by
    have h1 : ((ρ : E) * hE.bar (ρ : E)) ^ 2 = 1 := by
      have h2 : ((ρ : E) * hE.bar (ρ : E)) ^ 2 =
          (ρ : E) ^ 2 * hE.bar ((ρ : E) ^ 2) := by
        rw [mul_pow, map_pow, mul_comm]
      rw [h2, hρcoe, hdetnorm']
    exact CharTwo.sq_inj.1 (h1.trans (one_pow 2).symm)
  let s : LinearMap.GeneralLinearGroup E M := (ρ⁻¹ : Eˣ) • G
  have hscoe : (s : M →ₗ[E] M) = (ρ⁻¹ : E) • (G : M →ₗ[E] M) := by
    show ((ρ⁻¹ : Eˣ) : E) • (G : M →ₗ[E] M) = (ρ⁻¹ : E) • (G : M →ₗ[E] M)
    rw [Units.val_inv_eq_inv_val]
  have hunit : s ∈ sesqUnitaryGroup B := by
    rw [mem_sesqUnitaryGroup]
    intro x y
    rw [hscoe]
    simp only [LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul, RingHom.id_apply]
    rw [mem_sesqUnitaryGroup.mp hG x y]
    have hρinv' : ((ρ : E)⁻¹) * hE.bar ((ρ : E)⁻¹) = 1 := by
      have hb : hE.bar (ρ : E) * (ρ : E) = 1 := by rw [mul_comm, hρnorm]
      have h1 : (hE.bar (ρ : E))⁻¹ = (ρ : E) := inv_eq_of_mul_eq_one_right hb
      have h2 : ((ρ : E))⁻¹ = hE.bar (ρ : E) := inv_eq_of_mul_eq_one_right hρnorm
      rw [map_inv₀, h1, h2]
      simpa [mul_comm] using hb
    change ((ρ : E)⁻¹) * (hE.bar ((ρ : E)⁻¹) * (B x) y) = (B x) y
    rw [← mul_assoc, hρinv', one_mul]
  have hdet : LinearMap.det (s : M →ₗ[E] M) = 1 := by
    rw [hscoe, LinearMap.det_smul, hdim]
    rw [← hρcoe, inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero 2 (Units.ne_zero ρ))
  have hsmem : s ∈ sesqSpecialUnitaryGroup B :=
    mem_sesqSpecialUnitaryGroup.mpr ⟨hunit, hdet⟩
  let s' : ↥(sesqSpecialUnitaryGroup B) := ⟨s, hsmem⟩
  refine ⟨s', ?_⟩
  ext x v
  have hg : G = ((ρ : Eˣ) • (1 : LinearMap.GeneralLinearGroup E M)) * s := by
    ext w
    simp [s, smul_smul]
  have hcomm : ∀ y : LinearMap.GeneralLinearGroup E M,
      ((ρ : Eˣ) • (1 : LinearMap.GeneralLinearGroup E M)) * y =
      y * ((ρ : Eˣ) • (1 : LinearMap.GeneralLinearGroup E M)) := by
    intro y
    ext w
    simp [smul_smul, mul_comm]
  have hgroup : G * (x : LinearMap.GeneralLinearGroup E M) * G⁻¹ =
      s * (x : LinearMap.GeneralLinearGroup E M) * s⁻¹ := by
    rw [hg]
    have hcomm' : ((ρ : Eˣ) • (1 : LinearMap.GeneralLinearGroup E M)) *
        (s * (x : LinearMap.GeneralLinearGroup E M) * s⁻¹) =
        (s * (x : LinearMap.GeneralLinearGroup E M) * s⁻¹) *
        ((ρ : Eˣ) • (1 : LinearMap.GeneralLinearGroup E M)) := hcomm _
    calc ((ρ : Eˣ) • (1 : LinearMap.GeneralLinearGroup E M)) * s *
          (x : LinearMap.GeneralLinearGroup E M) *
          (((ρ : Eˣ) • (1 : LinearMap.GeneralLinearGroup E M)) * s)⁻¹
        = ((ρ : Eˣ) • (1 : LinearMap.GeneralLinearGroup E M)) *
            (s * (x : LinearMap.GeneralLinearGroup E M) * s⁻¹) *
            ((ρ : Eˣ) • (1 : LinearMap.GeneralLinearGroup E M))⁻¹ := by group
      _ = s * (x : LinearMap.GeneralLinearGroup E M) * s⁻¹ := by
          rw [hcomm']
          group
  change ((((g : LinearMap.GeneralLinearGroup E M) *
      (x : LinearMap.GeneralLinearGroup E M) * (g : LinearMap.GeneralLinearGroup E M)⁻¹) :
      LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) v =
    (((s * (x : LinearMap.GeneralLinearGroup E M) * s⁻¹) :
      LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) v
  exact congrArg (fun e : LinearMap.GeneralLinearGroup E M => (e : M →ₗ[E] M) v) hgroup

theorem indAut_mem_innAutDerived_of_sesqSUConj {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {J : Subgroup Γ} (hqJ : CFSG.Open.IsQuasisimple ↥J)
    (hdvd : p ∣ Nat.card ↥J) {y : Γ} (hN : y ∈ Subgroup.normalizer (J : Set Γ))
    (hyp : y ^ p = 1) {ℓ f : ℕ} {E : Type} [Field E] [Finite E] {M : Type} [AddCommGroup M]
    [Module E M] [FiniteDimensional E M]
    {hE : UnitaryFieldData ℓ f E} {B : M →ₛₗ[hE.bar] M →ₗ[E] E}
    (hBs : B.IsSymm) (hBl : B.SeparatingLeft)
    (hperf : commutator ↥(sesqSpecialUnitaryGroup B) = ⊤)
    (g : ↥(sesqUnitaryGroup B)) (π' : ↥(sesqSpecialUnitaryGroup B) →* ↥J)
    (hsurj : Function.Surjective π')
    (hker : π'.ker ≤ Subgroup.center ↥(sesqSpecialUnitaryGroup B))
    (hconj : ∀ s : ↥(sesqSpecialUnitaryGroup B),
      CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩ (π' s) =
        π' (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.sesqSUConj g s)) :
    MI.indAut p J y hN ∈ innAutDerived (PSimple p J) := by
  classical
  have hconjpow : (MulAut.conj y : MulAut Γ) ^ p = 1 := by
    rw [← map_pow, hyp, map_one]
  have hαpow : (⟨MulAut.conj y, by
      change J.map (MulAut.conj y).toMonoidHom = J
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩ :
      CFSG.GroupActions.subgroupStabAut J) ^ p = 1 := Subtype.ext hconjpow
  have hrestpow : (CFSG.GroupActions.subgroupStabRestrict J
      ⟨MulAut.conj y, by
        change J.map (MulAut.conj y).toMonoidHom = J
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩) ^ p = 1 := by
    rw [← map_pow, hαpow, map_one]
  have hγp : centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J
      ⟨MulAut.conj y, by
        change J.map (MulAut.conj y).toMonoidHom = J
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩) ^ p = 1 := by
    rw [← map_pow, hrestpow, map_one]
  exact (indAut_mem_innAutDerived_iff_centerQuotientHom hp hqJ hdvd hN).mpr
    (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.centerQuotientHom_mem_innAutDerived_of_sesqSUConj
      hE hBs hBl hperf hp hp2 g π' hsurj hker hconj hγp)

theorem indAut_mem_inner_of_sesqSUConj_two {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {J : Subgroup Γ} (hqJ : CFSG.Open.IsQuasisimple ↥J)
    (hdvd : p ∣ Nat.card ↥J) {y : Γ} (hN : y ∈ Subgroup.normalizer (J : Set Γ))
    (hyp : y ^ p = 1) {ℓ f : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2] {M : Type}
    [AddCommGroup M] [Module E M] [FiniteDimensional E M]
    {hE : UnitaryFieldData ℓ f E} {B : M →ₛₗ[hE.bar] M →ₗ[E] E}
    (hBs : B.IsSymm) (hBl : B.SeparatingLeft) (hdim : Module.finrank E M = 2)
    (g : ↥(sesqUnitaryGroup B)) (π' : ↥(sesqSpecialUnitaryGroup B) →* ↥J)
    (hsurj : Function.Surjective π')
    (hker : π'.ker ≤ Subgroup.center ↥(sesqSpecialUnitaryGroup B))
    (hconj : ∀ t : ↥(sesqSpecialUnitaryGroup B),
      CFSG.GroupActions.subgroupStabRestrict J
        ⟨MulAut.conj y, by
          change J.map (MulAut.conj y).toMonoidHom = J
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩ (π' t) =
        π' (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.sesqSUConj g t)) :
    MI.indAut p J y hN ∈ inner (PSimple p J) := by
  classical
  obtain ⟨s, hsconj⟩ := exists_special_sesqSUConj_eq hBs hBl hdim g
  let sU : ↥(sesqUnitaryGroup B) := ⟨s, sesqSpecialUnitaryGroup_le B s.2⟩
  let hstab : CFSG.GroupActions.subgroupStabAut J :=
    ⟨MulAut.conj y, by
      change J.map (MulAut.conj y).toMonoidHom = J
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩
  have hstab_eq : hstab = ⟨MulAut.conj y, by
      change J.map (MulAut.conj y).toMonoidHom = J
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩ := Subtype.ext rfl
  have hconj_s : ∀ t : ↥(sesqSpecialUnitaryGroup B),
      CFSG.GroupActions.subgroupStabRestrict J hstab (π' t) =
        π' (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.sesqSUConj sU t) := by
    intro t
    rw [hstab_eq]
    rw [← hsconj]
    exact hconj t
  have hcenter : centerQuotientHom ↥J
      (CFSG.GroupActions.subgroupStabRestrict J hstab) =
      MulAut.conj (QuotientGroup.mk (π' s)) := by
    ext z
    obtain ⟨z0, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨t, rfl⟩ := hsurj z0
    rw [show centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J hstab)
        (QuotientGroup.mk (π' t)) =
        QuotientGroup.mk ((CFSG.GroupActions.subgroupStabRestrict J hstab) (π' t)) from
      onCenterQuotient_apply_mk _ _]
    rw [hconj_s t, MulAut.conj_apply]
    have hgroup : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.sesqSUConj sU t = s * t * s⁻¹ :=
      Subtype.ext (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.sesqSUConj_apply sU t)
    rw [hgroup, map_mul, map_mul, map_inv]
    rfl
  have hcenter_inner : centerQuotientHom ↥J
      (CFSG.GroupActions.subgroupStabRestrict J hstab) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (↥J ⧸ Subgroup.center ↥J) :=
    ⟨QuotientGroup.mk (π' s), hcenter.symm⟩
  have hmain : centerQuotientHom ↥J (CFSG.GroupActions.subgroupStabRestrict J
      ⟨MulAut.conj y, by
        change J.map (MulAut.conj y).toMonoidHom = J
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN⟩) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (↥J ⧸ Subgroup.center ↥J) := by
    rw [← hstab_eq]
    exact hcenter_inner
  exact (indAut_mem_inner_iff_centerQuotientHom hp hqJ hdvd hN).mpr hmain


@[expose] def OrthSelfDualCatalogue : Prop :=
  ∀ {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V),
    ∀ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x y : ↥(orthDerived Q))
      (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
      (hyc : (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V))
      (hyp : y ^ p = 1) {h : K[X]}
      (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
      (hself : h = reciprocalPolynomial h)
      (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h))
      (J : Subgroup (ProjOrthDerived Q))
      (hJeq : J = componentImage Q (x : V ≃ₗ[K] V) h)
      (hN : piOrth Q y ∈ Subgroup.normalizer (J : Set (ProjOrthDerived Q))),
      3 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h →
      catalogIs (PSimple p J) (onLie isUnitaryCharTwoIdx)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh


namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient_apply_mk)
open CFSG.ComponentClassification.AssemblyBPredicates
open scoped Classical

theorem orthSelfDualBlock_of_catalogue {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hcat : OrthSelfDualCatalogue) : OrthSelfDualBlock Q := by
  classical
  intro p hp hp2 x y hx hyc hyp h hh hne1 hself hq J hJeq hN
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hdvd : p ∣ Nat.card J
  · have hspecΩ : specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q :=
      specialBlock_le_orthDerived_of_perfect hq.1
        ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
    have hqJ_nat : CFSG.IsQuasisimple ↥J := by
      rw [hJeq]
      exact isQuasisimple_map_projective hspecΩ hq
    have hqJ : CFSG.Open.IsQuasisimple ↥J :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hqJ_nat)
    have hqblock : CFSG.Open.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq)
    have hJstab : MulAut.conj (QuotientGroup.mk'
        ((scalars K V).subgroupOf (orthDerived Q)) y) ∈
        CFSG.GroupActions.subgroupStabAut J := by
      change MulAut.conj (piOrth Q y) ∈ CFSG.GroupActions.subgroupStabAut J
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN
    obtain ⟨ℓ, f, hU, B, hBs, hBl, hperf, g, π', hsurj, hker, hconj⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_sesqSUConjData hx (hp.odd_of_ne_two hp2)
        hh hne1 hself hqblock y hyc J hJeq hJstab
    let hN' : piOrth Q y ∈ Subgroup.normalizer (J : Set (ProjOrthDerived Q)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hJstab
    let hstab : CFSG.GroupActions.subgroupStabAut J :=
      ⟨MulAut.conj (piOrth Q y), by
        change J.map (MulAut.conj (piOrth Q y)).toMonoidHom = J
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hN'⟩
    have hconj' : ∀ s : ↥(sesqSpecialUnitaryGroup B),
        CFSG.GroupActions.subgroupStabRestrict J hstab (π' s) =
        π' (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.sesqSUConj g s) := by
      intro s
      convert hconj s using 2
    have hypN : (piOrth Q y) ^ p = 1 := by rw [← map_pow, hyp, map_one]
    have hmem' : MI.indAut p J (piOrth Q y) hN' ∈ innAutDerived (PSimple p J) :=
      indAut_mem_innAutDerived_of_sesqSUConj hp hp2 hqJ hdvd hN' hypN hBs hBl hperf g π' hsurj
        hker hconj'
    have hmem : MI.indAut p J (piOrth Q y) hN ∈ innAutDerived (PSimple p J) := by
      rw [CFSG.LocalAnalysis.GLTheoremA.T171Sh.indAut_eq_of_proof hN hN']
      exact hmem'
    set m := primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h with hm
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have hpos := hx.primaryMultiplicity_pos hh
      have h1 : m = 1 := by omega
      have hbot := hx.specialBlock_eq_bot_of_finrank_eq_one hh h1
      haveI : Subsingleton ↥(specialBlock Q (x : V ≃ₗ[K] V) h) := by
        rw [hbot]
        infer_instance
      obtain ⟨u, v, huv⟩ := hq.2.2
      exact huv (Subsingleton.elim (u * v) (v * u))
    rcases Nat.lt_or_ge m 3 with hm_lt | hm_ge
    · have hm2' : m = 2 := by omega
      haveI : CharP (AdjoinRoot h) 2 :=
        charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective 2
      have hdim : Module.finrank (AdjoinRoot h)
          (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) = 2 := by
        change m = 2
        exact hm2'
      have hinner' : MI.indAut p J (piOrth Q y) hN' ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J) :=
        indAut_mem_inner_of_sesqSUConj_two hp hp2 hqJ hdvd hN' hypN hBs hBl hdim g π' hsurj
          hker hconj'
      refine Or.inr ?_
      rw [CFSG.LocalAnalysis.GLTheoremA.T171Sh.indAut_eq_of_proof hN hN']
      exact hinner'
    · exact Or.inl ⟨hcat Q hp hp2 x y hx hyc hyp hh hne1 hself hq J hJeq hN
        (by simpa [hm] using hm_ge), hmem⟩
  · haveI := subsingleton_pSimple_of_not_dvd hp hdvd
    exact Or.inr (mem_inner_of_subsingleton _)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
