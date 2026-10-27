module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutSL
import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneDescent
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthAut
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

section Generic

theorem mem_of_pow_eq_one_of_pow_mem {G : Type*} [Group G] {I : Subgroup G} {x : G} {p m : ℕ}
    (hp : 1 < p) (hcop : Nat.Coprime m p) (hxp : x ^ p = 1) (hxm : x ^ m ∈ I) : x ∈ I := by
  have hord : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (Nat.Coprime.coprime_dvd_right hord hcop)
  rw [← hk]
  exact I.pow_mem hxm k

theorem mem_of_pow_eq_one_of_card_quotient_dvd {G : Type*} [Group G] {I D : Subgroup G}
    [I.Normal] {p m : ℕ} (hm : Nat.card (↥D ⧸ I.subgroupOf D) ∣ m) (hcop : Nat.Coprime m p)
    {x : G} (hxD : x ∈ D) (hxp : x ^ p = 1) : x ∈ I := by
  set y : D := ⟨x, hxD⟩ with hydef
  have hy : y ^ p = 1 := Subtype.ext (by simpa using hxp)
  have h1 : orderOf (y : ↥D ⧸ I.subgroupOf D) ∣ p :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one])
  have h2 : orderOf (y : ↥D ⧸ I.subgroupOf D) ∣ m := (orderOf_dvd_natCard _).trans hm
  have h3 : orderOf (y : ↥D ⧸ I.subgroupOf D) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem exists_conj_of_congr {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z) (α : MulAut Y)
    (h : ∃ z, MulAut.congr e α = MulAut.conj z) : ∃ y, α = MulAut.conj y := by
  obtain ⟨z, hz⟩ := h
  refine ⟨e.symm z, MulEquiv.ext fun y => e.injective ?_⟩
  have h1 : e (α y) = z * e y * z⁻¹ := by
    have := congrArg (fun φ : MulAut Z => φ (e y)) hz
    simpa [MulAut.congr_apply, MulAut.conj_apply] using this
  rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end Generic

section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {F : Type} [Field F] [Finite F]

private theorem conjAut_toGL_eq_conj (g : Matrix.SpecialLinearGroup (Fin n) F) :
    conjAut n F (Matrix.SpecialLinearGroup.toGL g) = MulAut.conj (proj n F g) := by
  ext x
  obtain ⟨y, rfl⟩ := proj_surjective n F x
  rw [conjAut_proj, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  show (g : Matrix (Fin n) (Fin n) F) * (y : Matrix (Fin n) (Fin n) F) *
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
    ((g * y * g⁻¹ : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
  rfl

theorem exists_conj_of_pow_prime_projectiveSL_three (hn : 3 ≤ n) (hF : Nat.card F = 3) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (β : MulAut (projectiveSL n F)) (hβ : β ^ p = 1) :
    ∃ y, β = MulAut.conj y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP F 3 :=
    charP_of_card_eq_prime_pow (p := 3) (f := 1) (by rw [← Nat.card_eq_fintype_card, hF, pow_one])
  have hβE : β ∈ semilinearAutGroup n F :=
    mem_semilinearAutGroup_of_pow_odd hn (hp.odd_of_ne_two (by omega)) hβ
  by_cases hD : β ∈ linearAutGroup n F
  · rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq] at hD
    obtain ⟨A, rfl⟩ := hD
    have hdet : ((A ^ 2 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
      have hu : (Matrix.GeneralLinearGroup.det A : F) ≠ 0 := Units.ne_zero _
      have h2 := FiniteField.pow_card_sub_one_eq_one _ hu
      rw [← Nat.card_eq_fintype_card, hF] at h2
      rw [Units.val_pow_eq_pow_val, Matrix.det_pow, ← Matrix.GeneralLinearGroup.val_det_apply]
      exact h2
    set S : Matrix.SpecialLinearGroup (Fin n) F := ⟨_, hdet⟩ with hS
    have hSA : Matrix.SpecialLinearGroup.toGL S = A ^ 2 := Units.ext rfl
    have hmem : conjAut n F A ∈ (MulAut.conj : projectiveSL n F →* _).range := by
      refine mem_of_pow_eq_one_of_pow_mem (by omega) (m := 2)
        ((Nat.coprime_primes Nat.prime_two hp).2 (by omega)) hβ ?_
      rw [← map_pow, ← hSA, conjAut_toGL_eq_conj]
      exact ⟨_, rfl⟩
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, hy.symm⟩
  · have hβ1 : β ≠ 1 := fun h1 => hD (h1 ▸ one_mem _)
    obtain ⟨hpf, -⟩ :=
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
        (ℓ := 3) (f := 1) Nat.prime_three le_rfl hn (by rw [hF, pow_one]) hp β hβE hD
        (orderOf_eq_prime hβ hβ1)
    exact absurd (Nat.le_of_dvd one_pos hpf) (by omega)

end Linear

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem exists_conj_of_pow_prime_primeFormP_three {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 3 1 K) {n : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (β : MulAut (primeFormP h (idGram K n))) (hβ : β ^ p = 1) : ∃ y, β = MulAut.conj y := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_idGram
  have hq : ¬(n = 3 ∧ 3 ^ 1 = 2) := by norm_num
  obtain ⟨-, -, -, -, -, -, -, hker, -, -, hcard⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set σ := primeFormFieldFactor h hC hn hq β with hσdef
  have hσp : σ ^ p = 1 := by rw [hσdef, ← map_pow, hβ, map_one]
  have hσ2 : σ ^ 2 = 1 := by
    have h1 := CFSG.HardMathSupport.Solomon.Coordinator.ringEquiv_pow_eq_one Nat.prime_three
      (by rw [h.card]) σ
    simpa using h1
  have hσ1 : σ = 1 := by
    have h1 := mem_of_pow_eq_one_of_pow_mem (I := ⊥) (by omega)
      ((Nat.coprime_primes Nat.prime_two hp).2 (by omega)) hσp (by rw [hσ2]; exact one_mem _)
    rwa [Subgroup.mem_bot] at h1
  have hβD : β ∈ primeFormD h (idGram K n) := by
    rw [← hker, MonoidHom.mem_ker]
    exact hσ1
  have : (inner (primeFormP h (idGram K n))).Normal := inner_normal _
  have h4 : Nat.Coprime (3 ^ 1 + 1) p := (Nat.Coprime.pow_left 2
    ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))).symm.symm
  obtain ⟨y, hy⟩ := mem_of_pow_eq_one_of_card_quotient_dvd hcard h4 hβD hβ
  exact ⟨y, hy.symm⟩

end Unitary

section Symplectic

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpComm
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem exists_conj_of_pow_prime_psp_three {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (β : MulAut (StatedProj (StatedSp r K))) (hβ : β ^ p = 1) : ∃ y, β = MulAut.conj y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hO := spOuter (K := K) Nat.prime_three le_rfl hr (by rw [hK, pow_one])
  have hodd : Odd (orderOf β) :=
    (hp.odd_of_ne_two (by omega)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ)
  have hE : β ∈ spSemilinearAutGroup r K :=
    mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  by_cases hD : β ∈ spLinearAutGroup r K
  · have : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := mem_of_pow_eq_one_of_relIndex_dvd_two hrel hp (by omega) hD hβ
    exact ⟨t, ht.symm⟩
  · have hord : orderOf β = p := orderOf_eq_prime hβ fun h => hD (h ▸ one_mem _)
    obtain ⟨hpf, -⟩ := hO.descent p hp β hE hD hord
    exact absurd (Nat.le_of_dvd one_pos hpf) (by omega)

end Symplectic

section Orthogonal

open CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.HardMathSupport.Lang.Proving
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (mem_E_of_pow_eq_one_omega
  mem_inner_of_mem_D_omega)

theorem exists_conj_of_pow_prime_omegaOdd_three {G : Type} [Group G] {n : ℕ}
    (hG : StatedClassicalModel G .POmegaOdd n 3 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (β : MulAut G) (hβ : β ^ p = 1) : ∃ a, β = MulAut.conj a := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
    (Or.inl rfl) n 3 1 hG K hK e
  set e' := coordinateOddWitnessEquiv K e
  haveI : Finite G := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (matrixProjectiveDerived (coordinateQuadOdd n K)) := Finite.of_equiv _ e'.toEquiv
  haveI : Fact p.Prime := ⟨hp⟩
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hE := mem_E_of_pow_eq_one_omega hgates hp (Or.inl (by omega)) hβ'
  by_cases hD : MulAut.congr e' β ∈ (linearConjugationHom (coordinateQuadOdd n K)).range
  · obtain ⟨t, ht⟩ := mem_inner_of_mem_D_omega hgates hp (by omega) hD hβ'
    exact exists_conj_of_congr e' β ⟨t, ht.symm⟩
  · have hord : orderOf (MulAut.congr e' β) = p :=
      orderOf_eq_prime hβ' fun h => hD (h ▸ one_mem _)
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd
      (Or.inl rfl) n 3 1 p hG hp (by omega) K hK e _ hE hD hord
    exact absurd (Nat.le_of_dvd one_pos hdesc.1) (by omega)

end Orthogonal

section G2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree


theorem exists_conj_of_pow_prime_g2_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (β : MulAut (adjointGroup Tag.G2 K)) (hβ : β ^ p = 1) :
    ∃ y, β = MulAut.conj y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 3 :=
    charP_of_card_eq_prime_pow (p := 3) (f := 1) (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  haveI : CharP K ReeTag.G2.prime := by
    show CharP K 3
    infer_instance
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
    G2_three_exact_automorphism_normal_form (f := 1) le_rfl K (by rw [hK, pow_one])
  set β' : MulAut (adjointGroup ReeTag.G2.tag K) := β with hβ'def
  have hβ' : β' ^ p = 1 := hβ
  have h2 : Θ β' ^ 2 = 1 := by
    have := pow_card_eq_one (G := Multiplicative (ZMod (2 * 1))) (x := Θ β')
    simpa using this
  have hΘ : Θ β' ∈ (⊥ : Subgroup (Multiplicative (ZMod (2 * 1)))) :=
    mem_of_pow_eq_one_of_pow_mem (by omega) ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))
      (by rw [← map_pow, hβ', map_one]) (by rw [h2]; exact one_mem _)
  have hβk : β' ∈ Θ.ker := by
    rw [MonoidHom.mem_ker]
    exact (Subgroup.mem_bot).1 hΘ
  rw [hker] at hβk
  obtain ⟨y, hy⟩ := hβk
  exact ⟨y, hy.symm⟩

end G2

end CFSG.LocalAnalysis.GLTheoremA.S2019
