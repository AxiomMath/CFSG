module

public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal
  OuterAutomorphisms.congr_conj)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)

section Core

variable {K : Type} [Field K] {d : ℕ}

theorem eq_zero_or_eq_one_of_natCard_two [Finite K] (hK : Nat.card K = 2) (x : K) :
    x = 0 ∨ x = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  by_contra hx
  push Not at hx
  have h3 : ({0, 1, x} : Finset K).card ≤ Fintype.card K := Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem (by simp [hx.1.symm]), Finset.card_insert_of_notMem
    (by simp [hx.2.symm]), Finset.card_singleton] at h3
  omega

theorem fieldAut_subsingleton [Finite K] (hK : Nat.card K = 2) : Subsingleton (K ≃+* K) :=
  ⟨fun σ τ => RingEquiv.ext fun x => by
    rcases eq_zero_or_eq_one_of_natCard_two hK x with rfl | rfl <;> simp⟩

theorem inner_of_gates [Finite K] (hK : Nat.card K = 2) (Q : QuadraticForm K (Fin d → K))
    (hG : OrthogonalGates Q 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htop : p = 3 → projectivePointFamilyAut Q = ⊤)
    (α : MulAut (matrixProjectiveDerived Q)) (hα : α ^ p = 1) :
    α ∈ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
  obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨hHD, k₂, hk₂⟩, -, -, hEA, hpK, -, -⟩ := hG
  have hE : α ∈ matrixProjectiveImage Q := by
    rcases (show p = 3 ∨ 3 < p by have := hp.two_le; omega) with h3 | h3
    · rw [← hEA, htop h3]; exact Subgroup.mem_top _
    · have hA : IsPGroup p (Subgroup.zpowers α) := by
        intro x
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
        refine ⟨1, ?_⟩
        apply Subtype.ext
        simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
      have := hpK p hp h3 _ hA (Subgroup.mem_zpowers α)
      rw [← hEA]
      exact familyOrbitKernel_le Q this
  have : Subsingleton (K ≃+* K) := fieldAut_subsingleton hK
  have hD : α ∈ (linearConjugationHom Q).range := by
    have h1 : (⟨α, hE⟩ : matrixProjectiveImage Q) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]; exact Subsingleton.elim _ _
    rw [hψker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  set H := OuterAutomorphisms.inner (matrixProjectiveDerived Q) with hH
  set D := (linearConjugationHom Q).range with hDdef
  have : H.Normal := OuterAutomorphisms.inner_normal _
  set y : D := ⟨α, hD⟩ with hydef
  have hy : y ^ p = 1 := Subtype.ext (by simpa [hydef] using hα)
  have h1 : orderOf (y : D ⧸ H.subgroupOf D) ∣ p :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one])
  have h2 : orderOf (y : D ⧸ H.subgroupOf D) ∣ 2 ^ k₂ := by
    rw [← hk₂, Subgroup.relIndex, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (y : D ⧸ H.subgroupOf D) = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_right k₂ hcop2).coprime_dvd_left h1) h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

end Core

section Transport

theorem exists_conj_of_mulEquiv {G T : Type*} [Group G] [Group T] (φ : G ≃* T) (p : ℕ)
    (h : ∀ α : MulAut T, α ^ p = 1 → α ∈ OuterAutomorphisms.inner T)
    (σ : MulAut G) (hσ : σ ^ p = 1) : ∃ y : G, σ = MulAut.conj y := by
  have hα : (MulAut.congr φ σ) ^ p = 1 := by rw [← map_pow, hσ, map_one]
  obtain ⟨t, ht⟩ := h _ hα
  refine ⟨φ.symm t, ?_⟩
  apply (MulAut.congr φ).injective
  rw [OuterAutomorphisms.congr_conj, φ.apply_symm_apply]
  exact ht.symm

@[expose] noncomputable def statedProjEquivZMod2 {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι (ZMod 2))) : StatedProj H ≃* H := by
  have hZ : (StatedScalars ι (ZMod 2)).subgroupOf H = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨g, hg⟩ hgZ
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hgZ
    obtain ⟨u, hu⟩ := hgZ
    have hu1 : u = 1 := by
      have : Subsingleton (ZMod 2)ˣ := by
        rw [← Finite.card_le_one_iff_subsingleton, Nat.card_units, Nat.card_zmod]
      exact Subsingleton.elim u 1
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hu, hu1, map_one]
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

end Transport

section Models

open CFSG.RankThree.Classical.SteinbergBY (orthogonal_large_prime_semilinear_field_and_diagonal_gates
  ModelOrthogonalGates)
open CFSG.LocalAnalysis.ComponentInitial

theorem statedOmega_quadPlus_aut_odd_inner (m p : ℕ) (hm : 4 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hexc : ¬ (p = 3 ∧ m = 4)) :
    ∀ σ : MulAut ↥(StatedOmega (StatedQuadPlus m (ZMod 2))), σ ^ p = 1 →
      ∃ y : ↥(StatedOmega (StatedQuadPlus m (ZMod 2))), σ = MulAut.conj y := by
  intro σ hσ
  set G := ↥(StatedOmega (StatedQuadPlus m (ZMod 2))) with hG
  let e : G ≃* StatedProj (StatedOmega (StatedQuadPlus m (ZMod 2))) :=
    (statedProjEquivZMod2 _).symm
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hM : StatedClassicalModel G .POmegaPlus m 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, hm⟩, ZMod 2, inferInstance, inferInstance, hK, ⟨e⟩⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) m 2 1 hM (ZMod 2) hK e
  refine exists_conj_of_mulEquiv (coordinatePlusWitnessEquiv (ZMod 2) e) p ?_ σ hσ
  intro α hα
  refine inner_of_gates (by simp) _ hgates hp hp2 ?_ α hα
  intro h3
  have h5 : 5 ≤ m := by
    rcases (show m = 4 ∨ 5 ≤ m by omega) with h4 | h5
    · exact absurd ⟨h3, h4⟩ hexc
    · exact h5
  exact (CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit.orthogonal_geometry_plus_point_family_orbit
    hM hK e).2.2.2.2.1 h5

theorem statedOmega_quadMinus_aut_odd_inner (m p : ℕ) (hm : 4 ≤ m) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ∀ σ : MulAut ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)), σ ^ p = 1 →
      ∃ y : ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)), σ = MulAut.conj y := by
  intro σ hσ
  set G := ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)) with hG
  let e : G ≃* StatedProj (StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)) :=
    (statedProjEquivZMod2 _).symm
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  have hM : StatedClassicalModel G .POmegaMinus m 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, hm⟩, ZMod 2, inferInstance, inferInstance, hK, 1, 1, hirr, ⟨e⟩⟩
  have hn1 : 1 ≤ m := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) m 2 1 hM hn1 (ZMod 2) hK 1 1 hirr e
  refine exists_conj_of_mulEquiv (coordinateMinusWitnessEquiv (ZMod 2) hn1 1 1 e) p ?_ σ hσ
  intro α hα
  refine inner_of_gates (by simp) _ hgates hp hp2 ?_ α hα
  intro _
  exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus
    (.inr rfl) m 2 1 hM) hn1 (ZMod 2) hK 1 1 hirr).2

end Models

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
