module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FOLin
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.CLSEvenOrthogonalSemilinearFourGroup

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2.OmegaTwo

open Matrix QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs
  mem_unitMultiplierPairs_iff evenOrthogonalRealization_of_regular)
open CFSG.LocalAnalysis.ComponentInitial.EvenOrthogonalFourGroup
  (mem_matrixDerived_of_mem_elementaryGroup)

variable {K : Type} [Field K] {n : ℕ}

theorem exists_fixed_of_linear {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {g : similarityPairs Q} (hgU : g ∈ unitMultiplierPairs Q) (hr : g.val.right = 1)
    (hgg : ∀ v, coordinateSemilinearMap g.val (coordinateSemilinearMap g.val v) = v)
    (hg1 : g.val.left ≠ 1) :
    ∃ M : matrixDerived Q, matrixDerivedConjugation Q g M = M ∧ M ≠ 1 ∧ M ^ 3 = 1 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hTv : ∀ v, coordinateSemilinearMap g.val v = matrixLinearEquiv g.val.left v := fun v => by
    rw [coordinateSemilinearMap_apply, matrixLinearEquiv_apply, hr]
    rfl
  have hT : ∀ x, Q (matrixLinearEquiv g.val.left x) = Q x := fun x => by
    rw [← hTv, (mem_unitMultiplierPairs_iff Q g).mp hgU x, hr]
    rfl
  have hTT : ∀ x, matrixLinearEquiv g.val.left (matrixLinearEquiv g.val.left x) = x :=
    fun x => by
      rw [← hTv, ← hTv]
      exact hgg x
  have hT1 : matrixLinearEquiv g.val.left ≠ 1 := fun h1 =>
    hg1 (matrixLinearIso.injective (by rw [map_one]; exact h1))
  obtain ⟨h, hhE, hhT, hh3, hh1⟩ :=
    exists_eichler_commuting hn (Module.finrank_fin_fun K) hQ hT hTT hT1
  obtain ⟨M, hMdef⟩ : ∃ M : GL (Fin (2 * n)) K, M = matrixLinearIso.symm h := ⟨_, rfl⟩
  have hMh : matrixLinearIso M = h := by rw [hMdef, MulEquiv.apply_symm_apply]
  have hM : M ∈ matrixDerived Q :=
    mem_matrixDerived_of_mem_elementaryGroup Q hE (by rw [hMh]; exact hhE)
  have hAM : g.val.left * M = M * g.val.left := by
    apply matrixLinearIso.injective
    rw [map_mul, map_mul, hMh]
    apply LinearEquiv.ext
    intro z
    exact (hhT z).symm
  refine ⟨⟨M, hM⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [matrixDerivedConjugation_val, hr, map_one, MulAut.one_apply, hAM, mul_inv_cancel_right]
  · intro h1
    apply hh1
    have h3 : M = 1 := congrArg Subtype.val h1
    rw [← hMh, h3, map_one]
  · apply Subtype.ext
    apply matrixLinearIso.injective
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, map_pow, map_one, hMh, hh3]

theorem exists_fixed_of_field {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hcj : Function.Injective (MulAut.conj : matrixProjectiveDerived Q →*
      MulAut (matrixProjectiveDerived Q)))
    {α : MulAut (matrixProjectiveDerived Q)} (hαE : α ∈ matrixProjectiveImage Q)
    (hα : orderOf α = 2) {g : similarityPairs Q} (hgU : g ∈ unitMultiplierPairs Q)
    (hgα : matrixProjectiveConjugationHom Q g = α) (hσ1 : g.val.right ≠ 1) :
    ∃ y, α y = y ∧ y ≠ 1 ∧ y ^ 3 = 1 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨-, -, -, -, -, -, -, -, hinv⟩ :=
    evenOrthogonalRealization_of_regular hf hK (by omega) Q hQ hT hE
  obtain ⟨hSS, hTT, -⟩ := hinv α hαE hα g hgU hgα
  have hσσ : g.val.right * g.val.right = 1 := by
    have h1 := congrArg (fun y : similarityPairs Q => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  obtain ⟨hfeven, hk, -⟩ := card_descentField hf hK hσσ hσ1
  obtain ⟨hfin, -, -, hQ₀, -⟩ := even_quadratic_semilinear_involution_descent hσσ hσ1 hQ
    (T := pairSemilinearMap g.val) hTT (pairSemilinearMap_quad hgU)
  have hk2 : 1 ≤ f / 2 := by
    obtain ⟨m, hm⟩ := hfeven
    omega
  have : CharP (descentField g.val.right) 2 :=
    finite_field_prime_power_characteristic Nat.prime_two hk2 hk
  have : FiniteDimensional (descentField g.val.right) (pairFix g) := finite_fixSpace
  have hdim : finrank (descentField g.val.right) (pairFix g) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  have hJ := derived_simple_even hn (pairDescentForm hgU) hQ₀ hdim
  obtain ⟨P₁, P₂, -, h12, -, -⟩ :=
    (finite_even_regular_quadratic_normal_forms (pairDescentForm hgU) hQ₀).2.2.2.2.2 n hdim hn
  obtain ⟨h3, h1⟩ := eichler_pair_pow_three P₁.Q_e P₂.Q_e P₂.Q_f P₁.Q_f h12.ef
    (by rw [polar_comm]; exact h12.fe) h12.ee (by rw [polar_comm]; exact h12.ff) P₁.polar_ef
    P₂.polar_ef
  have hmem : eichler (pairDescentForm hgU) P₁.e P₂.f * eichler (pairDescentForm hgU) P₂.e P₁.f ∈
      pairDescentDerived hgU := by
    change _ ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hgU),
      TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hgU)⁆
    rw [hJ.1]
    exact mul_mem (eichler_mem_elementaryGroup _ _ _) (eichler_mem_elementaryGroup _ _ _)
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : pairDescentDerived hgU, h₀ = ⟨_, hmem⟩ := ⟨_, rfl⟩
  have hh₀3 : h₀ ^ 3 = 1 := by
    rw [hh₀]
    exact Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact h3)
  have hh₀1 : h₀ ≠ 1 := fun h0 => h1 (by rw [hh₀] at h0; exact congrArg Subtype.val h0)
  obtain ⟨-, -, -, -, ext, -, -, hinj, hinn, hcent, -⟩ :=
    evenOrthogonalFieldCentralizer_of_regular hf hK hn Q hQ hT hE α hαE hα g hgU hgα hσ1
  obtain ⟨y, hy⟩ := hinn ⟨h₀, rfl⟩
  have hyα : MulAut.conj y * α = α * MulAut.conj y := by
    have h5 := (Subgroup.mem_inf.mp (hcent ⟨h₀, rfl⟩)).2
    rw [Subgroup.mem_centralizer_singleton_iff] at h5
    rw [hy]
    exact h5
  refine ⟨y, ?_, ?_, ?_⟩
  · apply hcj
    apply MulEquiv.ext
    intro z
    have h6 := congrArg (fun φ : MulAut (matrixProjectiveDerived Q) => φ (α.symm z)) hyα
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.apply_symm_apply, map_mul,
      map_inv] at h6
    rw [MulAut.conj_apply, MulAut.conj_apply, h6]
  · intro hy1
    apply hh₀1
    apply hinj
    rw [map_one, ← hy, hy1, map_one]
  · apply hcj
    rw [map_pow, hy, ← map_pow, hh₀3, map_one, map_one]

theorem exists_fixed_order_three {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hcj : Function.Injective (MulAut.conj : matrixProjectiveDerived Q →*
      MulAut (matrixProjectiveDerived Q)))
    {α : MulAut (matrixProjectiveDerived Q)} (hαE : α ∈ matrixProjectiveImage Q)
    (hα : orderOf α = 2) : ∃ y, α y = y ∧ y ≠ 1 ∧ y ^ 3 = 1 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨hZ, -, -, huniq, -, -, -, -, hinv⟩ :=
    evenOrthogonalRealization_of_regular hf hK (by omega) Q hQ hT hE
  obtain ⟨g, ⟨hgU, hgα⟩, -⟩ := huniq α hαE
  by_cases hr : g.val.right = 1
  · obtain ⟨-, hgg, -⟩ := hinv α hαE hα g hgU hgα
    have hg1 : g.val.left ≠ 1 := by
      intro h1
      have hg : g = 1 := Subtype.ext (SemidirectProduct.ext h1 hr)
      rw [hg, map_one] at hgα
      rw [← hgα, orderOf_one] at hα
      exact absurd hα (by norm_num)
    obtain ⟨M, hMg, hM1, hM3⟩ := exists_fixed_of_linear hf hK hn hQ hE hgU hr hgg hg1
    refine ⟨matrixProjectiveProjection Q M, ?_, ?_, ?_⟩
    · rw [← hgα]
      change matrixProjectiveConjugation Q g (matrixProjectiveProjection Q M) = _
      rw [matrixProjectiveConjugation_mk, hMg]
    · intro h1
      apply hM1
      have h2 : M ∈ matrixDerivedScalars Q := (QuotientGroup.eq_one_iff _).mp h1
      rw [hZ, Subgroup.mem_bot] at h2
      exact h2
    · rw [← map_pow, hM3, map_one]
  · exact exists_fixed_of_field hf hK hn hQ hT hE hcj hαE hα hgU hgα hr

end CFSG.ComponentClassification.HarrisLit.L33.C2.OmegaTwo
