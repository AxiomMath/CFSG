module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Two
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Field

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Open CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K]

theorem commutator_le_twInndiag (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (H₁ H₂ : Subgroup (MulAut ↥(twistedE6RootGroup K σ))) :
    ⁅H₁, H₂⁆ ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
  haveI := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  rw [← hker, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (IsMulCommutative.is_comm (M := RingAut K)).comm _ _

theorem mem_inner_of_twInndiag_of_two_pow (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {φ : MulAut ↥(twistedE6RootGroup K σ)} (hφ : φ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    {k : ℕ} (h2 : φ ^ 2 ^ k = 1) : φ ∈ twistedE6Inn K σ := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨_Θ, -, -, -, -, h3, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hx : (⟨φ, hφ⟩ : ↥(twistedE6Inn K σ ⊔ twistedE6Diag K σ)) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using h2)
  have ha2 : (QuotientGroup.mk ⟨φ, hφ⟩ : ↥(twistedE6Inn K σ ⊔ twistedE6Diag K σ) ⧸
      (twistedE6Inn K σ).subgroupOf (twistedE6Inn K σ ⊔ twistedE6Diag K σ)) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (h3 _)) (orderOf_dvd_of_pow_eq_one ha2)
  have hg : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  rw [Nat.Coprime.gcd_eq_one hg, Nat.dvd_one, orderOf_eq_one_iff, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hd
  exact hd

theorem card_le_three_mul_card_inf_inner_of_fieldActor (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h3 : 3 ∣ ℓ ^ f + 1) {η : K ≃+* K} (hη : orderOf η = 3)
    {A : Subgroup (MulAut ↥(twistedE6RootGroup K σ))} (hA : IsElemAbelian 3 A)
    (hηA : fieldActor σ η ∈ A) :
    Nat.card A ≤ 3 * Nat.card ↥(A ⊓ twistedE6Inn K σ) := by
  have h1 := S267.BadExc.card_le_three_mul_card_inf_twInndiag hℓ hf hK σ hσ hA
  have hle : A ⊓ (twistedE6Inn K σ ⊔ twistedE6Diag K σ) ≤ A ⊓ twistedE6Inn K σ := fun φ hφ =>
    ⟨hφ.1, CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSFourU.inner_of_inndiag_comm_fieldActor
      hℓ hf hK σ hσ h3 hη hφ.2 (IsElemAbelian.comm hA hφ.1 hηA)⟩
  exact h1.trans (Nat.mul_le_mul_left 3 (Subgroup.card_le_of_le hle))

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
