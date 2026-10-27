module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75Inner
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGFourDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L225Theta

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups

namespace F3FG

open F3L225 F3A75 in
theorem fourGroupResidualStep_of_outQuat (hOut : Harris82OutQuatThree)
    (hD4 : FourGroupResidualStepD4) (hθ : Harris82ThetaBalanceThree) :
    FourGroupResidualStep := by
  intro G _ _ _ hnab hKP hnC z₁ z₂ hz₁ hz₂ hne hc L₁ K hL₁ hz₁L₁ hsl hK hWN hcomm hz₂K hcat
  by_cases hD : ∃ f : ℕ, Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .POmegaPlus 4 3 f
  · exact hD4 G hnab hKP hnC z₁ z₂ hz₁ hz₂ hne hc L₁ K hL₁ hz₁L₁ hsl hK hWN hcomm hz₂K hcat hD
  have hS : (IsSimpleChevalleyOver 3 (↥K ⧸ Open.fusionZStar ↥K) ∧
      (∀ f : ℕ, ¬ Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSL 2 3 f) ∧
        ∀ f : ℕ, ¬ Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .POmegaPlus 4 3 f) ∨
      Nonempty (↥K ⧸ Open.fusionZStar ↥K ≃* ↥Blueprint.NativeSporadic.M11) := by
    rcases hcat with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1, h2, fun f h => hD ⟨f, h⟩⟩
    · exact Or.inr h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hz₂K', -⟩ := hz₂K
  set C := centralizer ({z₁} : Set G) with hC
  have hz₂C : z₂ ∈ C := mem_centralizer_singleton_iff.mpr hc.symm
  have hz₁C : z₁ ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hL₁C : L₁ ≤ C := hL₁.1.trans inf_le_left
  have hL₁N : L₁ ≤ normalizer (K : Set G) := hL₁.1.trans hWN
  set t : MBar z₁ := QuotientGroup.mk (⟨z₂, hz₂C⟩ : ↥C) with ht
  obtain ⟨hKc, hKq⟩ := F3L226.isComponentOf_hatIn hK
  have hLs : (hatIn z₁ K).IsSubnormal := F3L226.isSubnormal_of_isComponentOf hKc
  have htL : t ∈ hatIn z₁ K := mk_mem_hatIn hz₂K' hz₂C
  have ht2 : orderOf t = 2 := by
    apply orderOf_mk_mbar_eq_two
    rw [Subgroup.orderOf_mk]
    exact hz₂
  have hM := F3L226.isSolvableTwoComponentIn_hatIn hz₂ hz₂C hL₁
  have hMN : hatIn z₁ L₁ ≤ normalizer ((hatIn z₁ K : Subgroup (MBar z₁)) : Set (MBar z₁)) :=
    F3L226.hatIn_le_normalizer hL₁N
  obtain ⟨eZ⟩ := nonempty_fusionZStar_equiv_hatIn hK
  set z : MBar z₁ := QuotientGroup.mk (⟨z₁, hz₁C⟩ : ↥C) with hz
  have hzM : z ∈ hatIn z₁ L₁ := mk_mem_hatIn hz₁L₁ hz₁C
  have hz2 : orderOf z = 2 := by
    apply orderOf_mk_mbar_eq_two
    rw [Subgroup.orderOf_mk]
    exact hz₁
  have hzc : ∀ k ∈ hatIn z₁ L₁, k * z = z * k := by
    intro k _
    obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective k
    rw [hz, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp k'.2)
  obtain ⟨e⟩ := F3L221.nonempty_sl23_of_central hM hzM hz2 hzc
  have hinner : ∀ s ∈ hatIn z₁ L₁, (∃ n : ℕ, s ^ 2 ^ n = 1) →
      s ∈ hatIn z₁ K ⊔ centralizer ((hatIn z₁ K : Subgroup (MBar z₁)) : Set (MBar z₁)) := by
    rintro s hs ⟨n, hsn⟩
    exact mem_sup_centralizer_of_outQuat (hOut _ hS _ hKq ⟨eZ.symm⟩) hMN e hs hsn
  by_contra hnot
  have hnot' : ¬ ∀ s ∈ hatIn z₁ L₁, (∃ n : ℕ, s ^ 2 ^ n = 1) → s ∈ hatIn z₁ K :=
    fun hall => hnot (oPrimeResidualOf_two_le_of_hatIn hK hL₁C hall)
  have h2 : ∀ s ∈ hatIn z₁ L₁, (∃ n : ℕ, s ^ 2 ^ n = 1) →
      ∀ l ∈ hatIn z₁ K, s * l = l * s := by
    rcases mem_or_centralizes htL hM hMN e hzM hz2 hzc hinner with h | h
    · exact absurd h hnot'
    · exact h
  have hθ' := isThetaBalanced_of_mulEquiv eZ (hθ.1 _ hcat)
  have hle := commutator_le_of_centralizes hK hL₁C hL₁N
    (commute_of_three hLs hKq ht2 htL hM hMN h2 hnot' hθ')
  rw [hcomm] at hle
  have hbot : ∀ x : ↥(hatIn z₁ K), x = 1 := by
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    apply Subtype.ext
    have hkK : (k : G) ∈ K := hk
    obtain ⟨k', hk', hk'e⟩ := hle hkK
    have hk'' : (⟨(k : G), hkK⟩ : ↥K) ∈ pPrimeCore 2 ↥K := by
      have h1 : k' = ⟨(k : G), hkK⟩ := Subtype.ext hk'e
      rw [← h1]
      exact hk'
    have h3 := (F3L226.mem_pPrimeCore_iff hK hkK).mp hk''
    show QuotientGroup.mk' (pPrimeCore 2 ↥C) k = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h3
  obtain ⟨a, b, hab⟩ := hKq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [hbot a', hbot b'])

end F3FG

end CFSG.ComponentClassification.HarrisLit.T1
