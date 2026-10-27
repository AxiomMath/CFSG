module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.Sporadic.HS

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Blueprint

@[expose] def IsTypeHS (G : Type) [Group G] : Prop :=
  ∃ (P : Sylow 2 G) (Q : Sylow 2 NativeSporadic.HS),
    Nonempty ((P : Subgroup G) ≃* (Q : Subgroup NativeSporadic.HS))

@[expose] def GorensteinHarrisInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsTypeHS G →
    (∀ N : Subgroup G, N.Normal → N.index ≠ 2) →
    Nonempty (G ⧸ pPrimeCore 2 G ≃* NativeSporadic.HS) ∨
      ∃ A K : Subgroup (G ⧸ pPrimeCore 2 G), A.Normal ∧
        Nonempty (A ≃* Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) ∧
        Nonempty (K ≃* GL (Fin 3) (ZMod 2)) ∧ A ⊓ K = ⊥ ∧ A ⊔ K = ⊤ ∧
        ∃ g ∈ K, ∃ a ∈ A, g * a * g⁻¹ ≠ a

theorem card_sylow_HS (Q : Sylow 2 NativeSporadic.HS) :
    Nat.card (Q : Subgroup NativeSporadic.HS) = 512 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite NativeSporadic.HS := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Sporadic.HS.card_HS]; norm_num)
  rw [Sylow.card_eq_multiplicity, CFSG.Sporadic.HS.card_HS,
    show (44352000 : ℕ) = 2 ^ 9 * 86625 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 86625)]
  norm_num

theorem IsTypeHS.card_sylow {G : Type} [Group G] (h : IsTypeHS G) :
    ∃ P : Sylow 2 G, Nat.card (P : Subgroup G) = 512 := by
  obtain ⟨P, Q, ⟨e⟩⟩ := h
  exact ⟨P, by rw [Nat.card_congr e.toEquiv, card_sylow_HS]⟩

theorem gorensteinHarris_corollaryA (hGH : GorensteinHarrisInput) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hG : IsTypeHS G) : Nonempty (G ≃* NativeSporadic.HS) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hG.card_sylow
  have h512 : 512 ∣ Nat.card G := by
    rw [← hP]
    exact (P : Subgroup G).card_subgroup_dvd_card
  have hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN h2
    rcases hN.eq_bot_or_eq_top with rfl | rfl
    · rw [index_bot] at h2
      rw [h2] at h512
      norm_num at h512
    · rw [index_top] at h2
      norm_num at h2
  have hO : pPrimeCore 2 G = ⊥ := by
    rcases (pPrimeCore_normal (p := 2) (G := G)).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 G)) := pPrimeCore_coprime_card
      rw [h, card_top] at hcop
      have h2 : 2 ∣ Nat.card G := (by norm_num : 2 ∣ 512).trans h512
      exact absurd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop) (not_not.mpr h2)
  have e : G ⧸ pPrimeCore 2 G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  rcases hGH G hG hidx with hf | ⟨A, K, hA, ⟨eA⟩, ⟨eK⟩, hAK, -, -⟩
  · obtain ⟨f⟩ := hf
    exact ⟨e.symm.trans f⟩
  · exfalso
    have : IsSimpleGroup (G ⧸ pPrimeCore 2 G) := e.isSimpleGroup
    have hcardA : Nat.card A = 64 := by
      rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card]
      rfl
    have hcardK : Nat.card K = 168 := by
      rw [Nat.card_congr eK.toEquiv, Matrix.card_GL_field, ZMod.card]
      decide
    rcases hA.eq_bot_or_eq_top with rfl | rfl
    · rw [card_bot] at hcardA
      norm_num at hcardA
    · rw [top_inf_eq] at hAK
      rw [hAK, card_bot] at hcardK
      norm_num at hcardK

end CFSG.ComponentClassification.HSFLit
