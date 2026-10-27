module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRA8
import CFSG.RankThree.PartOne.S9.Extraction.Basic
import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open Equiv Equiv.Perm CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

@[expose] def kv4 : Finset (Perm (Fin 4)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

theorem kv4_mul : ∀ a ∈ kv4, ∀ b ∈ kv4, a * b ∈ kv4 := by
  unfold kv4
  decide +kernel

theorem kv4_inv : ∀ a ∈ kv4, a⁻¹ ∈ kv4 := by
  unfold kv4
  decide +kernel

theorem kv4_conj : ∀ a ∈ kv4, ∀ g : Perm (Fin 4), g * a * g⁻¹ ∈ kv4 := by
  unfold kv4
  decide +kernel

theorem card_kv4 : kv4.card = 4 := by
  unfold kv4
  decide +kernel

@[expose] def V4S4 : Subgroup (Perm (Fin 4)) where
  carrier := {p | p ∈ kv4}
  mul_mem' := fun {a b} ha hb => kv4_mul a ha b hb
  one_mem' := by
    unfold kv4
    simp
  inv_mem' := fun {a} ha => kv4_inv a ha

instance : V4S4.Normal := ⟨fun n hn g => kv4_conj n hn g⟩

theorem card_V4S4 : Nat.card V4S4 = 4 := by
  have h : Nat.card V4S4 = Nat.card (↑kv4 : Set (Perm (Fin 4))) := rfl
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset, card_kv4]

theorem pCore_two_perm_four_ne_bot : CFSG.pCore 2 (Perm (Fin 4)) ≠ ⊥ := by
  intro h
  have hle : V4S4 ≤ CFSG.pCore 2 (Perm (Fin 4)) :=
    le_sSup ⟨inferInstance, IsPGroup.of_card (n := 2) (by rw [card_V4S4]; norm_num)⟩
  rw [h] at hle
  have h1 : Nat.card V4S4 ≤ 1 := by
    have : V4S4 = ⊥ := le_bot_iff.mp hle
    rw [this]
    simp
  rw [card_V4S4] at h1
  omega

theorem not_pCore_quotient_perm_four {Q : Type*} [Group Q] [Finite Q]
    (e : Q ⧸ CFSG.pCore 2 Q ≃* Perm (Fin 4)) : False := by
  have h1 := CFSG.LieType.SteinbergBR.pCore_map_equiv 2 e
  have h2 : CFSG.pCore 2 (Q ⧸ CFSG.pCore 2 Q) = ⊥ :=
    CFSG.RankThree.PartOne.Extract.pCore_two_quotient_eq_bot
  rw [h2, Subgroup.map_bot] at h1
  exact pCore_two_perm_four_ne_bot h1.symm

theorem eq_four_of_alt_even {X : Type} [Group X] [Finite X] {n : ℕ}
    (e : X ≃* alternatingGroup (Fin (2 * n))) (e8 : X ≃* alternatingGroup (Fin 8)) : n = 4 := by
  have h8 : Nat.card (alternatingGroup (Fin 8)) = (8 : ℕ).factorial / 2 :=
    card_alt_fin (by norm_num)
  have hX : Nat.card X = (8 : ℕ).factorial / 2 := (Nat.card_congr e8.toEquiv).trans h8
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exfalso
    have hle : Nat.card (alternatingGroup (Fin (2 * 0))) ≤ Nat.card (Perm (Fin (2 * 0))) :=
      Subgroup.card_le_card_group _
    have hX' : Nat.card X = Nat.card (alternatingGroup (Fin (2 * 0))) := Nat.card_congr e.toEquiv
    have hp : Nat.card (Perm (Fin (2 * 0))) = 1 := by
      simp
    rw [hp] at hle
    rw [← hX'] at hle
    rw [hX] at hle
    revert hle
    decide +kernel
  · have h3 := (Nat.card_congr e.toEquiv).symm.trans hX
    rw [card_alt_fin (by omega)] at h3
    have h5 : 2 ∣ (2 * n).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h6 : 2 ∣ (8 : ℕ).factorial := Nat.dvd_factorial (by norm_num) (by norm_num)
    have h7 : (2 * n).factorial = (8 : ℕ).factorial := by omega
    have h8' : 1 < (2 * n).factorial := Nat.one_lt_factorial.mpr (by omega)
    have := (Nat.factorial_inj' (Or.inl (by omega))).mp h7
    omega

variable {G : Type} [Group G] [Finite G]

theorem not_nineThreeSix_alt_eight {M S L : Subgroup G} (h : NineThreeSix M S L)
    (e8 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 8))) :
    False := by
  obtain ⟨-, n, ⟨e⟩, ⟨eQ⟩⟩ := h
  obtain ⟨e8⟩ := e8
  have hn : n = 4 := eq_four_of_alt_even e e8
  subst hn
  exact not_pCore_quotient_perm_four eQ

theorem kFactBlockPLSylow_of_formalized : KFactBlockPLSylow := by
  intro G _ _ P M A H R _ L _ h6 e8
  exact (not_nineThreeSix_alt_eight h6 e8).elim

end CFSG.AGLEmbeddingD2.McLaughlin
