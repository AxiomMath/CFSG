module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
import TauCeti.LinearAlgebra.LinearMap.Cardinality

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

theorem card_submodule_eq_card_inf_ker_mul_card_map {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (δ : V →ₗ[ZMod 2] V) (X : Submodule (ZMod 2) V) :
    Nat.card ↥X = Nat.card ↥(X ⊓ LinearMap.ker δ) * Nat.card ↥(Submodule.map δ X) := by
  have hker : Nat.card ↥(LinearMap.ker (δ.domRestrict X)) =
      Nat.card ↥(X ⊓ LinearMap.ker δ) := by
    rw [LinearMap.ker_domRestrict]
    rw [← Submodule.map_comap_subtype X (LinearMap.ker δ)]
    exact Nat.card_congr (Submodule.equivSubtypeMap X ((LinearMap.ker δ).comap X.subtype)).toEquiv
  rw [LinearMap.card_eq_card_range_mul_card_ker (δ.domRestrict X), hker,
    LinearMap.range_domRestrict, Nat.mul_comm]

theorem card_fixSub_le_two_mul_of_index_two {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V) {A K : Subgroup G}
    (hbest : IsBestOffenderOn ρ A ⊤) (hKA : K ≤ A) (hidx : Nat.card A = 2 * Nat.card K) :
    Nat.card ↥(fixSub ρ K) ≤ 2 * Nat.card ↥(fixSub ρ A) := by
  have : Nonempty V := ⟨0⟩
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have hApos : 0 < Nat.card A := by
    have h := hbest.2 ⊥ bot_le
    rw [Subgroup.card_bot, fixOn_top, fixSub_bot, card_top_submodule, one_mul] at h
    exact pos_of_mul_pos_left (lt_of_lt_of_le hVpos h) (Nat.zero_le _)
  have hKpos : 0 < Nat.card K := by
    by_contra hK
    have hK' : Nat.card K = 0 := Nat.eq_zero_of_le_zero (not_lt.mp hK)
    have hA0 : Nat.card A = 0 := by rw [hidx, hK', mul_zero]
    exact hApos.ne' hA0
  have h := hbest.2 K hKA
  rw [fixOn_top, fixOn_top, hidx] at h
  have hcanon : Nat.card K * Nat.card ↥(fixSub ρ K) ≤
      Nat.card K * (2 * Nat.card ↥(fixSub ρ A)) := by
    calc Nat.card K * Nat.card ↥(fixSub ρ K)
        ≤ 2 * Nat.card K * Nat.card ↥(fixSub ρ A) := h
      _ = Nat.card K * (2 * Nat.card ↥(fixSub ρ A)) := by ring
  exact Nat.le_of_mul_le_mul_left hcanon hKpos

theorem card_mul_le_of_bestOffender_fixes {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V) {A K B : Subgroup G}
    (hbest : IsBestOffenderOn ρ A ⊤) (hKA : K ≤ A) (hBK : B ≤ K)
    (heq : Nat.card K * Nat.card ↥(fixSub ρ K) = Nat.card A * Nat.card ↥(fixSub ρ A))
    (I : Submodule (ZMod 2) V) (hBI : ∀ b ∈ B, ∀ v ∈ I, ρ b v = v) :
    Nat.card ↥I * Nat.card B ≤ Nat.card K * Nat.card ↥(I ⊓ fixSub ρ K) := by
  have hSle : fixSub ρ K ≤ fixSub ρ B := fixSub_antitone hBK
  have hIle : I ≤ fixSub ρ B := fun v hv b hb => hBI b hb v hv
  have hcard_sup : Nat.card ↥(I ⊔ fixSub ρ K) ≤ Nat.card ↥(fixSub ρ B) :=
    card_le_of_le_submodule (sup_le hIle hSle)
  have hbestB : Nat.card B * Nat.card ↥(fixSub ρ B) ≤
      Nat.card K * Nat.card ↥(fixSub ρ K) := by
    have h := hbest.2 B (hBK.trans hKA)
    rwa [fixOn_top, fixOn_top, ← heq] at h
  have hpos : 0 < Nat.card ↥(fixSub ρ K) := by
    have : Nonempty ↥(fixSub ρ K) := ⟨0, (fixSub ρ K).zero_mem⟩
    exact Nat.card_pos
  have key : Nat.card ↥(fixSub ρ K) * (Nat.card ↥I * Nat.card B) ≤
      Nat.card ↥(fixSub ρ K) * (Nat.card K * Nat.card ↥(I ⊓ fixSub ρ K)) := by
    calc Nat.card ↥(fixSub ρ K) * (Nat.card ↥I * Nat.card B)
        = Nat.card B * (Nat.card ↥I * Nat.card ↥(fixSub ρ K)) := by ring
      _ = Nat.card B * (Nat.card ↥(I ⊓ fixSub ρ K) * Nat.card ↥(I ⊔ fixSub ρ K)) := by
            rw [← card_inf_mul_card_sup I (fixSub ρ K)]
      _ ≤ Nat.card B * (Nat.card ↥(I ⊓ fixSub ρ K) * Nat.card ↥(fixSub ρ B)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcard_sup)
      _ = (Nat.card B * Nat.card ↥(fixSub ρ B)) * Nat.card ↥(I ⊓ fixSub ρ K) := by ring
      _ ≤ (Nat.card K * Nat.card ↥(fixSub ρ K)) * Nat.card ↥(I ⊓ fixSub ρ K) :=
            Nat.mul_le_mul_right _ hbestB
      _ = Nat.card ↥(fixSub ρ K) * (Nat.card K * Nat.card ↥(I ⊓ fixSub ρ K)) := by ring
  exact Nat.le_of_mul_le_mul_left key hpos

end CFSG.LocalAnalysis.RankThreeUC.S15

end
