module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixSModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem card_sup_eq_mul_of_le_normalizer_sixS {X : Type*} [Group X] {A B : Subgroup X}
    (hB : B ≤ normalizer (A : Set X)) (hinf : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup X) = Nat.card A * Nat.card B := by
  have h := card_sup_mul_card_inf_of_le_normalizer_sOne hB
  rwa [hinf, Subgroup.card_bot, mul_one] at h

variable {n : ℕ} {K : Type*} [Field K]

theorem pointRadOn_le_normalizer_insert_sixS {a b : Fin n} (hab : a ≠ b) {S : Finset (Fin n)}
    (haS : a ∉ S) :
    pointRadOn (K := K) b S ≤
      normalizer (pointRadOn (K := K) a (insert b S) : Set (LinearFlag.projectiveSL n K)) :=
  (pointRadOn_le_blockSL b S).trans
    (blockSL_le_normalizer_pointRadOn_sixS (by simp [hab, haS]) subset_rfl)

theorem card_jGroup_sixS (hK : Nat.card K = 2) {a b : Fin n} (hab : a ≠ b)
    {S : Finset (Fin n)} (haS : a ∉ S) (hbS : b ∉ S) :
    Nat.card (pointRadOn (K := K) a (insert b S) ⊔ pointRadOn b S : Subgroup _) =
      2 ^ (S.card + 1) * 2 ^ S.card := by
  rw [card_sup_eq_mul_of_le_normalizer_sixS (pointRadOn_le_normalizer_insert_sixS hab haS)
    (pointRadOn_inf_pointRadOn_eq_bot_sixS hK hab _ _), card_pointRadOn hK a (by simp [hab, haS]),
    card_pointRadOn hK b hbS, Finset.card_insert_of_notMem hbS]

theorem fGroup_le_blockSL_sixS (d₁ d₂ d₃ : Fin n) :
    pointRadOn (K := K) d₁ {d₂, d₃} ⊔ pointRadOn d₂ {d₃} ≤ blockSL {d₁, d₂, d₃} :=
  sup_le (pointRadOn_le_blockSL d₁ _)
    ((pointRadOn_le_blockSL d₂ _).trans (blockSL_mono (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto)))

theorem card_fGroup_sixS (hK : Nat.card K = 2) {d₁ d₂ d₃ : Fin n} (h12 : d₁ ≠ d₂)
    (h13 : d₁ ≠ d₃) (h23 : d₂ ≠ d₃) :
    Nat.card (pointRadOn (K := K) d₁ {d₂, d₃} ⊔ pointRadOn d₂ {d₃} : Subgroup _) = 2 ^ 3 := by
  have hN : pointRadOn (K := K) d₂ {d₃} ≤
      normalizer (pointRadOn (K := K) d₁ {d₂, d₃} : Set (LinearFlag.projectiveSL n K)) :=
    (pointRadOn_le_blockSL d₂ _).trans
      (blockSL_le_normalizer_pointRadOn_sixS (by simp [h12, h13]) subset_rfl)
  rw [card_sup_eq_mul_of_le_normalizer_sixS hN (pointRadOn_inf_pointRadOn_eq_bot_sixS hK h12 _ _),
    card_pointRadOn hK d₁ (by simp [h12, h13]), card_pointRadOn hK d₂ (by simp [h23]),
    Finset.card_pair h23, Finset.card_singleton]
  norm_num

theorem blockSL_le_normalizer_jGroup_sixS {a b : Fin n} {S : Finset (Fin n)} (haS : a ∉ S)
    (hbS : b ∉ S) :
    blockSL (K := K) S ≤ normalizer ((pointRadOn (K := K) a (insert b S) ⊔ pointRadOn b S :
      Subgroup _) : Set (LinearFlag.projectiveSL n K)) := by
  intro g hg
  exact Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨blockSL_le_normalizer_pointRadOn_sixS haS (Finset.subset_insert b S) hg,
      blockSL_le_normalizer_pointRadOn_sixS hbS subset_rfl hg⟩

theorem card_unitriangular_sixS (hK : Nat.card K = 2) {a b d₁ d₂ d₃ : Fin n} (hab : a ≠ b)
    (h12 : d₁ ≠ d₂) (h13 : d₁ ≠ d₃) (h23 : d₂ ≠ d₃) (ha1 : a ≠ d₁) (ha2 : a ≠ d₂)
    (ha3 : a ≠ d₃) (hb1 : b ≠ d₁) (hb2 : b ≠ d₂) (hb3 : b ≠ d₃) :
    Nat.card ((pointRadOn (K := K) a (insert b {d₁, d₂, d₃}) ⊔ pointRadOn b {d₁, d₂, d₃}) ⊔
      (pointRadOn d₁ {d₂, d₃} ⊔ pointRadOn d₂ {d₃}) : Subgroup _) = 2 ^ 10 := by
  have haS : a ∉ ({d₁, d₂, d₃} : Finset (Fin n)) := by simp [ha1, ha2, ha3]
  have hbS : b ∉ ({d₁, d₂, d₃} : Finset (Fin n)) := by simp [hb1, hb2, hb3]
  have hS3 : ({d₁, d₂, d₃} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
  have hle := fGroup_le_blockSL_sixS (K := K) d₁ d₂ d₃
  have hN := hle.trans (blockSL_le_normalizer_jGroup_sixS haS hbS)
  have hinf : (pointRadOn (K := K) a (insert b {d₁, d₂, d₃}) ⊔ pointRadOn b {d₁, d₂, d₃}) ⊓
      (pointRadOn d₁ {d₂, d₃} ⊔ pointRadOn d₂ {d₃}) = ⊥ := by
    rw [eq_bot_iff]
    refine le_trans (inf_le_inf_left _ hle) ?_
    rw [pointRadOn_sup_inf_blockSL_eq_bot_sixS hK hab haS haS hbS]
  rw [card_sup_eq_mul_of_le_normalizer_sixS hN hinf, card_jGroup_sixS hK hab haS hbS, hS3,
    card_fGroup_sixS hK h12 h13 h23]
  norm_num

end CFSG.SeitzReduction.LinearPilot
