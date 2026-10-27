module

import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Generic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28OrthMinusTorus
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Arith
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

theorem minusTwoPow_eq_eight_of_mem {f : ℕ} (h : 504 ∈ orthMinusBlockOrders (2 ^ f)) :
    2 ^ f = 8 := by
  rcases h with ⟨k, -, hk⟩ | ⟨m, -, hm⟩
  · exact ((ordA_eq_504_iff rfl).1 hk.symm).2
  · exact absurd hm.symm (ordTwistedD_ne_504 rfl)

omit [CharP K 2] in
theorem minusLeviBlock_inl_of_504 {f : ℕ} (hK : Nat.card K = 2 ^ f) (l : Fin s)
    (hq : CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c (.inl l)))
    (h504 : Nat.card (↥(orthLeviBlock K r d b c (.inl l)) ⧸
      Subgroup.center ↥(orthLeviBlock K r d b c (.inl l))) = 504) :
    d l.succ - d l.castSucc = 2 ∧ Nat.card K = 8 := by
  change CFSG.Open.IsQuasisimple ↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range at hq
  change Nat.card (↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range ⧸
    Subgroup.center ↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range) = 504 at h504
  have h2 := two_le_of_isQuasisimple_specialLinear
    (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) _).symm hq)
  rw [card_range_toGL_quotient_center (by omega)] at h504
  obtain ⟨h1, h8⟩ := (ordA_eq_504_iff hK).1 h504
  exact ⟨by omega, h8⟩

theorem minusLeviBlock_inr_ne_504 {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (u : Unit)
    (hq : CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c (.inr u))) :
    Nat.card (↥(orthLeviBlock K r d b c (.inr u)) ⧸
      Subgroup.center ↥(orthLeviBlock K r d b c (.inr u))) ≠ 504 := by
  obtain ⟨-, -, h⟩ := card_orthResDer_quotient_center hK hirr hq
  change Nat.card (↥(orthResDer K b c (r - d (Fin.last s))) ⧸
    Subgroup.center ↥(orthResDer K b c (r - d (Fin.last s)))) ≠ 504
  rw [h]
  exact ordTwistedD_ne_504 rfl

omit [Finite K] [CharP K 2] in
theorem minus_four_le_of_two_blocks (hd : OrthCuts r d) {l l' : Fin s} (hne : l ≠ l')
    (h : d l.succ - d l.castSucc = 2) (h' : d l'.succ - d l'.castSucc = 2) : 4 ≤ r := by
  wlog hlt : l < l' generalizing l l'
  · exact this hne.symm h' h (lt_of_le_of_ne (not_lt.1 hlt) hne.symm)
  have h1 := hd.mono.monotone (Fin.succ_le_castSucc_iff.2 hlt)
  have h2 := hd.mono.monotone (Fin.le_last l'.succ)
  have h3 := hd.last
  have h4 := hd.mono (Fin.castSucc_lt_succ (i := l))
  omega

theorem minus_card_eq_eight_and_four_le (hd : OrthCuts r d)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {j₁ j₂ : Fin s ⊕ Unit} (hne : j₁ ≠ j₂)
    (h₁ : CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c j₁) ∧
      Nat.card (↥(orthLeviBlock K r d b c j₁) ⧸
        Subgroup.center ↥(orthLeviBlock K r d b c j₁)) = 504)
    (h₂ : CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c j₂) ∧
      Nat.card (↥(orthLeviBlock K r d b c j₂) ⧸
        Subgroup.center ↥(orthLeviBlock K r d b c j₂)) = 504) :
    Nat.card K = 8 ∧ 4 ≤ r := by
  obtain ⟨f, hK⟩ := orthMinus_card_eq_two_pow (K := K)
  rcases j₁ with l | u
  · rcases j₂ with l' | u'
    · obtain ⟨e₁, e₈⟩ := minusLeviBlock_inl_of_504 hK l h₁.1 h₁.2
      obtain ⟨e₁', -⟩ := minusLeviBlock_inl_of_504 hK l' h₂.1 h₂.2
      exact ⟨e₈, minus_four_le_of_two_blocks hd (fun e => hne (by rw [e])) e₁ e₁'⟩
    · exact absurd h₂.2 (minusLeviBlock_inr_ne_504 hK hirr u' h₂.1)
  · exact absurd h₁.2 (minusLeviBlock_inr_ne_504 hK hirr u h₁.1)

omit [Finite K] in
theorem minus_three_le_pRank {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (ρ : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) ≃* ↥L)
    (hK : Nat.card K = 8) (hr : 4 ≤ r) : 3 ≤ Open.pRank 7 L := by
  have hunits : Nat.card Kˣ = 7 := by rw [Nat.card_units, hK]
  set φ : (Fin 3 → Kˣ) →* Y := L.subtype.comp (ρ.toMonoidHom.comp
    ((orthParab r (minusTailForm K b c) (fun _ : Fin 1 => 0)).subtype.comp
      (minusParabTorus b c 3 (by omega) (by omega)))) with hφ
  refine three_le_pRank_of_torus hunits φ ?_ ?_
  · exact (L.subtype_injective.comp (ρ.injective.comp Subtype.val_injective)).comp
      (minusParabTorus_injective b c 3 (by omega) (by omega))
  · rintro _ ⟨t, rfl⟩
    exact (ρ _).2

theorem minus_exists_levi_data {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (ρ : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) ≃* ↥L)
    (hρ : (P.subgroupOf L).comap ρ.toMonoidHom = orthParab r (minusTailForm K b c) d)
    (hd : OrthCuts r d) (hr : 3 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ β : ↥((P.subgroupOf L).comap ρ.toMonoidHom) →* ∀ j, orthLeviGroup K r d j,
      IsPGroup 2 β.ker ∧ Subgroup.pi Set.univ (orthLeviBlock K r d b c) ≤ β.range ∧
        ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ (orthLeviBlock K r d b c) := by
  rw [hρ]
  exact ⟨orthLeviHom b c hd, isPGroup_ker_orthLeviHom hd,
    pi_orthLeviBlock_le_range hd hr (commutator_orthogonalGroup_quadTail_minus hr hirr),
    commutator_range_orthLeviHom_le hd⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
