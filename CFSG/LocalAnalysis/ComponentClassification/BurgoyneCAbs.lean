module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCData

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open CFSG Subgroup
open scoped MatrixGroups

variable {P : Type} [Group P] [Finite P]

@[expose] def TwoInvolutions (N : Subgroup P) : Prop :=
  ∃ a ∈ N, ∃ b ∈ N, orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧ a ≠ b

@[expose] def BlockOK (F : Type) [Field F] [Finite F] (N : Subgroup P) : Prop :=
  Group.IsSolvable N ∨ (IsQuasisimple N ∧ Nat.card SL(2, F) ∣ Nat.card N ∧
    (TwoInvolutions N ∨ Nonempty (N ≃* SL(2, F))))

theorem propCData_false_of_layer {x : P} {R₁ R₂ : Subgroup P} {p n : ℕ} [Fact p.Prime]
    (hC : PropCData x R₁ R₂ p n) {N : Subgroup P}
    (hNH : N ≤ centralizer ({x} : Set P))
    (hperf : ∀ L : Subgroup P, L ≤ centralizer ({x} : Set P) → ⁅L, L⁆ = L → L ≤ N)
    (hN : Group.IsSolvable N ∨ IsQuasisimple N) : False := by
  have hR : ∀ {R : Subgroup P}, R ≤ centralizer ({x} : Set P) →
      IsPComponent 2 (R.subgroupOf (centralizer ({x} : Set P))) → R = N := by
    intro R hRH hR
    have hRN := hperf R hRH (commutator_eq_of_isPComponent hRH hR)
    rcases hN with hs | hq
    · exact (not_le_of_isSolvable hRH hR hs hRN).elim
    · exact eq_of_le_of_isQuasisimple hRN hNH hR hq
  exact hC.card_ne (by rw [hR hC.le₁ hC.comp₁, hR hC.le₂ hC.comp₂])

theorem propCData_false_of_blocks {x : P} {R₁ R₂ : Subgroup P} {p n : ℕ} [Fact p.Prime]
    (hC : PropCData x R₁ R₂ p n) {F : Type} [Field F] [Finite F]
    {N₁ N₂ : Subgroup P} (hN₁ : N₁ ≤ centralizer ({x} : Set P))
    (hN₂ : N₂ ≤ centralizer ({x} : Set P))
    (hs₁ : (N₁.subgroupOf (centralizer ({x} : Set P))).IsSubnormal)
    (hs₂ : (N₂.subgroupOf (centralizer ({x} : Set P))).IsSubnormal)
    (hperf : ∀ L : Subgroup P, L ≤ centralizer ({x} : Set P) → ⁅L, L⁆ = L → L ≤ N₁ ⊔ N₂)
    (hB₁ : BlockOK F N₁) (hB₂ : BlockOK F N₂) : False := by
  have hGF : ringChar (GaloisField p n) ≠ 2 := ringChar_galoisField_ne_two hC.p_ne_two
  have hGF2 : (2 : GaloisField p n) ≠ 0 := two_ne_zero_galoisField hC.p_ne_two
  have hcardGF : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hC.n_pos.ne'
  have hblock : ∀ {L : Subgroup P}, L ≤ centralizer ({x} : Set P) →
      IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set P))) →
      IsQuasisimple L ∧ Nat.card SL(2, F) ∣ Nat.card L ∧
        (TwoInvolutions L ∨ Nonempty (L ≃* SL(2, F))) := by
    intro L hLH hL
    have hsup := hperf L hLH (commutator_eq_of_isPComponent hLH hL)
    have key : ∀ {N : Subgroup P}, N ≤ centralizer ({x} : Set P) → BlockOK F N → L ≤ N →
        IsQuasisimple L ∧ Nat.card SL(2, F) ∣ Nat.card L ∧
          (TwoInvolutions L ∨ Nonempty (L ≃* SL(2, F))) := by
      intro N hNH hB hLN
      rcases hB with hs | ⟨hq, hdvd, h⟩
      · exact (not_le_of_isSolvable hLH hL hs hLN).elim
      · have := eq_of_le_of_isQuasisimple hLN hNH hL hq
        subst this
        exact ⟨hq, hdvd, h⟩
    rcases le_or_le_of_le_sup hLH hL hN₁ hN₂ hs₁ hs₂ hsup with h | h
    · exact key hN₁ hB₁ h
    · exact key hN₂ hB₂ h
  obtain ⟨hq₂, -, h₂⟩ := hblock hC.le₂ hC.comp₂
  obtain ⟨-, hdvd₁, -⟩ := hblock hC.le₁ hC.comp₁
  obtain ⟨e₁⟩ := hC.iso₁
  obtain ⟨e₂⟩ := hC.iso₂
  rcases h₂ with ⟨a, ha, b, hb, hao, hbo, hab, hne⟩ | ⟨⟨f₂⟩⟩
  ·
    apply hne
    have := eq_of_involutions hGF2 e₂ (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
      (by rw [Subgroup.orderOf_mk]; exact hao) (by rw [Subgroup.orderOf_mk]; exact hbo)
      (Subtype.ext hab)
    exact congrArg Subtype.val this
  have hO₂ : pPrimeCore 2 R₂ = ⊥ := pPrimeCore_eq_bot_of_center hq₂
    (a := ⟨x, hC.mem⟩) (by rw [Subgroup.orderOf_mk]; exact hC.orderOf_eq) (by
      intro z hz
      have hz' : f₂ z ∈ center SL(2, F) := by
        rw [mem_center_iff]
        intro g
        obtain ⟨g', rfl⟩ := f₂.surjective g
        rw [← map_mul, ← map_mul, (mem_center_iff.1 hz g')]
      apply f₂.injective
      rw [map_pow, sq_eq_one_of_mem_center_SL hz', map_one])
  have hcardF : Nat.card F = p ^ n := by
    have h1 := card_eq_card_pPrimeCore_mul (R := R₂)
    rw [Nat.card_congr e₂.toEquiv, hO₂, Subgroup.card_bot, one_mul,
      Nat.card_congr f₂.toEquiv] at h1
    rw [← hcardGF]
    exact card_eq_of_card_SL_eq h1
  have h1 := card_eq_card_pPrimeCore_mul (R := R₁)
  rw [Nat.card_congr e₁.toEquiv] at h1
  have hSL : Nat.card SL(2, F) = Nat.card PSL(2, GaloisField p n) * 2 := by
    rw [card_PSL_mul_two hGF, GorensteinWalter.sl2_card_formula,
      GorensteinWalter.sl2_card_formula, hcardF, hcardGF]
  rw [hSL, h1, mul_comm (Nat.card (pPrimeCore 2 R₁))] at hdvd₁
  have hpos : 0 < Nat.card PSL(2, GaloisField p n) := Nat.card_pos
  have h2 : 2 ∣ Nat.card (pPrimeCore 2 R₁) := Nat.dvd_of_mul_dvd_mul_left hpos hdvd₁
  exact (Nat.not_even_iff_odd.2 odd_card_pPrimeCore) (even_iff_two_dvd.2 h2)

end CFSG.ComponentClassification.Burgoyne.C
