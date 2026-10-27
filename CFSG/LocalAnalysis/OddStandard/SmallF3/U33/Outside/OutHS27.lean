module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutHS27Char

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

private theorem natCard_ZmodSq (n : ℕ) :
    Nat.card (Multiplicative (ZMod (2 ^ n) × ZMod (2 ^ n))) = 4 ^ n := by
  have h1 : Nat.card (ZMod (2 ^ n)) = 2 ^ n := Nat.card_zmod _
  calc Nat.card (Multiplicative (ZMod (2 ^ n) × ZMod (2 ^ n)))
      = Nat.card (ZMod (2 ^ n) × ZMod (2 ^ n)) := Nat.card_congr Multiplicative.toAdd
    _ = Nat.card (ZMod (2 ^ n)) * Nat.card (ZMod (2 ^ n)) := Nat.card_prod _ _
    _ = 2 ^ n * 2 ^ n := by simp only [h1]
    _ = 4 ^ n := by rw [← mul_pow]; norm_num

private theorem comm_of_mulEquiv {G H : Type*} [Group G] [CommGroup H]
    (e : G ≃* H) (a b : G) : a * b = b * a := by
  apply e.injective
  rw [map_mul, map_mul]
  exact mul_comm (e a) (e b)

theorem HS27_card32 {T : Type} [Group T] [Finite T] (hT : IsPGroup 2 T) {t : T}
    (ht : orderOf t = 2) (hC : Nonempty (↥(centralizer ({t} : Set T)) ≃* E2 3))
    {α : MulAut T} (hα1 : α ≠ 1) (hα3 : ∃ n : ℕ, orderOf α = 3 ^ n) (hαt : α t = t)
    (h32 : Nat.card T = 32) :
    (commAut α).Normal ∧ commAut α ⊓ zpowers t = ⊥ ∧ commAut α ⊔ zpowers t = ⊤ ∧
      (∀ g : T, α g = g ↔ g ∈ zpowers t) ∧ (commAut α).Characteristic ∧
      (Nonempty (↥(commAut α) ≃* E2 4) ∨ Nonempty (↥(commAut α) ≃* Z4Z4)) := by
  obtain ⟨hN, hinf, hsup, hY⟩ := iv2_2_7 T hT t ht hC α hα1 hα3 hαt
  have hfix : ∀ g : T, α g = g ↔ g ∈ zpowers t :=
    fun g => hs27_fixed hT ht hC hα1 hα3 hαt g
  have hcardT := hs27_card_T hT ht hC hα1 hα3 hαt
  have h16 : Nat.card ↥(commAut α) = 16 := by omega
  have hab : ∀ a ∈ commAut α, ∀ b ∈ commAut α, a * b = b * a := by
    rcases hY with hE | hSLc | hSUc | ⟨n, hn1, hZn⟩
    · intro a ha b hb
      have h := comm_of_mulEquiv hE.some ⟨a, ha⟩ ⟨b, hb⟩
      simpa using h
    · obtain ⟨e⟩ := hSLc
      exfalso
      have hc : Nat.card ↥(commAut α) = 64 :=
        (Nat.card_congr e.toEquiv).trans (L26.sfacts_SylSL3_4).1
      omega
    · obtain ⟨e⟩ := hSUc
      exfalso
      have hc : Nat.card ↥(commAut α) = 64 :=
        (Nat.card_congr e.toEquiv).trans (L26.sfacts_SylSU3_4).1
      omega
    · intro a ha b hb
      have h := comm_of_mulEquiv hZn.some ⟨a, ha⟩ ⟨b, hb⟩
      simpa using h
  have hchar : (commAut α).Characteristic :=
    hs27_char_abelian hT ht hC hα1 hα3 hαt hab (by omega)
  refine ⟨hN, hinf, hsup, hfix, hchar, ?_⟩
  rcases hY with hE | hSLc | hSUc | ⟨n, hn1, hZn⟩
  · exact Or.inl hE
  · obtain ⟨e⟩ := hSLc
    exfalso
    have hc : Nat.card ↥(commAut α) = 64 :=
      (Nat.card_congr e.toEquiv).trans (L26.sfacts_SylSL3_4).1
    omega
  · obtain ⟨e⟩ := hSUc
    exfalso
    have hc : Nat.card ↥(commAut α) = 64 :=
      (Nat.card_congr e.toEquiv).trans (L26.sfacts_SylSU3_4).1
    omega
  · have hc : Nat.card ↥(commAut α) = 4 ^ n :=
      (Nat.card_congr hZn.some.toEquiv).trans (natCard_ZmodSq n)
    have hn : n = 2 := by
      have h : 4 ^ n = 4 ^ 2 := by rw [← hc]; omega
      exact Nat.pow_right_injective (by norm_num) h
    subst hn
    exact Or.inr ⟨hZn.some⟩

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
