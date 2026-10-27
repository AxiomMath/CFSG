module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56G

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_of_sq_eq_one {X : Subgroup G} (hXsq : ∀ c ∈ X, c * c = 1) {c d : G}
    (hc : c ∈ X) (hd : d ∈ X) : c * d = d * c := by
  have h1 := hXsq _ (mul_mem hc hd)
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right (hXsq c hc)
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right (hXsq d hd)
  calc c * d = (c * d)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = d * c := by rw [mul_inv_rev, hci, hdi]

theorem eq_of_mem_four {X : Subgroup G} (hX4 : Nat.card X = 4) (hXsq : ∀ c ∈ X, c * c = 1)
    {x q c : G} (hx : x ∈ X) (hq : q ∈ X) (hx1 : x ≠ 1) (hq1 : q ≠ 1) (hxq : x ≠ q)
    (hc : c ∈ X) : c = x * q ∨ c = x ∨ c = q ∨ c = 1 := by
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions x q (hXsq x hx) (hXsq q hq)
    (commute_of_sq_eq_one hXsq hx hq) with hV
  have hVmem : ∀ e, e ∈ V ↔ e = x * q ∨ e = x ∨ e = q ∨ e = 1 := fun e => by
    change e ∈ ({x * q, x, q, 1} : Set G) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hV4 : Nat.card V = 4 := (GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    x q (hXsq x hx) (hXsq q hq) hx1 hq1 hxq (commute_of_sq_eq_one hXsq hx hq)).card_four
  have hVX : V ≤ X := fun e he => by
    rcases (hVmem e).mp he with rfl | rfl | rfl | rfl
    · exact mul_mem hx hq
    · exact hx
    · exact hq
    · exact one_mem _
  have heq : V = X := eq_of_le_of_card_ge hVX (by rw [hX4, hV4])
  exact (hVmem c).mp (heq ▸ hc)

omit [Finite G] in
theorem commute_of_mem_sup_abelian {X X' : Subgroup G}
    (hcomm : ∀ c ∈ X, ∀ d ∈ X', c * d = d * c) (hXc : ∀ c ∈ X, ∀ d ∈ X, c * d = d * c)
    (hX'c : ∀ c ∈ X', ∀ d ∈ X', c * d = d * c) {a b : G} (ha : a ∈ X ⊔ X')
    (hb : b ∈ X ⊔ X') : a * b = b * a := by
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_commute hcomm ha
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mul_of_mem_sup_commute hcomm hb
  calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
    _ = a₁ * (b₁ * a₂) * b₂ := by rw [← hcomm b₁ hb₁ a₂ ha₂]
    _ = (a₁ * b₁) * (a₂ * b₂) := by group
    _ = (b₁ * a₁) * (b₂ * a₂) := by rw [hXc a₁ ha₁ b₁ hb₁, hX'c a₂ ha₂ b₂ hb₂]
    _ = b₁ * (a₁ * b₂) * a₂ := by group
    _ = b₁ * (b₂ * a₁) * a₂ := by rw [hcomm a₁ ha₁ b₂ hb₂]
    _ = b₁ * b₂ * (a₁ * a₂) := by group

theorem gen4_of_wreath_four (hMW : MacWilliamsStatement) {T S X X' : Subgroup G}
    (hT : IsSylowOf 2 T ⊤) (hST : S ≤ T) (hXS : X ≤ S) (hX'S : X' ≤ S)
    (hcomm : ∀ c ∈ X, ∀ d ∈ X', c * d = d * c) (hbot : X ⊓ X' = ⊥)
    (hX4 : Nat.card X = 4) (hX'4 : Nat.card X' = 4) (hXsq : ∀ c ∈ X, c * c = 1)
    (hX'sq : ∀ c ∈ X', c * c = 1) (hS32 : Nat.card S = 32)
    (hXn : ∀ g ∈ S, ∀ c ∈ X, g * c * g⁻¹ ∈ X) (hX'n : ∀ g ∈ S, ∀ c ∈ X', g * c * g⁻¹ ∈ X')
    {x x' : G} (hxX : x ∈ X) (hx'X' : x' ∈ X') (hx1 : x ≠ 1) (hx'1 : x' ≠ 1)
    (hxZ : ∀ g ∈ S, g * x = x * g) (hx'Z : ∀ g ∈ S, g * x' = x' * g)
    (hXnc : ∃ g ∈ S, ∃ c ∈ X, g * c ≠ c * g) (hX'nc : ∃ g ∈ S, ∃ c ∈ X', g * c ≠ c * g)
    (hCx : ∀ y ∈ T, y * x = x * y → y ∈ S) : GH74.Gen4 G := by
  have hXc : ∀ c ∈ X, ∀ d ∈ X, c * d = d * c := fun c hc d hd =>
    commute_of_sq_eq_one hXsq hc hd
  have hX'c : ∀ c ∈ X', ∀ d ∈ X', c * d = d * c := fun c hc d hd =>
    commute_of_sq_eq_one hX'sq hc hd
  have hAc : ∀ a ∈ X ⊔ X', ∀ b ∈ X ⊔ X', a * b = b * a := fun a ha b hb =>
    commute_of_mem_sup_abelian hcomm hXc hX'c ha hb
  have hAS : X ⊔ X' ≤ S := sup_le hXS hX'S
  have hA16 : Nat.card ↥(X ⊔ X') = 16 := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer X X'
      (le_normalizer_of_commute hcomm) (disjoint_iff.mpr hbot), hX4, hX'4]
  have hidx : Nat.card S = 2 * Nat.card ↥(X ⊔ X') := by rw [hS32, hA16]
  have hmul : ∀ y ∈ S, ∀ g ∈ S, y ∉ X ⊔ X' → g ∉ X ⊔ X' → y * g ∈ X ⊔ X' :=
    fun y hy g hg hyA hgA => mul_mem_of_card_eq_two_mul hAS hidx hy hg hyA hgA
  obtain ⟨g, hgS, hgA⟩ : ∃ g ∈ S, g ∉ X ⊔ X' := by
    by_contra hno
    push Not at hno
    have h1 := card_le_of_le (show S ≤ X ⊔ X' from hno)
    omega
  have hmove : ∀ Y : Subgroup G, Y ≤ X ⊔ X' → (∃ g' ∈ S, ∃ c ∈ Y, g' * c ≠ c * g') →
      ∃ q ∈ Y, g * q ≠ q * g := by
    intro Y hYA hYnc
    obtain ⟨g', hg'S, c, hcY, hgc⟩ := hYnc
    by_contra hall
    push Not at hall
    have hg'A : g' ∉ X ⊔ X' := fun h1 => hgc (hAc _ h1 _ (hYA hcY))
    have h1 := hmul g' hg'S g⁻¹ (inv_mem hgS) hg'A (fun h2 => hgA (by
      have h3 := inv_mem h2
      rwa [inv_inv] at h3))
    apply hgc
    calc g' * c = (g' * g⁻¹) * (g * c) := by group
      _ = (g' * g⁻¹) * (c * g) := by rw [hall c hcY]
      _ = c * (g' * g⁻¹) * g := by rw [← mul_assoc, hAc _ h1 _ (hYA hcY)]
      _ = c * g' := by group
  obtain ⟨q, hqX, hgq⟩ := hmove X le_sup_left hXnc
  obtain ⟨q', hq'X', hgq'⟩ := hmove X' le_sup_right hX'nc
  have hq1 : q ≠ 1 := fun h1 => hgq (by rw [h1, mul_one, one_mul])
  have hqx : x ≠ q := fun h1 => hgq (by rw [← h1]; exact hxZ g hgS)
  have hq'1 : q' ≠ 1 := fun h1 => hgq' (by rw [h1, mul_one, one_mul])
  have hq'x' : x' ≠ q' := fun h1 => hgq' (by rw [← h1]; exact hx'Z g hgS)
  have htrans : ∀ (Y : Subgroup G) (y p : G), Nat.card Y = 4 → (∀ c ∈ Y, c * c = 1) →
      (∀ c ∈ Y, g * c * g⁻¹ ∈ Y) → y ∈ Y → p ∈ Y → y ≠ 1 → p ≠ 1 → y ≠ p →
      g * y = y * g → g * p ≠ p * g → g * p * g⁻¹ = y * p := by
    intro Y y p hY4 hYsq hYn hy hp hy1 hp1 hyp hgy hgp
    rcases eq_of_mem_four hY4 hYsq hy hp hy1 hp1 hyp (hYn p hp) with h1 | h1 | h1 | h1
    · exact h1
    · exfalso
      have h2 : g * y * g⁻¹ = y := by rw [hgy, mul_inv_cancel_right]
      apply hyp
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = g⁻¹ * y * g := by rw [h2]
        _ = g⁻¹ * (g * p * g⁻¹) * g := by rw [h1]
        _ = p := by group
    · exfalso
      exact hgp (by calc g * p = g * p * g⁻¹ * g := by group
        _ = p * g := by rw [h1])
    · exfalso
      exact hp1 (by calc p = g⁻¹ * (g * p * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group)
  have hgqx := htrans X x q hX4 hXsq (fun c hc => hXn g hgS c hc) hxX hqX hx1 hq1 hqx
    (hxZ g hgS) hgq
  have hgq'x' := htrans X' x' q' hX'4 hX'sq (fun c hc => hX'n g hgS c hc) hx'X' hq'X' hx'1
    hq'1 hq'x' (hx'Z g hgS) hgq'
  have hfix : ∀ (Y : Subgroup G) (y p c : G), Nat.card Y = 4 → (∀ c ∈ Y, c * c = 1) →
      y ∈ Y → p ∈ Y → y ≠ 1 → p ≠ 1 → y ≠ p → g * y = y * g →
      g * p * g⁻¹ = y * p → c ∈ Y → g * c * g⁻¹ = c → c = y ∨ c = 1 := by
    intro Y y p c hY4 hYsq hy hp hy1 hp1 hyp hgy hgp hc hgc
    rcases eq_of_mem_four hY4 hYsq hy hp hy1 hp1 hyp hc with h1 | h1 | h1 | h1
    · exfalso
      rw [h1] at hgc
      have h2 : g * (y * p) * g⁻¹ = p := by
        rw [show g * (y * p) * g⁻¹ = g * y * g⁻¹ * (g * p * g⁻¹) by group, hgp,
          show g * y * g⁻¹ = y by rw [hgy, mul_inv_cancel_right], ← mul_assoc, hYsq y hy,
          one_mul]
      rw [h2] at hgc
      apply hy1
      calc y = y * p * p⁻¹ := by group
        _ = 1 := by rw [← hgc, mul_inv_cancel]
    · exact Or.inl h1
    · exfalso
      rw [h1, hgp] at hgc
      apply hy1
      calc y = y * p * p⁻¹ := by group
        _ = 1 := by rw [hgc, mul_inv_cancel]
    · exact Or.inr h1
  have hCA : ∀ c ∈ X ⊔ X', g * c = c * g → c = x * x' ∨ c = x ∨ c = x' ∨ c = 1 := by
    intro c hc hgc
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := exists_mul_of_mem_sup_commute hcomm hc
    have h1 : g * c₁ * g⁻¹ * (g * c₂ * g⁻¹) = c₁ * c₂ := by
      calc g * c₁ * g⁻¹ * (g * c₂ * g⁻¹) = g * (c₁ * c₂) * g⁻¹ := by group
        _ = c₁ * c₂ := by rw [hgc, mul_inv_cancel_right]
    obtain ⟨e₁, e₂⟩ := eq_of_mul_eq_mul_of_disjoint hbot (hXn g hgS c₁ hc₁) hc₁
      (hX'n g hgS c₂ hc₂) hc₂ h1
    rcases hfix X x q c₁ hX4 hXsq hxX hqX hx1 hq1 hqx (hxZ g hgS) hgqx hc₁ e₁ with f₁ | f₁ <;>
      rcases hfix X' x' q' c₂ hX'4 hX'sq hx'X' hq'X' hx'1 hq'1 hq'x' (hx'Z g hgS) hgq'x' hc₂ e₂
        with f₂ | f₂ <;> rw [f₁, f₂]
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (mul_one x))
    · exact Or.inr (Or.inr (Or.inl (one_mul x')))
    · exact Or.inr (Or.inr (Or.inr (one_mul 1)))
  have hAsq : ∀ a ∈ X ⊔ X', a * a = 1 := by
    intro a ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_commute hcomm ha
    rw [show a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ by group, ← hcomm a₁ ha₁ a₂ ha₂,
      show a₁ * (a₁ * a₂) * a₂ = (a₁ * a₁) * (a₂ * a₂) by group, hXsq a₁ ha₁, hX'sq a₂ ha₂,
      one_mul]
  have hgg : g * g ∈ X ⊔ X' := hmul g hgS g hgS hgA hgA
  have hqxq : q * (x * q) = x := by
    rw [← mul_assoc, hXc q hqX x hxX, mul_assoc, hXsq q hqX, mul_one]
  have hq'x'q' : q' * (x' * q') = x' := by
    rw [← mul_assoc, hX'c q' hq'X' x' hx'X', mul_assoc, hX'sq q' hq'X', mul_one]
  have hc : ∃ c ∈ X ⊔ X', c * (g * c * g⁻¹) = g * g := by
    rcases hCA _ hgg (by group) with h1 | h1 | h1 | h1 <;> rw [h1]
    · refine ⟨q * q', mul_mem (mem_sup_left hqX) (mem_sup_right hq'X'), ?_⟩
      rw [show g * (q * q') * g⁻¹ = g * q * g⁻¹ * (g * q' * g⁻¹) by group, hgqx, hgq'x',
        show q * q' * (x * q * (x' * q')) = q * (q' * (x * q)) * (x' * q') by group,
        ← hcomm (x * q) (mul_mem hxX hqX) q' hq'X',
        show q * (x * q * q') * (x' * q') = (q * (x * q)) * (q' * (x' * q')) by group,
        hqxq, hq'x'q']
    · exact ⟨q, mem_sup_left hqX, by rw [hgqx, hqxq]⟩
    · exact ⟨q', mem_sup_right hq'X', by rw [hgq'x', hq'x'q']⟩
    · exact ⟨1, one_mem _, by group⟩
  obtain ⟨c, hcA, hcg⟩ := hc
  have hg₀S : c * g ∈ S := mul_mem (hAS hcA) hgS
  have hg₀A : c * g ∉ X ⊔ X' := fun h1 => hgA (by
    have h2 := mul_mem (inv_mem hcA) h1
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2)
  have hg₀2 : c * g * (c * g) = 1 := by
    calc c * g * (c * g) = c * (g * c * g⁻¹) * (g * g) := by group
      _ = (g * g) * (g * g) := by rw [hcg]
      _ = 1 := hAsq _ hgg
  have hcomm₀ : ∀ w ∈ X ⊔ X', w * (c * g) = c * g * w → g * w = w * g := by
    intro w hw hw₀
    have h1 : c * (w * g) = c * (g * w) := by
      calc c * (w * g) = (c * w) * g := (mul_assoc _ _ _).symm
        _ = (w * c) * g := by rw [hAc c hcA w hw]
        _ = w * (c * g) := mul_assoc _ _ _
        _ = c * g * w := hw₀
        _ = c * (g * w) := mul_assoc _ _ _
    exact (mul_left_cancel h1).symm
  have hxx' : x ≠ x' := fun h1 => hx1 (by
    have h2 : x ∈ X ⊓ X' := mem_inf.mpr ⟨hxX, h1 ▸ hx'X'⟩
    rwa [hbot, mem_bot] at h2)
  have he₃ : ¬ (c * g = x * x' ∨ c * g = x ∨ c * g = x' ∨ c * g = 1) := by
    rintro (h1 | h1 | h1 | h1) <;> apply hg₀A <;> rw [h1]
    · exact mul_mem (mem_sup_left hxX) (mem_sup_right hx'X')
    · exact mem_sup_left hxX
    · exact mem_sup_right hx'X'
    · exact one_mem _
  refine gen4_of_three_involutions hMW hT (hST (hXS hxX)) (hST (hX'S hx'X')) (hST hg₀S)
    (hXsq x hxX) (hX'sq x' hx'X') hg₀2 (hcomm x hxX x' hx'X') (hxZ _ hg₀S).symm
    (hx'Z _ hg₀S).symm hx1 hx'1 hxx' he₃ fun y hyT hy₁ hy₂ hy₃ => ?_
  have hyS := hCx y hyT hy₁
  by_cases hyA : y ∈ X ⊔ X'
  · exact Or.inl (hCA y hyA (hcomm₀ y hyA hy₃))
  · have hw := hmul y hyS _ hg₀S hyA hg₀A
    refine Or.inr (hCA _ hw (hcomm₀ _ hw ?_))
    calc y * (c * g) * (c * g) = y * (c * g * (c * g)) := mul_assoc _ _ _
      _ = y := by rw [hg₀2, mul_one]
      _ = c * g * (c * g) * y := by rw [hg₀2, one_mul]
      _ = c * g * (c * g * y) := mul_assoc _ _ _
      _ = c * g * (y * (c * g)) := by rw [hy₃]

end CFSG.ComponentClassification.Foote5
