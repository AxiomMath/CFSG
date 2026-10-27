module


import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

section Count

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_iff (hcomm : ∀ a b : G, a * b = b * a) (hsq : ∀ a : G, a * a = 1)
    (A : Subgroup G) (g x : G) : x ∈ A ⊔ Subgroup.zpowers g ↔ x ∈ A ∨ x * g ∈ A := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hsq g)
  constructor
  · intro hx
    let B : Subgroup G :=
      { carrier := {x | x ∈ A ∨ x * g ∈ A}
        mul_mem' := by
          rintro x y (hx | hx) (hy | hy)
          · exact Or.inl (A.mul_mem hx hy)
          · exact Or.inr (by rw [mul_assoc]; exact A.mul_mem hx hy)
          · refine Or.inr ?_
            have : x * y * g = x * g * y := by rw [mul_assoc, hcomm y g, ← mul_assoc]
            rw [this]
            exact A.mul_mem hx hy
          · refine Or.inl ?_
            have : x * y = x * g * (y * g) := by
              rw [mul_assoc x g (y * g), ← mul_assoc g y g, hcomm g y, mul_assoc y g g, hsq g, mul_one]
            rw [this]
            exact A.mul_mem hx hy
        one_mem' := Or.inl A.one_mem
        inv_mem' := by
          rintro x (hx | hx)
          · exact Or.inl (A.inv_mem hx)
          · refine Or.inr ?_
            have : x⁻¹ * g = (x * g)⁻¹ := by rw [mul_inv_rev, hginv, hcomm]
            rw [this]
            exact A.inv_mem hx }
    have hAB : A ≤ B := fun a ha => Or.inl ha
    have hgB : Subgroup.zpowers g ≤ B :=
      Subgroup.zpowers_le.mpr (Or.inr (by rw [hsq g]; exact A.one_mem))
    exact sup_le hAB hgB hx
  · rintro (hx | hx)
    · exact Subgroup.mem_sup_left hx
    · have : x = (x * g) * g⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers g)))

theorem card_sup_zpowers_ge [Finite G] {A : Subgroup G} {g : G} (hg : g ∉ A) :
    2 * Nat.card A ≤ Nat.card ↥(A ⊔ Subgroup.zpowers g) := by
  have hle : A ≤ A ⊔ Subgroup.zpowers g := le_sup_left
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    have heq : A = A ⊔ Subgroup.zpowers g :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hk, mul_one])
    exact hg (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  have hk0 : k ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := ↥(A ⊔ Subgroup.zpowers g))
    rw [hk, mul_zero] at this
    exact lt_irrefl _ this
  have hk2 : 2 ≤ k := by omega
  rw [hk, mul_comm]
  exact Nat.mul_le_mul_left _ hk2

theorem card_ge_32_aux [Finite G] (hcomm : ∀ a b : G, a * b = b * a) (hsq : ∀ a : G, a * a = 1)
    {t e₀ e₁ e₂ f₀ f₁ f₂ : G} (ht : t ≠ 1) (hE : e₀ * e₁ * e₂ = t) (hF : f₀ * f₁ * f₂ = t)
    (h0 : e₀ ≠ 1 ∧ e₀ ≠ t) (h1 : e₁ ≠ 1 ∧ e₁ ≠ t ∧ e₁ ≠ e₀ ∧ e₁ ≠ t * e₀)
    (hf : ∀ x ∈ ({f₀, f₁, f₂} : Set G), x ≠ 1 ∧ x ≠ t ∧ x ≠ e₀ ∧ x ≠ e₁ ∧ x ≠ e₂ ∧ x ≠ t * e₀ ∧
      x ≠ t * e₁ ∧ x ≠ t * e₂) : 32 ≤ Nat.card G := by
  classical
  letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  have hinv : ∀ a : G, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hsq a)
  have key : ∀ a b : G, a * b = 1 → a = b := fun a b h => by
    rw [mul_eq_one_iff_eq_inv, hinv] at h
    exact h
  have hmem := mem_sup_zpowers_iff hcomm hsq
  have peel : ∀ x a b : G, x * a = b → x = b * a := fun x a b h => by
    rw [← h, mul_assoc, hsq, mul_one]
  have he₂ : e₂ = e₀ * e₁ * t := by
    rw [← hE]
    calc e₂ = (e₀ * e₀) * (e₁ * e₁) * e₂ := by rw [hsq, hsq, one_mul, one_mul]
      _ = e₀ * e₁ * (e₀ * e₁ * e₂) := by ac_rfl
  have ht2e : t * e₂ = e₀ * e₁ := by
    rw [he₂]
    calc t * (e₀ * e₁ * t) = e₀ * e₁ * (t * t) := by ac_rfl
      _ = e₀ * e₁ := by rw [hsq, mul_one]
  have hf₂ : f₂ = f₀ * f₁ * t := by
    rw [← hF]
    calc f₂ = (f₀ * f₀) * (f₁ * f₁) * f₂ := by rw [hsq, hsq, one_mul, one_mul]
      _ = f₀ * f₁ * (f₀ * f₁ * f₂) := by ac_rfl
  set A₁ : Subgroup G := ⊥ ⊔ Subgroup.zpowers t with hA₁
  set A₂ : Subgroup G := A₁ ⊔ Subgroup.zpowers e₀ with hA₂
  set A₃ : Subgroup G := A₂ ⊔ Subgroup.zpowers e₁ with hA₃
  set A₄ : Subgroup G := A₃ ⊔ Subgroup.zpowers f₀ with hA₄
  set A₅ : Subgroup G := A₄ ⊔ Subgroup.zpowers f₁ with hA₅
  have mA₁ : ∀ x : G, x ∈ A₁ ↔ x = 1 ∨ x * t = 1 := fun x => by
    rw [hA₁, hmem, Subgroup.mem_bot, Subgroup.mem_bot]
  have mA₂ : ∀ x : G, x ∈ A₂ ↔ x ∈ A₁ ∨ x * e₀ ∈ A₁ := fun x => by rw [hA₂]; exact hmem _ _ _
  have mA₃ : ∀ x : G, x ∈ A₃ ↔ x ∈ A₂ ∨ x * e₁ ∈ A₂ := fun x => by rw [hA₃]; exact hmem _ _ _
  have mA₄ : ∀ x : G, x ∈ A₄ ↔ x ∈ A₃ ∨ x * f₀ ∈ A₃ := fun x => by rw [hA₄]; exact hmem _ _ _
  have hA₁₂ : A₁ ≤ A₂ := le_sup_left
  have hA₂₃ : A₂ ≤ A₃ := le_sup_left
  have htA₃ : t ∈ A₃ := hA₂₃ (hA₁₂ ((mA₁ t).mpr (Or.inr (hsq t))))
  have hn₀ : e₀ ∉ A₁ := by
    rw [mA₁]
    rintro (h | h)
    · exact h0.1 h
    · exact h0.2 (key _ _ h)
  have hn₁ : e₁ ∉ A₂ := by
    rw [mA₂, mA₁, mA₁]
    rintro ((h | h) | (h | h))
    · exact h1.1 h
    · exact h1.2.1 (key _ _ h)
    · exact h1.2.2.1 (key _ _ h)
    · exact h1.2.2.2 (peel _ _ _ (key _ _ h))
  have hA3mem : ∀ x ∈ A₃, x = 1 ∨ x = t ∨ x = e₀ ∨ x = e₁ ∨ x = e₂ ∨ x = t * e₀ ∨ x = t * e₁ ∨
      x = t * e₂ := by
    intro x hx
    rw [mA₃, mA₂, mA₂, mA₁, mA₁, mA₁, mA₁] at hx
    rcases hx with ((h | h) | (h | h)) | ((h | h) | (h | h))
    · exact Or.inl h
    · exact Or.inr (Or.inl (key _ _ h))
    · exact Or.inr (Or.inr (Or.inl (key _ _ h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (peel _ _ _ (key _ _ h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (key _ _ h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (peel _ _ _ (key _ _ h))))))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
      rw [ht2e, peel _ _ _ (key _ _ h)]
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      have h' := peel _ _ _ (peel _ _ _ (key _ _ h))
      rw [h', he₂]
      ac_rfl
  have hnot : ∀ x ∈ ({f₀, f₁, f₂} : Set G), x ∉ A₃ := by
    intro x hx hxA
    have hx' := hf x hx
    rcases hA3mem x hxA with h | h | h | h | h | h | h | h
    · exact hx'.1 h
    · exact hx'.2.1 h
    · exact hx'.2.2.1 h
    · exact hx'.2.2.2.1 h
    · exact hx'.2.2.2.2.1 h
    · exact hx'.2.2.2.2.2.1 h
    · exact hx'.2.2.2.2.2.2.1 h
    · exact hx'.2.2.2.2.2.2.2 h
  have hnf₀ : f₀ ∉ A₃ := hnot f₀ (by simp)
  have hnf₁ : f₁ ∉ A₄ := by
    rw [mA₄]
    rintro (h | h)
    · exact hnot f₁ (by simp) h
    · apply hnot f₂ (by simp)
      rw [hf₂]
      have : f₀ * f₁ * t = t * (f₁ * f₀) := by ac_rfl
      rw [this]
      exact A₃.mul_mem htA₃ h
  have c1 : 2 ≤ Nat.card A₁ := by
    have := card_sup_zpowers_ge (A := (⊥ : Subgroup G)) (g := t) (by simpa using ht)
    rwa [Subgroup.card_bot, mul_one] at this
  have c2 : 2 * Nat.card A₁ ≤ Nat.card A₂ := card_sup_zpowers_ge hn₀
  have c3 : 2 * Nat.card A₂ ≤ Nat.card A₃ := card_sup_zpowers_ge hn₁
  have c4 : 2 * Nat.card A₃ ≤ Nat.card A₄ := card_sup_zpowers_ge hnf₀
  have c5 : 2 * Nat.card A₄ ≤ Nat.card A₅ := card_sup_zpowers_ge hnf₁
  have c6 : Nat.card A₅ ≤ Nat.card G := Subgroup.card_le_card_group A₅
  omega

theorem card_ge_32 {Y : Type*} [Group Y] [Finite Y] {Z : Subgroup Y}
    (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hsq : ∀ a ∈ Z, a * a = 1) {t : Y} (htZ : t ∈ Z)
    (ht : t ≠ 1) (e f : ℕ → Y) (heZ : ∀ i, e i ∈ Z) (hfZ : ∀ i, f i ∈ Z)
    (hE : e 0 * e 1 * e 2 = t) (hF : f 0 * f 1 * f 2 = t)
    (h0 : e 0 ≠ 1 ∧ e 0 ≠ t) (h1 : e 1 ≠ 1 ∧ e 1 ≠ t ∧ e 1 ≠ e 0 ∧ e 1 ≠ t * e 0)
    (hf : ∀ l, l < 3 → f l ≠ 1 ∧ f l ≠ t) (hfe : ∀ l i, l < 3 → i < 3 → f l ≠ e i)
    (hfte : ∀ l i, l < 3 → i < 3 → f l ≠ t * e i) : 32 ≤ Nat.card Z := by
  have hsq' : ∀ a : ↥Z, a * a = 1 := fun a => Subtype.ext (hsq a a.2)
  have hcomm' : ∀ a b : ↥Z, a * b = b * a := fun a b => Subtype.ext (hcomm a a.2 b b.2)
  have key : ∀ l, l < 3 → (⟨f l, hfZ l⟩ : ↥Z) ≠ 1 ∧ (⟨f l, hfZ l⟩ : ↥Z) ≠ ⟨t, htZ⟩ ∧
      (⟨f l, hfZ l⟩ : ↥Z) ≠ ⟨e 0, heZ 0⟩ ∧ (⟨f l, hfZ l⟩ : ↥Z) ≠ ⟨e 1, heZ 1⟩ ∧
      (⟨f l, hfZ l⟩ : ↥Z) ≠ ⟨e 2, heZ 2⟩ ∧
      (⟨f l, hfZ l⟩ : ↥Z) ≠ ⟨t, htZ⟩ * ⟨e 0, heZ 0⟩ ∧ (⟨f l, hfZ l⟩ : ↥Z) ≠ ⟨t, htZ⟩ * ⟨e 1, heZ 1⟩ ∧
      (⟨f l, hfZ l⟩ : ↥Z) ≠ ⟨t, htZ⟩ * ⟨e 2, heZ 2⟩ := fun l hl =>
    ⟨fun h => (hf l hl).1 (congrArg Subtype.val h), fun h => (hf l hl).2 (congrArg Subtype.val h),
      fun h => hfe l 0 hl (by norm_num) (congrArg Subtype.val h),
      fun h => hfe l 1 hl (by norm_num) (congrArg Subtype.val h),
      fun h => hfe l 2 hl (by norm_num) (congrArg Subtype.val h),
      fun h => hfte l 0 hl (by norm_num) (congrArg Subtype.val h),
      fun h => hfte l 1 hl (by norm_num) (congrArg Subtype.val h),
      fun h => hfte l 2 hl (by norm_num) (congrArg Subtype.val h)⟩
  refine card_ge_32_aux (G := ↥Z) hcomm' hsq' (t := ⟨t, htZ⟩) (e₀ := ⟨e 0, heZ 0⟩)
    (e₁ := ⟨e 1, heZ 1⟩) (e₂ := ⟨e 2, heZ 2⟩) (f₀ := ⟨f 0, hfZ 0⟩) (f₁ := ⟨f 1, hfZ 1⟩)
    (f₂ := ⟨f 2, hfZ 2⟩) ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun h => ht (congrArg Subtype.val h)
  · exact Subtype.ext hE
  · exact Subtype.ext hF
  · exact ⟨fun h => h0.1 (congrArg Subtype.val h), fun h => h0.2 (congrArg Subtype.val h)⟩
  · exact ⟨fun h => h1.1 (congrArg Subtype.val h), fun h => h1.2.1 (congrArg Subtype.val h),
      fun h => h1.2.2.1 (congrArg Subtype.val h), fun h => h1.2.2.2 (congrArg Subtype.val h)⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact key 0 (by norm_num)
    · exact key 1 (by norm_num)
    · exact key 2 (by norm_num)

end Count

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO
