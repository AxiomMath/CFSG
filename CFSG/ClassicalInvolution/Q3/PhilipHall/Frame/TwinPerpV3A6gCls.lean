module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gCoord

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Thin
open scoped Matrix

theorem perm_decide : ∀ (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (b : Fin 3 → ZMod 2),
    ModPi (fun i => ind {0, 2, 4, 6} (binIdx (A *ᵥ bin i + b))) (ind {0, 2, 4, 6}) →
    ModPi (fun i => ind {0, 1, 4, 5} (binIdx (A *ᵥ bin i + b))) (ind {0, 1, 4, 5}) →
    ModPi (fun i => ind {0, 1, 2, 3} (binIdx (A *ᵥ bin i + b))) (ind {0, 1, 2, 3}) → A = 1 := by
  decide +kernel

theorem modPi_comp {f g : Fin 8 → ZMod 2} (h : ModPi f g) (e : Equiv.Perm (Fin 8)) :
    ModPi (fun i => f (e i)) (fun i => g (e i)) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem modPi_symm' {f g : Fin 8 → ZMod 2} (h : ModPi f g) : ModPi g f := modPi_symm h

theorem mem_nBar_of_comm {g : AEQ 8} (hg : g ∈ e29Sub)
    (hc : ∀ δ ∈ affinePlanes, ∀ h : δ.card = 4, g * zBar δ h = zBar δ h * g) : g ∈ nBar := by
  obtain ⟨w, hw, rfl⟩ := hg
  have hσ : w.perm ∈ agl32 := hw.2
  obtain ⟨A, b, hAb⟩ := exists_aperm_eq hσ
  have key : ∀ δ ∈ affinePlanes,
      ModPi (fun i => ind δ (binIdx (A.1 *ᵥ bin i + b))) (ind δ) := by
    intro δ hδ
    have h1 := hc δ hδ (affinePlanes_card δ hδ)
    rw [zBar_eq_vbar] at h1
    have h2 : mkQ 8 w * vbar 8 (ind δ) * (mkQ 8 w)⁻¹ = vbar 8 (ind δ) := by
      rw [h1]
      group
    rw [conj_vbar (permBar_mkQ w)] at h2
    have h3 := modPi_comp (vbar_eq_iff.mp h2) w.perm
    have h4 : ModPi (ind δ) (fun j => ind δ (w.perm j)) := by
      simpa [actV] using h3
    have h5 := modPi_symm' h4
    rw [← hAb] at h5
    exact h5
  have hA : A.1 = 1 := perm_decide A.1 b (key _ (by decide)) (key _ (by decide)) (key _ (by decide))
  have hA' : A = 1 := Subtype.ext hA
  refine ⟨⟨w, hw, rfl⟩, ?_⟩
  show permQ 8 (mkQ 8 w) ∈ translSub
  rw [permQ_mkQ, ← hAb, hA']
  exact aperm_one_mem_translSub b


theorem exists_E8_of_mem_nBar {x : AEQ 8} (hx : x ∈ nBar) : ∃ f b, EvF f ∧ x = E8 f b := by
  obtain ⟨⟨w, hw, rfl⟩, hT⟩ := hx
  have hp : w.perm ∈ translSub := hT
  obtain ⟨b, hb⟩ := exists_eq_aperm_of_mem_translSub hp
  refine ⟨w.vec, b, hw.1.1, ?_⟩
  unfold E8 vbar tl
  rw [← map_mul, ← hb]
  exact congrArg (mkQ 8) (eq_ofVec_mul_ofPerm w)

theorem cover3_excl {G : Type*} [Group G] {A H₁ H₂ H₃ : Subgroup G}
    (hcov : ∀ a ∈ A, a ∈ H₁ ∨ a ∈ H₂ ∨ a ∈ H₃) (hn₂ : ¬ A ≤ H₂) (hn₃ : ¬ A ≤ H₃) :
    ∃ a ∈ A, a ∈ H₁ ∧ a ∉ H₂ ∧ a ∉ H₃ := by
  by_contra hno
  push Not at hno
  have h23 : ∀ a ∈ A, a ∈ H₂ ∨ a ∈ H₃ := by
    intro a ha
    rcases hcov a ha with h | h | h
    · by_cases h2 : a ∈ H₂
      · exact Or.inl h2
      · exact Or.inr (hno a ha h h2)
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨x, hxA, hx2⟩ := SetLike.not_le_iff_exists.mp hn₂
  obtain ⟨y, hyA, hy3⟩ := SetLike.not_le_iff_exists.mp hn₃
  have hx3 : x ∈ H₃ := (h23 x hxA).resolve_left hx2
  have hy2 : y ∈ H₂ := (h23 y hyA).resolve_right hy3
  rcases h23 (x * y) (A.mul_mem hxA hyA) with h | h
  · exact hx2 (by simpa using H₂.mul_mem h (H₂.inv_mem hy2))
  · exact hy3 (by simpa using H₃.mul_mem (H₃.inv_mem hx3) h)

theorem cover3 {G : Type*} [Group G] {A H₁ H₂ H₃ N : Subgroup G}
    (h12 : H₁ ⊓ H₂ ≤ N) (h13 : H₁ ⊓ H₃ ≤ N) (h23 : H₂ ⊓ H₃ ≤ N)
    (hcov : ∀ a ∈ A, a ∈ H₁ ∨ a ∈ H₂ ∨ a ∈ H₃)
    (hn₁ : ¬ A ≤ H₁) (hn₂ : ¬ A ≤ H₂) (hn₃ : ¬ A ≤ H₃) :
    ∃ a b : G, ∀ x ∈ A, x ∈ N ∨ x * a⁻¹ ∈ N ∨ x * b⁻¹ ∈ N ∨ x * (a * b⁻¹)⁻¹ ∈ N := by
  obtain ⟨a, haA, ha1, ha2, ha3⟩ := cover3_excl hcov hn₂ hn₃
  obtain ⟨b, hbA, hb2, hb1, hb3⟩ := cover3_excl
    (A := A) (H₁ := H₂) (H₂ := H₁) (H₃ := H₃)
    (fun x hx => by rcases hcov x hx with h | h | h <;> tauto) hn₁ hn₃
  have hab : a * b ∈ H₃ := by
    rcases hcov (a * b) (A.mul_mem haA hbA) with h | h | h
    · exact absurd (by simpa using H₁.mul_mem (H₁.inv_mem ha1) h) hb1
    · exact absurd (by simpa using H₂.mul_mem h (H₂.inv_mem hb2)) ha2
    · exact h
  have hba : b * a ∈ H₃ := by
    rcases hcov (b * a) (A.mul_mem hbA haA) with h | h | h
    · exact absurd (by simpa using H₁.mul_mem h (H₁.inv_mem ha1)) hb1
    · exact absurd (by simpa using H₂.mul_mem (H₂.inv_mem hb2) h) ha2
    · exact h
  have habi : a * b⁻¹ ∈ H₃ := by
    rcases hcov (a * b⁻¹) (A.mul_mem haA (A.inv_mem hbA)) with h | h | h
    · exact absurd (by simpa using H₁.inv_mem (by simpa using H₁.mul_mem (H₁.inv_mem ha1) h)) hb1
    · exact absurd (by simpa using H₂.mul_mem h hb2) ha2
    · exact h
  refine ⟨a, b, fun x hxA => ?_⟩
  by_cases hxN : x ∈ N
  · exact Or.inl hxN
  right
  rcases hcov x hxA with hx | hx | hx
  · left
    have hx2 : x ∉ H₂ := fun h => hxN (h12 ⟨hx, h⟩)
    have hxb : x * b ∈ H₃ := by
      rcases hcov (x * b) (A.mul_mem hxA hbA) with h | h | h
      · exact absurd (by simpa using H₁.mul_mem (H₁.inv_mem hx) h) hb1
      · exact absurd (by simpa using H₂.mul_mem h (H₂.inv_mem hb2)) hx2
      · exact h
    have : x * a⁻¹ ∈ H₃ := by
      have := H₃.mul_mem hxb (H₃.inv_mem hab)
      simpa [mul_assoc] using this
    exact h13 ⟨H₁.mul_mem hx (H₁.inv_mem ha1), this⟩
  · right; left
    have hx1 : x ∉ H₁ := fun h => hxN (h12 ⟨h, hx⟩)
    have hxa : x * a ∈ H₃ := by
      rcases hcov (x * a) (A.mul_mem hxA haA) with h | h | h
      · exact absurd (by simpa using H₁.mul_mem h (H₁.inv_mem ha1)) hx1
      · exact absurd (by simpa using H₂.mul_mem (H₂.inv_mem hx) h) ha2
      · exact h
    have : x * b⁻¹ ∈ H₃ := by
      have := H₃.mul_mem hxa (H₃.inv_mem hba)
      simpa [mul_assoc] using this
    exact h23 ⟨H₂.mul_mem hx (H₂.inv_mem hb2), this⟩
  · right; right
    have hx1 : x ∉ H₁ := fun h => hxN (h13 ⟨h, hx⟩)
    have hx2 : x ∉ H₂ := fun h => hxN (h23 ⟨h, hx⟩)
    have hxb : x * b ∈ H₁ := by
      rcases hcov (x * b) (A.mul_mem hxA hbA) with h | h | h
      · exact h
      · exact absurd (by simpa using H₂.mul_mem h (H₂.inv_mem hb2)) hx2
      · exact absurd (by simpa using H₃.mul_mem (H₃.inv_mem hx) h) hb3
    have e : x * (a * b⁻¹)⁻¹ = (x * b) * a⁻¹ := by group
    rw [e]
    have h1 : (x * b) * a⁻¹ ∈ H₁ := H₁.mul_mem hxb (H₁.inv_mem ha1)
    have h3 : (x * b) * a⁻¹ ∈ H₃ := by
      have := H₃.mul_mem hx (H₃.inv_mem habi)
      rw [e] at this
      exact this
    exact h13 ⟨h1, h3⟩

theorem card_le_of_cover {G : Type*} [Group G] [Finite G] {A N : Subgroup G} {a b : G}
    (h : ∀ x ∈ A, x ∈ N ∨ x * a⁻¹ ∈ N ∨ x * b⁻¹ ∈ N ∨ x * (a * b⁻¹)⁻¹ ∈ N) :
    Nat.card A ≤ 4 * Nat.card N := by
  set c := a * b⁻¹ with hc
  let cos : G → Set G := fun g => (fun n => n * g) '' (N : Set G)
  have hcos : ∀ g, (cos g).ncard = (N : Set G).ncard := fun g =>
    Set.ncard_image_of_injective _ (mul_left_injective g)
  have hsub : (A : Set G) ⊆ (N : Set G) ∪ cos a ∪ cos b ∪ cos c := by
    intro x hx
    rcases h x hx with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨x * a⁻¹, h, by simp⟩))
    · exact Or.inl (Or.inr ⟨x * b⁻¹, h, by simp⟩)
    · exact Or.inr ⟨x * c⁻¹, h, by simp⟩
  have h1 := Set.ncard_le_ncard hsub
  have h2 := Set.ncard_union_le ((N : Set G) ∪ cos a ∪ cos b) (cos c)
  have h3 := Set.ncard_union_le ((N : Set G) ∪ cos a) (cos b)
  have h4 := Set.ncard_union_le (N : Set G) (cos a)
  have hA : Nat.card A = (A : Set G).ncard := by rw [← Nat.card_coe_set_eq]; rfl
  have hN : Nat.card N = (N : Set G).ncard := by rw [← Nat.card_coe_set_eq]; rfl
  have ha := hcos a
  have hb := hcos b
  have hc' := hcos c
  omega


theorem classify {A : Subgroup (AEQ 8)} (hA : A ≤ e29Sub) (hsq : ∀ a ∈ A, a * a = 1)
    (hcard : Nat.card A = 64)
    (hz : ∀ δ ∈ affinePlanes, ∀ h : δ.card = 4, zBar δ h ∈ A) : A = AE ∨ A = AT ∨ A = AD := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have h1 := hsq (a * b) (A.mul_mem ha hb)
    have h2 := hsq a ha
    have h3 := hsq b hb
    have ainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right h2
    have binv : b⁻¹ = b := inv_eq_of_mul_eq_one_right h3
    have : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [mul_inv_rev, ainv, binv] at this
    exact this
  have hnB : ∀ a ∈ A, a ∈ nBar := fun a ha =>
    mem_nBar_of_comm (hA ha) (fun δ hδ h => hcomm a ha _ (hz δ hδ h))
  have hcov : ∀ a ∈ A, a ∈ AE ∨ a ∈ AT ∨ a ∈ AD := by
    intro a ha
    obtain ⟨f, b, hf, rfl⟩ := exists_E8_of_mem_nBar (hnB a ha)
    have hsq' := (E8_sq_iff f b).mp (hsq _ ha)
    rcases inv_class f hf b hsq' with hb | hT | hD
    · left; exact mem_AE.mpr ⟨f, hf, by rw [hb]⟩
    · right; left; exact mem_AT.mpr ⟨f, b, hT, rfl⟩
    · right; right; exact mem_AD.mpr ⟨f, b, hD, rfl⟩
  by_cases h1 : A ≤ AE
  · left; exact Subgroup.eq_of_le_of_card_ge h1 (by rw [card_AE, hcard])
  by_cases h2 : A ≤ AT
  · right; left; exact Subgroup.eq_of_le_of_card_ge h2 (by rw [card_AT, hcard])
  by_cases h3 : A ≤ AD
  · right; right; exact Subgroup.eq_of_le_of_card_ge h3 (by rw [card_AD, hcard])
  exfalso
  obtain ⟨a, b, hab⟩ := cover3 (N := E3p) AE_inf_AT_le AE_inf_AD_le AT_inf_AD_le hcov h1 h2 h3
  have := card_le_of_cover hab
  rw [hcard, card_E3p] at this
  omega

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
