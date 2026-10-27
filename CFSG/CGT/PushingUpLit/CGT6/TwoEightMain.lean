module

public import CFSG.CGT.PushingUpLit.CGT6.TwoEightCore
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightSylow

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

section Main

variable {F L : Type} [Field F] [AddCommGroup L] [Module F L] [CharP F 2] (D : Data F L)

omit [CharP F 2] in
theorem IsAddPerm.mul {a b : Equiv.Perm (Wd F L)} (ha : IsAddPerm a) (hb : IsAddPerm b) :
    IsAddPerm (a * b) := fun w w' => by
  simp only [Equiv.Perm.mul_apply]
  rw [hb, ha]

theorem isPGroup_two_of_sq {G : Type*} [Group G] {H : Subgroup G} (h : ∀ a ∈ H, a * a = 1) :
    IsPGroup 2 H := fun g => ⟨1, by
  rw [pow_one, sq]
  exact Subtype.ext (h g.1 g.2)⟩

theorem isPGroup_S0 : IsPGroup 2 (S0 D) := isPGroup_two_of_sq fun a ⟨x, hx⟩ => by
  rw [← hx, sigPerm_mul, add_self_L F, sigPerm_zero]

theorem card_S0 : Nat.card (S0 D) = Nat.card L := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun x : L => (⟨sigPerm D x, x, rfl⟩ : S0 D)) ⟨?_, ?_⟩)
  · intro x y h
    exact sigPerm_injective D (congrArg Subtype.val h)
  · rintro ⟨g, x, rfl⟩
    exact ⟨x, rfl⟩

theorem flag_main [Finite F] [Finite L] [Module.Finite F L] (hF : 3 ≤ Nat.card F)
    {Γ Γ₁ Γ₂ Ā : Subgroup (Equiv.Perm (Wd F L))}
    (hΓσ : ∀ x, sigPerm D x ∈ Γ) {x₁ : L} (hx₁ : x₁ ≠ 0) (hΓl : lamPerm D x₁ ∈ Γ)
    (hΓQ : ∀ g ∈ Γ, ∀ w, Qt D (g w) = Qt D w) (hΓadd : ∀ g ∈ Γ, IsAddPerm g)
    (hΓmax : ∀ P : Subgroup (Equiv.Perm (Wd F L)), P ≤ Γ → IsPGroup 2 P →
      Nat.card P ≤ Nat.card L)
    (hΓ₁ : ∀ h ∈ Γ, ∀ g ∈ Γ₁, h * g * h⁻¹ ∈ Γ₁) (hΓ₂ : ∀ h ∈ Γ, ∀ g ∈ Γ₂, h * g * h⁻¹ ∈ Γ₂)
    (hadd : ∀ a ∈ Ā, IsAddPerm a) (hsq : ∀ a ∈ Ā, a * a = 1)
    (hnormΓ : ∀ a ∈ Ā, ∀ g ∈ Γ, a * g * a⁻¹ ∈ Γ)
    (hnorm₁ : ∀ a ∈ Ā, ∀ g ∈ Γ₁, a * g * a⁻¹ ∈ Γ₁)
    (hnorm₂ : ∀ a ∈ Ā, ∀ g ∈ Γ₂, a * g * a⁻¹ ∈ Γ₂)
    (hidx : ∀ Ā' : Subgroup (Equiv.Perm (Wd F L)), (∀ a ∈ Ā', IsAddPerm a) →
      (∀ a ∈ Ā', a * a = 1) → (∀ a ∈ Ā', ∀ g ∈ Γ, a * g * a⁻¹ ∈ Γ) →
      (∀ a ∈ Ā', ∀ g ∈ Γ₁, a * g * a⁻¹ ∈ Γ₁) → (∀ a ∈ Ā', ∀ g ∈ Γ₂, a * g * a⁻¹ ∈ Γ₂) →
      (∀ a ∈ Ā', ∀ x, ∃ x', a * sigPerm D x * a⁻¹ = sigPerm D x') →
      Nat.card Ā' ≤ 2 * Nat.card ↥(Ā' ⊓ Subgroup.centralizer
        (S0 D : Set (Equiv.Perm (Wd F L)))))
    (hoff : Nat.card (Wd F L) ≤ Nat.card Ā * Nat.card (Fix Ā)) : Ā = ⊥ := by
  classical
  have hĀ2 : IsPGroup 2 Ā := isPGroup_two_of_sq hsq
  have hN : Ā ≤ Subgroup.normalizer (Γ : Set (Equiv.Perm (Wd F L))) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hnormΓ a ha g hg, fun hg => ?_⟩
    have := hnormΓ a⁻¹ (Ā.inv_mem ha) _ hg
    simpa [mul_assoc] using this
  have hSΓ : S0 D ≤ Γ := by
    rintro _ ⟨x, rfl⟩
    exact hΓσ x
  have hmax : ∀ P : Subgroup (Equiv.Perm (Wd F L)), P ≤ Γ → IsPGroup 2 P →
      Nat.card P ≤ Nat.card (S0 D) := by
    intro P hP hP2
    rw [card_S0]
    exact hΓmax P hP hP2
  obtain ⟨h, hhΓ, hconj⟩ := exists_conj_normalizes hN hĀ2 hSΓ (isPGroup_S0 D) hmax
  obtain ⟨Ā', hĀ'⟩ : ∃ Ā' : Subgroup (Equiv.Perm (Wd F L)),
      Ā' = Ā.map (MulAut.conj h⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hmem : ∀ b ∈ Ā', ∃ a ∈ Ā, b = h⁻¹ * a * h := by
    intro b hb
    rw [hĀ'] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨a, ha, by simp⟩
  have hmem' : ∀ a ∈ Ā, h⁻¹ * a * h ∈ Ā' := fun a ha => by
    rw [hĀ']
    exact ⟨a, ha, by simp⟩
  have hhinv : h⁻¹ ∈ Γ := Γ.inv_mem hhΓ
  have hadd' : ∀ b ∈ Ā', IsAddPerm b := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hmem b hb
    exact ((hΓadd _ hhinv).mul (hadd a ha)).mul (hΓadd h hhΓ)
  have hsq' : ∀ b ∈ Ā', b * b = 1 := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hmem b hb
    calc h⁻¹ * a * h * (h⁻¹ * a * h) = h⁻¹ * (a * a) * h := by group
      _ = 1 := by rw [hsq a ha]; group
  have hnormΓ' : ∀ b ∈ Ā', ∀ g ∈ Γ, b * g * b⁻¹ ∈ Γ := by
    intro b hb g hg
    obtain ⟨a, ha, rfl⟩ := hmem b hb
    have h1 : h * g * h⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hhΓ hg) hhinv
    have h2 := Γ.mul_mem (Γ.mul_mem hhinv (hnormΓ a ha _ h1)) hhΓ
    have h3 : h⁻¹ * a * h * g * (h⁻¹ * a * h)⁻¹ = h⁻¹ * (a * (h * g * h⁻¹) * a⁻¹) * h := by
      group
    rw [h3]
    exact h2
  have hnorm₁' : ∀ b ∈ Ā', ∀ g ∈ Γ₁, b * g * b⁻¹ ∈ Γ₁ := by
    intro b hb g hg
    obtain ⟨a, ha, rfl⟩ := hmem b hb
    have h1 : h * g * h⁻¹ ∈ Γ₁ := hΓ₁ h hhΓ g hg
    have h2 := hΓ₁ h⁻¹ hhinv _ (hnorm₁ a ha _ h1)
    have h3 : h⁻¹ * a * h * g * (h⁻¹ * a * h)⁻¹ = h⁻¹ * (a * (h * g * h⁻¹) * a⁻¹) * h⁻¹⁻¹ := by
      group
    rw [h3]
    exact h2
  have hnorm₂' : ∀ b ∈ Ā', ∀ g ∈ Γ₂, b * g * b⁻¹ ∈ Γ₂ := by
    intro b hb g hg
    obtain ⟨a, ha, rfl⟩ := hmem b hb
    have h1 : h * g * h⁻¹ ∈ Γ₂ := hΓ₂ h hhΓ g hg
    have h2 := hΓ₂ h⁻¹ hhinv _ (hnorm₂ a ha _ h1)
    have h3 : h⁻¹ * a * h * g * (h⁻¹ * a * h)⁻¹ = h⁻¹ * (a * (h * g * h⁻¹) * a⁻¹) * h⁻¹⁻¹ := by
      group
    rw [h3]
    exact h2
  have hnormS' : ∀ b ∈ Ā', ∀ x, ∃ x', b * sigPerm D x * b⁻¹ = sigPerm D x' := by
    intro b hb x
    obtain ⟨a, ha, rfl⟩ := hmem b hb
    obtain ⟨x', hx'⟩ := hconj a ha (sigPerm D x) ⟨x, rfl⟩
    exact ⟨x', hx'.symm⟩
  have hcardĀ : Nat.card Ā' = Nat.card Ā := by
    rw [hĀ']
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective Ā _ (MulAut.conj h⁻¹).injective).toEquiv.symm
  have hcancel : ∀ w : Wd F L, h (h⁻¹ w) = w := fun w => by simp
  have hfix : Nat.card (Fix Ā) ≤ Nat.card (Fix Ā') := by
    refine Nat.card_le_card_of_injective (fun w : Fix Ā => (⟨h⁻¹ w.1, ?_⟩ : Fix Ā')) ?_
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := hmem b hb
      have h1 := w.2 a ha
      simp only [Equiv.Perm.mul_apply]
      rw [hcancel, h1]
    · intro w w' hww
      apply Subtype.ext
      have := congrArg (fun z : Fix Ā' => (z : Wd F L)) hww
      simp only at this
      calc w.1 = h (h⁻¹ w.1) := (hcancel _).symm
        _ = h (h⁻¹ w'.1) := by rw [this]
        _ = w'.1 := hcancel _
  have hoff' : Nat.card (Wd F L) ≤ Nat.card Ā' * Nat.card (Fix Ā') := by
    rw [hcardĀ]
    exact hoff.trans (Nat.mul_le_mul_left _ hfix)
  have hbot : Ā' = ⊥ := core_eq_bot D hF hΓσ hx₁ hΓl hΓQ hadd' hsq' hnormΓ' hnormS'
    (hidx Ā' hadd' hsq' hnormΓ' hnorm₁' hnorm₂' hnormS') hoff'
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  have h1 : h⁻¹ * a * h = 1 := Subgroup.mem_bot.mp (hbot ▸ hmem' a ha)
  calc a = h * (h⁻¹ * a * h) * h⁻¹ := by group
    _ = 1 := by rw [h1]; group

end Main

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
