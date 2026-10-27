module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltBasic

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Equiv Equiv.Perm

section Cent

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem eq_one_of_commute_alternating (h5 : 5 ≤ Nat.card α) {σ : Perm α}
    (h : ∀ g ∈ alternatingGroup α, σ * g = g * σ) : σ = 1 := by
  let C : Subgroup (Perm α) := Subgroup.centralizer (alternatingGroup α : Set (Perm α))
  have hCn : C.Normal := by
    refine ⟨fun c hc g a ha => ?_⟩
    have hc' : ∀ b ∈ alternatingGroup α, c * b = b * c := fun b hb =>
      (Subgroup.mem_centralizer_iff.1 hc b hb).symm
    have hb : g⁻¹ * a * g ∈ alternatingGroup α := by
      have := (inferInstance : (alternatingGroup α).Normal).conj_mem a ha g⁻¹
      simpa using this
    have := hc' _ hb
    calc a * (g * c * g⁻¹) = g * (g⁻¹ * a * g) * c * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by rw [mul_assoc g, ← this, ← mul_assoc]
      _ = g * c * g⁻¹ * a := by group
  by_contra hσ
  have hσC : σ ∈ C := Subgroup.mem_centralizer_iff.2 fun g hg => (h g hg).symm
  have hnt : Nontrivial C := ⟨⟨⟨σ, hσC⟩, 1, fun e => hσ (congrArg Subtype.val e)⟩⟩
  have hle : alternatingGroup α ≤ C := Equiv.Perm.alternatingGroup_le_of_normal h5 hnt
  have := alternatingGroup.nontrivial_of_three_le_card (α := α) (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup α)
  have hZ := alternatingGroup.center_eq_bot (α := α) (by omega)
  have : a ∈ Subgroup.center (alternatingGroup α) := by
    rw [Subgroup.mem_center_iff]
    intro b
    have := Subgroup.mem_centralizer_iff.1 (hle a.2) b b.2
    exact Subtype.ext this
  rw [hZ, Subgroup.mem_bot] at this
  exact ha this

end Cent

section CentF

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem exists_mem_altOn_moves {F : Finset Ω} (hF : 3 ≤ F.card) {x : Ω} (hx : x ∈ F) :
    ∃ h ∈ altOn F, h x ≠ x := by
  have h1 : ((F.erase x).Nonempty) := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hx]; omega
  obtain ⟨a, ha⟩ := h1
  have haF : a ∈ F := Finset.mem_of_mem_erase ha
  have hax : a ≠ x := Finset.ne_of_mem_erase ha
  have h2 : (((F.erase x).erase a).Nonempty) := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha, Finset.card_erase_of_mem hx]; omega
  obtain ⟨b, hb⟩ := h2
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  have hb' := Finset.mem_of_mem_erase hb
  have hbx : b ≠ x := Finset.ne_of_mem_erase hb'
  have hbF : b ∈ F := Finset.mem_of_mem_erase hb'
  refine ⟨Equiv.swap x a * Equiv.swap a b, ?_, ?_⟩
  · refine mem_altOn.2 ⟨fun y hy => ?_, ?_⟩
    · have hyx : y ≠ x := fun h => hy (h ▸ hx)
      have hya : y ≠ a := fun h => hy (h ▸ haF)
      have hyb : y ≠ b := fun h => hy (h ▸ hbF)
      simp [Equiv.swap_apply_of_ne_of_ne, hyx, hya, hyb]
    · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hax.symm, Equiv.Perm.sign_swap hba.symm]
      decide
  · simp [Equiv.swap_apply_of_ne_of_ne, hax.symm, hbx.symm, Equiv.swap_apply_left]
    exact hax

theorem mem_of_commute_altOn {F : Finset Ω} (hF : 3 ≤ F.card) {g : Perm Ω}
    (hg : ∀ k ∈ altOn F, g * k = k * g) {x : Ω} (hx : x ∈ F) : g x ∈ F := by
  by_contra hgx
  obtain ⟨h, hh, hhx⟩ := exists_mem_altOn_moves hF hx
  have h1 := congrArg (fun p : Perm Ω => p x) (hg h hh)
  simp only [Perm.mul_apply] at h1
  have h2 : h (g x) = g x := (mem_altOn.1 hh).1 _ hgx
  rw [h2] at h1
  exact hhx (g.injective h1)

theorem fixes_of_commute_altOn {F : Finset Ω} (hF : 5 ≤ F.card) {g : Perm Ω}
    (hg : ∀ k ∈ altOn F, g * k = k * g) {x : Ω} (hx : x ∈ F) : g x = x := by
  have hF3 : 3 ≤ F.card := by omega
  have hg' : ∀ k ∈ altOn F, g⁻¹ * k = k * g⁻¹ := by
    intro k hk
    have := hg k hk
    calc g⁻¹ * k = g⁻¹ * (k * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * k) * g⁻¹ := by rw [this]
      _ = k * g⁻¹ := by group
  have hiff : ∀ y, g y ∈ F ↔ y ∈ F := by
    intro y
    refine ⟨fun hy => ?_, mem_of_commute_altOn hF3 hg⟩
    have := mem_of_commute_altOn hF3 hg' hy
    simpa using this
  let gF : Perm {x // x ∈ F} := g.subtypePerm hiff
  have hc : gF = 1 := by
    refine eq_one_of_commute_alternating
      (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hF) (fun f hf => ?_)
    have hk : Equiv.Perm.ofSubtype f ∈ altOn F := (altOnEquiv F ⟨f, hf⟩).2
    have hgk := hg _ hk
    ext z
    have h1 := congrArg (fun p : Perm Ω => p z) hgk
    simp only [Perm.mul_apply, Equiv.Perm.ofSubtype_apply_coe] at h1
    have h2 : (Equiv.Perm.ofSubtype f) (g z) = f ⟨g z, (hiff z).2 z.2⟩ :=
      Equiv.Perm.ofSubtype_apply_of_mem f ((hiff z).2 z.2)
    rw [h2] at h1
    simpa [gF] using h1
  have := congrArg (fun p : Perm {x // x ∈ F} => (p ⟨x, hx⟩ : Ω)) hc
  simpa [gF] using this

omit [Fintype Ω] in
theorem commute_of_symOn_of_fixes {F : Finset Ω} {g y : Perm Ω} (hg : g ∈ symOn F)
    (hy : ∀ x ∈ F, y x = x) : g * y = y * g := by
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x ∈ F
  · rw [hy x hx]
    have hgx : g x ∈ F := (symOn_mem_iff hg x).2 hx
    rw [hy _ hgx]
  · rw [hg x hx]
    have hyx : y x ∉ F := by
      intro h
      have h1 : y x = x := y.injective (hy _ h)
      exact hx (h1 ▸ h)
    rw [hg _ hyx]

end CentF

end CFSG.GH74.GLS.IVK.GHInv
