module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec9m_graph {V : Type*} [Group V] [Finite V] {H : Subgroup (MulAut V)}
    (htrans : ∀ b b' : V, b ≠ 1 → b' ≠ 1 → ∃ h ∈ H, h b = b')
    (hcent : ∀ φ : MulAut V, (∀ h ∈ H, φ * h = h * φ) → φ = 1)
    (W : Subgroup (V × V)) (hW : Nat.card W ≤ Nat.card V)
    (hinv : ∀ h ∈ H, ∀ w ∈ W, (h w.1, h w.2) ∈ W) :
    (∀ w ∈ W, w.1 = 1) ∨ (∀ w ∈ W, w.2 = 1) ∨ (∀ w ∈ W, w.1 = w.2) := by
  by_cases h1 : ∀ w ∈ W, w.1 = 1
  · exact Or.inl h1
  by_cases h2 : ∀ w ∈ W, w.2 = 1
  · exact Or.inr (Or.inl h2)
  push Not at h1 h2
  let π₁ : W →* V := (MonoidHom.fst V V).comp W.subtype
  let π₂ : W →* V := (MonoidHom.snd V V).comp W.subtype
  have hπ₁ : ∀ x : W, π₁ x = (x : V × V).1 := fun x => rfl
  have hπ₂ : ∀ x : W, π₂ x = (x : V × V).2 := fun x => rfl
  have hsurj₁ : Function.Surjective π₁ := by
    intro b
    by_cases hb : b = 1
    · exact ⟨1, by rw [map_one, hb]⟩
    · obtain ⟨w₀, hw₀, hw₀ne⟩ := h1
      obtain ⟨h, hh, hh'⟩ := htrans w₀.1 b hw₀ne hb
      exact ⟨⟨(h w₀.1, h w₀.2), hinv h hh w₀ hw₀⟩, hh'⟩
  have hsurj₂ : Function.Surjective π₂ := by
    intro b
    by_cases hb : b = 1
    · exact ⟨1, by rw [map_one, hb]⟩
    · obtain ⟨w₀, hw₀, hw₀ne⟩ := h2
      obtain ⟨h, hh, hh'⟩ := htrans w₀.2 b hw₀ne hb
      exact ⟨⟨(h w₀.1, h w₀.2), hinv h hh w₀ hw₀⟩, hh'⟩
  have hbij₁ : Function.Bijective π₁ := hsurj₁.bijective_of_nat_card_le hW
  have hbij₂ : Function.Bijective π₂ := hsurj₂.bijective_of_nat_card_le hW
  let e₁ : W ≃* V := MulEquiv.ofBijective π₁ hbij₁
  let e₂ : W ≃* V := MulEquiv.ofBijective π₂ hbij₂
  have he₁ : ∀ x : W, e₁ x = (x : V × V).1 := by
    intro x
    rw [MulEquiv.ofBijective_apply]
    exact hπ₁ x
  have he₂ : ∀ x : W, e₂ x = (x : V × V).2 := by
    intro x
    rw [MulEquiv.ofBijective_apply]
    exact hπ₂ x
  let φ : MulAut V := e₁.symm.trans e₂
  have hφe : ∀ x : W, φ (e₁ x) = (x : V × V).2 := by
    intro x
    show e₂ (e₁.symm (e₁ x)) = (x : V × V).2
    rw [MulEquiv.symm_apply_apply, he₂ x]
  have hcomm : ∀ h ∈ H, φ * h = h * φ := by
    intro h hh
    ext v
    rw [MulAut.mul_apply, MulAut.mul_apply]
    let w : W := e₁.symm v
    have hw1 : (w : V × V).1 = v := by
      rw [← he₁ w]
      exact e₁.apply_symm_apply v
    have hw2 : φ v = (w : V × V).2 := by
      rw [← hw1, ← he₁ w, hφe w]
    have hw' : (h (w : V × V).1, h (w : V × V).2) ∈ W :=
      hinv h hh (w : V × V) w.2
    let w' : W := ⟨(h (w : V × V).1, h (w : V × V).2), hw'⟩
    have he₁w' : e₁ w' = h v := by
      rw [he₁ w']
      show h (w : V × V).1 = h v
      rw [hw1]
    have hA : φ (h v) = h (w : V × V).2 := by
      rw [← he₁w', hφe w']
    have hB : h (φ v) = h (w : V × V).2 := by rw [hw2]
    rw [hA, hB]
  have hφ1 : φ = 1 := hcent φ hcomm
  refine Or.inr (Or.inr ?_)
  intro w hw
  have hφw : φ w.1 = w.2 := by
    have hx := hφe ⟨w, hw⟩
    rw [he₁ ⟨w, hw⟩] at hx
    exact hx
  have hw1 : φ w.1 = w.1 := by rw [hφ1]; rfl
  exact hw1.symm.trans hφw

end CFSG.OddStandard.SmallF3.Omega
