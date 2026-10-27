module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open

section Assembly

variable {H L X : Type} [Group H] [Finite H] [Group L] [Finite L] [Group X]

theorem cover_assembly (α : H →* X) (β : L →* X) (φ : H →* L) (hφs : Function.Surjective φ)
    (hβφ : β.comp φ = α) {D E' : Subgroup H} (hker : α.ker = D) {m : ℕ} (hE'card : Nat.card E' = m)
    (hE'D : E' ⊓ D = ⊥) (hE : IsElemAbelian 3 (E' ⊔ D)) {s₀ : H} (hs2 : s₀ * s₀ = 1) (hsD : s₀ ∉ D)
    (hsc : ∀ e ∈ E' ⊔ D, e * s₀ = s₀ * e) :
    ∃ (Eb : Subgroup L) (s : L), IsElemAbelian 3 Eb ∧ Nat.card Eb = m * Nat.card β.ker ∧
      s ^ 2 = 1 ∧ β s ≠ 1 ∧ ∀ x ∈ Eb, x * s = s * x := by
  set Ep : Subgroup H := E' ⊔ D with hEp
  have hβα : ∀ h, β (φ h) = α h := fun h => by rw [← hβφ]; rfl
  refine ⟨Ep.map φ, φ s₀, hE.map φ, ?_, ?_, ?_, ?_⟩
  ·
    have hkβ : β.ker ≤ Ep.map φ := by
      intro z hz
      obtain ⟨h, rfl⟩ := hφs z
      have hh : h ∈ α.ker := by
        rw [MonoidHom.mem_ker, ← hβα]
        exact hz
      rw [hker] at hh
      exact ⟨h, Subgroup.mem_sup_right hh, rfl⟩
    set g : ↥(Ep.map φ) →* X := β.comp (Ep.map φ).subtype with hg
    have hcard : Nat.card ↥(Ep.map φ) = Nat.card g.range * Nat.card g.ker := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at h1
      rw [h1]
    have hrange : g.range = E'.map α := by
      have h1 : g.range = (Ep.map φ).map β := by
        rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
      rw [h1, Subgroup.map_map, hβφ, hEp, Subgroup.map_sup]
      have : D.map α = ⊥ := by
        rw [← hker]
        exact (Subgroup.map_eq_bot_iff _).2 le_rfl
      rw [this, sup_bot_eq]
    have hinj : Function.Injective (α.comp E'.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hx1 : α (x : H) = 1 := hx
      have : (x : H) ∈ E' ⊓ D := ⟨x.2, by rw [← hker]; exact hx1⟩
      rw [hE'D, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    have hrc : Nat.card g.range = m := by
      rw [hrange, ← card_eq_of_injective_comp_subtype α hinj, hE'card]
    have hkc : Nat.card g.ker = Nat.card β.ker := by
      refine Nat.card_congr
        { toFun := fun x => ⟨(x.1 : L), x.2⟩
          invFun := fun y => ⟨⟨(y : L), hkβ y.2⟩, y.2⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    rw [hcard, hrc, hkc]
  · rw [pow_two, ← map_mul, hs2, map_one]
  · intro h
    apply hsD
    rw [← hker, MonoidHom.mem_ker, ← hβα]
    exact h
  · rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, ← map_mul, hsc e he]

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.CatB
