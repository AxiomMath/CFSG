module

public import CFSG.ClassicalInvolution.RouteD.GapsD4AThree

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.WeakCT CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def restrictAut {Y : Type*} [Group Y] (σ : Y ≃* Y) (Q : Subgroup Y)
    (hQ : Q.map σ.toMonoidHom = Q) : Q ≃* Q :=
  (σ.subgroupMap Q).trans (MulEquiv.subgroupCongr hQ)

theorem coe_restrictAut {Y : Type*} [Group Y] (σ : Y ≃* Y) (Q : Subgroup Y)
    (hQ : Q.map σ.toMonoidHom = Q) (x : Q) : ((restrictAut σ Q hQ x : Q) : Y) = σ x := rfl

theorem map_eq_of_involutive {Y : Type*} [Group Y] (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (Q : Subgroup Y) (hQ : ∀ y ∈ Q, σ y ∈ Q) : Q.map σ.toMonoidHom = Q := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact hQ y hy
  · intro y hy
    exact ⟨σ y, hQ y hy, hσ y⟩

theorem innerDiag_of_partner_blocks_amb [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) {m : ℕ} (hm : 3 ≤ m) (hcl : LinearAutClassification F (m + 1))
    {Y : Type} [Group Y] (θ : SL(m + 1, F) →* Y)
    (hker : θ.ker ≤ Subgroup.center SL(m + 1, F)) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ a : Fin m, partnerFixed m a → ∀ A : SL(2, F),
      σ (θ (blockSL2 F m a A)) = θ (blockSL2 F m a A))
    (hmove : ∃ A : SL(2, F), σ (θ (blockSL2 F m ⟨0, by omega⟩ A)) ≠
      θ (blockSL2 F m ⟨0, by omega⟩ A)) :
    ∃ g : GL (Fin (m + 1)) F, ∀ x, σ (θ x) = θ (slConjugation (m + 1) F g x) := by
  have hQ : θ.range.map σ.toMonoidHom = θ.range :=
    map_eq_of_involutive σ hσ θ.range (by rintro _ ⟨x, rfl⟩; exact hstab x)
  have hcoe : ∀ x, ((θ.rangeRestrict x : θ.range) : Y) = θ x := fun x => rfl
  obtain ⟨g, hg⟩ := innerDiag_of_partner_blocks hodd h5 hm hcl θ.rangeRestrict
    θ.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
    (restrictAut σ θ.range hQ)
    (fun x => Subtype.ext (by simp only [coe_restrictAut]; exact hσ _))
    (fun a ha A => Subtype.ext (by
      simp only [coe_restrictAut, hcoe]; exact hfix a ha A))
    (by
      obtain ⟨A, hA⟩ := hmove
      exact ⟨A, fun h => hA (by simpa [coe_restrictAut, hcoe] using congrArg Subtype.val h)⟩)
  exact ⟨g, fun x => by
    have := congrArg Subtype.val (hg x)
    simpa [coe_restrictAut, hcoe] using this⟩

theorem partner_pattern_amb [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) {m : ℕ}
    (hm : 4 ≤ m) (hcl : LinearAutClassification F (m + 1)) {Y : Type} [Group Y]
    (θ : SL(m + 1, F) →* Y) (hker : θ.ker ≤ Subgroup.center SL(m + 1, F)) (σ : Y ≃* Y)
    (hσ : ∀ y, σ (σ y) = y) (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ a : Fin m, partnerFixed m a → ∀ A : SL(2, F),
      σ (θ (blockSL2 F m a A)) = θ (blockSL2 F m a A))
    (hmove : ∃ A : SL(2, F), σ (θ (blockSL2 F m ⟨0, by omega⟩ A)) ≠
      θ (blockSL2 F m ⟨0, by omega⟩ A)) :
    ∃ μ : Fˣ, (μ = 1 ∨ μ = -1) ∧
      (∀ x, σ (θ x) = θ (slConjugation (m + 1) F (partnerDiag m μ) x)) ∧
      ((μ = 1) ↔ ∀ A : SL(2, F),
        σ (θ (blockSL2 F m ⟨m - 2, by omega⟩ A)) = θ (blockSL2 F m ⟨m - 2, by omega⟩ A)) := by
  obtain ⟨g, hg⟩ := innerDiag_of_partner_blocks_amb hodd h5 (by omega) hcl θ hker σ hσ hstab hfix
    hmove
  exact partner_pattern_of_innerDiag hodd h5 hm θ hker σ hσ g hg hfix hmove

theorem partner_chart_three_amb [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hcl : LinearAutClassification F (3 + 1)) {Y : Type} [Group Y] (θ : SL(3 + 1, F) →* Y)
    (hker : θ.ker ≤ Subgroup.center SL(3 + 1, F)) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ A : SL(2, F), σ (θ (blockSL2 F 3 ⟨2, by omega⟩ A)) =
      θ (blockSL2 F 3 ⟨2, by omega⟩ A))
    (hmove : ∃ A : SL(2, F), σ (θ (blockSL2 F 3 ⟨0, by omega⟩ A)) ≠
      θ (blockSL2 F 3 ⟨0, by omega⟩ A)) :
    ∃ h : GL (Fin (3 + 1)) F,
      (blockSL2 F 3 ⟨0, by omega⟩).range.map (slConjugation (3 + 1) F h).toMonoidHom =
        (blockSL2 F 3 ⟨0, by omega⟩).range ∧
      (∀ A : SL(2, F), slConjugation (3 + 1) F h (blockSL2 F 3 ⟨2, by omega⟩ A) =
        blockSL2 F 3 ⟨2, by omega⟩ A) ∧
      ∀ x, σ (θ (slConjugation (3 + 1) F h x)) =
        θ (slConjugation (3 + 1) F h (slConjugation (3 + 1) F (partnerDiag 3 1) x)) := by
  obtain ⟨g, hg⟩ := innerDiag_of_partner_blocks_amb hodd h5 (m := 3) (by omega) hcl θ hker σ hσ
    hstab (fun a ha A => by
      have : a = ⟨2, by omega⟩ := by
        rcases ha with ha | ⟨ha1, ha2⟩
        · exact Fin.ext (by simp only; omega)
        · omega
      subst this
      exact hfix A) hmove
  exact partner_chart_three hodd h5 θ hker σ hσ g hg hfix hmove

end CFSG.ClassicalInvolution.RouteD.Gaps
