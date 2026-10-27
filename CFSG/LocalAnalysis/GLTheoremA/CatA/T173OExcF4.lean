module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcWeyl

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType

@[expose] def IsLongRoot (α : Fin Tag.F4.rank → ℤ) : Prop :=
  ∃ w : WeylGroup .F4, w • (Pi.single (⟨0, by decide⟩ : Fin Tag.F4.rank) 1) = α

@[expose] def IsShortRoot (α : Fin Tag.F4.rank → ℤ) : Prop :=
  ∃ w : WeylGroup .F4, w • (Pi.single (⟨3, by decide⟩ : Fin Tag.F4.rank) 1) = α

theorem IsLongRoot.isRoot {α : Fin Tag.F4.rank → ℤ} (h : IsLongRoot α) : IsRoot .F4 α := by
  obtain ⟨w, rfl⟩ := h
  exact IsRoot.smul (.basis _) w

theorem IsShortRoot.isRoot {α : Fin Tag.F4.rank → ℤ} (h : IsShortRoot α) : IsRoot .F4 α := by
  obtain ⟨w, rfl⟩ := h
  exact IsRoot.smul (.basis _) w

theorem isLongRoot_or_isShortRoot
    {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) : IsLongRoot α ∨ IsShortRoot α := by
  induction hα with
  | basis j =>
    fin_cases j
    · exact Or.inl ⟨1, one_smul _ _⟩
    · exact Or.inl (exists_weyl_smul_single_of_cartan (τ := .F4)
        (i := (⟨0, by decide⟩ : Fin Tag.F4.rank)) (j := ⟨1, by decide⟩) (by decide) (by decide))
    · exact Or.inr (exists_weyl_smul_single_of_cartan (τ := .F4)
        (i := (⟨3, by decide⟩ : Fin Tag.F4.rank)) (j := ⟨2, by decide⟩) (by decide) (by decide))
    · exact Or.inr ⟨1, one_smul _ _⟩
  | reflect i hv ih =>
    rcases ih with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact Or.inl ⟨simple .F4 i * w, by rw [mul_smul, hw, simple_smul]⟩
    · exact Or.inr ⟨simple .F4 i * w, by rw [mul_smul, hw, simple_smul]⟩

theorem exists_weyl_smul_eq_of_isLong {α β : Fin Tag.F4.rank → ℤ} (hα : IsLongRoot α)
    (hβ : IsLongRoot β) : ∃ w : WeylGroup .F4, w • α = β := by
  obtain ⟨wα, hα⟩ := hα
  obtain ⟨wβ, hβ⟩ := hβ
  exact ⟨wβ * wα⁻¹, by rw [mul_smul, ← hα, inv_smul_smul, hβ]⟩

theorem exists_weyl_smul_eq_of_isShort {α β : Fin Tag.F4.rank → ℤ} (hα : IsShortRoot α)
    (hβ : IsShortRoot β) : ∃ w : WeylGroup .F4, w • α = β := by
  obtain ⟨wα, hα⟩ := hα
  obtain ⟨wβ, hβ⟩ := hβ
  exact ⟨wβ * wα⁻¹, by rw [mul_smul, ← hα, inv_smul_smul, hβ]⟩

theorem eq_top_of_rootSubgroup_le_F4 (F : Type) [Field F] (p : ℕ)
    {X : Subgroup ↥(adjointGroup .F4 F)}
    (hN : Subgroup.normalizer
        ((TableBExc.torusPow .F4 F p : Subgroup ↥(adjointGroup .F4 F)) :
          Set ↥(adjointGroup .F4 F)) ≤
      Subgroup.normalizer (X : Set ↥(adjointGroup .F4 F)))
    {α β : Fin Tag.F4.rank → ℤ} (hα : IsLongRoot α) (hβ : IsShortRoot β)
    (hαX : (rootSubgroup .F4 F α).subgroupOf (adjointGroup .F4 F) ≤ X)
    (hβX : (rootSubgroup .F4 F β).subgroupOf (adjointGroup .F4 F) ≤ X) : X = ⊤ := by
  have hroot : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot .F4 γ →
      (rootSubgroup .F4 F γ).subgroupOf (adjointGroup .F4 F) ≤ X := by
    intro γ hγ
    rcases isLongRoot_or_isShortRoot hγ with hγL | hγS
    · obtain ⟨w, hw⟩ := exists_weyl_smul_eq_of_isLong hα hγL
      exact rootSubgroup_subgroupOf_le_of_weyl_smul F p hN hα.isRoot hαX w hw
    · obtain ⟨w, hw⟩ := exists_weyl_smul_eq_of_isShort hβ hγS
      exact rootSubgroup_subgroupOf_le_of_weyl_smul F p hN hβ.isRoot hβX w hw
  set S : Set (ModGL .F4 F) := {g | ∃ (i : Fin Tag.F4.rank) (c : F),
    (g : Module.End F (RootModule .F4 F)) = xOp .F4 F i c ∨
      (g : Module.End F (RootModule .F4 F)) = yOp .F4 F i c}
  have hgen : Subgroup.closure (((↑) : ↥(adjointGroup .F4 F) → ModGL .F4 F) ⁻¹' S) = ⊤ :=
    Subgroup.closure_closure_coe_preimage (k := S)
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro g ⟨i, c, hg | hg⟩
  · have hgx : g = ⟨xUnit .F4 F i c, xUnit_mem_adjointGroup i c⟩ := by
      apply Subtype.ext
      exact Units.ext hg
    rw [hgx]
    exact hroot _ (IsRoot.basis i) (Subgroup.mem_subgroupOf.2 (by
      change xUnit .F4 F i c ∈ rootSubgroup .F4 F (Pi.single i 1)
      rw [← pinnedX_single]
      exact Subgroup.subset_closure ⟨c, rfl⟩))
  · have hgy : g = ⟨yUnit .F4 F i c, yUnit_mem_adjointGroup i c⟩ := by
      apply Subtype.ext
      exact Units.ext hg
    rw [hgy]
    exact hroot _ (IsRoot.neg (IsRoot.basis i)) (Subgroup.mem_subgroupOf.2 (by
      change yUnit .F4 F i c ∈ rootSubgroup .F4 F (-Pi.single i 1)
      rw [← pinnedX_neg_single]
      exact Subgroup.subset_closure ⟨c, rfl⟩))

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
