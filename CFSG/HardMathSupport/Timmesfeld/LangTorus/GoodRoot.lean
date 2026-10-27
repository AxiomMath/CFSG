module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false

section Defs

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def rhoOrbitPM (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (β : Fin τ.rank → ℤ) :
    Set (Fin τ.rank → ℤ) :=
  {γ | ∃ j : ℕ, γ = (ρ : (Fin τ.rank → ℤ) → _)^[j] β ∨ γ = (ρ : (Fin τ.rank → ℤ) → _)^[j] (-β)}

@[expose] def IsGoodRoot (S : LangSetup τ L p) (β : Fin τ.rank → ℤ) : Prop :=
  IsRoot τ β ∧ ∃ Y : Subgroup (ModGL τ L), Y ≤ S.Γ ∧ ⁅Y, Y⁆ = Y ∧
    Y ≤ rootSpan τ L (rhoOrbitPM S.ρ β) ∧ (∃ x ∈ Y, orderOf x = p) ∧
    (∀ z : ModGL τ L, (∀ y ∈ Y, Commute z y) → ∀ x ∈ rootRankOneGroup τ L β, Commute z x) ∧
    (∀ (r f j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f → 0 < j → j < f →
      ∀ z : ModGL τ L, ¬ ∀ y ∈ Y,
        z * Units.map (entrywiseHom (iterateFrobenius L r j)) y * z⁻¹ = y)

inductive ReflClosure (τ : Tag) (G : Set (Fin τ.rank → ℤ)) : (Fin τ.rank → ℤ) → Prop
  | base {γ} : γ ∈ G → ReflClosure τ G γ
  | refl {α γ} : IsRoot τ α → ReflClosure τ G α → ReflClosure τ G γ →
      ReflClosure τ G (γ - (2 * iform α γ / iform α α) • α)

theorem ReflClosure.nonempty {G : Set (Fin τ.rank → ℤ)} {γ : Fin τ.rank → ℤ}
    (h : ReflClosure τ G γ) : G.Nonempty := by
  induction h with
  | base hγ => exact ⟨_, hγ⟩
  | refl _ _ _ _ ih => exact ih

@[expose] def GoodRootsGenerate (S : LangSetup τ L p) : Prop :=
  ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ReflClosure τ {β | IsGoodRoot S β} γ

end Defs

section Refl

variable {τ : Tag} {L : Type} [Field L]

theorem rootRankOneGroup_eq_rootSpan_pair {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootRankOneGroup τ L β = rootSpan τ L {β, -β} := by
  rw [(exceptional_Lang_root_rank_one_torus_transport τ L hβ).1]
  apply le_antisymm
  · exact sup_le (le_iSup₂_of_le (f := fun γ (_ : γ ∈ ({β, -β} : Set (Fin τ.rank → ℤ))) =>
      rootSubgroup τ L γ) β (Set.mem_insert _ _) le_rfl)
      (le_iSup₂_of_le (f := fun γ (_ : γ ∈ ({β, -β} : Set (Fin τ.rank → ℤ))) =>
      rootSubgroup τ L γ) (-β) (Set.mem_insert_of_mem _ rfl) le_rfl)
  · refine iSup₂_le fun γ hγ => ?_
    rcases hγ with rfl | hγ
    · exact le_sup_left
    · rw [Set.mem_singleton_iff.1 hγ]
      exact le_sup_right

theorem commute_rankOne_reflect {z : ModGL τ L} {α γ : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hγ : IsRoot τ γ) (hzα : ∀ x ∈ rootRankOneGroup τ L α, Commute z x)
    (hzγ : ∀ x ∈ rootRankOneGroup τ L γ, Commute z x) :
    ∀ x ∈ rootRankOneGroup τ L (γ - (2 * iform α γ / iform α α) • α), Commute z x := by
  classical
  set w := rootReflection α with hw
  have hwγ : w • γ = γ - (2 * iform α γ / iform α α) • α :=
    ((exceptional_Lang_root_rank_one_torus_transport τ L hα).2.2.2.1 γ).1
  have hγ' : IsRoot τ (w • γ) := IsRoot.smul hγ w
  rw [← hwγ] at *
  obtain ⟨hsup, hmon, hmaps⟩ := rootWeylOne_spec (K := L) hα
  have hn : Commute z (rootWeylOne τ L α) := by
    apply hzα
    rw [(exceptional_Lang_root_rank_one_torus_transport τ L hα).1]
    exact hsup
  have hwinv : w⁻¹ • (w • γ) = γ := inv_smul_smul w γ
  intro x hx
  rw [rootRankOneGroup_eq_rootSpan_pair hγ'] at hx
  have hmaps' : MapsRootLines (rootWeylOne τ L α)⁻¹ w⁻¹ := hmaps.inv
  have hS : ∀ a ∈ ({w • γ, -(w • γ)} : Set (Fin τ.rank → ℤ)), IsRoot τ a := by
    rintro a (rfl | ha)
    · exact hγ'
    · rw [Set.mem_singleton_iff.1 ha]
      exact IsRoot.neg hγ'
  have h1 := conj_mem_rootSpan_of_mapsRootLines (inv_mem hmon) hmaps' hS hx
  have himg : ((fun a => w⁻¹ • a) '' ({w • γ, -(w • γ)} : Set (Fin τ.rank → ℤ))) = {γ, -γ} := by
    rw [Set.image_pair, hwinv, smul_neg, hwinv]
  rw [himg, ← rootRankOneGroup_eq_rootSpan_pair hγ] at h1
  have h2 := hzγ _ h1
  have e : x = (rootWeylOne τ L α) * ((rootWeylOne τ L α)⁻¹ * x * ((rootWeylOne τ L α)⁻¹)⁻¹) *
      (rootWeylOne τ L α)⁻¹ := by group
  rw [e]
  exact (hn.mul_right h2).mul_right hn.inv_right

end Refl

section Assembly

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem goodRoot_subset_bigComponentSet (S : LangSetup τ L p) {D₁ : Subgroup (ModGL τ L)}
    (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2) {β : Fin τ.rank → ℤ} (hg : IsGoodRoot S β) :
    ∃ Y : Subgroup (ModGL τ L), (Y : Set (ModGL τ L)) ⊆ bigComponentSet S D₁ ∧
      (∀ z : ModGL τ L, (∀ y ∈ Y, Commute z y) → ∀ x ∈ rootRankOneGroup τ L β, Commute z x) ∧
      (∀ (r f j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f → 0 < j → j < f →
        ∀ z : ModGL τ L, ¬ ∀ y ∈ Y,
          z * Units.map (entrywiseHom (iterateFrobenius L r j)) y * z⁻¹ = y) := by
  obtain ⟨hβ, Y, hYΓ, hYp, hYspan, ⟨x, hxY, hxp⟩, hcomm, hfield⟩ := hg
  exact ⟨Y, subset_bigComponentSet_of_perfect S hD₁E hD₁c hβ hYΓ hYp hYspan hxY hxp, hcomm, hfield⟩

theorem noFrobeniusInner_of_goodRoot (S : LangSetup τ L p) {D₁ : Subgroup (ModGL τ L)}
    (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2) {β : Fin τ.rank → ℤ} (hg : IsGoodRoot S β) :
    NoFrobeniusInner S D₁ := by
  intro r f j _ hr hqf hj0 hjf z hz
  obtain ⟨Y, hYbig, -, hfield⟩ := goodRoot_subset_bigComponentSet S hD₁E hD₁c hg
  exact hfield r f j hr hqf hj0 hjf z fun y hy => hz y (Or.inl (hYbig hy))

theorem noFrobeniusInner_of_goodRootsGenerate (S : LangSetup τ L p) (hgen : GoodRootsGenerate S)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2) :
    NoFrobeniusInner S D₁ := by
  obtain ⟨β, hβ⟩ := (hgen _ (isRoot_single τ ⟨0, by cases τ <;> decide⟩)).nonempty
  exact noFrobeniusInner_of_goodRoot S hD₁E hD₁c hβ

theorem centralizes_adjointGroup_of_goodRoots (S : LangSetup τ L p) (hgen : GoodRootsGenerate S)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2)
    {z : ModGL τ L} (hcomm : ∀ x ∈ rigidTestSet S D₁, Commute z x) :
    ∀ g ∈ adjointGroup τ L, Commute z g := by
  have key : ∀ γ, ReflClosure τ {β | IsGoodRoot S β} γ →
      IsRoot τ γ ∧ ∀ x ∈ rootRankOneGroup τ L γ, Commute z x := by
    intro γ hγ
    induction hγ with
    | base hg =>
      refine ⟨hg.1, ?_⟩
      obtain ⟨Y, hYbig, hYc, -⟩ := goodRoot_subset_bigComponentSet S hD₁E hD₁c hg
      exact hYc z fun y hy => hcomm y (Or.inl (hYbig hy))
    | @refl α γ hα _ _ ihα ihγ =>
      exact ⟨by
        have hw := ((exceptional_Lang_root_rank_one_torus_transport τ L hα).2.2.2.1 γ).1
        rw [← hw]
        exact IsRoot.smul ihγ.1 _, commute_rankOne_reflect hα ihγ.1 ihα.2 ihγ.2⟩
  exact commute_adjointGroup_of_simple fun i => (key _ (hgen _ (isRoot_single τ i))).2

theorem centralizerTrivial_of_goodRoots (S : LangSetup τ L p) (hgen : GoodRootsGenerate S)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2) :
    CentralizerTrivial S D₁ := by
  intro z hzC hcomm
  have hle := centralizes_adjointGroup_of_goodRoots S hgen hD₁E hD₁c hcomm
  have hcent : (⟨z, hzC⟩ : adjointGroup τ L) ∈ Subgroup.center (adjointGroup τ L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hle g g.2).eq.symm
  rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
  exact congrArg Subtype.val hcent

end Assembly

end CFSG.HardMathSupport.Timmesfeld.LangTorus
