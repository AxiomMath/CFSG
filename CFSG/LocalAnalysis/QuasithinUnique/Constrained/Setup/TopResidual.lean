module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopNodes

public section

namespace CFSG.QuasithinUnique.Setup.Top

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Lift
open scoped Pointwise

variable {G : Type} [Group G]

theorem isConjAction_unique {A : Type} [Group A] {H L : Subgroup A} (hLH : L ≤ H)
    (hn : (L.subgroupOf H).Normal) {α α' : ↥H →* MulAut (CQ L)} (hα : IsConjAction H L α)
    (hα' : IsConjAction H L α') : α = α' := by
  ext h q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hl : (⟨l.1, hLH l.2⟩ : ↥H) ∈ L.subgroupOf H := l.2
  have hl' : h * ⟨l.1, hLH l.2⟩ * h⁻¹ ∈ L.subgroupOf H := hn.conj_mem _ hl h
  have h1 := hα h l ⟨(h : A) * l * (h : A)⁻¹, hl'⟩ rfl
  have h2 := hα' h l ⟨(h : A) * l * (h : A)⁻¹, hl'⟩ rfl
  rw [h1, h2]

theorem residual_bundle [Finite G] (hSQT : NonsolvableActionSQT) (hone : OneQuasisimpleResidualProp)
    (hfam : FamilyRestrictionProp) {S P : Subgroup G} (h : PushUpObstruction S P)
    (hns : ¬ Group.IsSolvable (autOn P (reducedModule S P)))
    (hno : NoEvenSL2Component (autOn P (reducedModule S P))) :
    ∃ (L : Subgroup (MulAut (reducedModule S P)))
      (E : Subgroup (MulAut (reducedModule S P))),
      OneQuasisimpleData S P (reducedAction_of_pushUpObstruction h).isElemAbelian
        (reducedAction_of_pushUpObstruction h).le_normalizer L ∧ ResidualFamily (CQ L) ∧
      @FFHyp (reducedModule S P)
        (commGroupOfElemAbelian (reducedAction_of_pushUpObstruction h).isElemAbelian)
        inferInstance (autOn P (reducedModule S P)) (autOn S (reducedModule S P))
        (autOn (uniqueMaxOver S P) (reducedModule S P)) E ∧
      IsSQTKCat (autOn P (reducedModule S P)) := by
  have hR := reducedAction_of_pushUpObstruction h
  have hV := hR.isElemAbelian
  have hP := hR.le_normalizer
  let _ : CommGroup (reducedModule S P) := commGroupOfElemAbelian hV
  have hsqtk : IsSQTKCat (autOn P (reducedModule S P)) :=
    ⟨hSQT G S P h hns, hR.isKGroupCat_autOn⟩
  obtain ⟨A, hA⟩ := hR.offender
  have hFF := ffHyp_of_offender hR hA
  obtain ⟨L, hL⟩ := @hone (reducedModule S P) (commGroupOfElemAbelian hV) inferInstance
    (autOn P (reducedModule S P)) (autOn S (reducedModule S P))
    (autOn (uniqueMaxOver S P) (reducedModule S P)) (autOn A (reducedModule S P)) hFF hns hsqtk hno
  have hfamL := (@hfam (reducedModule S P) (commGroupOfElemAbelian hV) inferInstance
    (autOn P (reducedModule S P)) (autOn S (reducedModule S P))
    (autOn (uniqueMaxOver S P) (reducedModule S P)) (autOn A (reducedModule S P)) hFF hns hsqtk hno
    L hL.isComp).1
  refine ⟨L, autOn A (reducedModule S P), ⟨hL, ?_, ?_⟩, hfamL, hFF, hsqtk⟩
  · intro α hα p
    obtain ⟨α₀, hα₀, hker, -⟩ := hL.action
    obtain rfl : α = α₀ := isConjAction_unique hL.isComp.1 hL.normal hα hα₀
    have hmem : (⟨rho (reducedModule S P) P hP p, (mem_autOn_self_iff hP).2 ⟨p, rfl⟩⟩ :
        ↥(autOn P (reducedModule S P))) ∈ α.ker ↔ _ := Iff.rfl
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  · have hNP : oddOrderSubgroup P ≤ P := oddOrderSubgroup_le P
    have hNL : ∀ n : ↥(oddOrderSubgroup P),
        rho (reducedModule S P) P hP ⟨n, hNP n.2⟩ ∈ L := by
      intro n
      have h1 : rho (reducedModule S P) P hP ⟨n, hNP n.2⟩ ∈
          autOn (oddOrderSubgroup P) (reducedModule S P) :=
        (mem_autOn_iff_rho hP hNP).mpr ⟨⟨n, hNP n.2⟩, n.2, rfl⟩
      rw [autOn_oddOrderSubgroup hP, hL.K_eq] at h1
      exact h1
    refine ⟨((rho (reducedModule S P) P hP).comp (Subgroup.inclusion hNP)).codRestrict L hNL,
      ?_, ?_, fun n => rfl⟩
    · intro l
      have h1 : (l : MulAut (reducedModule S P)) ∈
          autOn (oddOrderSubgroup P) (reducedModule S P) := by
        rw [autOn_oddOrderSubgroup hP, hL.K_eq]
        exact l.2
      obtain ⟨p, hpN, hp⟩ := (mem_autOn_iff_rho hP hNP).mp h1
      exact ⟨⟨p, hpN⟩, Subtype.ext hp⟩
    · ext n
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro hn
        have h1 : rho (reducedModule S P) P hP ⟨n, hNP n.2⟩ = 1 :=
          congrArg Subtype.val hn
        exact ⟨hNP n.2, (rho_eq_one_iff hP ⟨n, hNP n.2⟩).mp h1⟩
      · rintro ⟨-, hn⟩
        exact Subtype.ext ((rho_eq_one_iff hP ⟨n, hNP n.2⟩).mpr hn)

theorem linearThreeOrSymplecticFour (hSQT : NonsolvableActionSQT)
    (hone : OneQuasisimpleResidualProp) (hfam : FamilyRestrictionProp) (hA6 : NoAlt6Component)
    (hU33 : NoPSU33Component) (hU32 : NoEvenUnitaryThreeComponent)
    (hTri : NoTrialityOrLargeReeComponent) (hG2 : NoG2OrTitsComponent) :
    ∀ (G : Type) [Group G] [Finite G] (S P : Subgroup G) (h : PushUpObstruction S P),
      ¬ Group.IsSolvable (autOn P (reducedModule S P)) →
      NoEvenSL2Component (autOn P (reducedModule S P)) →
      ∃ L : Subgroup (MulAut (reducedModule S P)),
        OneQuasisimpleData S P (reducedAction_of_pushUpObstruction h).isElemAbelian
          (reducedAction_of_pushUpObstruction h).le_normalizer L ∧
        (∃ f : ℕ, 2 ≤ f ∧ (StatedClassicalModel (CQ L) .PSL 3 2 f ∨
          StatedClassicalModel (CQ L) .PSp 2 2 f)) ∧
        ActorData S P (reducedAction_of_pushUpObstruction h).isElemAbelian := by
  intro G _ _ S P h hns hno
  obtain ⟨L, E, hdata, hfamL, hFF, hsqtk⟩ := residual_bundle hSQT hone hfam h hns hno
  have hV := (reducedAction_of_pushUpObstruction h).isElemAbelian
  let _ : CommGroup (reducedModule S P) := commGroupOfElemAbelian hV
  have hLc := hdata.residual.isComp
  refine ⟨L, hdata, ?_, hsqtk, E, hFF⟩
  rcases hfamL with h6 | h33 | ⟨f, hf, hmodel⟩ | ⟨f, hf, hmodel⟩ | ⟨f, hf, hmodel⟩ |
    ⟨f, hodd, h3, hmodel⟩ | hTits
  · exact absurd h6 (@hA6 (reducedModule S P) (commGroupOfElemAbelian hV) inferInstance _ _ _ E
      hFF hns hsqtk L hLc)
  · exact absurd h33 (@hU33 (reducedModule S P) (commGroupOfElemAbelian hV) inferInstance _ _ _ E
      hFF hns hsqtk L hLc)
  · rcases hmodel with h3 | hU | h4
    · exact ⟨f, hf, Or.inl h3⟩
    · exact absurd hU (@hU32 (reducedModule S P) (commGroupOfElemAbelian hV) inferInstance _ _ _ E
        hFF hns hsqtk L hLc f hf)
    · exact ⟨f, hf, Or.inr h4⟩
  · exact absurd hmodel ((@hG2 (reducedModule S P) (commGroupOfElemAbelian hV) inferInstance
      _ _ _ E hFF hns hsqtk L hLc).1 f hf)
  · exact absurd hmodel ((@hTri (reducedModule S P) (commGroupOfElemAbelian hV) inferInstance
      _ _ _ E hFF hns hsqtk L hLc).1 f hf)
  · exact absurd hmodel ((@hTri (reducedModule S P) (commGroupOfElemAbelian hV) inferInstance
      _ _ _ E hFF hns hsqtk L hLc).2 f hodd h3)
  · exact absurd hTits (@hG2 (reducedModule S P) (commGroupOfElemAbelian hV) inferInstance
      _ _ _ E hFF hns hsqtk L hLc).2

theorem evenLinearThree (hSQT : NonsolvableActionSQT) (hone : OneQuasisimpleResidualProp)
    (hfam : FamilyRestrictionProp) (hA6 : NoAlt6Component) (hU33 : NoPSU33Component)
    (hU32 : NoEvenUnitaryThreeComponent) (hTri : NoTrialityOrLargeReeComponent)
    (hG2 : NoG2OrTitsComponent) (hSp4 : NoPSp4Component) :
    ∀ (G : Type) [Group G] [Finite G] (S P : Subgroup G) (h : PushUpObstruction S P),
      ¬ Group.IsSolvable (autOn P (reducedModule S P)) →
      NoEvenSL2Component (autOn P (reducedModule S P)) →
      ∃ L : Subgroup (MulAut (reducedModule S P)),
        OneQuasisimpleData S P (reducedAction_of_pushUpObstruction h).isElemAbelian
          (reducedAction_of_pushUpObstruction h).le_normalizer L ∧
        (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel (CQ L) .PSL 3 2 f) ∧
        ActorData S P (reducedAction_of_pushUpObstruction h).isElemAbelian := by
  intro G _ _ S P h hns hno
  obtain ⟨L, hdata, ⟨f, hf, hmodel⟩, hact⟩ :=
    linearThreeOrSymplecticFour hSQT hone hfam hA6 hU33 hU32 hTri hG2 G S P h hns hno
  refine ⟨L, hdata, ⟨f, hf, ?_⟩, hact⟩
  rcases hmodel with h3 | h4
  · exact h3
  · obtain ⟨hsqtk, E, hFF⟩ := hact
    have hV := (reducedAction_of_pushUpObstruction h).isElemAbelian
    let _ : CommGroup (reducedModule S P) := commGroupOfElemAbelian hV
    exact absurd h4 (@hSp4 (reducedModule S P) (commGroupOfElemAbelian hV) inferInstance _ _ _ E
      hFF hns hsqtk L hdata.residual.isComp f hf)

end CFSG.QuasithinUnique.Setup.Top
