module

public import CFSG.LocalAnalysis.ComponentClassification.SolvableRadical
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core

public section

namespace CFSG.ComponentClassification.Fitting

@[expose] noncomputable def subgroup (G : Type*) [Group G] : Subgroup G :=
  CFSG.fittingSubgroup G

theorem subgroup.eq_sSup (G : Type*) [Group G] :
    subgroup G = sSup {candidate : Subgroup G | candidate.Normal ∧ Group.IsNilpotent candidate} :=
  rfl

attribute [eqns subgroup.eq_sSup] subgroup

theorem normal (G : Type*) [Group G] : (subgroup G).Normal :=
  Subgroup.sSup_normal _ (fun _ hcandidate => hcandidate.1)

theorem maximal {G : Type*} [Group G] (candidate : Subgroup G) [candidate.Normal]
    [Group.IsNilpotent candidate] : candidate ≤ subgroup G :=
  le_sSup ⟨inferInstance, inferInstance⟩

theorem le_radical (G : Type*) [Group G] : subgroup G ≤ SolvableRadical.subgroup G := by
  apply sSup_le
  intro candidate hcandidate
  let : candidate.Normal := hcandidate.1
  let : Group.IsNilpotent candidate := hcandidate.2
  exact SolvableRadical.maximal candidate

theorem solvable (G : Type*) [Group G] [Finite G] : Group.IsSolvable (subgroup G) := by
  let : Group.IsSolvable (SolvableRadical.subgroup G) := SolvableRadical.solvable G
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (le_radical G))

theorem characteristic (G : Type*) [Group G] : (subgroup G).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro automorphism
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro candidate hcandidate
  let : candidate.Normal := hcandidate.1
  let : Group.IsNilpotent candidate := hcandidate.2
  let : (candidate.map automorphism.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance automorphism.toMonoidHom automorphism.surjective
  let : Group.IsNilpotent (candidate.map automorphism.toMonoidHom) :=
    (Group.isNilpotent_congr (automorphism.subgroupMap candidate)).mp inferInstance
  exact Subgroup.map_le_iff_le_comap.mp (maximal (candidate.map automorphism.toMonoidHom))

theorem nilpotent_of_commutator_le_center {G : Type*} [Group G]
    (hcentral : commutator G ≤ Subgroup.center G) : Group.IsNilpotent G := by
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  refine ⟨2, ?_⟩
  apply Subgroup.lowerCentralSeries_succ_eq_bot
  simpa only [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero,
    ← commutator_def] using hcentral

theorem nilpotent_of_ambient_commutator_le_center {G : Type*} [Group G]
    (candidate : Subgroup G) (hcentral : ⁅candidate, candidate⁆ ≤ Subgroup.center G) :
    Group.IsNilpotent candidate := by
  apply nilpotent_of_commutator_le_center
  intro member hmember
  have hambient : member.val ∈ Subgroup.center G := hcentral
    (Subgroup.map_subtype_commutator candidate ▸
      Subgroup.mem_map_of_mem candidate.subtype hmember)
  apply Subgroup.mem_center_iff.mpr
  intro other
  exact Subtype.ext (Subgroup.mem_center_iff.mp hambient other.val)

theorem solvable_normal_central_of_nilpotent_normal_central {G : Type*} [Group G]
    (hnilpotent : ∀ candidate : Subgroup G, candidate.Normal → Group.IsNilpotent candidate →
      candidate ≤ Subgroup.center G)
    (solvableNormal : Subgroup G) [solvableNormal.Normal] [Group.IsSolvable solvableNormal] :
    solvableNormal ≤ Subgroup.center G := by
  have hdescend : ∀ stage : ℕ, (derivedSeries solvableNormal stage).map solvableNormal.subtype ≤
      Subgroup.center G → solvableNormal ≤ Subgroup.center G := by
    intro stage
    induction stage with
    | zero =>
        intro hcentral member hmember
        apply hcentral
        rw [derivedSeries_zero]
        exact Subgroup.mem_map.mpr ⟨⟨member, hmember⟩, Subgroup.mem_top _, rfl⟩
    | succ stage hinduction =>
        intro hcentral
        let image := (derivedSeries solvableNormal stage).map solvableNormal.subtype
        let : image.Normal := ConjAct.normal_of_characteristic_of_normal
        have hderived : ⁅image, image⁆ ≤ Subgroup.center G := by
          rw [← Subgroup.map_commutator, ← derivedSeries_succ]
          exact hcentral
        exact hinduction (hnilpotent image inferInstance
          (nilpotent_of_ambient_commutator_le_center image hderived))
  obtain ⟨stage, hbot⟩ := Group.IsSolvable.solvable (G := solvableNormal)
  apply hdescend stage
  rw [hbot, Subgroup.map_bot]
  exact bot_le

theorem radical_le_center_of_fitting_le_center {G : Type*} [Group G] [Finite G]
    (hcentral : subgroup G ≤ Subgroup.center G) :
    SolvableRadical.subgroup G ≤ Subgroup.center G := by
  let : (SolvableRadical.subgroup G).Normal := SolvableRadical.normal G
  let : Group.IsSolvable (SolvableRadical.subgroup G) := SolvableRadical.solvable G
  apply solvable_normal_central_of_nilpotent_normal_central _ (SolvableRadical.subgroup G)
  intro candidate hnormal hnilpotent
  let : candidate.Normal := hnormal
  let : Group.IsNilpotent candidate := hnilpotent
  exact (maximal candidate).trans hcentral

theorem solvable_normal_centralizing_fitting_le {G : Type*} [Group G]
    (solvableNormal : Subgroup G) [solvableNormal.Normal] [Group.IsSolvable solvableNormal]
    (hcommutes : ⁅solvableNormal, subgroup G⁆ = ⊥) : solvableNormal ≤ subgroup G := by
  have hdescend : ∀ stage : ℕ, (derivedSeries solvableNormal stage).map solvableNormal.subtype ≤
      subgroup G → solvableNormal ≤ subgroup G := by
    intro stage
    induction stage with
    | zero =>
        intro hle member hmember
        apply hle
        rw [derivedSeries_zero]
        exact Subgroup.mem_map.mpr ⟨⟨member, hmember⟩, Subgroup.mem_top _, rfl⟩
    | succ stage hinduction =>
        intro hle
        let image := (derivedSeries solvableNormal stage).map solvableNormal.subtype
        let : image.Normal := ConjAct.normal_of_characteristic_of_normal
        have hderived : ⁅image, image⁆ ≤ subgroup G := by
          rw [← Subgroup.map_commutator, ← derivedSeries_succ]
          exact hle
        have hintrinsic : commutator image ≤ Subgroup.center image := by
          intro member hmember
          have hmem : member.val ∈ subgroup G := hderived
            (Subgroup.map_subtype_commutator image ▸ Subgroup.mem_map_of_mem image.subtype hmember)
          apply Subgroup.mem_center_iff.mpr
          intro other
          have hother : other.val ∈ solvableNormal :=
            Subgroup.map_subtype_le _ other.property
          exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes hother) member.val hmem).symm
        let : Group.IsNilpotent image := nilpotent_of_commutator_le_center hintrinsic
        exact hinduction (maximal image)
  obtain ⟨stage, hbot⟩ := Group.IsSolvable.solvable (G := solvableNormal)
  apply hdescend stage
  rw [hbot, Subgroup.map_bot]
  exact bot_le

end CFSG.ComponentClassification.Fitting
