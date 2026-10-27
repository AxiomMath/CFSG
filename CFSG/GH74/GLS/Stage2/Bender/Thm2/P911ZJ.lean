module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open Subgroup CFSG CFSG.GH74.GLS.Bg

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

theorem center_component_le_fitting {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (hK : IsComponent K) : (Subgroup.center K).map K.subtype ≤ fittingSubgroup X := by
  have hZKE : (Subgroup.center K).map K.subtype ≤ layer X :=
    (Subgroup.map_subtype_le _).trans (le_sSup hK)
  have hZKC : (Subgroup.center K).map K.subtype ≤ Subgroup.centralizer (layer X : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    refine sSup_le fun K' hK' => ?_
    rw [← Subgroup.le_centralizer_iff]
    rcases LocalCores.distinct_components_commute hK hK' with rfl | hcomm
    · rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
    · exact (Subgroup.map_subtype_le _).trans
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have : (layer X).Characteristic := LocalCores.layer_characteristic
  have hWn : (layer X ⊓ Subgroup.centralizer (layer X : Set X)).Normal :=
    Subgroup.normal_inf_normal _ _
  have hWcomm : IsMulCommutative (layer X ⊓ Subgroup.centralizer (layer X : Set X) : Subgroup X) :=
    ⟨⟨fun x y => Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2.2 y y.2.1).symm⟩⟩
  have hWF : layer X ⊓ Subgroup.centralizer (layer X : Set X) ≤ fittingSubgroup X :=
    LocalCores.fitting_characteristic.2.2 _ hWn inferInstance
  exact (le_inf hZKE hZKC).trans hWF

theorem isPGroup_center_of_component {G : Type} [Group G] [Finite G] {N : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hFm : Fm N = Op p N) {J : Subgroup ↥N} (hJ : IsComponent J) :
    IsPGroup p ↥(Subgroup.center ↥J) := by
  have : Fact p.Prime := ⟨hp⟩
  have hF : fittingSubgroup ↥N = pCore p ↥N := by
    have h1 : (fittingSubgroup ↥N).map N.subtype = (pCore p ↥N).map N.subtype := by
      have := hFm
      rw [Fm, Op] at this
      exact this
    exact Subgroup.map_injective N.subtype_injective h1
  have hZ : (Subgroup.center ↥J).map J.subtype ≤ pCore p ↥N :=
    hF ▸ center_component_le_fitting hJ
  have hpg : IsPGroup p ↥((Subgroup.center ↥J).map J.subtype) := CFSG.pCore_isPGroup.to_le hZ
  exact hpg.of_equiv (Subgroup.equivMapOfInjective _ J.subtype J.subtype_injective).symm

theorem odd_card_center_of_component {G : Type} [Group G] [Finite G] {N : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hFm : Fm N = Op p N) {J : Subgroup ↥N} (hJ : IsComponent J) :
    Odd (Nat.card ↥(Subgroup.center ↥J)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (isPGroup_center_of_component hp hFm hJ)
  rw [hn]
  exact hpodd.pow

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
