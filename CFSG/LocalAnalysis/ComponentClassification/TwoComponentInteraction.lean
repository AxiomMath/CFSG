module

public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentSubnormal
public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoComponentInteraction

theorem core_ne_top {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (hcomponent : TwoComponents.IsTwoComponent component) :
    componentClassificationOddCore component ≠ ⊤ := by
  intro htop
  let : Nontrivial (component ⧸ componentClassificationOddCore component) :=
    Quasisimple.nontrivial (TwoComponents.quasisimple_quotient hcomponent)
  obtain ⟨left, right, hne⟩ := exists_pair_ne
    (component ⧸ componentClassificationOddCore component)
  have hsubsingleton : Subsingleton (component ⧸ componentClassificationOddCore component) :=
    QuotientGroup.subsingleton_iff.mpr htop
  exact hne (hsubsingleton.elim _ _)

theorem quasisimple_iff_core_central {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (hcomponent : TwoComponents.IsTwoComponent component) :
    IsQuasisimple component ↔
      componentClassificationOddCore component ≤ Subgroup.center component := by
  constructor
  · intro hquasisimple
    exact Quasisimple.normal_le_center_of_ne_top hquasisimple _ (core_ne_top component hcomponent)
  · intro hcentral
    let : Group.IsPerfect component := ⟨TwoComponents.perfect hcomponent⟩
    exact CentralExtensions.quasisimple_of_surjective
      (TwoComponents.quasisimple_quotient hcomponent)
      (QuotientGroup.mk' (componentClassificationOddCore component))
      (QuotientGroup.mk'_surjective _) (by rwa [QuotientGroup.ker_mk'])

theorem mutual_normalization_core_commutation {G : Type*} [Group G] [Finite G]
    (first second : Subgroup G) (hfirst : TwoComponents.IsTwoComponent first)
    (hsecond : TwoComponents.IsTwoComponent second) (hne : first ≠ second) :
    second ≤ Subgroup.normalizer (first : Set G) ∧
      first ≤ Subgroup.normalizer (second : Set G) ∧
        ⁅first, second⁆ ≤
          (componentClassificationOddCore first).map first.subtype ⊓
            (componentClassificationOddCore second).map second.subtype := by
  have hfirstNotLe : ¬ first ≤ second :=
    fun hle => hne (TwoComponentSubnormal.eq_of_le first second hfirst hsecond hle)
  have hsecondNotLe : ¬ second ≤ first :=
    fun hle => hne (TwoComponentSubnormal.eq_of_le second first hsecond hfirst hle).symm
  obtain ⟨hsecondNormalizes, hfirstCore⟩ :=
    (TwoComponentSubnormal.contains_or_normalizes_core first second hfirst hsecond.1).resolve_left
      hfirstNotLe
  obtain ⟨hfirstNormalizes, hsecondCore⟩ :=
    (TwoComponentSubnormal.contains_or_normalizes_core second first hsecond hfirst.1).resolve_left
      hsecondNotLe
  rw [Subgroup.commutator_comm second first] at hsecondCore
  exact ⟨hsecondNormalizes, hfirstNormalizes, le_inf hfirstCore hsecondCore⟩

theorem commutes_of_quasisimple_left {G : Type*} [Group G] [Finite G]
    (first second : Subgroup G) (hfirst : TwoComponents.IsTwoComponent first)
    (hsecond : TwoComponents.IsTwoComponent second) (hne : first ≠ second)
    (hquasisimple : IsQuasisimple first) : ⁅first, second⁆ = ⊥ := by
  have hcore := (mutual_normalization_core_commutation first second hfirst hsecond hne).2.2
  have hcentral := (quasisimple_iff_core_central first hfirst).mp hquasisimple
  have hcenter : ⁅first, second⁆ ≤ (Subgroup.center first).map first.subtype :=
    (hcore.trans inf_le_left).trans (Subgroup.map_mono hcentral)
  have hdouble : ⁅⁅first, second⁆, first⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    apply hcenter.trans
    intro element hmem
    obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmem
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hlift (⟨member, hmember⟩ : first))
  let : Group.IsPerfect first := ⟨TwoComponents.perfect hfirst⟩
  exact Quasisimple.perfect_double_commutator first second hdouble

theorem commutes_of_quasisimple {G : Type*} [Group G] [Finite G]
    (first second : Subgroup G) (hfirst : TwoComponents.IsTwoComponent first)
    (hsecond : TwoComponents.IsTwoComponent second) (hne : first ≠ second)
    (hquasisimple : IsQuasisimple first ∨ IsQuasisimple second) : ⁅first, second⁆ = ⊥ := by
  rcases hquasisimple with hfirstQuasisimple | hsecondQuasisimple
  · exact commutes_of_quasisimple_left first second hfirst hsecond hne hfirstQuasisimple
  · rw [Subgroup.commutator_comm]
    exact commutes_of_quasisimple_left second first hsecond hfirst hne.symm hsecondQuasisimple

end CFSG.ComponentClassification.TwoComponentInteraction
