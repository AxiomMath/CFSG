module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AY
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AR
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AX
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AG

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK CFSG.OddStandard.HigherRank.G2Three

variable {Y : Type} [Group Y] [Finite Y] {τ : Y} {J M : Subgroup Y}

private theorem y6f4a_perfect_le_of_outer {X : Type*} [Group X] {K : Subgroup X} [K.Normal]
    (hC : Subgroup.centralizer (K : Set X) = ⊥)
    (hout : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K))
    {B : Subgroup X} (hB : ⁅B, B⁆ = B) : B ≤ K := by
  let τ : X →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K :=
    (QuotientGroup.mk'
      (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K)).comp MulAut.conjNormal
  have hker : ∀ x, τ x = 1 → x ∈ K := by
    intro x hx
    have hx' : (MulAut.conjNormal x : MulAut ↥K) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K :=
      (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := hx'
    have hcomm : ∀ y : X, y ∈ K → x * y * x⁻¹ = k * y * (k : X)⁻¹ := by
      intro y hy
      have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨y, hy⟩ : ↥K) : X)) hk
      simpa [MulAut.conjNormal_apply] using h1.symm
    have hz : (k : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hcomm y hy
      calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * (k * y * (k : X)⁻¹) * x := by group
        _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
        _ = (k : X)⁻¹ * x * y := by group
    rw [hC, Subgroup.mem_bot] at hz
    have hx1 : x = k := by
      have h2 := congrArg (fun z => (k : X) * z) hz
      simpa using h2
    exact hx1 ▸ k.2
  haveI := hout
  have hperf : ⁅B.map τ, B.map τ⁆ = B.map τ := by
    rw [← Subgroup.map_commutator, hB]
  have hbot : B.map τ = ⊥ := by
    by_contra hne
    exact (ne_of_lt (Group.IsSolvable.commutator_lt_of_ne_bot hne)) hperf
  intro y hy
  refine hker y ?_
  have hmem : τ y ∈ B.map τ := ⟨y, hy, rfl⟩
  rw [hbot] at hmem
  simpa using hmem

theorem y6f4a_outcome_lie (hG : G23Facts) (hY : Y6YData τ J M)
    (hsol : CFSG.solvableRadical Y = ⊥) (h : LayerOutcome Y J 3) :
    Y6TargetLie ↥(CFSG.layer Y) := by
  haveI : (CFSG.layer Y).Characteristic := CFSG.LocalCores.layer_characteristic
  let ρ0 : ↥M →* MulAut ↥(CFSG.layer Y) := MulAut.conjNormal.comp M.subtype
  have hρ0 : Function.Injective ρ0 := by
    change Function.Injective (MulAut.conjNormal.comp M.subtype)
    intro a b hab
    apply Subtype.ext
    have hmem : (b : Y)⁻¹ * (a : Y) ∈
        Subgroup.centralizer (CFSG.layer Y : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : ((MulAut.conjNormal.comp M.subtype) a ⟨x, hx⟩ : Y) =
          ((MulAut.conjNormal.comp M.subtype) b ⟨x, hx⟩ : Y) :=
        congrArg (fun f : MulAut ↥(CFSG.layer Y) =>
          ((f ⟨x, hx⟩ : ↥(CFSG.layer Y)) : Y)) hab
      have h1 : (a : Y) * x * (a : Y)⁻¹ = (b : Y) * x * (b : Y)⁻¹ := by
        simpa [MulAut.conjNormal_apply] using hx'
      calc x * ((b : Y)⁻¹ * (a : Y))
          = (b : Y)⁻¹ * ((b : Y) * x * (b : Y)⁻¹) * (a : Y) := by group
        _ = (b : Y)⁻¹ * ((a : Y) * x * (a : Y)⁻¹) * (a : Y) := by rw [h1]
        _ = ((b : Y)⁻¹ * (a : Y)) * x := by group
    have hz : (b : Y)⁻¹ * (a : Y) = 1 := by
      rw [CFSG.SignalizerFunctorTheorem.Nonsolvable.centralizer_layer_eq_bot hsol,
        Subgroup.mem_bot] at hmem
      exact hmem
    have hx1 : (a : Y) = (b : Y) := by
      have h2 := congrArg (fun z => (b : Y) * z) hz
      simpa using h2
    exact hx1
  unfold LayerOutcome at h
  unfold Y6TargetLie
  rcases h with hAA | hLie | hsmall | hg23
  · rcases hAA with ⟨e⟩
    haveI : IsSimpleGroup ↥J := hY.J_simple
    let ρ : ↥M →* MulAut (↥J × ↥J) := (MulAut.congr e).toMonoidHom.comp ρ0
    have hρ : Function.Injective ρ := fun a b hab => hρ0 ((MulAut.congr e).injective hab)
    exact (y6f4a_no_z4cube_aut_prod hY.J_nonab hY.J_aut hY.M_equiv ρ hρ).elim
  · rcases hLie with h | h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact absurd hsmall.1 (by norm_num)
  · have hQ : HRG23 ↥(CFSG.layer Y) := hg23.2
    exact (y6f4a_no_z4cube_aut_g23 hG hQ hY.M_equiv ρ0 hρ0).elim

theorem y6f4a_layer_facts (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Catalog)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hsol : CFSG.solvableRadical Y = ⊥) (h : Y6TargetLie ↥(CFSG.layer Y)) :
    IsSimpleGroup ↥(CFSG.layer Y) ∧ (∃ a b : ↥(CFSG.layer Y), a * b ≠ b * a) ∧
      centralizer (CFSG.layer Y : Set Y) = ⊥ ∧
      ∀ B : Subgroup Y, Group.IsPerfect ↥B → B ≤ CFSG.layer Y := by
  obtain ⟨hsimple, hnonab⟩ := y6f4a_target_simple_nonab hO h
  haveI : IsSimpleGroup ↥(CFSG.layer Y) := hsimple
  haveI : (CFSG.layer Y).Characteristic := CFSG.LocalCores.layer_characteristic
  have hnoncomm : ∃ a b : ↥(CFSG.layer Y), a * b ≠ b * a :=
    y6f4a_exists_noncomm_of_not_comm hnonab
  have hC : Subgroup.centralizer (CFSG.layer Y : Set Y) = ⊥ :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.centralizer_layer_eq_bot hsol
  unfold Y6TargetLie at h
  have hcat : Catalog ↥(CFSG.layer Y) := by
    rcases h with h1 | h2 | h3
    · exact lieModel_catalog ↥(CFSG.layer Y) .PSL 2 2 6 h1
    · exact lieModel_catalog ↥(CFSG.layer Y) .PSU 3 2 3 h2
    · exact lieModel_catalog ↥(CFSG.layer Y) .PSL 3 2 3 h3
  have hout := hSch ↥(CFSG.layer Y) hnoncomm hcat
  refine ⟨hsimple, hnoncomm, hC, ?_⟩
  intro B hB
  exact y6f4a_perfect_le_of_outer hC hout (Subgroup.isPerfect_iff.mp hB)

theorem y6f4a_layer_of_data
    (hGMS : GMSLinearStandardLayerListKRankOneStatement)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Catalog) (hG : G23Facts)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hK : CFSG.SectionRank.IsKGroupCat Y) (hodd : CFSG.Open.standardComponentOddCore Y = ⊥)
    (hY : Y6YData τ J M) :
    IsSimpleGroup ↥(CFSG.layer Y) ∧ (∃ a b : ↥(CFSG.layer Y), a * b ≠ b * a) ∧
      centralizer (CFSG.layer Y : Set Y) = ⊥ ∧
      (∀ B : Subgroup Y, Group.IsPerfect ↥B → B ≤ CFSG.layer Y) ∧
      Y6TargetLie ↥(CFSG.layer Y) := by
  have hsol : CFSG.solvableRadical Y = ⊥ := y6f4a_solvableRadical_eq_bot_of_data hodd hY
  obtain ⟨hstd, hsyl⟩ := y6f4a_stdLinearData hY
  have hout : LayerOutcome Y J 3 := hGMS Y hK hodd 3 J hstd hsyl
  have hlie : Y6TargetLie ↥(CFSG.layer Y) := y6f4a_outcome_lie hG hY hsol hout
  have hfacts := y6f4a_layer_facts hSch hO hsol hlie
  exact ⟨hfacts.1, hfacts.2.1, hfacts.2.2.1, hfacts.2.2.2, hlie⟩

end CFSG.OddStandard.HigherRank.YamadaG23
