module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74

section Comp

variable {Y : Type} [Group Y] [Finite Y]

theorem fitting_eq_bot_of_cores (h2 : pPrimeCore 2 Y = ⊥) (h2' : pCore 2 Y = ⊥) :
    fittingSubgroup Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Fitting_eq_pcore Y 2 h2, h2']

omit [Finite Y] in
theorem center_layer_le_fitting :
    (center ↥(layer Y)).map (layer Y).subtype ≤ fittingSubgroup Y := by
  set Z := (center ↥(layer Y)).map (layer Y).subtype with hZ
  have hchar : (layer Y).Characteristic := CFSG.LocalCores.layer_characteristic (G := Y)
  have hn : (layer Y).Normal := inferInstance
  have hZmem : ∀ g ∈ Z, g ∈ layer Y ∧ ∀ l ∈ layer Y, l * g = g * l := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨c.2, fun l hl => ?_⟩
    have := Subgroup.mem_center_iff.1 hc ⟨l, hl⟩
    exact congrArg Subtype.val this
  have hZn : Z.Normal := ⟨fun n hn' g => by
    obtain ⟨hnL, hnc⟩ := hZmem n hn'
    refine ⟨⟨g * n * g⁻¹, hn.conj_mem n hnL g⟩, ?_, rfl⟩
    show _ ∈ center ↥(layer Y)
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    have hl' : g⁻¹ * (l : Y) * g ∈ layer Y := by simpa using hn.conj_mem (l : Y) l.2 g⁻¹
    have := hnc _ hl'
    calc (l : Y) * (g * n * g⁻¹) = g * ((g⁻¹ * (l : Y) * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * (l : Y) * g)) * g⁻¹ := by rw [this]
      _ = g * n * g⁻¹ * (l : Y) := by group⟩
  have hcomm : IsMulCommutative ↥Z := ⟨⟨fun a b => Subtype.ext ((hZmem b b.2).2 a (hZmem a a.2).1)⟩⟩
  have hnil : Group.IsNilpotent ↥Z := inferInstance
  exact le_sSup ⟨hZn, hnil⟩

theorem center_component_eq_bot (hF : fittingSubgroup Y = ⊥) {K : Subgroup Y} (hK : IsComponent K) :
    center ↥K = ⊥ := by
  have h1 := (CFSG.LocalCores.center_component_le_center_layer hK).trans (center_layer_le_fitting (Y := Y))
  rw [hF, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
  rw [Subgroup.ker_subtype] at h1
  exact le_bot_iff.1 h1

theorem component_isSimple (hF : fittingSubgroup Y = ⊥) {K : Subgroup Y} (hK : IsComponent K) :
    IsSimpleGroup ↥K ∧ ∃ a b : ↥K, a * b ≠ b * a := by
  obtain ⟨-, hs, a, b, hab⟩ := hK.1
  have hc := center_component_eq_bot hF hK
  let e : ↥K ⧸ center ↥K ≃* ↥K := (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨(e.isSimpleGroup_congr).1 hs, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem components_commute_inf (hF : fittingSubgroup Y = ⊥) {K L : Subgroup Y} (hK : IsComponent K)
    (hL : IsComponent L) (hne : K ≠ L) : (∀ a ∈ K, ∀ b ∈ L, a * b = b * a) ∧ K ⊓ L = ⊥ := by
  have hcomm : ⁅K, L⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hK hL).resolve_left hne
  have h1 : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a := by
    intro a ha b hb
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm ha
    exact (Subgroup.mem_centralizer_iff.1 this b hb).symm
  refine ⟨h1, ?_⟩
  rw [eq_bot_iff]
  intro x hx
  have hxZ : (⟨x, hx.1⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h1 g g.2 x hx.2)
  rw [center_component_eq_bot hF hK, Subgroup.mem_bot] at hxZ
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hxZ)

omit [Finite Y] in
theorem generalizedFitting_eq_layer (hF : fittingSubgroup Y = ⊥) : generalizedFitting Y = layer Y := by
  rw [generalizedFitting, hF, bot_sup_eq]

theorem generalizedFitting_simple_of_unique (hF : fittingSubgroup Y = ⊥) {K : Subgroup Y}
    (hK : IsComponent K) (huniq : ∀ L : Subgroup Y, IsComponent L → L = K) :
    IsSimpleGroup ↥(generalizedFitting Y) ∧ ∃ a b : ↥(generalizedFitting Y), a * b ≠ b * a := by
  have hlayer : generalizedFitting Y = K := by
    rw [generalizedFitting_eq_layer hF]
    refine le_antisymm (sSup_le fun L hL => (huniq L hL).le) (CFSG.LocalCores.component_le_layer hK)
  obtain ⟨hs, hnab⟩ := component_isSimple hF hK
  rw [hlayer]
  exact ⟨hs, hnab⟩

end Comp

end CFSG.GH74.GLS.Stage2.Local.P34
