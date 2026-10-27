module

public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54SchreierAbstract
public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {B : Type} [Group B] [Finite B]

theorem centralizer_layer_eq_bot (hodd : CFSG.pPrimeCore 2 B = ⊥) (h2 : CFSG.pCore 2 B = ⊥) :
    centralizer (CFSG.layer B : Set B) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro c hc
  rw [← h2]
  refine CFSG.EvenSporadicStandard.TwoB.Layer54.mem_pCore_of_centralizes_layer hodd ?_ ?_
  · intro c' hc' y
    rw [h2] at hc'
    rw [Subgroup.mem_bot.mp hc']
    simp
  · intro x hx
    exact ((Subgroup.mem_centralizer_iff.mp hc) x (by
      rw [CFSG.layer_eq_componentClassification B]
      exact hx)).symm

theorem center_component_eq_bot (hodd : CFSG.pPrimeCore 2 B = ⊥) (h2 : CFSG.pCore 2 B = ⊥)
    {K : Subgroup B} (hK : CFSG.IsComponent K) : center ↥K = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro z hz
  have hz' : (z : B) ∈ (center (CFSG.layer B)).map (CFSG.layer B).subtype :=
    CFSG.LocalCores.center_component_le_center_layer hK ⟨z, hz, rfl⟩
  have hz'' : (z : B) ∈ CFSG.pCore 2 B :=
    (CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot 2 hodd) hz'
  rw [h2] at hz''
  rw [Subgroup.mem_bot]
  exact Subtype.ext (Subgroup.mem_bot.mp hz'')

theorem layer_ne_bot (hodd : CFSG.pPrimeCore 2 B = ⊥) (h2 : CFSG.pCore 2 B = ⊥)
    (hB : Nontrivial B) : CFSG.layer B ≠ ⊥ := by
  intro hlayer
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar := CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot B 2 hodd hlayer
  change centralizer (CFSG.pCore 2 B : Set B) ≤ CFSG.pCore 2 B at hchar
  rw [h2] at hchar
  have htop : (⊤ : Subgroup B) ≤ ⊥ := by
    intro x _
    refine hchar ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y = 1 := by simpa using hy
    rw [hy1]
    simp
  haveI : Subsingleton B := ⟨fun a b => by
    have ha : a ∈ (⊥ : Subgroup B) := htop trivial
    have hb : b ∈ (⊥ : Subgroup B) := htop trivial
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]⟩
  exact (not_subsingleton_iff_nontrivial.mpr hB) inferInstance

theorem layer_normal_Fi24 (B : Type) [Group B] [Finite B] : (CFSG.layer B).Normal := by
  haveI : (CFSG.layer B).Characteristic := CFSG.LocalCores.layer_characteristic
  infer_instance

theorem even_card_layer (hne : CFSG.layer B ≠ ⊥) : Even (Nat.card ↥(CFSG.layer B)) := by
  by_contra h
  have hodd : Odd (Nat.card ↥(CFSG.layer B)) := Nat.not_even_iff_odd.mp h
  haveI : Nontrivial ↥(CFSG.layer B) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  haveI : Group.IsPerfect ↥(CFSG.layer B) := CFSG.LocalCores.layer_isPerfect
  exact Group.IsPerfect.not_isSolvable (CFSG.layer B)
    (CFSG.Milestones.odd_order_solvable hodd)

theorem le_layer_of_selfCentralizing (hodd : CFSG.pPrimeCore 2 B = ⊥) (h2 : CFSG.pCore 2 B = ⊥)
    {Rb : Subgroup B} (hR2 : IsPGroup 2 ↥Rb) (hRne : Rb ≠ ⊥)
    (hRc : centralizer (Rb : Set B) ≤ Rb)
    (hirr : ∀ U : Subgroup B, U ≤ Rb → (∀ x ∈ normalizer (Rb : Set B), ∀ u ∈ U, x * u * x⁻¹ ∈ U) →
      U = ⊥ ∨ U = Rb) :
    Rb ≤ CFSG.layer B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hNontriv : Nontrivial B := by
    haveI : Nontrivial ↥Rb := (Subgroup.nontrivial_iff_ne_bot Rb).mpr hRne
    exact Function.Injective.nontrivial Rb.subtype_injective
  have hne : CFSG.layer B ≠ ⊥ := layer_ne_bot hodd h2 hNontriv
  let E : Subgroup B := CFSG.layer B
  have hEnorm : E.Normal := layer_normal_Fi24 B
  haveI : E.Normal := hEnorm
  have hEeven : 2 ∣ Nat.card ↥E := by
    simpa [E] using even_iff_two_dvd.mp (even_card_layer hne)
  have h1fix : (1 : ↥E) ∈ MulAction.fixedPoints ↥Rb ↥E := by
    rw [MulAction.mem_fixedPoints]
    intro r
    apply Subtype.ext
    simp
  obtain ⟨x, hxfix, hxne1⟩ :=
    hR2.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥E hEeven h1fix
  have hxne : (x : B) ≠ 1 := fun h => hxne1 (Subtype.ext h.symm)
  have hxmem : (x : B) ∈ centralizer (Rb : Set B) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrfix : (⟨r, hr⟩ : ↥Rb) • x = x := (MulAction.mem_fixedPoints.mp hxfix) ⟨r, hr⟩
    have hval : r * (x : B) * r⁻¹ = (x : B) := by
      have := congrArg Subtype.val hrfix
      simpa using this
    calc r * (x : B) = (r * (x : B) * r⁻¹) * r := by group
      _ = (x : B) * r := by rw [hval]
  have hxRb : (x : B) ∈ Rb := hRc hxmem
  have hxE : (x : B) ∈ E := x.2
  have hUne : Rb ⊓ E ≠ ⊥ := by
    intro hbot
    have hmem : (x : B) ∈ (⊥ : Subgroup B) := by
      rw [← hbot]
      exact ⟨hxRb, hxE⟩
    exact hxne (Subgroup.mem_bot.mp hmem)
  have hinv : ∀ y ∈ normalizer (Rb : Set B), ∀ u ∈ Rb ⊓ E, y * u * y⁻¹ ∈ Rb ⊓ E := by
    intro y hy u hu
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_set_normalizer_iff.mp hy u).mp hu.1
    · exact hEnorm.conj_mem u hu.2 y
  rcases hirr (Rb ⊓ E) inf_le_left hinv with h | h
  · exact absurd h hUne
  · rw [← h]
    exact inf_le_right

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
