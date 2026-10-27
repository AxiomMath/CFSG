module

public import CFSG.GF2Type.SmithTypeE.E8.TransMain
public import CFSG.GF2Type.SmithTypeE.E8.Isometry
public import CFSG.GF2Type.SmithTypeE.E8.IdMod
public import CFSG.GF2Type.SmithTypeE.E8.Defs

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup QuadraticMap CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open
  CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LieType.Steinberg.Minuscule (e7Data)
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7Rep56 e7Y56 e7n6)
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)


variable {G : Type} [Group G] [Finite G]

section Ext


theorem twoRankMbar8_of_equiv {S : Setting G} (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))) :
    TwoRankMbar8 S := by
  intro E hE hel
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hel
  by_contra hlt
  push Not at hlt
  have h1 : CFSG.IsElementaryAbelian 2 (E.subgroupOf S.Mbar) :=
    CFSG.IsElementaryAbelian.subgroupOf hE
  have h2 : CFSG.IsElementaryAbelian 2 ((E.subgroupOf S.Mbar).map ψ.toMonoidHom) :=
    CFSG.IsElementaryAbelian.map ψ.toMonoidHom
  have h3 : CFSG.IsElementaryAbelian 2 (((E.subgroupOf S.Mbar).map ψ.toMonoidHom).map
      (adjointGroup .E7 (ZMod 2)).subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  have hEle : ((E.subgroupOf S.Mbar).map ψ.toMonoidHom).map
      (adjointGroup .E7 (ZMod 2)).subtype ≤ adjointGroup .E7 (ZMod 2) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcard : 2 ^ 27 ≤ Nat.card (((E.subgroupOf S.Mbar).map ψ.toMonoidHom).map
      (adjointGroup .E7 (ZMod 2)).subtype) := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective,
      Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv]
    exact hlt.le
  haveI := h3
  obtain ⟨g, hg, hgE⟩ := abelian_conj_QA_of_sq _ hEle
    (fun a ha b hb => by
      have := (IsMulCommutative.is_comm (M := ↥(((E.subgroupOf S.Mbar).map ψ.toMonoidHom).map
        (adjointGroup .E7 (ZMod 2)).subtype))).comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this)
    (fun a ha => by
      have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
      rwa [pow_two] at this) hcard
  have hc : Nat.card (((E.subgroupOf S.Mbar).map ψ.toMonoidHom).map
      (adjointGroup .E7 (ZMod 2)).subtype) = 2 ^ 27 := by
    rw [hgE, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact card_QA
  rw [hc] at hcard
  have h4 : Nat.card (((E.subgroupOf S.Mbar).map ψ.toMonoidHom).map
      (adjointGroup .E7 (ZMod 2)).subtype) = Nat.card E := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective,
      Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv]
  omega

variable [IsSimpleGroup G]

theorem smithE8E33_of_clauses {S : Setting G} (hw : S.width = 28)
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)} {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))}
    (hφ : SmithE8Clauses123 S φ ψ) (g : G) (hxM : g * S.z * g⁻¹ ∈ S.M)
    (hxQ : g * S.z * g⁻¹ ∉ S.QG) :
    ∃ v : G, IsConj S.z v ∧ v ∈ S.QG ∧ v ∈ S.Qa g := by
  have hiso : ∀ u v, polar (S.q.comp (φ.symm : (Fin e7Data.d →₀ ZMod 2) →ₗ[ZMod 2] S.Qt)) u v =
      F.ff u v := by
    intro u v
    have h := isometry8 hφ.1 (φ.symm u) (φ.symm v)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    rw [h]
    simp only [QuadraticMap.polar, comp_apply, LinearEquiv.coe_coe, map_add]
  exact smithE8E33_of_model (twoRankMbar8_of_equiv ψ) hw hφ.1 hφ.2.2.1 hiso g hxM hxQ

theorem smithE8E33_of (I : Inputs10) (hAS : AschbacherSmithWideInput) : SmithE8E33 := by
  intro G _ _ _ S hw hU g hxM hxQ
  obtain ⟨φ, ψ, hφ⟩ := clauses123 I hAS S hw hU
  exact smithE8E33_of_clauses hw hφ g hxM hxQ

end Ext

end CFSG.GF2Type.SmithTypeE.E8
