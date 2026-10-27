module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.OddStandard.Harada75

open CFSG Subgroup
open scoped commutatorElement IsMulCommutative

@[expose] def E32Section {S : Type*} [Group S] (T U : Subgroup S) : Prop :=
  U ≤ T ∧ (∀ x ∈ T, x ^ 2 ∈ U) ∧ (∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ U) ∧
    Nat.card T = 32 * Nat.card U

@[expose] def NoE32 (S : Type*) [Group S] : Prop := ∀ T U : Subgroup S, ¬ E32Section T U

private theorem sq_eq_one_fin_five (a : Multiplicative (Fin 5 → ZMod 2)) : a ^ 2 = 1 := by
  refine Multiplicative.toAdd.injective ?_
  ext i
  simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
  generalize Multiplicative.toAdd a i = c
  revert c
  decide

private theorem e32Section_of_surjective {S : Type*} [Group S] (P : Subgroup S)
    (φ : P →* Multiplicative (Fin 5 → ZMod 2)) (hφ : Function.Surjective φ) :
    E32Section P (φ.ker.map P.subtype) := by
  refine ⟨map_subtype_le _, ?_, ?_, ?_⟩
  · intro x hx
    refine mem_map.mpr ⟨⟨x, hx⟩ ^ 2, ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_pow]
    exact sq_eq_one_fin_five _
  · intro x hx y hy
    refine mem_map.mpr ⟨⁅(⟨x, hx⟩ : P), ⟨y, hy⟩⁆, ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  · have hU : Nat.card (φ.ker.map P.subtype) = Nat.card φ.ker :=
      card_map_of_injective P.subtype_injective
    have hq : Nat.card (P ⧸ φ.ker) = 32 := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
        Nat.card_congr Multiplicative.toAdd]
      simp
    rw [hU, card_eq_card_quotient_mul_card_subgroup φ.ker, hq]

private theorem exists_surjective_fin_five {G : Type*} [Group G] [Finite G]
    [Fact (IsPGroup 2 G)] (h : 4 < generatorRank G) :
    ∃ φ : G →* Multiplicative (Fin 5 → ZMod 2), Function.Surjective φ := by
  have : IsElementaryAbelian 2 (G ⧸ frattini G) := isElementaryAbelian_quotient_frattini
  have h1 : generatorRank G ≤ generatorRank (G ⧸ frattini G) :=
    generatorRank_le_generatorRank_quotient_frattini (p := 2) G
  have h2 := generatorRank_le_finrank_of_elementaryAbelian (p := 2) (G ⧸ frattini G)
  have h5 : 5 ≤ Module.finrank (ZMod 2) (Additive (G ⧸ frattini G)) := by omega
  have : Module.Finite (ZMod 2) (Additive (G ⧸ frattini G)) := Module.Finite.of_finite
  let b := Module.finBasis (ZMod 2) (Additive (G ⧸ frattini G))
  let L : Additive (G ⧸ frattini G) →ₗ[ZMod 2] (Fin 5 → ZMod 2) :=
    (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castLE h5)).comp b.equivFun.toLinearMap
  have hL : Function.Surjective L :=
    (LinearMap.funLeft_surjective_of_injective (ZMod 2) (ZMod 2) _
      (Fin.castLE_injective h5)).comp b.equivFun.surjective
  refine ⟨(AddMonoidHom.toMultiplicativeRight L.toAddMonoidHom).comp
    (QuotientGroup.mk' (frattini G)), fun w => ?_⟩
  obtain ⟨v, hv⟩ := hL (Multiplicative.toAdd w)
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (frattini G) (Additive.toMul v)
  refine ⟨g, ?_⟩
  simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply, hg]
  simp [hv]

theorem gen4_of_noE32 {S : Type} [Group S] [Finite S] (h2 : IsPGroup 2 S) (h : NoE32 S)
    (P : Subgroup S) : ∃ s : Finset S, s.card ≤ 4 ∧ Subgroup.closure (s : Set S) = P := by
  have : Fact (IsPGroup 2 P) := ⟨h2.to_subgroup P⟩
  have hrank : generatorRank P ≤ 4 := by
    by_contra hnot
    obtain ⟨φ, hφ⟩ := exists_surjective_fin_five (G := P) (by omega)
    exact h P _ (e32Section_of_surjective P φ hφ)
  obtain ⟨T, hTcard, hTtop⟩ := Group.rank_spec P
  refine ⟨T.map ⟨P.subtype, P.subtype_injective⟩, ?_, ?_⟩
  · rw [Finset.card_map, hTcard, ← generatorRank_eq_group_rank]
    exact hrank
  · rw [Finset.coe_map, Function.Embedding.coeFn_mk, ← MonoidHom.map_closure, hTtop,
      ← MonoidHom.range_eq_map, range_subtype]

end CFSG.OddStandard.Harada75
