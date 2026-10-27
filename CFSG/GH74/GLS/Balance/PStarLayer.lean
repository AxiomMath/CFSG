module

public import CFSG.GH74.GLS.Balance.PStarDefs
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

instance oResidual_normal (p : ℕ) (G : Type*) [Group G] : (oResidual p G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold oResidual at hn ⊢
  refine Subgroup.closure_induction (p := fun n _ => g * n * g⁻¹ ∈ Subgroup.closure
    {x : G | Nat.Coprime (orderOf x) p}) ?_ ?_ ?_ ?_ hn
  · intro y hy
    apply Subgroup.subset_closure
    show Nat.Coprime (orderOf (g * y * g⁻¹)) p
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
    have e : (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := rfl
    rw [e] at this
    rw [this]; exact hy
  · simp
  · intro a b _ _ ha hb
    have := Subgroup.mul_mem _ ha hb
    simpa [mul_assoc] using this
  · intro a _ ha
    have h1 := Subgroup.inv_mem _ ha
    rwa [show (g * a * g⁻¹)⁻¹ = g * a⁻¹ * g⁻¹ by group] at h1

theorem oResidual_two_eq_top_of_isPerfect {G : Type*} [Group G] [Finite G] (hG : Group.IsPerfect G) :
    oResidual 2 G = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (G ⧸ oResidual 2 G) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    set n := orderOf g with hn
    have hn0 : n ≠ 0 := (orderOf_pos g).ne'
    set a := n.factorization 2 with ha
    refine ⟨a, ?_⟩
    show (g : G ⧸ oResidual 2 G) ^ (2 ^ a) = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    apply Subgroup.subset_closure
    show Nat.Coprime (orderOf (g ^ (2 ^ a))) 2
    rw [orderOf_pow' g (by positivity)]
    have hd : 2 ^ a ∣ n := Nat.ordProj_dvd n 2
    rw [Nat.gcd_eq_right hd]
    exact (Nat.coprime_ordCompl Nat.prime_two hn0).symm
  have hnil : Group.IsNilpotent (G ⧸ oResidual 2 G) := h2.isNilpotent
  by_contra hne
  have hidx : (oResidual 2 G).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hcard : Nat.card (G ⧸ oResidual 2 G) ≠ 1 := by
    rw [← Subgroup.index]; exact hidx
  have hpos : 0 < Nat.card (G ⧸ oResidual 2 G) := Nat.card_pos
  have : Nontrivial (G ⧸ oResidual 2 G) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact Group.IsPerfect.not_isNilpotent (G := G ⧸ oResidual 2 G) hnil

theorem isPStar_layer (X : Type) [Group X] [Finite X] : IsPStar 2 ↥(layer X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨oResidual_two_eq_top_of_isPerfect (CFSG.LocalCores.layer_isPerfect), ?_⟩
  intro N hN P
  rw [eq_top_iff]
  rw [← Subgroup.map_le_map_iff_of_injective (layer X).subtype_injective]
  have hrange : (⊤ : Subgroup ↥(layer X)).map (layer X).subtype = layer X := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hrange]
  refine sSup_le fun K hK => ?_
  have hKE : K ≤ layer X := CFSG.LocalCores.component_le_layer hK
  have hK' : IsComponent (K.subgroupOf (layer X)) := CFSG.LocalCores.component_overgroup hK hKE
  have hKmap : (K.subgroupOf (layer X)).map (layer X).subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le hKE
  rw [← hKmap]
  refine Subgroup.map_mono ?_
  rcases CFSG.LocalCores.component_normal_subgroup hK' hN with h | h
  · exact h.trans le_sup_left
  · refine le_trans ?_ le_sup_right
    have h1 : K.subgroupOf (layer X) ≤ centralizer (N : Set ↥(layer X)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact h1.trans (Subgroup.centralizer_le (by
      intro y hy
      obtain ⟨p, -, rfl⟩ := hy
      exact p.2))

end CFSG.GH74.GLS.Balance
