module

public import CFSG.GroupTheory.GLnTwoSplitting.Main
public import CFSG.LargeExtraspecial.GLRSplitBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module CFSG.GroupTheory.GLnTwoSplitting
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (C : Config S)

namespace Config

noncomputable abbrev N : Subgroup G := normalizer (C.A : Set G)

theorem A_le_N : C.A ≤ C.N := le_normalizer

noncomputable abbrev AN : Subgroup C.N := C.A.subgroupOf C.N

instance normal_AN : C.AN.Normal := normal_in_normalizer

instance isElementaryAbelian_AN : IsElementaryAbelian 2 C.AN where
  is_comm := ⟨fun a b => Subtype.ext (Subtype.ext (C.A_comm a.2 b.2))⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext
    (Subtype.ext (by rw [pow_two]; exact C.A_mul_self a.2))

theorem card_AN : Nat.card C.AN = 2 ^ (S.width + 1) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe C.A_le_N).toEquiv, C.card_A]

theorem finrank_AN : finrank (ZMod 2) (Additive C.AN) = S.width + 1 := by
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive C.AN)
  rw [Nat.card_zmod, show Nat.card (Additive C.AN) = Nat.card C.AN from rfl, C.card_AN] at h1
  exact (Nat.pow_right_injective le_rfl h1).symm

theorem centralizer_AN_le : centralizer (C.AN : Set C.N) ≤ C.AN := by
  intro g hg
  rw [mem_subgroupOf]
  change (g : G) ∈ S.clPre C.At
  rw [← C.centralizer_A]
  rw [mem_centralizer_iff] at hg ⊢
  intro a ha
  have := hg ⟨a, C.A_le_N ha⟩ (by rw [SetLike.mem_coe, mem_subgroupOf]; exact ha)
  exact congrArg Subtype.val this

theorem card_quotient_AN :
    Nat.card (C.N ⧸ C.AN) = Nat.card (GL (Fin (S.width + 1)) (ZMod 2)) := by
  have h := card_eq_card_quotient_mul_card_subgroup C.AN
  have hN : Nat.card C.N = 2 ^ (S.width + 1) * Nat.card (GL (Fin (S.width + 1)) (ZMod 2)) :=
    C.card_normalizer
  rw [C.card_AN, hN] at h
  refine Nat.eq_of_mul_eq_mul_right (pow_pos two_pos (S.width + 1)) ?_
  rw [← h, mul_comm]

@[expose] noncomputable def natExt : NatExt C.N (Additive C.AN) :=
  natExtOfNormal C.centralizer_AN_le C.card_quotient_AN C.finrank_AN

theorem natExt_V : C.natExt.V = C.AN := by
  ext g
  exact ⟨fun ⟨e, he⟩ => he ▸ (Additive.toMul e).2, fun hg => ⟨Additive.ofMul ⟨g, hg⟩, rfl⟩⟩

theorem exists_K (h5 : 5 ≤ S.width) :
    ∃ K : Subgroup G, K ≤ C.N ∧ (∀ g ∈ C.N, ∃ a ∈ C.A, ∃ k ∈ K, a * k = g) ∧
      ∀ k ∈ K, k ∈ C.A → k = 1 := by
  have h6 : 6 ≤ finrank (ZMod 2) (Additive C.AN) := by
    rw [C.finrank_AN]
    omega
  obtain ⟨K, hK, hK'⟩ := C.natExt.exists_complement h6
  rw [natExt_V] at hK hK'
  refine ⟨K.map C.N.subtype, fun _ ⟨k, _, hk⟩ => hk ▸ k.2, fun g hg => ?_, ?_⟩
  · have hmem : (⟨g, hg⟩ : C.N) ∈ C.AN ⊔ K := by rw [hK']; exact mem_top _
    obtain ⟨a, ha, k, hk, hak⟩ := mem_sup_of_normal_left.mp hmem
    exact ⟨a, ha, k, ⟨k, hk, rfl⟩, congrArg Subtype.val hak⟩
  · rintro _ ⟨k, hk, rfl⟩ hkA
    have : k ∈ C.AN ⊓ K := ⟨hkA, hk⟩
    rw [hK, mem_bot] at this
    rw [this]
    rfl

end Config

end CFSG.LargeExtraspecial.GLR
