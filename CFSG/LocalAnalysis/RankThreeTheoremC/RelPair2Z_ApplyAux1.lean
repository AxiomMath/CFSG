module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup
open scoped commutatorElement

theorem zja_pElementSubgroup_subgroupOf {p : ℕ} {Y : Type*} [Group Y] {J W : Subgroup Y}
    (hJW : J ≤ W) (hJp : pElementSubgroup p J = J) :
    pElementSubgroup p (J.subgroupOf W) = J.subgroupOf W := by
  have himg : W.subtype '' {x : W | x ∈ J.subgroupOf W ∧ ∃ k : ℕ, orderOf x = p ^ k} =
      {y : Y | y ∈ J ∧ ∃ k : ℕ, orderOf y = p ^ k} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxJ, k, hk⟩, rfl⟩
      exact ⟨hxJ, k, by rw [← hk]; exact Subgroup.orderOf_coe x⟩
    · rintro ⟨hyJ, k, hk⟩
      refine ⟨⟨y, hJW hyJ⟩, ⟨hyJ, k, ?_⟩, rfl⟩
      rw [Subgroup.orderOf_mk]
      exact hk
  have hmap : (pElementSubgroup p (J.subgroupOf W)).map W.subtype = J := by
    unfold pElementSubgroup at hJp ⊢
    rw [MonoidHom.map_closure, himg]
    exact hJp
  calc pElementSubgroup p (J.subgroupOf W)
      = ((pElementSubgroup p (J.subgroupOf W)).map W.subtype).comap W.subtype :=
        (Subgroup.comap_map_eq_self_of_injective W.subtype_injective _).symm
    _ = J.subgroupOf W := by rw [hmap]; rfl

theorem zja_characteristic_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) {C : Subgroup G}
    (hC : C.Characteristic) : (C.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq] at hC ⊢
  intro ψ
  have h := hC (e.trans (ψ.trans e.symm))
  calc (C.map e.toMonoidHom).map ψ.toMonoidHom
      = C.map (ψ.toMonoidHom.comp e.toMonoidHom) := by rw [Subgroup.map_map]
    _ = C.map (e.toMonoidHom.comp (e.trans (ψ.trans e.symm)).toMonoidHom) := by
        congr 1
        ext x
        simp
    _ = (C.map (e.trans (ψ.trans e.symm)).toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_map]
    _ = C.map e.toMonoidHom := by rw [h]

theorem zja_isQuasisimple_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : CFSG.IsQuasisimple G := by
  obtain ⟨a, b, hab⟩ := hnab
  have hcen : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact h
    · exfalso
      refine hab ?_
      have ha : a ∈ center G := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  let e : G ⧸ center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  refine ⟨?_, e.isSimpleGroup, e.symm a, e.symm b, fun h => hab ?_⟩
  · rw [Group.isPerfect_def]
    rcases (Subgroup.commutator_normal (⊤ : Subgroup G) ⊤).eq_bot_or_eq_top with h | h
    · exfalso
      refine hab ?_
      have hmem : ⁅a, b⁆ ∈ (⁅(⊤ : Subgroup G), ⊤⁆ : Subgroup G) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at hmem
      exact hmem
    · exact h
  · simpa using congrArg e h

theorem zja_le_of_isSylowOf {Y : Type*} [Group Y] [Finite Y] {R K Q : Subgroup Y} [R.Normal]
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R K) (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) : Q ≤ R := by
  have hsup : IsPGroup 2 (R ⊔ Q : Subgroup Y) := hR.isPGroup.to_sup_of_normal_left hQ
  have h := hR.eq_of_le le_sup_left (sup_le hR.le hQK) hsup
  exact le_sup_right.trans h.le

theorem zja_coprime_of_isPGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type*} [Group G]
    [Finite G] {N : Subgroup G} (hN : IsPGroup 2 N) : p.Coprime (Nat.card N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  rw [hn]
  exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right n

theorem zja_chevTwo_or_alt_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsChevTwo A ∨ ∃ n : ℕ, Nonempty (A ≃* alternatingGroup (Fin n))) :
    IsChevTwo B ∨ ∃ n : ℕ, Nonempty (B ≃* alternatingGroup (Fin n)) := by
  rcases h with h | ⟨n, ⟨f⟩⟩
  · left
    rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
    · exact Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩
    · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
    · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans f⟩⟩)
  · exact Or.inr ⟨n, ⟨e.symm.trans f⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
