module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Tactic.Group
public import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
public import CFSG.FeitThompson.OddOrder.CommutingSubgroupsJoinProduct
public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Function

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem conjugatesOfSet_eq_iUnion_conj_image (A : Set G) :
    Group.conjugatesOfSet A = ⋃ g : G, MulAut.conj g '' A := by
  ext x
  simp only [Group.mem_conjugatesOfSet_iff, Set.mem_iUnion, Set.mem_image, MulAut.conj_apply,
    isConj_iff]
  exact ⟨fun ⟨a, ha, c, hc⟩ => ⟨c, a, ha, hc⟩, fun ⟨g, a, ha, hg⟩ => ⟨a, ha, g, hg⟩⟩

theorem conjugatesOfSet_eq_iUnion_image_conj_inv (A : Set G) :
    Group.conjugatesOfSet A = ⋃ g : G, (fun x => g⁻¹ * x * g) '' A := by
  rw [conjugatesOfSet_eq_iUnion_conj_image]
  refine Set.iUnion_congr_of_surjective _ (inv_surjective (G := G)) fun g => ?_
  exact Set.image_congr' fun x => by simp only [MulAut.conj_apply]; group

theorem iUnion_conj_image_eq_iUnion_out (A : Set G) (S : Subgroup G)
    (hS : S ≤ Subgroup.normalizer A) :
    ⋃ g : G, MulAut.conj g '' A = ⋃ c : G ⧸ S, MulAut.conj (Quotient.out c) '' A := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun g => ?_)
    (Set.iUnion_subset fun c => Set.subset_iUnion_of_subset (Quotient.out c) le_rfl)
  refine Set.subset_iUnion_of_subset ((g : G ⧸ S)) (le_of_eq ?_)
  set o := Quotient.out (↑g : G ⧸ S) with ho
  have hmem : o⁻¹ * g ∈ S := QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
  have hs : MulAut.conj (o⁻¹ * g) '' A = A :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp (hS hmem)
  calc MulAut.conj g '' A
      = MulAut.conj o '' (MulAut.conj (o⁻¹ * g) '' A) := by
        rw [Set.image_image]
        exact Set.image_congr' fun x => by simp only [MulAut.conj_apply]; group
    _ = MulAut.conj o '' A := by rw [hs]

theorem ncard_conjugatesOfSet_le_index_mul_ncard [Finite G] {A : Set G} {S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer A) :
    (Group.conjugatesOfSet A).ncard ≤ S.index * A.ncard := by
  classical
  have : Fintype (G ⧸ S) := Fintype.ofFinite _
  rw [conjugatesOfSet_eq_iUnion_conj_image, iUnion_conj_image_eq_iUnion_out A S hS]
  refine (Set.ncard_iUnion_le_of_fintype _).trans ?_
  simp only [Set.ncard_image_of_injective _ (MulAut.conj _).injective]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Subgroup.index_eq_card,
    Nat.card_eq_fintype_card]

theorem ncard_conjugatesOfSet_eq_index_mul_ncard [Finite G] {D : Set G} {L : Subgroup G}
    (h : IsTIWithNormalizer D L) :
    (Group.conjugatesOfSet D).ncard = L.index * D.ncard := by
  classical
  have : Fintype (G ⧸ L) := Fintype.ofFinite _
  have hdisj : Pairwise (Disjoint on fun c : G ⧸ L => MulAut.conj (Quotient.out c) '' D) := by
    intro c c' hcc
    refine h.disjoint_conj_image_conj_image fun hmem => hcc ?_
    have := QuotientGroup.eq.mpr hmem
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  rw [conjugatesOfSet_eq_iUnion_conj_image,
    iUnion_conj_image_eq_iUnion_out D L h.normalizer_eq.ge,
    Set.ncard_iUnion_of_finite (fun c => Set.toFinite _) hdisj, finsum_eq_sum_of_fintype]
  simp only [Set.ncard_image_of_injective _ (MulAut.conj _).injective]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Subgroup.index_eq_card,
    Nat.card_eq_fintype_card]

theorem measure_conjugatesOfSet_le [Finite G] {A : Set G} {S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer A) :
    ((Group.conjugatesOfSet A).ncard : ℝ) / Nat.card G ≤ A.ncard / Nat.card S := by
  have hG : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos (α := G)
  have hSp : (0 : ℝ) < Nat.card S := by exact_mod_cast Nat.card_pos (α := S)
  have hidx : (S.index : ℝ) * Nat.card S = Nat.card G := by
    rw [← Nat.cast_mul, Subgroup.index_mul_card]
  have key : ((Group.conjugatesOfSet A).ncard : ℝ) ≤ (S.index : ℝ) * A.ncard := by
    exact_mod_cast ncard_conjugatesOfSet_le_index_mul_ncard hS
  rw [div_le_div_iff₀ hG hSp]
  calc ((Group.conjugatesOfSet A).ncard : ℝ) * Nat.card S
      ≤ ((S.index : ℝ) * A.ncard) * Nat.card S := mul_le_mul_of_nonneg_right key hSp.le
    _ = (A.ncard : ℝ) * ((S.index : ℝ) * Nat.card S) := by ring
    _ = (A.ncard : ℝ) * Nat.card G := by rw [hidx]

theorem measure_conjugatesOfSet_eq [Finite G] {D : Set G} {L : Subgroup G}
    (h : IsTIWithNormalizer D L) :
    ((Group.conjugatesOfSet D).ncard : ℝ) / Nat.card G = D.ncard / Nat.card L := by
  have hG : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos (α := G)
  have hL : (0 : ℝ) < Nat.card L := by exact_mod_cast Nat.card_pos (α := L)
  have hidx : (L.index : ℝ) * Nat.card L = Nat.card G := by
    rw [← Nat.cast_mul, Subgroup.index_mul_card]
  have key : ((Group.conjugatesOfSet D).ncard : ℝ) = (L.index : ℝ) * D.ncard := by
    exact_mod_cast ncard_conjugatesOfSet_eq_index_mul_ncard h
  rw [div_eq_div_iff hG.ne' hL.ne', key, ← hidx]
  ring

theorem le_normalizer_sdiff_singleton_one {S P : Subgroup G}
    (h : S ≤ Subgroup.normalizer (P : Set G)) :
    S ≤ Subgroup.normalizer ((P : Set G) \ {1}) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have hP := Subgroup.mem_normalizer_iff_conj_image_eq.mp (h hg)
  rw [Set.image_sdiff (MulAut.conj g).injective, hP]
  congr 1
  simp

theorem ncard_sdiff_singleton_one_add_one [Finite G] (P : Subgroup G) :
    (((P : Set G) \ {1}).ncard : ℝ) + 1 = Nat.card P := by
  have h := Set.ncard_sdiff_singleton_add_one (s := (P : Set G)) (a := (1 : G)) P.one_mem
  rw [← Nat.card_coe_set_eq] at h
  exact_mod_cast h

theorem measure_conjugatesOfSet_punctured_lt [Finite G] {P S : Subgroup G} {u q : ℕ}
    (hu : 0 < u) (hq : 0 < q) (hPS : P ≤ S) (hPnormal : (P.subgroupOf S).Normal)
    (hcard : Nat.card S = Nat.card P * u * q) :
    ((Group.conjugatesOfSet ((P : Set G) \ {1})).ncard : ℝ) / Nat.card G < 1 / (u * q) := by
  have hnorm : S ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hPS
  have hPpos : (0 : ℝ) < Nat.card P := by exact_mod_cast Nat.card_pos (α := P)
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine (measure_conjugatesOfSet_le (le_normalizer_sdiff_singleton_one hnorm)).trans_lt ?_
  have hSc : ((Nat.card S : ℝ)) = Nat.card P * u * q := by rw [hcard]; push_cast; ring
  have hD : ((((P : Set G) \ {1}).ncard : ℝ)) = Nat.card P - 1 := by
    linarith [ncard_sdiff_singleton_one_add_one (G := G) P]
  rw [hSc, hD, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem natCard_of_coe_eq_mul [Finite G] {W W₁ W₂ : Subgroup G}
    (hW : (W : Set G) = (W₁ : Set G) * (W₂ : Set G)) (hinter : W₁ ⊓ W₂ = ⊥) :
    Nat.card W = Nat.card W₁ * Nat.card W₂ := by
  have h := natCard_mul_mul_natCard_inf W₁ W₂
  rw [hinter, Subgroup.card_bot, mul_one, ← hW] at h
  simpa using h

theorem ncard_union_add_one [Finite G] {W₁ W₂ : Subgroup G} (hinter : W₁ ⊓ W₂ = ⊥) :
    ((W₁ : Set G) ∪ (W₂ : Set G)).ncard + 1 = Nat.card W₁ + Nat.card W₂ := by
  have hi : (W₁ : Set G) ∩ (W₂ : Set G) = {1} := by
    rw [← Subgroup.coe_inf, hinter]; simp
  have h := Set.ncard_union_add_ncard_inter (W₁ : Set G) (W₂ : Set G)
  rw [hi, Set.ncard_singleton] at h
  rw [h, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, SetLike.coe_sort_coe]

theorem union_subset_of_coe_eq_mul {W W₁ W₂ : Subgroup G}
    (hW : (W : Set G) = (W₁ : Set G) * (W₂ : Set G)) :
    (W₁ : Set G) ∪ (W₂ : Set G) ⊆ (W : Set G) := by
  rw [hW]
  exact Set.union_subset (fun x hx => ⟨x, hx, 1, W₂.one_mem, mul_one x⟩)
    (fun x hx => ⟨1, W₁.one_mem, x, hx, one_mul x⟩)

theorem ncard_sdiff_union_eq [Finite G] {W W₁ W₂ : Subgroup G}
    (hW : (W : Set G) = (W₁ : Set G) * (W₂ : Set G)) (hinter : W₁ ⊓ W₂ = ⊥) :
    (((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))).ncard : ℝ)
      = (Nat.card W₁ - 1 : ℝ) * (Nat.card W₂ - 1 : ℝ) := by
  have hsub := Set.ncard_sdiff_add_ncard_of_subset (union_subset_of_coe_eq_mul hW)
    (Set.toFinite _)
  have h1 := ncard_union_add_one (G := G) hinter
  have h2 := natCard_of_coe_eq_mul (G := G) hW hinter
  rw [(Nat.card_coe_set_eq ((W : Set G))).symm] at hsub
  have hsub' : ((((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))).ncard : ℝ))
      + (((W₁ : Set G) ∪ (W₂ : Set G)).ncard : ℝ) = (Nat.card W : ℝ) := by
    exact_mod_cast hsub
  have h1' : ((((W₁ : Set G) ∪ (W₂ : Set G)).ncard : ℝ)) + 1
      = (Nat.card W₁ : ℝ) + Nat.card W₂ := by exact_mod_cast h1
  have h2' : (Nat.card W : ℝ) = (Nat.card W₁ : ℝ) * Nat.card W₂ := by exact_mod_cast h2
  nlinarith [hsub', h1', h2']

theorem isTIWithNormalizer_sdiff_union {W W₁ W₂ : Subgroup G}
    (hW : (W : Set G) = (W₁ : Set G) * (W₂ : Set G)) (hW₁ : W₁ ≠ ⊥) (hW₂ : W₂ ≠ ⊥)
    (hinter : W₁ ⊓ W₂ = ⊥)
    (hND : Subgroup.normalizer ((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))) = W)
    (hTI : ∀ g ∉ W, ((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))) ∩
      ((fun x => g⁻¹ * x * g) '' ((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G)))) = ∅) :
    IsTIWithNormalizer ((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))) W where
  nonempty := nonempty_sdiff_union hW hW₁ hW₂ hinter
  one_notMem := by simp
  normalizer_eq := hND
  disjoint_conj_image g hg := by
    have hg' : g⁻¹ ∉ W := fun hc => hg (by simpa using W.inv_mem hc)
    rw [Set.disjoint_iff_inter_eq_empty]
    refine Eq.trans (congrArg _ ?_) (hTI g⁻¹ hg')
    exact (Set.image_congr' fun x => by simp only [MulAut.conj_apply, inv_inv]).symm

theorem measure_conjugatesOfSet_mixed_eq [Finite G] {W W₁ W₂ : Subgroup G} {p q : ℕ}
    (hq : 1 < q) (hp : 1 < p) (hqcard : Nat.card W₁ = q) (hpcard : Nat.card W₂ = p)
    (hW : (W : Set G) = (W₁ : Set G) * (W₂ : Set G)) (hinter : W₁ ⊓ W₂ = ⊥)
    (hND : Subgroup.normalizer ((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))) = W)
    (hTI : ∀ g ∉ W, ((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))) ∩
      ((fun x => g⁻¹ * x * g) '' ((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G)))) = ∅) :
    ((Group.conjugatesOfSet ((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G)))).ncard : ℝ)
      / Nat.card G = ((p : ℝ) - 1) * ((q : ℝ) - 1) / (p * q) := by
  have hW₁ : W₁ ≠ ⊥ := by rintro rfl; rw [Subgroup.card_bot] at hqcard; omega
  have hW₂ : W₂ ≠ ⊥ := by rintro rfl; rw [Subgroup.card_bot] at hpcard; omega
  rw [measure_conjugatesOfSet_eq (isTIWithNormalizer_sdiff_union hW hW₁ hW₂ hinter hND hTI),
    ncard_sdiff_union_eq hW hinter, natCard_of_coe_eq_mul hW hinter, hqcard, hpcard]
  push_cast
  ring

theorem measure_union_le [Finite G] (A B : Set G) :
    ((A ∪ B).ncard : ℝ) / Nat.card G ≤ A.ncard / Nat.card G + B.ncard / Nat.card G := by
  have hG : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos (α := G)
  have h : ((A ∪ B).ncard : ℝ) ≤ (A.ncard : ℝ) + B.ncard := by
    exact_mod_cast Set.ncard_union_le A B
  rw [← add_div]
  exact div_le_div_of_nonneg_right h hG.le

theorem measure_union₃_le [Finite G] (A B C : Set G) :
    ((A ∪ B ∪ C).ncard : ℝ) / Nat.card G
      ≤ A.ncard / Nat.card G + B.ncard / Nat.card G + C.ncard / Nat.card G :=
  (measure_union_le _ C).trans (by linarith [measure_union_le (G := G) A B])

theorem two_core_mixed_saturation_measure [Finite G] {P S Q T W₁ W₂ : Subgroup G}
    {u v p q : ℕ} (_hP : P ≠ ⊥) (_hQ : Q ≠ ⊥)
    (hPS : P ≤ S) (hPnormal : (P.subgroupOf S).Normal)
    (hQT : Q ≤ T) (hQnormal : (Q.subgroupOf T).Normal)
    (hu : 0 < u) (hv : 0 < v) (hp : 1 < p) (hq : 1 < q)
    (hS : Nat.card S = Nat.card P * u * q) (hT : Nat.card T = Nat.card Q * v * p)
    (hcomm : ∀ x ∈ W₁, ∀ y ∈ W₂, Commute x y)
    (hqcard : Nat.card W₁ = q) (hpcard : Nat.card W₂ = p) (hinter : W₁ ⊓ W₂ = ⊥)
    (hND : Subgroup.normalizer
        (((W₁ ⊔ W₂ : Subgroup G) : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))) = W₁ ⊔ W₂)
    (hTI : ∀ g ∉ (W₁ ⊔ W₂ : Subgroup G),
      (((W₁ ⊔ W₂ : Subgroup G) : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))) ∩
        ((fun x => g⁻¹ * x * g) ''
          (((W₁ ⊔ W₂ : Subgroup G) : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G)))) = ∅) :
    ((Group.conjugatesOfSet ((P : Set G) \ {1})).ncard : ℝ) / Nat.card G < 1 / (u * q) ∧
    ((Group.conjugatesOfSet ((Q : Set G) \ {1})).ncard : ℝ) / Nat.card G < 1 / (v * p) ∧
    ((Group.conjugatesOfSet
        (((W₁ ⊔ W₂ : Subgroup G) : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G)))).ncard : ℝ)
        / Nat.card G = ((p : ℝ) - 1) * ((q : ℝ) - 1) / (p * q) ∧
    (((Group.conjugatesOfSet ((P : Set G) \ {1})
        ∪ Group.conjugatesOfSet ((Q : Set G) \ {1})
        ∪ Group.conjugatesOfSet
          (((W₁ ⊔ W₂ : Subgroup G) : Set G)
            \ ((W₁ : Set G) ∪ (W₂ : Set G)))).ncard : ℝ)) / Nat.card G
      ≤ 1 / (u * q) + 1 / (v * p) + ((p : ℝ) - 1) * ((q : ℝ) - 1) / (p * q) := by
  have hW : ((W₁ ⊔ W₂ : Subgroup G) : Set G) = (W₁ : Set G) * (W₂ : Set G) :=
    coe_sup_eq_mul_of_commute hcomm
  have h1 := measure_conjugatesOfSet_punctured_lt (G := G) hu (by omega : 0 < q) hPS hPnormal hS
  have h2 := measure_conjugatesOfSet_punctured_lt (G := G) hv (by omega : 0 < p) hQT hQnormal hT
  have h3 := measure_conjugatesOfSet_mixed_eq (G := G) hq hp hqcard hpcard hW hinter hND hTI
  refine ⟨h1, h2, h3, ?_⟩
  have h4 := measure_union₃_le (G := G) (Group.conjugatesOfSet ((P : Set G) \ {1}))
    (Group.conjugatesOfSet ((Q : Set G) \ {1}))
    (Group.conjugatesOfSet
      (((W₁ ⊔ W₂ : Subgroup G) : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))))
  linarith

end CFSG.FeitThompson
