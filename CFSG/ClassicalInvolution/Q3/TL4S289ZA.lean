module

public import CFSG.ClassicalInvolution.Q3.TL4S289Vtx

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance

namespace S289

variable {G : Type} [Group G] [Finite G] {t u w : G}

omit [Finite G] in
theorem mul_self_of_mem_inducedImage {B : Subgroup G} (hB : IsElemAbelian 2 B)
    {L : Subgroup (OddQuot t)} : ∀ x ∈ inducedImage L (modOdd t B), x * x = 1 := by
  rintro _ ⟨v, hv, rfl⟩
  rw [← map_mul]
  have hvv : v * v = 1 := Subtype.ext (mul_self_of_mem_modOdd hB _ (Subgroup.mem_subgroupOf.mp hv))
  rw [hvv, map_one]

omit [Finite G] in
theorem alphaOf_eq_bot_of_autFree {B : Subgroup G} (hB : IsElemAbelian 2 B)
    {L : Subgroup (OddQuot t)} (hL : Q3NM.AutOddFree ↥L) (huB : u ∈ B)
    (hutC : u ∈ Subgroup.centralizer ({t} : Set G))
    (huN : oddQuotMk t ⟨u, hutC⟩ ∈ Subgroup.normalizer (L : Set (OddQuot t)))
    (hmu : ∃ y ∈ L, oddQuotMk t ⟨u, hutC⟩ * y ≠ y * oddQuotMk t ⟨u, hutC⟩) :
    alphaOf (inducedImage L (modOdd t B)) = ⊥ := by
  obtain ⟨y, hy, hne⟩ := hmu
  exact Vtx.alphaOf_inducedImage_eq_bot_of_autOddFree hL (mul_self_of_mem_modOdd hB)
    (oddQuotMk_mem_modOdd huB hutC) huN (Lemma52Proof.toInducedAutOn_ne_one_of_moved L huN hy hne)

section Cit3


theorem alphaOf_eq_bot_of_innerFree
    (hB : IsElemAbelian 2 (Subgroup.closure ({t, u, w} : Set G)))
    (hutC : u ∈ Subgroup.centralizer ({t} : Set G))
    (hwtC : w ∈ Subgroup.centralizer ({t} : Set G)) {L : Subgroup (OddQuot t)}
    (hL : Q3NM.AutOddFreeInner ↥L) (huL : oddQuotMk t ⟨u, hutC⟩ ∈ L)
    (hwL : oddQuotMk t ⟨w, hwtC⟩ ∈ L)
    (hmu : ∃ y ∈ L, oddQuotMk t ⟨u, hutC⟩ * y ≠ y * oddQuotMk t ⟨u, hutC⟩) :
    alphaOf (inducedImage L (modOdd t (Subgroup.closure ({t, u, w} : Set G)))) = ⊥ := by
  obtain ⟨y, hy, hne⟩ := hmu
  have huN := Subgroup.le_normalizer huL
  refine Q3NM.alphaOf_inducedImage_eq_bot_of_inner L _ hL (mul_self_of_mem_inducedImage hB)
    ⟨_, Lemma52Proof.toInducedAutOn_mem_inducedImage L _
      (oddQuotMk_mem_modOdd (mem_closure_three_left t u w).2.1 hutC) huN,
      Lemma52Proof.toInducedAutOn_ne_one_of_moved L huN hy hne⟩
    (inner_of_frame hB hutC hwtC huL hwL)

theorem alphaOf_eq_bot_of_innerFour
    (hB : IsElemAbelian 2 (Subgroup.closure ({t, u, w} : Set G)))
    (hutC : u ∈ Subgroup.centralizer ({t} : Set G))
    (hwtC : w ∈ Subgroup.centralizer ({t} : Set G)) {L : Subgroup (OddQuot t)}
    (hα : ∀ 𝒳 : Subgroup (MulAut ↥L), Q3NM.innSubgroup ↥L ≤ 𝒳 →
      ∀ A : Subgroup ↥𝒳, (∀ a ∈ A, ((a : ↥𝒳) : MulAut ↥L) ∈ Q3NM.innSubgroup ↥L) →
        (∀ a ∈ A, a * a = 1) → Nat.card ↥A = 4 → alphaOf A = ⊥)
    (huL : oddQuotMk t ⟨u, hutC⟩ ∈ L) (hwL : oddQuotMk t ⟨w, hwtC⟩ ∈ L)
    (hmu : ∃ y ∈ L, oddQuotMk t ⟨u, hutC⟩ * y ≠ y * oddQuotMk t ⟨u, hutC⟩)
    (hmw : ∃ y ∈ L, oddQuotMk t ⟨w, hwtC⟩ * y ≠ y * oddQuotMk t ⟨w, hwtC⟩)
    (hmuw : ∃ y ∈ L, oddQuotMk t ⟨u, hutC⟩ * oddQuotMk t ⟨w, hwtC⟩ * y ≠
      y * (oddQuotMk t ⟨u, hutC⟩ * oddQuotMk t ⟨w, hwtC⟩)) :
    alphaOf (inducedImage L (modOdd t (Subgroup.closure ({t, u, w} : Set G)))) = ⊥ :=
  hα (inducedAutOn L) (innSubgroup_le_inducedAutOn L) _ (inner_of_frame hB hutC hwtC huL hwL)
    (mul_self_of_mem_inducedImage hB)
    (natCard_inducedImage_eq_four hB hutC hwtC huL hwL hmu hmw hmuw)

end Cit3

end S289

end CFSG.ClassicalInvolution.Q3.TL4
