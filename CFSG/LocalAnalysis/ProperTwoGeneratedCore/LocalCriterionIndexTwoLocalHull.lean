module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingConjugacy
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStar

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem point_class_not_mem_normal_of_point_not_mem
    (M : Subgroup G) [M.Normal] {z t : G} (hzM : z ∉ M)
    (ht : t ∈ involutionPointClass z) : t ∉ M := by
  obtain ⟨g, rfl⟩ := ht
  intro htM
  have hz := (inferInstance : M.Normal).conj_mem _ htM g
  exact hzM (by simpa only [rightConjugateElem, mul_assoc,
    mul_inv_cancel_left, mul_inv_cancel, mul_one] using hz)

theorem odd_card_of_no_order_two (A : Subgroup G)
    (hno : ∀ a ∈ A, orderOf a ≠ 2) : Odd (Nat.card A) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2
    (even_iff_two_dvd.mp heven)
  exact hno a a.property ((Subgroup.orderOf_coe a).trans ha)

theorem local_point_ambient_card_ne_two {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) : Nat.card G ≠ 2 := by
  intro hcard
  have hcyclic : Subgroup.zpowers z = ⊤ :=
    (Subgroup.zpowers z).eq_top_of_card_eq
      (by rw [Nat.card_zpowers, h.distinguished_order, hcard])
  exact h.proper (top_unique (hcyclic ▸ Subgroup.zpowers_le.mpr h.distinguished_mem))

theorem local_point_normal_index_two_even {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hodd : oddCore G = ⊥)
    (M : Subgroup G) [M.Normal] (hindex : M.index = 2) : Even (Nat.card M) := by
  apply Nat.not_odd_iff_even.mp
  intro hModd
  have hMle : M ≤ oddCore G := le_sSup ⟨inferInstance, hModd⟩
  have hMbot : M = ⊥ := le_antisymm (hodd ▸ hMle) bot_le
  have hcard := M.index_mul_card
  rw [hindex, hMbot, Subgroup.card_bot, mul_one] at hcard
  exact local_point_ambient_card_ne_two h hcard.symm

theorem local_point_not_strongly_embedded_of_index_two
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hodd : oddCore G = ⊥) (M : Subgroup G) [M.Normal]
    (hindex : M.index = 2) (hzM : z ∉ M) : ¬ IsStronglyEmbedded H := by
  intro hSE
  have hModd : Odd (Nat.card M) := by
    apply odd_card_of_no_order_two
    intro a ha haorder
    have haI := orderOf_eq_prime_iff.mp haorder
    have hzI := orderOf_eq_prime_iff.mp h.distinguished_order
    obtain ⟨g, hg⟩ := hSE.involutions_conjugate ⟨hzI.2, hzI.1⟩ ⟨haI.2, haI.1⟩
    exact point_class_not_mem_normal_of_point_not_mem M hzM ⟨g, hg⟩ ha
  exact (Nat.not_odd_iff_even.mpr (local_point_normal_index_two_even h hodd M hindex)) hModd

omit [Finite G] in
theorem local_point_hull_normalized_by_centralizer (z u : G) :
    Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (localInvolutionPointHull z u : Set G) := by
  intro c hc
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  have hforward : ∀ (a : G), a ∈ Subgroup.centralizer ({u} : Set G) →
      ∀ x ∈ localInvolutionPointHull z u, a * x * a⁻¹ ∈ localInvolutionPointHull z u := by
    intro a ha x hx
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp ha
    have hle : (localInvolutionPointHull z u).map (MulAut.conj a).toMonoidHom ≤
        localInvolutionPointHull z u := by
      rw [localInvolutionPointHull, MonoidHom.map_closure]
      apply (Subgroup.closure_le _).mpr
      rintro y ⟨s, hs, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨?_, ?_⟩
      · simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, rightConjugateElem,
          inv_inv] using LocalCriterionGeometry.pointClass_right_conjugate_mem hs.1 a⁻¹
      · apply Subgroup.mem_centralizer_singleton_iff.mpr
        have hsu := Subgroup.mem_centralizer_singleton_iff.mp hs.2
        have hconj := congrArg (MulAut.conj a) hsu
        have hau : (MulAut.conj a) u = u := by
          simp only [MulAut.conj_apply, hcomm, mul_assoc, mul_inv_cancel, mul_one]
        simpa only [map_mul, hau, MulAut.conj_apply, MulEquiv.coe_toMonoidHom] using hconj
    exact hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  constructor
  · exact hforward c hc x
  · intro hx
    have hh := hforward c⁻¹ ((Subgroup.centralizer ({u} : Set G)).inv_mem hc)
      (c * x * c⁻¹) hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh

omit [Finite G] in
theorem index_two_intersection_involution_decomposition
    (M L : Subgroup G) (hindex : M.index = 2) {z : G}
    (hzM : z ∉ M) (hzL : z ∈ L) (hzorder : orderOf z = 2) :
    (L ⊓ M).relIndex L = 2 ∧ L = (L ⊓ M) ⊔ Subgroup.zpowers z ∧
      ∀ l ∈ L, l * z ∈ L ⊓ M ∨ l ∈ L ⊓ M := by
  have hcases : ∀ l ∈ L, l * z ∈ L ⊓ M ∨ l ∈ L ⊓ M := by
    intro l hl
    by_cases hlM : l ∈ M
    · exact Or.inr ⟨hl, hlM⟩
    · exact Or.inl ⟨L.mul_mem hl hzL,
        (Subgroup.mul_mem_iff_of_index_two hindex).mpr (iff_of_false hlM hzM)⟩
  have hrel : (L ⊓ M).relIndex L = 2 :=
    Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
      ⟨z, hzL, fun hz => hzM hz.2, hcases⟩
  refine ⟨hrel, le_antisymm ?_ (sup_le inf_le_left (Subgroup.zpowers_le.mpr hzL)), hcases⟩
  intro l hl
  rcases hcases l hl with hlz | hlX
  · have hmem := ((L ⊓ M) ⊔ Subgroup.zpowers z).mul_mem
      (Subgroup.mem_sup_left hlz) (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    have hzz : z * z = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hzorder).1
    simpa only [mul_assoc, hzz, mul_one] using hmem
  · exact Subgroup.mem_sup_left hlX

theorem local_point_index_two_odd_kernel
    {H : Subgroup G} {z u : G} (h : InvolutionPointLocalEmbedding H z)
    (M : Subgroup G) [M.Normal] (hindex : M.index = 2) (hzM : z ∉ M)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    let L := localInvolutionPointHull z u
    let X := L ⊓ M
    Odd (Nat.card X) ∧
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (X : Set G) ∧
      X.relIndex L = 2 ∧ L = X ⊔ Subgroup.zpowers z ∧ ¬ X ≤ H := by
  let L := localInvolutionPointHull z u
  let X := L ⊓ M
  have hzL : z ∈ L := distinguished_mem_localInvolutionPointHull huz
  let zL : L := ⟨z, hzL⟩
  have hzLorder : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans h.distinguished_order
  have hSE : IsStronglyEmbedded (H.subgroupOf L) :=
    native_strong_embedding_of_order_conditions (h.local_embedding u hu huz hescape)
  have hXodd : Odd (Nat.card X) := by
    apply odd_card_of_no_order_two
    intro a ha haorder
    let aL : L := ⟨a, ha.1⟩
    have haLorder : orderOf aL = 2 := (Subgroup.orderOf_coe aL).symm.trans haorder
    have hzI := orderOf_eq_prime_iff.mp hzLorder
    have haI := orderOf_eq_prime_iff.mp haLorder
    obtain ⟨g, hg⟩ := hSE.involutions_conjugate ⟨hzI.2, hzI.1⟩ ⟨haI.2, haI.1⟩
    have haClass : a ∈ involutionPointClass z :=
      ⟨(g : G), congrArg Subtype.val hg⟩
    exact point_class_not_mem_normal_of_point_not_mem M hzM haClass ha.2
  have hLC := local_point_hull_normalized_by_centralizer z u
  have hXC : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    intro c hc
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hLC hc, Subgroup.le_normalizer_of_normal (H := M) hc⟩
  obtain ⟨hrel, hdecomp, _⟩ := index_two_intersection_involution_decomposition
    M L hindex hzM hzL h.distinguished_order
  have hXescape : ¬ X ≤ H := by
    intro hXH
    have hLH : L ≤ H := hdecomp ▸ sup_le hXH (Subgroup.zpowers_le.mpr h.distinguished_mem)
    apply hSE.ne_top
    apply top_unique
    intro l _
    exact hLH l.property
  exact ⟨hXodd, hLC, hXC, hrel, hdecomp, hXescape⟩

end CFSG.ProperTwoGeneratedCore
