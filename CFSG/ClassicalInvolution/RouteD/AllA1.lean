module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.RouteD.GapsR2
public import CFSG.ClassicalInvolution.RouteD.LocalTwinPartner

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem card_range_le_of_psl_two {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (i : Fin D.card) (ht : D.tag i = .PSL) (hr : D.rank i = 2) :
    Nat.card (D.hom i).range ≤ Nat.card SL(2, GaloisField p f) := by
  obtain ⟨ψ, -, hrange, -⟩ := exists_psl_hom D i ht (k := 1) hr
  rw [← hrange]
  exact Nat.card_le_card_of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective

theorem commutes_of_ne_of_all_a1 [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (hall : ∀ i, D.tag i = .PSL ∧ D.rank i = 2) {N N' : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) (hN' : N' ∈ centralizingMembers Ω {x}) (hne : N ≠ N') :
    Commutes N N' := by
  obtain ⟨i, hi, -⟩ := Gaps.exists_unique_comp hΩ hex D hN
  obtain ⟨j, hj, -⟩ := Gaps.exists_unique_comp hΩ hex D hN'
  by_cases hij : i = j
  · subst hij
    exfalso
    apply hne
    obtain ⟨-, hi'⟩ := hi
    obtain ⟨-, hj'⟩ := hj
    have e1 : locImg Ω x N = (D.hom i).range :=
      Subgroup.eq_of_le_of_card_ge hi' (by
        rw [card_locImg hΩ hex hN]
        exact card_range_le_of_psl_two D i (hall i).1 (hall i).2)
    have e2 : locImg Ω x N' = (D.hom i).range :=
      Subgroup.eq_of_le_of_card_ge hj' (by
        rw [card_locImg hΩ hex hN']
        exact card_range_le_of_psl_two D i (hall i).1 (hall i).2)
    exact locImg_injOn hΩ hP1 hN hN' (e1.trans e2.symm)
  · exact Gaps.commutes_of_ne_comp hΩ hP1 D hij hi hj

theorem false_of_all_a1 [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {K : Subgroup G} {z : G} (h : RouteDSetup p f K z) {a : ℕ}
    (hshape : LocalShapeT p f a .PSL 2 (conjClass K) z) : False := by
  have hΩ := h.inClass
  have hex := h.exact
  have hP1 := h.p1
  have hf : 0 < f := pos_of_five_le h.five
  obtain ⟨D, -, i₁, ht, hr, hrest⟩ := hshape
  have hall : ∀ i, D.tag i = .PSL ∧ D.rank i = 2 := fun i => by
    by_cases hi : i = i₁
    · subst hi
      exact ⟨ht, hr⟩
    · exact hrest i hi
  have hKΩ : K ∈ conjClass K := mem_conjClass_self K
  have hKz : K ∈ centralizingMembers (conjClass K) {z} :=
    ⟨hKΩ, le_centralizer_of_isClassicalMember h.cls⟩
  have htwin : ∀ L ∈ centralizingMembers (conjClass K) {z}, ∀ w : G, IsClassicalMember p f L w →
      centralizingMembers (conjClass K) {w} = centralizingMembers (conjClass K) {z} := by
    intro L hL w hw
    obtain ⟨g, hg⟩ := single_class K L hL.1
    exact centralizingMembers_eq_of_twin h.odd hf hΩ h.cls hw ⟨g, hg⟩ hL
      (fun N hN hNL => commutes_of_ne_of_all_a1 hΩ hex hP1 D hall hL hN (Ne.symm hNL))
  have hclosed : ∀ A ∈ centralizingMembers (conjClass K) {z}, ∀ B ∈ conjClass K, Commutes A B →
      B ∈ centralizingMembers (conjClass K) {z} := by
    intro A hA B hB hAB
    obtain ⟨w, hw⟩ := hΩ.classical A hA.1
    rw [← htwin A hA w hw]
    exact ⟨hB, fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hAB w hw.mem b hb).symm⟩
  have hall_mem : ∀ B : conjClass K, (B : Subgroup G) ∈ centralizingMembers (conjClass K) {z} := by
    intro B
    have hreach := h.conn.preconnected ⟨K, hKΩ⟩ B
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    induction hreach with
    | refl => exact hKz
    | @tail b c _ hbc ih =>
      exact hclosed b.1 ih c.1 c.2 ((CFSG.ClassicalInvolution.Models.commGraph_adj.mp hbc).2)
  have hle : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [← hΩ.generated]
    exact iSup₂_le fun L hL => (hall_mem ⟨L, hL⟩).2
  have hzc : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  rw [center_eq_bot hnab, Subgroup.mem_bot] at hzc
  have h2 := h.cls.orderOf_eq_two
  rw [hzc, orderOf_one] at h2
  omega

theorem pieceAllA1 : PieceAllA1 p f := by
  intro a t n hn G _ _ _ hnab K z h hshape
  obtain ⟨rfl, rfl⟩ := hn
  exact (false_of_all_a1 hnab h hshape).elim

end CFSG.ClassicalInvolution.RouteD
