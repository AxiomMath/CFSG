module

public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Q3.Q3WARow

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank

section Twin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem centralizingMembers_eq_of_twin3 (hΩ : InClass3 Ω) {L T : Subgroup G} {zL zT : G}
    (hL : IsClassicalMember3 L zL) (hT : IsClassicalMember3 T zT)
    (hLT : ∃ g : G, T = conjSub g L) (hTmem : T ∈ centralizingMembers Ω {zL})
    (hTcomm : ∀ N ∈ centralizingMembers Ω {zL}, N ≠ T → Commutes T N) :
    centralizingMembers Ω {zT} = centralizingMembers Ω {zL} := by
  have hsub : centralizingMembers Ω {zL} ⊆ centralizingMembers Ω {zT} := by
    intro N hN
    by_cases hNT : N = T
    · subst hNT
      exact ⟨hTmem.1, isSubnormal_le hT.subnormal⟩
    · exact mem_centralizingMembers_of_commutes hN.1 hT.mem (hTcomm N hN hNT).symm
  obtain ⟨g, hg⟩ := hLT
  have hzg : IsClassicalMember3 T (g * zL * g⁻¹) := by
    rw [hg]
    exact hL.conj g
  have hzz : zT = g * zL * g⁻¹ := involution_unique3 hT hzg
  have hcard : (centralizingMembers Ω {zT}).ncard ≤ (centralizingMembers Ω {zL}).ncard := by
    rw [hzz, ncard_centralizingMembers_conj hΩ.conjInvariant]
  exact (Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)).symm

end Twin

section AllA1


variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_comp_of_all_a1_3 {ι : Type} {Ω : Set (Subgroup G)} {x : G}
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) (hall : ∀ i, D.kind i = CompData.sl23)
    {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {x}) :
    ∃ i, locImg Ω x N = (D.hom i).range := by
  have hmem : locImg Ω x N ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨N, hN, rfl⟩
  obtain ⟨i, R, hR, hRN⟩ := D.fundamental _ hmem
  have key : ∀ c : CompData, c = CompData.sl23 → ∀ (φ : c.G →* locQuot Ω x)
      (R' : Subgroup c.G), R' ∈ c.fund → R'.map φ = φ.range := by
    rintro c rfl φ R' hR'
    have : R' = ⊤ := hR'
    rw [this, Subgroup.map_top]
  exact ⟨i, hRN.trans (key _ (hall i) (D.hom i) R hR)⟩

theorem commutes_of_ne_of_all_a1_3 {ι : Type} {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x))
    (hall : ∀ i, D.kind i = CompData.sl23) {N N' : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) (hN' : N' ∈ centralizingMembers Ω {x}) (hne : N ≠ N') :
    Commutes N N' := by
  obtain ⟨i, hi⟩ := exists_comp_of_all_a1_3 D hall hN
  obtain ⟨j, hj⟩ := exists_comp_of_all_a1_3 D hall hN'
  by_cases hij : i = j
  · subst hij
    exact absurd (locImg_injOn3 hΩ hex hP1 hO3 hN hN' (hi.trans hj.symm)) hne
  · refine commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hN hN' ?_
    rw [hi, hj]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i j hij a b

theorem false_of_all_a1_3 [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G}
    {z : G} (h : RouteD3Setup K z) (h3 : LocalOddThreeFree3 (conjClass3 K) z) {a : ℕ}
    (hshape : LocalShapeC3 a CompData.sl23 (conjClass3 K) z) : False := by
  have hΩ := h.inClass
  obtain ⟨hex, hP1⟩ := h.setup
  obtain ⟨ι, hι, D, hcard, i₁, hk, hrest⟩ := hshape
  have hall : ∀ i, D.kind i = CompData.sl23 := fun i => by
    by_cases hi : i = i₁
    · subst hi
      exact hk
    · exact hrest i hi
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} := ⟨hKΩ, isSubnormal_le h.cls.subnormal⟩
  have htwin : ∀ L ∈ centralizingMembers (conjClass3 K) {z}, ∀ w : G,
      IsClassicalMember3 L w →
      centralizingMembers (conjClass3 K) {w} = centralizingMembers (conjClass3 K) {z} := by
    intro L hL w hw
    obtain ⟨g, hg⟩ := hL.1
    exact centralizingMembers_eq_of_twin3 hΩ h.cls hw ⟨g, hg.symm⟩ hL
      (fun N hN hNL => commutes_of_ne_of_all_a1_3 hΩ hex hP1 h3 D hall hL hN (Ne.symm hNL))
  have hclosed : ∀ A ∈ centralizingMembers (conjClass3 K) {z}, ∀ B ∈ conjClass3 K, B ≠ A →
      Commutes A B → B ∈ centralizingMembers (conjClass3 K) {z} := by
    intro A hA B hB _ hAB
    obtain ⟨w, hw⟩ := hΩ.classical A hA.1
    rw [← htwin A hA w hw]
    exact ⟨hB, fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hAB w hw.mem b hb).symm⟩
  have hsub : conjClass3 K ⊆ centralizingMembers (conjClass3 K) {z} :=
    subset_of_adj_closed ((CoreAssembly.deltaConnected_iff K).mp h.conn)
      (fun A hA => hA.1) ⟨K, hKz⟩ hclosed
  have hle : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [← hΩ.generated]
    exact iSup₂_le fun L hL => (hsub hL).2
  have hzc : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at hzc
  have h2 := h.cls.orderOf_eq_two
  rw [hzc, orderOf_one] at h2
  omega

end AllA1

theorem pieceAllA1₃_of_odd3
    (h3 : OddThreeFreeInput) : PieceAllA1₃ := by
  intro a G _ _ _ hnab K z hR hshape
  exact (false_of_all_a1_3 hnab hR (h3 G K z hR) hshape).elim

end CFSG.ClassicalInvolution.Q3.Q3W
