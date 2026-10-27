module

public import CFSG.ClassicalInvolution.RouteD.TypeCBlock
public import CFSG.ClassicalInvolution.RouteD.Sp3C4Link
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.Sp3C4

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.NonClassical

variable {p f m : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {z : G}

structure BlockDataU (Fr : Frame p f m Ω K z) : Prop where
  p1 : ∀ i j : Fin (m + 1), i ≠ j → LocalOddCentral Ω {Fr.zf i * Fr.zf j}
  unl : ∀ i j : Fin (m + 1), i ≠ j → UnlinkedAt Ω (Fr.Kf i) (Fr.zf i) (Fr.zf j)
  clique : ∀ i j : Fin (m + 1), i ≠ j →
    CliqueAt Ω (Fr.Kf i) (Fr.Kf j) (Fr.zf i) (Fr.zf j)

section Local

variable [Finite G]

theorem exists_comp_of_pair_locU (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z)
    (B : BlockDataU Fr) {i j : Fin (m + 1)} (hij : i ≠ j)
    (D : LieSystemData p f (locQuot Ω (Fr.zf i * Fr.zf j)) (locFamily Ω (Fr.zf i * Fr.zf j))) :
    ∃ c : Fin D.card, locImg Ω (Fr.zf i * Fr.zf j) (Fr.Kf i) ≤ (D.hom c).range ∧
      locImg Ω (Fr.zf i * Fr.zf j) (Fr.Kf j) ≤ (D.hom c).range := by
  have hP1x := B.p1 _ _ hij
  have hKi := Fr.Kf_mem_cent_mul S i j i
  have hKj := Fr.Kf_mem_cent_mul S i j j
  obtain ⟨c, hc⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨_, hKi, rfl⟩)
  obtain ⟨cj, hcj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨_, hKj, rfl⟩)
  obtain ⟨L₀, hL₀, hn1, hn2⟩ := exists_noncommuting_member S Fr hij
  have hL₀x := memberSet_subset_cent S Fr hij hL₀
  obtain ⟨c₀, hc₀⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨_, hL₀x, rfl⟩)
  have e1 : c₀ = c := same_comp_of_not_commutes S.inClass hP1x D hL₀x hKi hn1 hc₀ hc
  have e2 : c₀ = cj := same_comp_of_not_commutes S.inClass hP1x D hL₀x hKj hn2 hc₀ hcj
  have e3 : cj = c := e2.symm.trans e1
  rw [e3] at hcj
  exact ⟨c, hc, hcj⟩

theorem not_le_range_of_commutes_locU (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z)
    (B : BlockDataU Fr) {i j : Fin (m + 1)} (hij : i ≠ j)
    (D : LieSystemData p f (locQuot Ω (Fr.zf i * Fr.zf j)) (locFamily Ω (Fr.zf i * Fr.zf j)))
    {c : Fin D.card} (hci : locImg Ω (Fr.zf i * Fr.zf j) (Fr.Kf i) ≤ (D.hom c).range)
    (hcj : locImg Ω (Fr.zf i * Fr.zf j) (Fr.Kf j) ≤ (D.hom c).range) {L : Subgroup G}
    (hL : L ∈ Ω) (hLi : Commutes L (Fr.Kf i)) (hLj : Commutes L (Fr.Kf j)) :
    ¬ locImg Ω (Fr.zf i * Fr.zf j) L ≤ (D.hom c).range := by
  intro hLc
  have hKi := Fr.Kf_mem_cent_mul S i j i
  have hKj := Fr.Kf_mem_cent_mul S i j j
  have hLx := mem_cent_mul_of_commutes S Fr hL hLi hLj
  have hLvis : L ∈ centralizingMembers Ω {Fr.zf i * Fr.zf j, Fr.zf i} :=
    mem_centralizingMembers_pair.mpr ⟨hLx, le_centralizer_of_commutes hLi (Frame.zf_mem S i)⟩
  have hLKi : L ≠ Fr.Kf i := fun h =>
    not_commutes_self_of_isClassicalMember (Fr.cls S i) (h ▸ hLi)
  have hLKj : L ≠ Fr.Kf j := fun h =>
    not_commutes_self_of_isClassicalMember (Fr.cls S j) (h ▸ hLj)
  obtain ⟨R, hRvis, hRn⟩ := B.unl i j hij
  have hKK : Linked Ω (Fr.zf i * Fr.zf j) (Fr.Kf i) (Fr.Kf j) :=
    linked_of_le_range S.inClass S.exact D hKi hKj hci hcj
  have hRKi : R ≠ Fr.Kf i := by
    intro h
    subst h
    exact hRn Relation.ReflTransGen.refl
  have hRKj : R ≠ Fr.Kf j := by
    intro h
    rw [h] at hRn
    exact hRn hKK
  have hKL : Linked Ω (Fr.zf i * Fr.zf j) (Fr.Kf i) L :=
    linked_of_le_range S.inClass S.exact D hKi hLx hci hLc
  have hRL : Linked Ω (Fr.zf i * Fr.zf j) R L :=
    B.clique i j hij R hRvis L hLvis hRKi hRKj hLKi hLKj
  exact hRn (hKL.trans hRL.symm)

theorem block_lemma_locU (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) (B : BlockDataU Fr)
    {i j : Fin (m + 1)} (hij : i ≠ j) {L : Subgroup G} (hL : L ∈ Ω) (hLi : Commutes L (Fr.Kf i))
    (hLj : Commutes L (Fr.Kf j)) : Commutes L (Mf Fr i j) := by
  have hxord := Fr.orderOf_zf_mul S hij
  have hP1x := B.p1 _ _ hij
  obtain ⟨D⟩ := S.exists_lieSystemData hxord
  obtain ⟨c, hci, hcj⟩ := exists_comp_of_pair_locU S Fr B hij D
  have hLx := mem_cent_mul_of_commutes S Fr hL hLi hLj
  have hKi := Fr.Kf_mem_cent_mul S i j i
  have hKj := Fr.Kf_mem_cent_mul S i j j
  have hMx : ∀ L' : memberSet Fr i j,
      (L' : Subgroup G) ≤ locLayer Ω (Fr.zf i * Fr.zf j) := fun L' =>
    le_centralizingLayer (memberSet_subset_cent S Fr hij L'.2)
  have hMimg : locImg Ω (Fr.zf i * Fr.zf j) (Mf Fr i j) ≤ (D.hom c).range := by
    rw [Mf, locImg_iSup _ hMx]
    refine iSup_le fun L' => ?_
    have hL'x := memberSet_subset_cent S Fr hij L'.2
    obtain ⟨c', hc'⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨_, hL'x, rfl⟩)
    by_cases hcc : c' = c
    · rw [hcc] at hc'
      exact hc'
    · exfalso
      refine not_commutes_both S Fr hij L'.2 ⟨?_, ?_⟩
      · refine commutes_of_commutes_locImg S.inClass hP1x hL'x hKi ?_
        intro a ha b hb
        exact range_commute_of_ne D hcc a (hc' ha) b (hci hb)
      · refine commutes_of_commutes_locImg S.inClass hP1x hL'x hKj ?_
        intro a ha b hb
        exact range_commute_of_ne D hcc a (hc' ha) b (hcj hb)
  obtain ⟨c', hc'⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨_, hLx, rfl⟩)
  have hcc : c' ≠ c := fun h =>
    not_le_range_of_commutes_locU S Fr B hij D hci hcj hL hLi hLj (by rw [h] at hc'; exact hc')
  obtain ⟨z', hz'⟩ := S.inClass.classical L hL
  refine commutes_of_commutes_locImg_perfect hP1x (le_centralizingLayer hLx) (iSup_le hMx)
    (commutator_eq_of_isClassicalMember hz').ge ?_
  intro a ha b hb
  exact range_commute_of_ne D hcc a (hc' ha) b (hMimg hb)

theorem commutes_Mf_Mf_locU (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z) (B : BlockDataU Fr)
    {i j k l : Fin (m + 1)} (hkl : k ≠ l) (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i)
    (hlj : l ≠ j) : Commutes (Mf Fr i j) (Mf Fr k l) :=
  commutes_iSup_left_of_forall _ _ fun L => by
    have := block_lemma_locU S Fr B hkl L.2.1 (L.2.2 k hki hkj) (L.2.2 l hli hlj)
    exact this

theorem layersCommute_of_blockDataU (S : CSetup p f m Ω K z) (Fr : Frame p f m Ω K z)
    (B : BlockDataU Fr) : LayersCommute Fr :=
  fun _ hkl hki hkj hli hlj => commutes_Mf_Mf_locU S Fr B hkl hki hkj hli hlj

end Local

end CFSG.ClassicalInvolution.RouteD.Sp3C4
