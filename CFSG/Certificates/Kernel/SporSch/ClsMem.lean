module

public import CFSG.Certificates.Kernel.SporSch.ChainKZTot
public import CFSG.Certificates.Kernel.KGC31PSound

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum
open CFSG.KS.SporSch.MBT CFSG.Certificates CFSG.Sporadic CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Monster.B.Mathieu CFSG.KS.SporSch.ClsSpec

variable {n w : Nat} {words : List (List Int)} {k : Nat} {bv : Vector (Fin n) k}
  {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat} {gA gB : Equiv.Perm (Fin n)}

theorem exists_of_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hr hs, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨b, hb, hab⟩ := exists_of_forall₂ hs a h
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem mem_orderTables_cls (hQ : ChainK n w [gA, gB] words bv PS PSI LR TR TRI kS BP NS CH)
    (hn : 1 ≤ n) (hbs : bv.toList.Nodup) {tA tB : List Nat} (hA : tA = imageList gA)
    (hB : tB = imageList gB) {mx cap : Nat} {CS : List ClsD} (hcls : ClsOK n w tA tB mx cap CS)
    (hRs : ∀ j < CS.length, bAnd(canonK n w (mask w) (n * w) (CS.getD j clsD0).R,
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 (CS.getD j clsD0).R) = true)
    (hmx : 0 < mx)
    (hX : (orderTables (certificate hn [gA, gB] words bv hbs) mx).length = (CS.map ClsD.c).sum) :
    ∀ T ∈ orderTables (certificate hn [gA, gB] words bv hbs) mx, ∃ j < CS.length,
      ∃ k' < (CS.getD j clsD0).c, T = CFSG.KC.Child3.tabP n w ((CS.getD j clsD0).ST k') := by
  classical
  set Q := certificate hn [gA, gB] words bv hbs
  set G := Q.originalSubgroup
  set K := Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))
  set L := CS.length
  have hV := chainK_valid hQ hn hbs
  have h32 := chainK_h32 hQ
  have hGK : G = K := orig_pair hn hbs
  have hex : ∀ j, ∃ r : Equiv.Perm (Fin n), j < L → PRep n w (CS.getD j clsD0).R r ∧ r ∈ G := by
    intro j
    by_cases hj : j < L
    · obtain ⟨r, pr, hr⟩ := rep_of_sift hQ hn hbs (hRs j hj)
      exact ⟨r, fun _ => ⟨pr, hr⟩⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose rs hrs using hex
  have hcf := fun j (hj : j < L) => datum_class hQ hA hB hcls hj (hrs j hj).1
  set xs := ((enumeration Q).filter fun h => decide (orderOf h = mx)).reverse
  have hXf := forall₂_orderTables h32 Q hmx
  have hmemxs : ∀ g, g ∈ xs ↔ g ∈ G ∧ orderOf g = mx := fun g => by
    simp only [xs, List.mem_reverse, List.mem_filter, decide_eq_true_eq]
    rw [mem_enumeration_iff Q hV]
  set XF := xs.toFinset
  have hXF : XF.card = (CS.map ClsD.c).sum := by
    rw [List.toFinset_card_of_nodup (List.nodup_reverse.2 ((enumeration_nodup Q hV).filter _)),
      ← hXf.length_eq, hX]
  set C : Nat → Finset (Equiv.Perm (Fin n)) :=
    fun j => XF.filter fun g => g ∈ SmallOddCore.conjClass K (rs j)
  have hclG : ∀ j < L, ∀ g ∈ SmallOddCore.conjClass K (rs j), g ∈ XF := by
    intro j hj g hg
    rw [List.mem_toFinset, hmemxs]
    obtain ⟨c, hc, rfl⟩ := hg
    rw [← hGK] at hc
    refine ⟨G.mul_mem (G.mul_mem hc (hrs j hj).2) (G.inv_mem hc), ?_⟩
    rw [← (hcf j hj).2.2.2]
    exact (MulAut.conj c).orderOf_eq (rs j)
  have hCcard : ∀ j < L, (C j).card = (CS.getD j clsD0).c := by
    intro j hj
    rw [← (hcf j hj).2.1, ← Set.ncard_coe_finset]
    congr 1
    ext g
    simp only [C, Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨hclG j hj g h, h⟩⟩
  have hpd : ∀ i ∈ Finset.range L, ∀ j ∈ Finset.range L, i ≠ j → Disjoint (C i) (C j) := by
    have h1 : ∀ i j, i < j → j < L → Disjoint (C i) (C j) := by
      intro i j hij hj
      rw [Finset.disjoint_left]
      intro g hgi hgj
      simp only [C, Finset.mem_filter] at hgi hgj
      exact datum_disj hQ hA hB hcls hij hj (hrs i (by omega)).1 (hrs j hj).1
        (conjClass_trans (conjClass_symm hgj.2) hgi.2)
    intro i hi j hj hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact h1 i j h (Finset.mem_range.1 hj)
    · exact (h1 j i h (Finset.mem_range.1 hi)).symm
  have hU : (Finset.range L).biUnion C = XF := by
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      obtain ⟨i, -, hgi⟩ := Finset.mem_biUnion.1 hg
      exact (Finset.mem_filter.1 hgi).1
    · rw [Finset.card_biUnion hpd, hXF, ← range_map_getD (d0 := clsD0) ClsD.c rfl,
        sum_range_list]
      exact (Finset.sum_congr rfl fun j hj => hCcard j (Finset.mem_range.1 hj)).ge
  intro T hT
  obtain ⟨g, hg, hTg⟩ := exists_of_forall₂ hXf T hT
  have hgF : g ∈ (Finset.range L).biUnion C := by
    rw [hU]
    exact List.mem_toFinset.2 hg
  obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.1 hgF
  have hj' := Finset.mem_range.1 hj
  obtain ⟨k', hk', pk⟩ := ((hcf j hj').1 g).1 (Finset.mem_filter.1 hgj).2
  refine ⟨j, hj', k', hk', ?_⟩
  have hs : T.size = n :=
    CFSG.KC.KGC31P.filterProducts_size _ (idT n) [] (by simp [idT])
      (fun _ h => absurd h List.not_mem_nil) T hT
  rw [CFSG.KS.Tbl.toTable_ext h32 hs hTg]
  exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img
    (CFSG.KC.KGC31P.imageList_of_prep pk)

end CFSG.KS.SporSch.MOC

end
