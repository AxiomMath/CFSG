module

public import CFSG.Literature.GL52Chain
public import Certificates.Data.L52Insp443
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermFano
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermMem
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermSix

public section

namespace CFSG.SectionRank.QTK.Insp443.L52

open Equiv CFSG.Certificates CFSG.Literature.GL52 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Native CFSG.SectionRank.QTK.Insp443.PermKit
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

theorem hn31 : 31 < 2 ^ 32 := by norm_num

theorem nodup_of_distinctT {n : ℕ} {ts : List Table} (ht : tabsOK n ts = true)
    (hd : distinctT n ts = true) : (ts.map (tabPerm n)).Nodup := by
  induction ts with
  | nil => exact List.nodup_nil
  | cons T ts ih =>
    simp only [tabsOK, List.all_cons, Bool.and_eq_true] at ht
    simp only [distinctT, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, ih ht.2 hd.2⟩
    obtain ⟨S, hS, hST⟩ := List.mem_map.mp hmem
    have hSt : tabOK n S (invT n S) = true := List.all_eq_true.mp ht.2 S hS
    have h2 : tblEq n T S = true :=
      (tblEq_iff_eq (rep_tabPerm ht.1) (rep_tabPerm hSt)).mpr hST.symm
    have h1 := hd.1 S hS
    rw [h2] at h1
    exact absurd h1 (by decide)

theorem orb_facts (h : chkOrb52 () = true) :
    tabsOK 31 memL = true ∧ distinctT 31 memL = true ∧
      countProducts 31 (inSp 31 memL) (levelTables glCert) (idT 31) = memL.length ∧
      ordTest 31 5 x5T = true ∧ ordTest 31 7 x7T = true ∧ ordTest 31 31 x31T = true ∧
      candsOK 31 cands5 = true ∧ candsOK 31 cands7 = true ∧
      orbCheck 31 5 (orderTables glCert 2) (powTabs 31 x5T 5) cands5 = true ∧
      orbCheck 31 7 (orderTables glCert 2) (powTabs 31 x7T 7) cands7 = true ∧
      orbCheck 31 31 (orderTables glCert 2) (powTabs 31 x31T 31) [] = true := by
  simpa only [chkOrb52, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

@[expose] def scanTests : List (Table → Bool) :=
  tests52 (e16.map (spanTabs 31)) ((List.range 2).map fun w => spanTabs 31 (wB w))
    ((List.range 2).map fun w => (aB w).map (spanTabs 31)) (x7Pairs (invT 31 x7T))

theorem p_facts (h : chkP52 () = true) :
    (∀ z < 7, e16OK z = true) ∧ (∀ w < 2, e64OK w = true) ∧
      (∀ k < 24, candOK (invT 31 x7T) (cands7.getD k []) (kind7.getD k (3, 0, 0)) = true) ∧
      (∀ z < 7, countProducts 31 (conjIn 31 (e16.getD z []) ((e16.map (spanTabs 31)).getD z []))
        (levelTables glCert) (idT 31) = 322560) ∧
      countProducts 31 (anyTest scanTests) (levelTables glCert) (idT 31) = 0 := by
  simp only [chkP52, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem getD_map_lt {α β : Type*} (f : α → β) {l : List α} {i : ℕ} (hi : i < l.length) (d : β)
    (d' : α) : (l.map f).getD i d = f (l.getD i d') := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getD_eq_getElem _ _ hi,
    List.getElem_map]

theorem getD_map_range {β : Type*} (f : ℕ → β) {m i : ℕ} (hi : i < m) (d : β) :
    ((List.range m).map f).getD i d = f i := by
  rw [getD_map_lt f (by rw [List.length_range]; exact hi) d 0, List.getD_eq_getElem _ _
    (by rw [List.length_range]; exact hi), List.getElem_range]

theorem length_e16 : e16.length = 7 := rfl

theorem length_e64a0 : e64a0.length = 2 := rfl

theorem length_e64a1 : e64a1.length = 2 := rfl

theorem length_cands7 : cands7.length = 24 := rfl

theorem length_cands5 : cands5.length = 2 := rfl

theorem mem_of_memL (h : chkOrb52 () = true) {T : Table} (hT : T ∈ memL) :
    tabPerm 31 T ∈ glCert.originalSubgroup := by
  obtain ⟨ht, hd, hc, -⟩ := orb_facts h
  exact mem_of_count_list hn31 glCert glCert_valid ht (nodup_of_distinctT ht hd) hc hT

theorem mem_memL {T : Table}
    (hT : T ∈ [x5T, x7T, x31T] ∨ T ∈ e16.flatten ∨ T ∈ e64a0.flatten ∨ T ∈ e64a1.flatten ∨
      T ∈ (List.range 2).flatMap fun w => diagT 31 (e64a0.getD w []) (e64a1.getD w [])) :
    T ∈ memL := by
  unfold memL
  rw [List.mem_dedup]
  simp only [List.mem_append]
  rcases hT with h | h | h | h | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem permBk_mem (h : chkOrb52 () = true) {bs : List Table} (hbs : ∀ T ∈ bs, T ∈ memL) {k : ℕ}
    (hk : bs.length = k) (i : Fin k) : permBk 31 k bs i ∈ glCert.originalSubgroup := by
  subst hk
  unfold permBk
  rw [List.getD_eq_getElem _ _ i.2]
  exact mem_of_memL h (hbs _ (List.getElem_mem i.2))

theorem e16_sub_memL {z : ℕ} (hz : z < 7) : ∀ T ∈ e16.getD z [], T ∈ memL := fun _ hT =>
  mem_memL (Or.inr (Or.inl (List.mem_flatten.mpr ⟨_, getD_mem (by rw [length_e16]; exact hz),
    hT⟩)))

theorem a0_sub_memL {w : ℕ} (hw : w < 2) : ∀ T ∈ e64a0.getD w [], T ∈ memL := fun _ hT =>
  mem_memL (Or.inr (Or.inr (Or.inl (List.mem_flatten.mpr
    ⟨_, getD_mem (by rw [length_e64a0]; exact hw), hT⟩))))

theorem a1_sub_memL {w : ℕ} (hw : w < 2) : ∀ T ∈ e64a1.getD w [], T ∈ memL := fun _ hT =>
  mem_memL (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_flatten.mpr
    ⟨_, getD_mem (by rw [length_e64a1]; exact hw), hT⟩)))))

theorem aB_sub_memL {w : ℕ} (hw : w < 2) {i : ℕ} (hi : i < 3) :
    ∀ T ∈ (aB w).getD i [], T ∈ memL := by
  interval_cases i
  · exact a0_sub_memL hw
  · exact a1_sub_memL hw
  · intro T hT
    exact mem_memL (Or.inr (Or.inr (Or.inr (Or.inr
      (List.mem_flatMap.mpr ⟨w, List.mem_range.mpr hw, hT⟩)))))

theorem wB_sub_memL {w : ℕ} (hw : w < 2) : ∀ T ∈ wB w, T ∈ memL := fun T hT => by
  unfold wB at hT
  rcases List.mem_append.mp hT with h | h
  · exact a0_sub_memL hw T h
  · exact a1_sub_memL hw T h

theorem exists_elt (h : chkOrb52 () = true) {xT : Table} (hx : xT ∈ [x5T, x7T, x31T]) {p : ℕ}
    (hp : 0 < p) (ho : ordTest 31 p xT = true) :
    ∃ x : glCert.originalSubgroup, Rep 31 xT (x : Perm (Fin 31)) ∧ orderOf x = p := by
  have hmem : xT ∈ memL := mem_memL (Or.inl hx)
  have ht : tabsOK 31 memL = true := (orb_facts h).1
  have hT : tabOK 31 xT (invT 31 xT) = true := List.all_eq_true.mp ht xT hmem
  have hrep : Rep 31 xT (tabPerm 31 xT) := rep_tabPerm hT
  have hord : orderOf (tabPerm 31 xT) = p := (ordTest_iff perm_faithful hrep hp).mp ho
  have hX := mem_of_memL h hmem
  generalize tabPerm 31 xT = g at hrep hord hX
  refine ⟨⟨g, hX⟩, hrep, ?_⟩
  rw [← Subgroup.orderOf_coe]
  exact hord

theorem mem_tests_e16 {z : ℕ} (hz : z < 7) :
    centTestS 31 (e16.getD z []) (spanTabs 31 (e16.getD z [])) ∈ scanTests := by
  unfold scanTests tests52
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inl (List.mem_map.mpr ⟨z, List.mem_range.mpr hz, ?_⟩))))))
  rw [getD_map_lt (spanTabs 31) (by rw [length_e16]; exact hz) [] []]

theorem mem_tests_cn {w : ℕ} (hw : w < 2) :
    cnTestS 31 (e64a0.getD w []) (e64a1.getD w []) (spanTabs 31 (e64a1.getD w []))
      (spanTabs 31 (wB w)) ∈ scanTests := by
  unfold scanTests tests52
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inr (List.mem_map.mpr ⟨w, List.mem_range.mpr hw, ?_⟩))))))
  rw [getD_map_range _ hw, getD_map_range _ hw]
  rfl

theorem mem_tests_perm3 {w : ℕ} (hw : w < 2) :
    perm3TestS 31 (wB w) (spanTabs 31 (wB w)) (aB w) ((aB w).map (spanTabs 31)) ∈ scanTests := by
  unfold scanTests tests52
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
    (List.mem_map.mpr ⟨w, List.mem_range.mpr hw, ?_⟩))))
  rw [getD_map_range _ hw, getD_map_range _ hw]

theorem mem_tests_cand {k : ℕ} (hk : k < 24) {t : Table → Bool}
    (ht : t ∈ candTests (e16.map (spanTabs 31)) ((List.range 2).map fun w => spanTabs 31 (wB w))
      (x7Pairs (invT 31 x7T)) (cands7.getD k []) (kind7.getD k (3, 0, 0))) : t ∈ scanTests := by
  unfold scanTests tests52
  exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ht⟩))

theorem mem_tests_s {k z w : ℕ} (hk : k < 24) (hz : z < 7) (hw : w < 2)
    (hkd : kind7.getD k (3, 0, 0) = (1, z, w)) :
    sTestS 31 (cands7.getD k []) (spanTabs 31 (e16.getD z [])) (spanTabs 31 (wB w))
      (x7Pairs (invT 31 x7T)) ∈ scanTests := by
  refine mem_tests_cand hk ?_
  rw [hkd]
  unfold candTests
  rw [if_pos rfl, getD_map_lt (spanTabs 31) (by rw [length_e16]; exact hz) [] [],
    getD_map_range _ hw]
  exact List.mem_cons_self

theorem mem_tests_c2 {k z w : ℕ} (hk : k < 24) (hkd : kind7.getD k (3, 0, 0) = (1, z, w)) :
    c2TestS 31 (cands7.getD k []) 128 ∈ scanTests := by
  refine mem_tests_cand hk ?_
  rw [hkd]
  unfold candTests
  rw [if_pos rfl]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem mem_tests_cent {k z w : ℕ} (hk : k < 24) (hw : w < 2)
    (hkd : kind7.getD k (3, 0, 0) = (2, z, w)) :
    centTestS 31 (cands7.getD k []) (spanTabs 31 (wB w)) ∈ scanTests := by
  refine mem_tests_cand hk ?_
  rw [hkd]
  unfold candTests
  rw [if_neg (by simp), if_pos rfl, getD_map_range _ hw]
  exact List.mem_cons_self

end CFSG.SectionRank.QTK.Insp443.L52

end
