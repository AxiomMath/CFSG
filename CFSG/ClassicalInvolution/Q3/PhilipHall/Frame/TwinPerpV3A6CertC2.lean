module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ModelSmall
public import Certificates.Certificate517506
public import Mathlib.Data.List.Sections

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.Certificates CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.EvenSmallLie.OmegaEight Certificates.AE6Model Certificates.S7Twin
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin

@[expose] def RepPair (p : Table × Table) (x : Equiv.Perm (Fin 360)) : Prop :=
  Rep 360 p.1 x ∧ Rep 360 p.2 x⁻¹

theorem repPair_one : RepPair (idT 360, idT 360) 1 := by
  unfold RepPair
  dsimp only
  refine ⟨Rep.idT degree_lt, ?_⟩
  rw [inv_one]
  exact Rep.idT degree_lt

theorem rep_of_tblEq' {n : ℕ} {S T : Table} {g : Equiv.Perm (Fin n)} (hS : Rep n S g)
    (h : tblEq n S T = true) : Rep n T g :=
  fun i hi => ((tblEq_iff.1 h) i hi).symm.trans (hS i hi)

theorem getD_map_lt {α β : Type*} (l : List α) (f : α → β) {i : ℕ} (hi : i < l.length) (d : β)
    (d' : α) : (l.map f).getD i d = f (l.getD i d') := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi, List.getElem_map]

theorem rep_tableEval {HT : List (Table × Table)} {xs : List (Equiv.Perm (Fin 360))}
    (h : ∀ j, RepPair (HT.getD j (idT 360, idT 360)) (xs.getD j 1)) (w : List ℕ) :
    Rep 360 (tableEval HT w) (A6.curtisEval xs w) := by
  have key : ∀ (w : List ℕ) (acc : Table) (accP : Equiv.Perm (Fin 360)), Rep 360 acc accP →
      Rep 360 (w.foldl (fun acc k => compT 360 acc
        (if k % 2 = 0 then (HT.getD (k / 2) (idT 360, idT 360)).1
          else (HT.getD (k / 2) (idT 360, idT 360)).2)) acc)
        (w.foldl (fun acc k => acc * if k % 2 = 0 then xs.getD (k / 2) 1
          else (xs.getD (k / 2) 1)⁻¹) accP) := by
    intro w
    induction w with
    | nil => exact fun _ _ hacc => hacc
    | cons k w ih =>
      intro acc accP hacc
      rw [List.foldl_cons, List.foldl_cons]
      refine ih _ _ (Rep.compT hacc ?_)
      have hk := h (k / 2)
      unfold RepPair at hk
      split_ifs
      · exact hk.1
      · exact hk.2
  exact key w _ _ (Rep.idT degree_lt)

theorem rep_wordTable {HT : List (Table × Table)} {xs : List (Equiv.Perm (Fin 360))}
    (h : ∀ j, RepPair (HT.getD j (idT 360, idT 360)) (xs.getD j 1)) (w : List ℕ) :
    Rep 360 (wordTable HT w) (w.map fun i => xs.getD i 1).prod := by
  have key : ∀ (w : List ℕ) (acc : Table) (accP : Equiv.Perm (Fin 360)), Rep 360 acc accP →
      Rep 360 (w.foldl (fun acc i => compT 360 acc (HT.getD i (idT 360, idT 360)).1) acc)
        (accP * (w.map fun i => xs.getD i 1).prod) := by
    intro w
    induction w with
    | nil => exact fun _ _ hacc => by simpa using hacc
    | cons i w ih =>
      intro acc accP hacc
      rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
      have hk := h i
      unfold RepPair at hk
      exact ih _ _ (Rep.compT hacc hk.1)
  have := key w (idT 360) 1 (Rep.idT degree_lt)
  rw [one_mul] at this
  unfold wordTable
  exact this

theorem curtisEval_map' {G H : Type*} [Group G] [Group H] (f : G →* H) (l : List G)
    (w : List ℕ) : A6.curtisEval (l.map f) w = f (A6.curtisEval l w) := by
  induction w with
  | nil => simp [A6.curtisEval_nil]
  | cons c w ih =>
    have hg : (l.map f).getD (c / 2) 1 = f (l.getD (c / 2) 1) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases l[c / 2]? <;> simp
    rw [A6.curtisEval_cons, A6.curtisEval_cons, ih, hg, map_mul]
    split_ifs <;> simp

theorem forall₂_filterProducts_levelTables {n : ℕ} (hn : n < 2 ^ 32)
    (Q : RawSchreierDatum n) {f : Table → Bool} {P : Equiv.Perm (Fin n) → Prop}
    [DecidablePred P] (hfP : ∀ T g, Rep n T g → (f T = true ↔ P g)) :
    List.Forall₂ (Rep n) (filterProducts n f (levelTables Q) (idT n) [])
      ((enumeration Q).filter fun h => decide (P h)).reverse := by
  have h := filterProducts_spec hfP (forall₂_levelTables hn Q) (Rep.idT hn) (acc := [])
    (accG := []) List.Forall₂.nil
  simp only [one_mul, List.map_id', List.append_nil] at h
  exact h

theorem c2_basic : (c2Qs ()).length = 8 ∧
    (∀ Q ∈ c2Qs (), memT 360 Q (toTable (z0 ())) = true ∧
      ∀ T ∈ (c2Qs ()).getD 3 [], memT 360 Q T = true) ∧
    ∀ L ∈ c2Ls (), ∀ T ∈ L, invOK 360 T (invT 360 T) = true := by
  have h : (pWordsC2.all (fun w => memT 360 (allTables (plQ ()))
      (toTable (aeWord (curtisPerms ()) w))) &&
      (c2Qs ()).length == 8 && (c2Qs ()).all (fun Q => memT 360 Q (toTable (z0 ())) &&
      ((c2Qs ()).getD 3 []).all (memT 360 Q)) &&
      (c2Ls ()).all fun L => L.all fun T => invOK 360 T (invT 360 T)) = true :=
    Certificates.certificate517506.1
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

theorem c2_words : ∀ w ∈ pWordsC2,
    memT 360 (allTables (plQ ())) (toTable (aeWord (curtisPerms ()) w)) = true := by
  have h : (pWordsC2.all (fun w => memT 360 (allTables (plQ ()))
      (toTable (aeWord (curtisPerms ()) w))) &&
      (c2Qs ()).length == 8 && (c2Qs ()).all (fun Q => memT 360 Q (toTable (z0 ())) &&
      ((c2Qs ()).getD 3 []).all (memT 360 Q)) &&
      (c2Ls ()).all fun L => L.all fun T => invOK 360 T (invT 360 T)) = true :=
    Certificates.certificate517506.1
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact h.1.1.1

theorem mem_c2Qs {i : ℕ} (hi : i < 8) {T : Table} (hT : T ∈ (c2Qs ()).getD i []) :
    ∃ q ∈ (plQ ()).originalSubgroup, Rep 360 T q ∧
      (curtisPerms ()).getD i 1 * q * ((curtisPerms ()).getD i 1)⁻¹ ∈
        (plQ ()).originalSubgroup := by
  have hn := degree_lt
  have hlen : (c2Qs ()).length = 8 := c2_basic.1
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)] at hT
  simp only [c2Qs, List.getElem_map, List.getElem_range, List.mem_filter] at hT
  obtain ⟨hTP, hTc⟩ := hT
  obtain ⟨q, hq, hqT⟩ := exists_of_forall₂_left (forall₂_allTables hn (plQ ())) hTP
  rw [List.mem_reverse, mem_enumeration_iff (plQ ()) plQ_valid] at hq
  refine ⟨q, hq, hqT, ?_⟩
  exact mem_of_memT_allTables hn plQ_valid
    (rep_conjT (rep_toTable hn _) (rep_toTable hn _) hqT) hTc

theorem c2Qs_getD_mem {i : ℕ} (hi : i < 8) : (c2Qs ()).getD i [] ∈ c2Qs () := by
  rw [List.getD_eq_getElem _ _ (by rw [c2_basic.1]; exact hi)]
  exact List.getElem_mem _

theorem commT_of_comm {i : ℕ} (hi : i < 8) {c : AE6Om}
    (hc : ∀ q ∈ ae6ModelP, A6.curtisGen ⟨i, hi⟩ * q * (A6.curtisGen ⟨i, hi⟩)⁻¹ ∈ ae6ModelP →
      c * q = q * c) :
    ∀ T ∈ (c2Qs ()).getD i [], commT 360 (toTable (c : Equiv.Perm (Fin 360))) T = true := by
  have hn := degree_lt
  intro T hT
  obtain ⟨q, hq, hqT, hgq⟩ := mem_c2Qs hi hT
  set qA : AE6Om := ⟨q, plQ_le hq⟩
  have hqP : qA ∈ ae6ModelP := le_ae6ModelP qA hq
  have hgqP : A6.curtisGen ⟨i, hi⟩ * qA * (A6.curtisGen ⟨i, hi⟩)⁻¹ ∈ ae6ModelP := by
    refine le_ae6ModelP _ ?_
    have hg : ((A6.curtisGen ⟨i, hi⟩ : AE6Om) : Equiv.Perm (Fin 360)) =
        (curtisPerms ()).getD i 1 := (curtisPerms_getD hi).symm
    simpa [qA, hg] using hgq
  have h1 := congrArg Subtype.val (hc qA hqP hgqP)
  simp only [Subgroup.coe_mul] at h1
  exact (commT_iff_commute (rep_toTable hn _) hqT).mpr h1

theorem rep_c2Qs {i : ℕ} (hi : i < 8) {T : Table} (hT : T ∈ (c2Qs ()).getD i []) :
    Rep 360 T (tablePerm 360 T) := by
  obtain ⟨q, -, hqT, -⟩ := mem_c2Qs hi hT
  rw [tablePerm_eq hqT]
  exact hqT

theorem commT_c2Qs_iff {i : ℕ} (hi : i < 8) {T X : Table} (hT : T ∈ (c2Qs ()).getD i [])
    {x : Equiv.Perm (Fin 360)} (hX : Rep 360 X x) :
    commT 360 X T = true ↔ x * tablePerm 360 T = tablePerm 360 T * x :=
  commT_iff_commute hX (rep_c2Qs hi hT)

theorem mem_c2Ls {i : ℕ} (hi : i < 8) {c : AE6Om}
    (hc : ∀ q ∈ ae6ModelP, A6.curtisGen ⟨i, hi⟩ * q * (A6.curtisGen ⟨i, hi⟩)⁻¹ ∈ ae6ModelP →
      c * q = q * c) :
    ∃ T ∈ (c2Ls ()).getD i [], Rep 360 T (c : Equiv.Perm (Fin 360)) := by
  classical
  have hn := degree_lt
  have hcomm := commT_of_comm hi hc
  obtain ⟨hz, h3⟩ := c2_basic.2.1 _ (c2Qs_getD_mem hi)
  have hcz : (c : Equiv.Perm (Fin 360)) * z0 () = z0 () * c := by
    obtain ⟨T, hT, hTz⟩ := List.any_eq_true.mp hz
    have := hcomm T hT
    rwa [commT_iff_commute (rep_toTable hn _) (rep_of_tblEq' (rep_toTable hn _) hTz)] at this
  have hcC : (c : Equiv.Perm (Fin 360)) ∈ (czQ ()).originalSubgroup := by
    rw [← centralizerIn_z0, mem_centralizerIn]
    exact ⟨c.2, hcz⟩
  have hQ3 : ∀ T ∈ (c2Qs ()).getD 3 [],
      (c : Equiv.Perm (Fin 360)) * tablePerm 360 T = tablePerm 360 T * c := by
    intro T hT
    obtain ⟨T', hT', hTT'⟩ := List.any_eq_true.mp (h3 T hT)
    have hrep := rep_c2Qs hi hT'
    have hrepT : Rep 360 T (tablePerm 360 T') := rep_of_tblEq hrep hTT'
    rw [tablePerm_eq hrepT]
    exact (commT_iff_commute (rep_toTable hn _) hrep).mp (hcomm T' hT')
  have hF := forall₂_filterProducts_levelTables hn (czQ ())
    (f := fun T => ((c2Qs ()).getD 3 []).all fun q => commT 360 T q)
    (P := fun g => ∀ T ∈ (c2Qs ()).getD 3 [], g * tablePerm 360 T = tablePerm 360 T * g)
    (fun T g hTg => by
      rw [List.all_eq_true]
      exact ⟨fun h q hq => (commT_c2Qs_iff (by norm_num) hq hTg).mp (h q hq),
        fun h q hq => (commT_c2Qs_iff (by norm_num) hq hTg).mpr (h q hq)⟩)
  have hmem : (c : Equiv.Perm (Fin 360)) ∈
      ((enumeration (czQ ())).filter fun h =>
        decide (∀ T ∈ (c2Qs ()).getD 3 [], h * tablePerm 360 T = tablePerm 360 T * h)).reverse := by
    rw [List.mem_reverse, List.mem_filter, mem_enumeration_iff (czQ ()) czQ_valid,
      decide_eq_true_iff]
    exact ⟨hcC, hQ3⟩
  obtain ⟨T, hT, hTc⟩ := exists_of_forall₂_right hF hmem
  refine ⟨T, ?_, hTc⟩
  have hlen : (c2Qs ()).length = 8 := c2_basic.1
  have hLs : c2Ls () = (c2Qs ()).map fun Q =>
      (c2L3 ()).filter fun T => Q.all fun q => commT 360 T q := rfl
  have hiQ : i < (c2Qs ()).length := by rw [hlen]; exact hi
  rw [hLs, getD_map_lt _ _ hiQ [] []]
  refine List.mem_filter.mpr ⟨hT, List.all_eq_true.mpr fun q hq' => ?_⟩
  rw [commT_iff_commute hTc (rep_c2Qs hi hq')]
  exact (commT_iff_commute (rep_toTable hn _) (rep_c2Qs hi hq')).mp (hcomm q hq')

theorem c2_search : ∀ cs ∈ List.sections (c2Ls ()),
    ((pWordsC2.map fun w => (w, toTable (aeWord (curtisPerms ()) w))).all (fun wt =>
        tblEq 360 (wordTable (c2HT ((curtisPerms ()).map fun g => (toTable g, toTable g⁻¹)) cs)
          wt.1) wt.2) = true ∧
      (A6.curtisRels.all fun r => tblEq 360 (tableEval (c2HT ((curtisPerms ()).map fun g =>
          (toTable g, toTable g⁻¹)) cs) r) (idT 360)) = true) →
    ((List.range 8).all fun i => tblEq 360 (cs.getD i (idT 360)) (idT 360)) = true ∨
      ((List.range 8).all fun i => tblEq 360 (cs.getD i (idT 360))
        (((List.range 8).map fun i => toTable (((curtisPerms ()).getD i 1)⁻¹ * z0 () *
          (curtisPerms ()).getD i 1 * (z0 ())⁻¹)).getD i (idT 360))) = true := by
  have h : c2Search () = true := Certificates.certificate517506.2
  unfold c2Search at h
  dsimp only at h
  intro cs hcs hok
  have h1 := List.all_eq_true.mp h cs hcs
  rw [hok.1, hok.2, Bool.and_true, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h1
  exact h1

theorem mem_sections_ofFn {L : List (List Table)} (hL : L.length = 8) {T : Fin 8 → Table}
    (hT : ∀ i : Fin 8, T i ∈ L.getD i []) : List.ofFn T ∈ List.sections L := by
  rw [List.mem_sections, List.forall₂_iff_get]
  refine ⟨by rw [List.length_ofFn, hL], fun i h₁ h₂ => ?_⟩
  have hi : i < 8 := by rwa [List.length_ofFn] at h₁
  have := hT ⟨i, hi⟩
  rw [List.getD_eq_getElem _ _ h₂] at this
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_ofFn]
  exact this

theorem length_curtisPerms : (curtisPerms ()).length = 8 := by
  rw [curtisPerms, List.length_map, List.length_range]

theorem ae6C2Search_proved : AE6C2Search := by
  have hn := degree_lt
  have hwords : pWordsC2 = ae6PWords.map fun w => w.map Fin.val := rfl
  refine ⟨fun w hw => ?_, fun c h1 h2 h3 => ?_⟩
  · refine le_ae6ModelP _ ?_
    rw [coe_ae6Word]
    exact mem_of_memT_allTables hn plQ_valid (rep_toTable hn _)
      (c2_words _ (by rw [hwords]; exact List.mem_map_of_mem hw))
  · classical
    have hT : ∀ i : Fin 8, ∃ T ∈ (c2Ls ()).getD i [], Rep 360 T (c i : Equiv.Perm (Fin 360)) :=
      fun i => mem_c2Ls i.2 (h1 i)
    choose T hTL hTr using hT
    have hLlen : (c2Ls ()).length = 8 := by
      rw [show c2Ls () = (c2Qs ()).map fun Q =>
          (c2L3 ()).filter fun T => Q.all fun q => commT 360 T q from rfl, List.length_map,
        c2_basic.1]
    have hcs := mem_sections_ofFn hLlen hTL
    set cs := List.ofFn T with hcsdef
    have hcsget : ∀ i : Fin 8, cs.getD i (idT 360) = T i := fun i => by
      rw [List.getD_eq_getElem _ _ (by rw [hcsdef, List.length_ofFn]; exact i.2),
        List.getElem_ofFn]
    set xs : List (Equiv.Perm (Fin 360)) :=
      List.ofFn fun i => ((A6.curtisGen i * c i : AE6Om) : Equiv.Perm (Fin 360)) with hxs
    have hxsget : ∀ i : Fin 8, xs.getD i 1 = (A6.curtisGen i * c i : AE6Om) := fun i => by
      rw [List.getD_eq_getElem _ _ (by rw [hxs, List.length_ofFn]; exact i.2), List.getElem_ofFn]
    set GT := (curtisPerms ()).map fun g => (toTable g, toTable g⁻¹) with hGTdef
    have hGT : ∀ j, RepPair ((c2HT GT cs).getD j (idT 360, idT 360)) (xs.getD j 1) := by
      intro j
      by_cases hj : j < 8
      · have hGj : GT.getD j (idT 360, idT 360) =
            (toTable ((curtisPerms ()).getD j 1), toTable ((curtisPerms ()).getD j 1)⁻¹) :=
          getD_map_lt _ _ (by rw [length_curtisPerms]; exact hj) _ 1
        have hrange : (List.range 8).getD j 0 = j := by
          rw [List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hj), List.getElem_range]
        rw [c2HT, getD_map_lt _ _ (by rw [List.length_range]; exact hj) _ 0, hrange]
        dsimp only
        rw [hGj, hcsget ⟨j, hj⟩, hxsget ⟨j, hj⟩]
        have hg : ((A6.curtisGen ⟨j, hj⟩ : AE6Om) : Equiv.Perm (Fin 360)) =
            (curtisPerms ()).getD j 1 := (curtisPerms_getD hj).symm
        have hinv : invOK 360 (T ⟨j, hj⟩) (invT 360 (T ⟨j, hj⟩)) = true :=
          c2_basic.2.2 _ (by
            rw [List.getD_eq_getElem _ _ (by rw [hLlen]; exact hj)]
            exact List.getElem_mem _) _ (hTL ⟨j, hj⟩)
        refine ⟨?_, ?_⟩
        · dsimp only
          rw [Subgroup.coe_mul, hg]
          exact Rep.compT (rep_toTable hn _) (hTr ⟨j, hj⟩)
        · dsimp only
          rw [Subgroup.coe_mul, hg, mul_inv_rev]
          exact Rep.compT (Rep.inv_of_invOK (hTr ⟨j, hj⟩) hinv) (rep_toTable hn _)
      · have h1 : (c2HT GT cs).getD j (idT 360, idT 360) = (idT 360, idT 360) := by
          rw [List.getD_eq_default _ _ (by rw [c2HT, List.length_map, List.length_range]; omega)]
        have h2 : xs.getD j 1 = 1 := by
          rw [List.getD_eq_default _ _ (by rw [hxs, List.length_ofFn]; omega)]
        rw [h1, h2]
        exact repPair_one
    have hw : ((pWordsC2.map fun w => (w, toTable (aeWord (curtisPerms ()) w))).all fun wt =>
        tblEq 360 (wordTable (c2HT GT cs) wt.1) wt.2) = true := by
      refine List.all_eq_true.mpr fun wt hwt => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hwt
      rw [hwords] at hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
      dsimp only
      rw [tblEq_iff_eq (rep_wordTable hGT _) (rep_toTable hn _)]
      have h := congrArg Subtype.val (h3 w' hw')
      rw [coe_ae6Word] at h
      rw [← h, List.map_map, ← Subgroup.coe_subtype, map_list_prod, List.map_map]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, Subgroup.coe_subtype]
      exact hxsget i
    have hr : (A6.curtisRels.all fun r => tblEq 360 (tableEval (c2HT GT cs) r) (idT 360)) =
        true := by
      refine List.all_eq_true.mpr fun r hr => ?_
      rw [tblEq_iff_eq (rep_tableEval hGT r) (Rep.idT hn)]
      have h := curtisEval_map' omegaT.subtype (List.ofFn fun i => A6.curtisGen i * c i) r
      rw [h2 r hr, map_one, List.map_ofFn] at h
      exact h
    rcases c2_search cs hcs ⟨hw, hr⟩ with h1 | h1
    · left
      funext i
      have := List.all_eq_true.mp h1 i.val (List.mem_range.mpr i.2)
      rw [hcsget i, tblEq_iff_eq (hTr i) (Rep.idT hn)] at this
      exact Subtype.ext this
    · right
      funext i
      have := List.all_eq_true.mp h1 i.val (List.mem_range.mpr i.2)
      rw [hcsget i, getD_map_lt _ _ (by rw [List.length_range]; exact i.2) _ 0] at this
      have hrange : (List.range 8).getD i.val 0 = i.val := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_range]; exact i.2), List.getElem_range]
      rw [hrange, tblEq_iff_eq (hTr i) (rep_toTable hn _)] at this
      apply Subtype.ext
      rw [this, curtisPerms_getD i.2]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_ae6ModelZ]
      rfl

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
