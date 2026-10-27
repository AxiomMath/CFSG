module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6CertF5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6CertC2
public import Certificates.Certificate517507

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.Certificates CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.EvenSmallLie.OmegaEight Certificates.AE6Model Certificates.S7Twin Certificates.S5Rows
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin

theorem cycWord_val : ∀ m : Fin 12, (ae6CycWord m).map Fin.val = fCycWordN m.val := by
  decide

theorem kWord_val : ∀ s : Fin 3, (ae6KWord s).map Fin.val = fKWordsN.getD s.val [] := by
  decide

theorem twinWord_val : ∀ i : Fin 4, (ae6TwinWord i).map Fin.val = fTwinWordsN.getD i.val [] := by
  decide

theorem cLetter_val : ∀ x : Fin 7, (ae6CLetter x).val = fCLettersN.getD x.val 0 := by
  decide

theorem diag_val : ∀ c : Fin 2, ∀ i : Fin 8,
    (ae6Diag c i).val = (fDiagN.getD c.val []).getD i.val 0 := by
  decide

theorem zWord_diag : ∀ c : Fin 2, (ae6ZWord.map (ae6Diag c)).map Fin.val =
    zWord.map fun i => (fDiagN.getD c.val []).getD i 0 := by
  decide

theorem cycWord_diag : ∀ c : Fin 2, ∀ m : Fin 12, ((ae6CycWord m).map (ae6Diag c)).map Fin.val =
    (fCycWordN m.val).map fun i => (fDiagN.getD c.val []).getD i 0 := by
  decide

theorem wWords_diag : ∀ c : Fin 2, ae6WWords.map (fun w => (w.map (ae6Diag c)).map Fin.val) =
    wWords.map fun w => w.map fun i => (fDiagN.getD c.val []).getD i 0 := by
  decide

theorem curtisPerms_length : (curtisPerms ()).length = 8 := by
  rw [curtisPerms, List.length_map, List.length_range]


theorem tblEq_toTable_iff {x y : Equiv.Perm (Fin 360)} :
    tblEq 360 (toTable x) (toTable y) = true ↔ x = y :=
  tblEq_iff_eq (rep_toTable degree_lt x) (rep_toTable degree_lt y)

theorem f_basic : (∀ w ∈ fKWordsN, aeWord (curtisPerms ()) w * aeWord (curtisPerms ()) w = z0 ()) ∧
    z0 () ≠ 1 ∧ z0 () * z0 () = 1 ∧
    aeWord (curtisPerms ()) (fKWordsN.getD 1 []) * aeWord (curtisPerms ()) (fKWordsN.getD 0 []) *
      (aeWord (curtisPerms ()) (fKWordsN.getD 0 []) *
        aeWord (curtisPerms ()) (fKWordsN.getD 1 [])) = 1 ∧
    ∀ g ∈ curtisPerms (), g * g = 1 := by
  have hn := degree_lt
  have h : fBasic () = true := Certificates.certificate517507.1
  unfold fBasic at h
  dsimp only at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun w hw => (tblEq_iff_eq (Rep.compT (rep_toTable hn _) (rep_toTable hn _))
      (rep_toTable hn _)).mp (h1 w hw), fun h0 => ?_, ?_, ?_, fun g hg => ?_⟩
  · rw [(tblEq_iff_eq (rep_toTable hn _) (Rep.idT hn)).mpr h0] at h2
    exact Bool.noConfusion h2
  · exact (tblEq_iff_eq (Rep.compT (rep_toTable hn _) (rep_toTable hn _)) (Rep.idT hn)).mp h3
  · have := (tblEq_iff_eq (Rep.compT (Rep.compT (rep_toTable hn _) (rep_toTable hn _))
      (Rep.compT (rep_toTable hn _) (rep_toTable hn _))) (Rep.idT hn)).mp h4
    exact this
  · exact (sqOneT_iff hn (rep_toTable hn g)).mp (h5 g hg)

theorem coe_kWord (s : Fin 3) : ((ae6Word (ae6KWord s) : AE6Om) : Equiv.Perm (Fin 360)) =
    aeWord (curtisPerms ()) (fKWordsN.getD s.val []) := by
  rw [coe_ae6Word, kWord_val]

theorem fKWordsN_getD_mem (s : Fin 3) : fKWordsN.getD s.val [] ∈ fKWordsN := by
  rw [List.getD_eq_getElem _ _ (by simp [fKWordsN])]
  exact List.getElem_mem _

theorem f_ksq (s : Fin 3) : ae6Word (ae6KWord s) ^ 2 = ae6ModelZ := by
  apply Subtype.ext
  rw [sq, Subgroup.coe_mul, coe_kWord, coe_ae6ModelZ]
  exact f_basic.1 _ (fKWordsN_getD_mem s)

theorem f_z_ne : ae6ModelZ ≠ 1 := fun h => f_basic.2.1 (by
  rw [← coe_ae6ModelZ, h]
  rfl)

theorem f_zz : ae6ModelZ * ae6ModelZ = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_ae6ModelZ]
  exact f_basic.2.2.1

theorem f_gen_sq (i : Fin 8) : A6.curtisGen i * A6.curtisGen i = 1 := by
  apply Subtype.ext
  have hg : ((A6.curtisGen i : AE6Om) : Equiv.Perm (Fin 360)) = (curtisPerms ()).getD i.val 1 :=
    (curtisPerms_getD i.2).symm
  rw [Subgroup.coe_mul, hg]
  refine f_basic.2.2.2.2 _ ?_
  rw [List.getD_eq_getElem _ _ (by rw [curtisPerms_length]; exact i.2)]
  exact List.getElem_mem _

theorem q8Rel_k01 : Q8Rel (ae6Word (ae6KWord 0)) (ae6Word (ae6KWord 1)) := by
  refine q8Rel_of_coe ?_
  rw [coe_kWord, coe_kWord]
  exact sm_k0.1

theorem ae6ModelK_eq : ae6ModelK =
    Subgroup.closure ({ae6Word (ae6KWord 0), ae6Word (ae6KWord 1)} : Set AE6Om) := rfl

theorem f_K0_elts : ∀ y ∈ ae6ModelK, y = 1 ∨ y = ae6ModelZ ∨
    ∃ s : Fin 3, y = ae6Word (ae6KWord s) ∨ y = (ae6Word (ae6KWord s))⁻¹ := by
  intro y hy
  rw [ae6ModelK_eq, mem_closure_pair_iff q8Rel_k01] at hy
  have h2 : ae6Word (ae6KWord 2) = ae6Word (ae6KWord 0) * ae6Word (ae6KWord 1) := by
    show ((ae6KWord 0 ++ ae6KWord 1).map A6.curtisGen).prod = _
    rw [List.map_append, List.prod_append]
    rfl
  have h10 : ae6Word (ae6KWord 1) * ae6Word (ae6KWord 0) = (ae6Word (ae6KWord 2))⁻¹ := by
    rw [h2, eq_inv_iff_mul_eq_one]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one, coe_kWord]
    exact f_basic.2.2.2.1
  simp only [q8Span, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (f_ksq 0))
  · exact Or.inr (Or.inr ⟨0, Or.inl rfl⟩)
  · exact Or.inr (Or.inr ⟨0, Or.inr rfl⟩)
  · exact Or.inr (Or.inr ⟨1, Or.inl rfl⟩)
  · exact Or.inr (Or.inr ⟨1, Or.inr rfl⟩)
  · exact Or.inr (Or.inr ⟨2, Or.inl h2.symm⟩)
  · exact Or.inr (Or.inr ⟨2, Or.inr h10⟩)

theorem cLetters_mem : ∀ x : Fin 7, (ae6CLetter x).val ∈ czLetters := by
  decide

theorem czLetters_cover : ∀ i ∈ czLetters, ∃ x : Fin 7, (ae6CLetter x).val = i := by
  decide

theorem f_cent : Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) =
    ae6LetterSub (Set.range ae6CLetter) := by
  apply Subgroup.map_injective omegaT.subtype_injective
  have h1 : (Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)).map omegaT.subtype =
      centralizerIn omegaT (z0 ()) := by
    ext x
    rw [Subgroup.mem_map, mem_centralizerIn]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      refine ⟨y.2, ?_⟩
      have := congrArg Subtype.val hy
      simpa [coe_ae6ModelZ] using this
    · rintro ⟨hx, hxz⟩
      exact ⟨⟨x, hx⟩, mem_CZ hx hxz, rfl⟩
  have h2 : (ae6LetterSub (Set.range ae6CLetter)).map omegaT.subtype =
      (czQ ()).originalSubgroup := by
    rw [ae6LetterSub, MonoidHom.map_closure, czQ, certificate_originalSubgroup]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_range, Set.mem_setOf_eq, Subgroup.coe_subtype]
    constructor
    · rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
      have hg : ((A6.curtisGen (ae6CLetter x) : AE6Om) : Equiv.Perm (Fin 360)) =
          (curtisPerms ()).getD (ae6CLetter x).val 1 := (curtisPerms_getD (ae6CLetter x).2).symm
      rw [hg]
      exact List.mem_map.mpr ⟨_, cLetters_mem x, rfl⟩
    · intro hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
      obtain ⟨x, hx⟩ := czLetters_cover i hi
      refine ⟨A6.curtisGen (ae6CLetter x), ⟨ae6CLetter x, ⟨x, rfl⟩, rfl⟩, ?_⟩
      rw [← hx]
      exact (curtisPerms_getD (ae6CLetter x).2).symm
  rw [h1, h2, centralizerIn_z0]

theorem fTwinPairs_getD {i : ℕ} (hi : i < 4) : (fTwinPairs ()).getD i (1, 1) =
    (aeWord (curtisPerms ()) (fTwinWordsN.getD i []) * (k0Gens ()).getD 0 1 *
        (aeWord (curtisPerms ()) (fTwinWordsN.getD i []))⁻¹,
      aeWord (curtisPerms ()) (fTwinWordsN.getD i []) * (k0Gens ()).getD 1 1 *
        (aeWord (curtisPerms ()) (fTwinWordsN.getD i []))⁻¹) := by
  rw [show fTwinPairs () = fTwinWordsN.map fun w =>
      (aeWord (curtisPerms ()) w * (k0Gens ()).getD 0 1 * (aeWord (curtisPerms ()) w)⁻¹,
        aeWord (curtisPerms ()) w * (k0Gens ()).getD 1 1 * (aeWord (curtisPerms ()) w)⁻¹) from rfl,
    getD_map_lt _ _ (by simpa [fTwinWordsN] using hi) _ []]

theorem fTwinPairs_length : (fTwinPairs ()).length = 4 := rfl

theorem mem_twin_iff (i : Fin 4) (y : AE6Om) : y ∈ ae6Twin i ↔ (y : Equiv.Perm (Fin 360)) ∈
    Subgroup.closure ({((fTwinPairs ()).getD i.val (1, 1)).1,
      ((fTwinPairs ()).getD i.val (1, 1)).2} : Set _) := by
  rw [ae6Twin, mem_conjSub_K0_iff, coe_ae6Word, twinWord_val, fTwinPairs_getD i.2]

theorem q8Rel_fTwinPair {i : ℕ} (hi : i < 4) :
    Q8Rel ((fTwinPairs ()).getD i (1, 1)).1 ((fTwinPairs ()).getD i (1, 1)).2 := by
  rw [fTwinPairs_getD hi]
  exact q8Rel_conj sm_k0.1 _

theorem f_twins (x : Fin 7) (i : Fin 4) :
    ∃ j : Fin 4, conjSub (A6.curtisGen (ae6CLetter x)) (ae6Twin i) = ae6Twin j := by
  have hn := degree_lt
  have h : fTwinChecks () = true := Certificates.certificate517507.2.1
  unfold fTwinChecks at h
  dsimp only at h
  have hl : fCLettersN.getD x.val 0 ∈ fCLettersN := by
    rw [List.getD_eq_getElem _ _ (by simp [fCLettersN])]
    exact List.getElem_mem _
  have hp : (fTwinPairs ()).getD i.val (1, 1) ∈ fTwinPairs () := by
    rw [List.getD_eq_getElem _ _ (by rw [fTwinPairs_length]; exact i.2)]
    exact List.getElem_mem _
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h _ hl) _ hp
  obtain ⟨sp, hsp, h2⟩ := List.any_eq_true.mp h1
  rw [Bool.and_eq_true] at h2
  obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hsp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp'
  have hj4 : j < 4 := by rwa [fTwinPairs_length] at hj
  set g := (curtisPerms ()).getD (fCLettersN.getD x.val 0) 1 with hgdef
  have hg : ((A6.curtisGen (ae6CLetter x) : AE6Om) : Equiv.Perm (Fin 360)) = g := by
    rw [hgdef, ← cLetter_val x]
    exact (curtisPerms_getD (ae6CLetter x).2).symm
  have hq := q8Rel_fTwinPair i.2
  have hq' : Q8Rel ((fTwinPairs ())[j]).1 ((fTwinPairs ())[j]).2 := by
    have := q8Rel_fTwinPair hj4
    rwa [List.getD_eq_getElem _ _ hj] at this
  have hrep : ∀ t : Equiv.Perm (Fin 360),
      Rep 360 (conjT 360 (toTable g) (toTable g⁻¹) (toTable t)) (g * t * g⁻¹) := fun t =>
    rep_conjT (rep_toTable hn g) (rep_toTable hn g⁻¹) (rep_toTable hn t)
  have h3 := (memT_spanQ_iff hq' (rep_toTable hn _) (rep_toTable hn _)
    (hrep ((fTwinPairs ()).getD i.val (1, 1)).1)).mp h2.1
  have h4 := (memT_spanQ_iff hq' (rep_toTable hn _) (rep_toTable hn _)
    (hrep ((fTwinPairs ()).getD i.val (1, 1)).2)).mp h2.2
  have hcl := closure_pair_eq_of_mem (q8Rel_conj hq g) hq' h3 h4
  have hcl' : conjSub g (Subgroup.closure ({((fTwinPairs ()).getD i.val (1, 1)).1,
      ((fTwinPairs ()).getD i.val (1, 1)).2} : Set (Equiv.Perm (Fin 360)))) =
      Subgroup.closure ({((fTwinPairs ()).getD j (1, 1)).1,
        ((fTwinPairs ()).getD j (1, 1)).2} : Set (Equiv.Perm (Fin 360))) := by
    rw [CFSG.ClassicalInvolution.Asc77.conjSub_closure_pair, List.getD_eq_getElem _ _ hj]
    exact hcl
  refine ⟨⟨j, hj4⟩, ?_⟩
  ext y
  rw [mem_conjSub_iff, mem_twin_iff, mem_twin_iff]
  dsimp only
  rw [← hcl', mem_conjSub_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg]

theorem fCycs_eq : fCycs () = (List.range 12).map fun m => aeWord (curtisPerms ()) (fCycWordN m) :=
  rfl

theorem fCycs_length : (fCycs ()).length = 12 := by
  rw [fCycs_eq, List.length_map, List.length_range]

theorem fCycs_getD {m : ℕ} (hm : m < 12) :
    (fCycs ()).getD m 1 = aeWord (curtisPerms ()) (fCycWordN m) := by
  rw [fCycs_eq, getD_map_lt _ _ (by rw [List.length_range]; exact hm) _ 0,
    List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hm), List.getElem_range]

theorem coe_cyc (m : Fin 12) : ((ae6Cyc m : AE6Om) : Equiv.Perm (Fin 360)) =
    (fCycs ()).getD m.val 1 := by
  rw [fCycs_getD m.2, ae6Cyc, coe_ae6Word, cycWord_val]

theorem fCycTabs_getD {m : ℕ} (hm : m < 12) : (fCycTabs ()).getD m (idT 360, idT 360) =
    (toTable ((fCycs ()).getD m 1), toTable ((fCycs ()).getD m 1)⁻¹) := by
  rw [show fCycTabs () = (fCycs ()).map fun g => (toTable g, toTable g⁻¹) from rfl,
    getD_map_lt _ _ (by rw [fCycs_length]; exact hm) _ 1]

theorem f_cyc_parts : (∀ m < 12, ∀ n < 12,
    (m = n ∨ (tblEq 360 ((fCycTabs ()).getD m (idT 360, idT 360)).1
        ((fCycTabs ()).getD n (idT 360, idT 360)).1 = false ∧
      tblEq 360 ((fCycTabs ()).getD m (idT 360, idT 360)).1
        ((fCycTabs ()).getD n (idT 360, idT 360)).2 = false)) ∧
    (m / 3 = n / 3 ∨ commT 360 ((fCycTabs ()).getD m (idT 360, idT 360)).1
      ((fCycTabs ()).getD n (idT 360, idT 360)).1 = true) ∧
    (m / 3 ≠ n / 3 ∨ m = n ∨ tblEq 360 (compT 360 (compT 360
      ((fCycTabs ()).getD m (idT 360, idT 360)).1 ((fCycTabs ()).getD n (idT 360, idT 360)).1)
        ((fCycTabs ()).getD m (idT 360, idT 360)).2)
      ((fCycTabs ()).getD n (idT 360, idT 360)).2 = true)) ∧
    ∀ x < 7, ∀ m < 12,
      tblEq 360 (compT 360 (compT 360 (toTable ((curtisPerms ()).getD (fCLettersN.getD x 0) 1))
          ((fCycTabs ()).getD m (idT 360, idT 360)).1)
          (toTable ((curtisPerms ()).getD (fCLettersN.getD x 0) 1)))
        ((fCycTabs ()).getD ((fLetterHat.getD x []).getD m 0) (idT 360, idT 360)).1 = true ∨
      tblEq 360 (compT 360 (compT 360 (toTable ((curtisPerms ()).getD (fCLettersN.getD x 0) 1))
          ((fCycTabs ()).getD m (idT 360, idT 360)).1)
          (toTable ((curtisPerms ()).getD (fCLettersN.getD x 0) 1)))
        ((fCycTabs ()).getD ((fLetterHat.getD x []).getD m 0) (idT 360, idT 360)).2 = true := by
  have h : fCycChecks () = true := Certificates.certificate517507.2.2.1
  unfold fCycChecks at h
  dsimp only at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    Bool.not_eq_true', List.all_eq_true, List.mem_range] at h
  refine ⟨fun m hm n hn => ?_, h.2⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := h.1 m hm n hn
  refine ⟨h1, h2, ?_⟩
  rcases h3 with (h3 | h3) | h3
  · exact Or.inl h3
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h3)

theorem f_cyc_distinct : ∀ m n : Fin 12, m ≠ n →
    ae6Cyc m ≠ ae6Cyc n ∧ ae6Cyc m ≠ (ae6Cyc n)⁻¹ := by
  have hn := degree_lt
  intro m n hmn
  have h := (f_cyc_parts.1 m.val m.2 n.val n.2).1
  rw [fCycTabs_getD m.2, fCycTabs_getD n.2] at h
  dsimp only at h
  rcases h with h | ⟨h1, h2⟩
  · exact absurd (Fin.ext h) hmn
  · constructor
    · intro he
      have := congrArg Subtype.val he
      rw [coe_cyc, coe_cyc] at this
      exact Bool.noConfusion (((tblEq_toTable_iff).mpr this).symm.trans h1)
    · intro he
      have := congrArg Subtype.val he
      rw [Subgroup.coe_inv, coe_cyc, coe_cyc] at this
      exact Bool.noConfusion (((tblEq_toTable_iff).mpr this).symm.trans h2)

theorem f_cyc_comm : ∀ m n : Fin 12, ae6Blk m ≠ ae6Blk n →
    ae6Cyc m * ae6Cyc n = ae6Cyc n * ae6Cyc m := by
  intro m n hmn
  have h := (f_cyc_parts.1 m.val m.2 n.val n.2).2.1
  rw [fCycTabs_getD m.2, fCycTabs_getD n.2] at h
  dsimp only at h
  rcases h with h | h
  · exact absurd (Fin.ext h) hmn
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_cyc, coe_cyc]
    exact (commT_iff_commute (rep_toTable degree_lt _) (rep_toTable degree_lt _)).mp h

theorem f_cyc_inv : ∀ m n : Fin 12, ae6Blk m = ae6Blk n → m ≠ n →
    ae6Cyc m * ae6Cyc n * (ae6Cyc m)⁻¹ = (ae6Cyc n)⁻¹ := by
  have hn := degree_lt
  intro m n hb hmn
  have h := (f_cyc_parts.1 m.val m.2 n.val n.2).2.2
  rw [fCycTabs_getD m.2, fCycTabs_getD n.2] at h
  dsimp only at h
  rcases h with h | h | h
  · exact absurd (congrArg Fin.val hb) h
  · exact absurd (Fin.ext h) hmn
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, coe_cyc, coe_cyc]
    exact (tblEq_iff_eq (Rep.compT (Rep.compT (rep_toTable hn _) (rep_toTable hn _))
      (rep_toTable hn _)) (rep_toTable hn _)).mp h

theorem f_cyc_letter : ∀ (x : Fin 7) (n : Fin 12),
    A6.curtisGen (ae6CLetter x) * ae6Cyc n * A6.curtisGen (ae6CLetter x) =
        ae6Cyc (ae6LetterHat x n) ∨
      A6.curtisGen (ae6CLetter x) * ae6Cyc n * A6.curtisGen (ae6CLetter x) =
        (ae6Cyc (ae6LetterHat x n))⁻¹ := by
  have hn := degree_lt
  intro x n
  have h := f_cyc_parts.2 x.val x.2 n.val n.2
  have hidx : (fLetterHat.getD x.val []).getD n.val 0 = (ae6LetterHat x n).val :=
    (fLetterHat_spec x).2 n
  rw [hidx, fCycTabs_getD n.2, fCycTabs_getD (ae6LetterHat x n).2] at h
  dsimp only at h
  have hg : ((A6.curtisGen (ae6CLetter x) : AE6Om) : Equiv.Perm (Fin 360)) =
      (curtisPerms ()).getD (fCLettersN.getD x.val 0) 1 := by
    rw [← cLetter_val x]
    exact (curtisPerms_getD (ae6CLetter x).2).symm
  have hrep := Rep.compT (Rep.compT
    (rep_toTable hn ((curtisPerms ()).getD (fCLettersN.getD x.val 0) 1))
    (rep_toTable hn ((fCycs ()).getD n.val 1)))
    (rep_toTable hn ((curtisPerms ()).getD (fCLettersN.getD x.val 0) 1))
  rcases h with h | h
  · left
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hg, coe_cyc, coe_cyc]
    exact (tblEq_iff_eq hrep (rep_toTable hn _)).mp h
  · right
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg, coe_cyc, coe_cyc]
    exact (tblEq_iff_eq hrep (rep_toTable hn _)).mp h

theorem f_diag_parts (c : Fin 2) :
    ((∀ x ∈ A6.curtisRels, tblEq 360 (tableEval ((List.range 8).map fun i =>
        (toTable ((curtisPerms ()).getD ((fDiagN.getD c.val []).getD i 0) 1),
          toTable ((curtisPerms ()).getD ((fDiagN.getD c.val []).getD i 0) 1)⁻¹)) x)
        (idT 360) = true) ∧
      tblEq 360 (diagWordTable (curtisPerms ()) (fDiagN.getD c.val []) zWord)
        (toTable (z0 ())) = true) ∧
    (∀ x < 12,
      tblEq 360 (diagWordTable (curtisPerms ()) (fDiagN.getD c.val []) (fCycWordN x))
        ((fCycTabs ()).getD ((fGammaHat.getD c.val []).getD x 0) (idT 360, idT 360)).1 = true ∨
      tblEq 360 (diagWordTable (curtisPerms ()) (fDiagN.getD c.val []) (fCycWordN x))
        ((fCycTabs ()).getD ((fGammaHat.getD c.val []).getD x 0) (idT 360, idT 360)).2 = true) ∧
    ∀ x ∈ wWords, memT 360 (allTables (wQ ()))
      (diagWordTable (curtisPerms ()) (fDiagN.getD c.val []) x) = true := by
  have h : fDiagChecks () = true := Certificates.certificate517507.2.2.2
  unfold fDiagChecks at h
  dsimp only at h
  have hc := List.all_eq_true.mp h c.val (List.mem_range.mpr c.2)
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem f_diag_rels (c : Fin 2) :
    ∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn fun i => A6.curtisGen (ae6Diag c i)) r = 1 := by
  intro r hr
  have hrep : ∀ j, RepPair (((List.range 8).map fun i =>
      (toTable ((curtisPerms ()).getD ((fDiagN.getD c.val []).getD i 0) 1),
        toTable ((curtisPerms ()).getD ((fDiagN.getD c.val []).getD i 0) 1)⁻¹)).getD j
        (idT 360, idT 360))
      (((List.ofFn fun i => A6.curtisGen (ae6Diag c i)).map omegaT.subtype).getD j 1) := by
    intro j
    by_cases hj : j < 8
    · rw [getD_map_lt _ _ (by rw [List.length_range]; exact hj) _ 0,
        List.getD_eq_getElem (List.range 8) 0 (by rw [List.length_range]; exact hj),
        List.getElem_range, getD_map_lt _ _ (by rw [List.length_ofFn]; exact hj) _ 1,
        List.getD_eq_getElem (List.ofFn fun i => A6.curtisGen (ae6Diag c i)) 1
          (by rw [List.length_ofFn]; exact hj), List.getElem_ofFn]
      have hg : omegaT.subtype (A6.curtisGen (ae6Diag c ⟨j, hj⟩)) =
          (curtisPerms ()).getD ((fDiagN.getD c.val []).getD j 0) 1 := by
        rw [show (fDiagN.getD c.val []).getD j 0 = (ae6Diag c ⟨j, hj⟩).val from
          (diag_val c ⟨j, hj⟩).symm]
        exact (curtisPerms_getD (ae6Diag c ⟨j, hj⟩).2).symm
      rw [hg]
      unfold RepPair
      dsimp only
      exact ⟨rep_toTable degree_lt _, rep_toTable degree_lt _⟩
    · rw [List.getD_eq_default _ _ (by rw [List.length_map, List.length_range]; omega),
        List.getD_eq_default _ _ (by rw [List.length_map, List.length_ofFn]; omega)]
      exact repPair_one
  have h := (tblEq_iff_eq (rep_tableEval hrep r) (Rep.idT degree_lt)).mp
    ((f_diag_parts c).1.1 r hr)
  rw [curtisEval_map'] at h
  exact omegaT.subtype_injective (h.trans (map_one omegaT.subtype).symm)

theorem f_diag_z (c : Fin 2) : ae6Word (ae6ZWord.map (ae6Diag c)) = ae6ModelZ := by
  have h := (f_diag_parts c).1.2
  unfold diagWordTable at h
  apply Subtype.ext
  rw [coe_ae6Word, zWord_diag, coe_ae6ModelZ]
  exact tblEq_toTable_iff.mp h

theorem f_diag_cyc (c : Fin 2) (n : Fin 12) :
    ae6Word ((ae6CycWord n).map (ae6Diag c)) = ae6Cyc (ae6GammaHat c n) ∨
      ae6Word ((ae6CycWord n).map (ae6Diag c)) = (ae6Cyc (ae6GammaHat c n))⁻¹ := by
  have h := (f_diag_parts c).2.1 n.val n.2
  rw [(fGammaHat_spec c).2 n, fCycTabs_getD (ae6GammaHat c n).2] at h
  dsimp only at h
  unfold diagWordTable at h
  have hw : ((ae6Word ((ae6CycWord n).map (ae6Diag c)) : AE6Om) : Equiv.Perm (Fin 360)) =
      aeWord (curtisPerms ()) ((fCycWordN n.val).map fun i => (fDiagN.getD c.val []).getD i 0) := by
    rw [coe_ae6Word, cycWord_diag]
  rcases h with h | h
  · left
    apply Subtype.ext
    rw [hw, coe_cyc]
    exact tblEq_toTable_iff.mp h
  · right
    apply Subtype.ext
    rw [hw, Subgroup.coe_inv, coe_cyc]
    exact tblEq_toTable_iff.mp h

theorem map_ae6ModelW : ae6ModelW.map omegaT.subtype = (wQ ()).originalSubgroup := by
  rw [wQ, certificate_originalSubgroup, ae6ModelW, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    w0Gens, wWords, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> rw [coe_ae6Word] <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨_, Or.inl rfl, by rw [coe_ae6Word]; rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), by rw [coe_ae6Word]; rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), by rw [coe_ae6Word]; rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by rw [coe_ae6Word]; rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr rfl))), by rw [coe_ae6Word]; rfl⟩

theorem f_diag_W (c : Fin 2) : ∀ w ∈ ae6WWords, ae6Word (w.map (ae6Diag c)) ∈ ae6ModelW := by
  intro w hw
  have hw' : (w.map (ae6Diag c)).map Fin.val ∈
      wWords.map fun w => w.map fun i => (fDiagN.getD c.val []).getD i 0 := by
    rw [← wWords_diag c]
    exact List.mem_map.mpr ⟨w, hw, rfl⟩
  obtain ⟨w', hw'', he⟩ := List.mem_map.mp hw'
  have h := (f_diag_parts c).2.2 w' hw''
  unfold diagWordTable at h
  rw [he] at h
  have hm := mem_of_memT_allTables degree_lt wQ_valid (rep_toTable degree_lt _) h
  rw [← coe_ae6Word, ← map_ae6ModelW] at hm
  exact (Subgroup.mem_map_iff_mem omegaT.subtype_injective).mp hm

theorem f_diag (c : Fin 2) :
    (∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn fun i => A6.curtisGen (ae6Diag c i)) r = 1) ∧
      ae6Word (ae6ZWord.map (ae6Diag c)) = ae6ModelZ ∧
      (∀ n : Fin 12, ae6Word ((ae6CycWord n).map (ae6Diag c)) = ae6Cyc (ae6GammaHat c n) ∨
        ae6Word ((ae6CycWord n).map (ae6Diag c)) = (ae6Cyc (ae6GammaHat c n))⁻¹) ∧
      ∀ w ∈ ae6WWords, ae6Word (w.map (ae6Diag c)) ∈ ae6ModelW :=
  ⟨f_diag_rels c, f_diag_z c, f_diag_cyc c, f_diag_W c⟩

theorem ae6FFin_proved : AE6FFin := by
  unfold AE6FFin
  exact ⟨f_cent, f_K0_elts, f_ksq, f_z_ne, f_zz, f_gen_sq, f_twins, f_cyc_distinct, f_cyc_comm,
    f_cyc_inv, f_cyc_letter, f_diag, ae6F5_holds⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
