module

public import CFSG.Certificates.Kernel.SporLatDcLabels

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

namespace DcSoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

variable (P : DcSoundCtx Γ n)

private theorem letters_append {k π : List ℕ} (hk : ∀ l ∈ k, l < 2 + P.C.ns)
    (hπ : ∀ l ∈ π, l < 2 + P.C.ns) : ∀ l ∈ k ++ π, l < 2 + P.C.ns := by
  intro l hl
  rw [List.mem_append] at hl
  rcases hl with h | h
  · exact hk l h
  · exact hπ l h

private theorem labF_map_eq_lab {x : List ℕ} (hx : ∀ p ∈ x, p < n) {k π : List ℕ}
    (hk : ∀ l ∈ k, l < 2 + P.C.ns) (hπ : ∀ l ∈ π, l < 2 + P.C.ns) :
    labF (wordF P.C.L k) (x.map (wordF P.C.L π)) =
      lab n ptLab x (evalElt P.els (k ++ π)) := by
  have h1 : lab n ptLab x (evalElt P.els (k ++ π)) =
      sortN (x.map fun p => act n (evalElt P.els (k ++ π)) p) := ptAct_tab _ _
  rw [h1, labF, List.map_map, ← CFSG.KC.E64F.sortN_eq]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [Function.comp_apply]
  have hA : act n (evalElt P.els (k ++ π)) p = wordF P.C.L (k ++ π) p :=
    P.act_wordF_eq (letters_append P hk hπ) (hx p hp)
  rw [hA, P.wordF_append]

private theorem mem_fold_union (extra : ℕ → Finset (List ℕ)) :
    ∀ (l : List ℕ) (U : Finset (List ℕ)) (M : List ℕ),
      M ∈ l.foldl (fun U q => U ∪ extra q) U ↔ M ∈ U ∨ ∃ q ∈ l, M ∈ extra q
  | [], U, M => by simp
  | a :: l, U, M => by
    rw [List.foldl_cons, mem_fold_union extra l (U ∪ extra a) M]
    constructor
    · rintro (h | h)
      · rcases Finset.mem_union.mp h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨a, List.mem_cons_self .., h⟩
      · obtain ⟨q, hq, hM⟩ := h
        exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hM⟩
    · rintro (h | ⟨q, hq, hM⟩)
      · exact Or.inl (Finset.mem_union_left _ h)
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inl (Finset.mem_union_right _ hM)
        · exact Or.inr ⟨q, hq, hM⟩

private noncomputable def imgsExtra (x : List ℕ) (j q : ℕ) : Finset (List ℕ) :=
  if Nat.beq (oid P.D q) j then
    (P.D.K.getD j []).toFinset.image
      (fun k => labF (wordF P.C.L k) (x.map (wordF P.C.L (pathW P.C P.D 64 q []))))
  else ∅

private theorem mem_imgsExtra {x : List ℕ} {j q : ℕ} {M : List ℕ} :
    M ∈ P.imgsExtra x j q ↔ oid P.D q = j ∧
      ∃ k ∈ P.D.K.getD j [],
        M = labF (wordF P.C.L k) (x.map (wordF P.C.L (pathW P.C P.D 64 q []))) := by
  unfold imgsExtra
  by_cases h : Nat.beq (oid P.D q) j = true
  · rw [if_pos h]
    have ho : oid P.D q = j := by rwa [Nat.beq_eq] at h
    constructor
    · intro hM
      rw [Finset.mem_image] at hM
      obtain ⟨k, hk, hkM⟩ := hM
      exact ⟨ho, k, by rwa [List.mem_toFinset] at hk, hkM.symm⟩
    · rintro ⟨-, k, hk, rfl⟩
      rw [Finset.mem_image]
      exact ⟨k, by rwa [List.mem_toFinset], rfl⟩
  · rw [if_neg h]
    constructor
    · intro hM
      exact absurd hM (by simp)
    · rintro ⟨h1, -⟩
      rw [← Nat.beq_eq] at h1
      exact absurd h1 h

noncomputable def imgsF (x : List ℕ) (j : ℕ) : Finset (List ℕ) :=
  x.foldl (fun U q => U ∪ P.imgsExtra x j q) ∅

omit [Finite Γ] in
private theorem lab_lab' {x : List ℕ} (hx : ∀ p ∈ x, p < n) (g h : Γ) :
    lab n ptLab (lab n ptLab x h) g = lab n ptLab x (g * h) := by
  have e : ∀ (L : List ℕ) (g : Γ), lab n ptLab L g = sortN (L.map fun p => act n g p) :=
    fun L g => ptAct_tab _ _
  simp only [e, sortN_map_sortN, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  exact (act_mul _ _ (hx p hp)).symm

private theorem pathsOK_spec' {x : List ℕ} {j : ℕ} (h : pathsOK P.C P.D x j = true) {q : ℕ}
    (hq : q ∈ x) (ho : oid P.D q = j) : isS P.C (pathW P.C P.D 64 q []) = true := by
  have h1 := (List.all_eq_true.mp h) q hq
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · have h2 : Nat.beq (oid P.D q) j = false := by simpa using h1
    rw [ho, Nat.beq_refl] at h2
    exact absurd h2 (by simp)
  · rw [Bool.and_eq_true] at h1
    exact h1.1

private theorem extra_sub {x : List ℕ} (hx : ∀ p ∈ x, p < n) {j : ℕ}
    (hj : j < P.D.obase.length) (h0 : 0 < (P.D.K.getD j []).length)
    (hpaths : pathsOK P.C P.D x j = true) {q q' : ℕ} (hq : q ∈ x) (hq' : q' ∈ x) {M : List ℕ}
    (hM : M ∈ P.imgsExtra x j q) (hM' : M ∈ P.imgsExtra x j q') :
    P.imgsExtra x j q ⊆ P.imgsExtra x j q' := by
  intro N hN
  rw [mem_imgsExtra] at hM hM' hN
  obtain ⟨ho, k1, hk1, rfl⟩ := hM
  obtain ⟨ho', k2, hk2, he⟩ := hM'
  obtain ⟨-, k, hk, rfl⟩ := hN
  have his := pathsOK_spec' P hpaths hq ho
  have his' := pathsOK_spec' P hpaths hq' ho'
  have hK : ∀ {k}, k ∈ P.D.K.getD j [] → ∀ l ∈ k, l < 2 + P.C.ns :=
    fun hk => isS_lt P (K_isS P hj hk)
  have hb := obase_lt P hj
  have hfix : ∀ {k}, k ∈ P.D.K.getD j [] →
      act n (evalElt P.els k) (P.D.obase.getD j 0) = P.D.obase.getD j 0 := fun hk => by
    rw [P.act_wordF_eq (hK hk) hb, K_fixes_word P hj hk]
  have hmem : ∀ {k}, k ∈ P.D.K.getD j [] → evalElt P.els k ∈ P.S :=
    fun hk => evalElt_mem_S P (isS_spec P (K_isS P hj hk))
  rw [labF_map_eq_lab P hx (hK hk1) (isS_lt P his),
    labF_map_eq_lab P hx (hK hk2) (isS_lt P his'), evalElt_append, evalElt_append] at he
  have hinv : act n (evalElt P.els k1)⁻¹ (P.D.obase.getD j 0) = P.D.obase.getD j 0 := by
    have e := act_mul (evalElt P.els k1)⁻¹ (evalElt P.els k1) hb
    rw [inv_mul_cancel, act_one hb, hfix hk1] at e
    exact e.symm
  have hgS : evalElt P.els k * (evalElt P.els k1)⁻¹ * evalElt P.els k2 ∈ P.S :=
    P.S.mul_mem (P.S.mul_mem (hmem hk) (P.S.inv_mem (hmem hk1))) (hmem hk2)
  have hgfix : act n (evalElt P.els k * (evalElt P.els k1)⁻¹ * evalElt P.els k2)
      (P.D.obase.getD j 0) = P.D.obase.getD j 0 := by
    rw [act_mul _ _ hb, hfix hk2, act_mul _ _ hb, hinv, hfix hk]
  obtain ⟨k3, hk3, hk3e⟩ := K_enum P hj h0 hgS hgfix
  rw [mem_imgsExtra]
  refine ⟨ho', k3, hk3, ?_⟩
  rw [labF_map_eq_lab P hx (hK hk) (isS_lt P his), labF_map_eq_lab P hx (hK hk3) (isS_lt P his'),
    evalElt_append, evalElt_append, hk3e]
  have e1 : evalElt P.els k * evalElt P.els (pathW P.C P.D 64 q []) =
      (evalElt P.els k * (evalElt P.els k1)⁻¹) *
        (evalElt P.els k1 * evalElt P.els (pathW P.C P.D 64 q [])) := by group
  have e2 : evalElt P.els k * (evalElt P.els k1)⁻¹ * evalElt P.els k2 *
        evalElt P.els (pathW P.C P.D 64 q' []) =
      (evalElt P.els k * (evalElt P.els k1)⁻¹) *
        (evalElt P.els k2 * evalElt P.els (pathW P.C P.D 64 q' [])) := by group
  rw [e1, e2, ← lab_lab' hx _ (evalElt P.els k1 * evalElt P.els (pathW P.C P.D 64 q [])),
    ← lab_lab' hx _ (evalElt P.els k2 * evalElt P.els (pathW P.C P.D 64 q' [])), he]

private theorem anyB_beq_mem {t : List ℕ} :
    ∀ {U : List (List ℕ)}, anyB (fun M => M == t) U = true → t ∈ U
  | [], h => absurd h (by simp [anyB])
  | a :: U, h => by
    rw [anyB, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [beq_iff_eq] at h
      rw [← h]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (anyB_beq_mem h)

private def ExtraInv (x : List ℕ) (j : ℕ) (F : Finset (List ℕ)) : Prop :=
  ∀ M ∈ F, ∃ q' ∈ x, M ∈ P.imgsExtra x j q' ∧ P.imgsExtra x j q' ⊆ F

private theorem step_toFinset {x : List ℕ} (hx : ∀ p ∈ x, p < n) {j : ℕ}
    (hj : j < P.D.obase.length) (h0 : 0 < (P.D.K.getD j []).length)
    (hpaths : pathsOK P.C P.D x j = true) {q : ℕ} (hq : q ∈ x) {U : List (List ℕ)}
    (hU : P.ExtraInv x j U.toFinset) :
    (bif Nat.beq (oid P.D q) j then
        insKs P.C (P.D.K.getD j []) (x.map (wordF P.C.L (pathW P.C P.D 64 q []))) U
      else U).toFinset = U.toFinset ∪ P.imgsExtra x j q := by
  cases h : Nat.beq (oid P.D q) j with
  | false =>
    rw [Bool.cond_false, imgsExtra, if_neg (by rw [h]; exact Bool.false_ne_true),
      Finset.union_empty]
  | true =>
    rw [Bool.cond_true, insKs]
    cases ha : anyB (fun M => M == labF (wordF P.C.L (headL (P.D.K.getD j [])))
        (x.map (wordF P.C.L (pathW P.C P.D 64 q [])))) U with
    | false => rw [Bool.cond_false, insK_toFinset, imgsExtra, if_pos h]
    | true =>
      rw [Bool.cond_true]
      have ht := List.mem_toFinset.mpr (anyB_beq_mem ha)
      obtain ⟨q', hq', hM', hsub⟩ := hU _ ht
      have hM : labF (wordF P.C.L (headL (P.D.K.getD j [])))
          (x.map (wordF P.C.L (pathW P.C P.D 64 q []))) ∈ P.imgsExtra x j q := by
        rw [mem_imgsExtra]
        refine ⟨by rwa [Nat.beq_eq] at h, headL (P.D.K.getD j []), ?_, rfl⟩
        obtain ⟨k0, ks, hks⟩ := List.exists_cons_of_length_pos h0
        rw [hks]
        exact List.mem_cons_self ..
      exact (Finset.union_eq_left.mpr
        ((extra_sub P hx hj h0 hpaths hq hq' hM hM').trans hsub)).symm

private theorem fold_imgs {x : List ℕ} (hx : ∀ p ∈ x, p < n) {j : ℕ}
    (hj : j < P.D.obase.length) (h0 : 0 < (P.D.K.getD j []).length)
    (hpaths : pathsOK P.C P.D x j = true) :
    ∀ (l : List ℕ), (∀ q ∈ l, q ∈ x) → ∀ (U : List (List ℕ)), P.ExtraInv x j U.toFinset →
      (l.foldl (fun U q => bif Nat.beq (oid P.D q) j then
          insKs P.C (P.D.K.getD j []) (x.map (wordF P.C.L (pathW P.C P.D 64 q []))) U
        else U) U).toFinset = l.foldl (fun U q => U ∪ P.imgsExtra x j q) U.toFinset
  | [], _, U, _ => rfl
  | a :: l, hl, U, hU => by
    rw [List.foldl_cons, List.foldl_cons]
    have ha : a ∈ x := hl a List.mem_cons_self
    have e := step_toFinset P hx hj h0 hpaths ha hU
    rw [fold_imgs hx hj h0 hpaths l (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ ?_, e]
    rw [e]
    unfold ExtraInv
    intro M hM
    rcases Finset.mem_union.mp hM with hM | hM
    · obtain ⟨q', hq', h1, h2⟩ := hU M hM
      exact ⟨q', hq', h1, h2.trans Finset.subset_union_left⟩
    · exact ⟨a, ha, hM, Finset.subset_union_right⟩

theorem imgs_toFinset {x : List ℕ} {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) (hx : ∀ p ∈ x, p < n)
    (hpaths : pathsOK P.C P.D x j = true) :
    (imgs P.C P.D x j).toFinset = P.imgsF x j :=
  fold_imgs P hx hj h0 hpaths x (fun _ hq => hq) [] (by
    unfold ExtraInv
    intro M hM
    simp at hM)

private theorem mem_imgsF {x : List ℕ} {j : ℕ} {M : List ℕ} :
    M ∈ P.imgsF x j ↔ ∃ q ∈ x, oid P.D q = j ∧
      ∃ k ∈ P.D.K.getD j [],
        M = labF (wordF P.C.L k) (x.map (wordF P.C.L (pathW P.C P.D 64 q []))) := by
  rw [imgsF, mem_fold_union]
  constructor
  · rintro (h | ⟨q, hq, hM⟩)
    · exact absurd h (by simp)
    · exact ⟨q, hq, (mem_imgsExtra P).mp hM⟩
  · rintro ⟨q, hq, ho, k, hk, rfl⟩
    exact Or.inr ⟨q, hq, (mem_imgsExtra P).mpr ⟨ho, k, hk, rfl⟩⟩

private theorem sortedLt_fold_imgs (x : List ℕ) (j : ℕ) :
    ∀ (l : List ℕ) (U : List (List ℕ)), sortedLt U = true →
      sortedLt (l.foldl (fun U q => bif Nat.beq (oid P.D q) j then
        insKs P.C (P.D.K.getD j []) (x.map (wordF P.C.L (pathW P.C P.D 64 q []))) U else U) U) = true
  | [], U, hU => hU
  | a :: l, U, hU => by
    rw [List.foldl_cons]
    cases h : Nat.beq (oid P.D a) j with
    | true =>
      rw [cond_true, insKs]
      cases anyB (fun M => M == labF (wordF P.C.L (headL (P.D.K.getD j [])))
          (x.map (wordF P.C.L (pathW P.C P.D 64 a [])))) U with
      | true => exact sortedLt_fold_imgs x j l U hU
      | false => exact sortedLt_fold_imgs x j l _ (sortedLt_insK P.C _ _ U hU)
    | false =>
      rw [cond_false]
      exact sortedLt_fold_imgs x j l U hU

theorem imgs_sortedLt (x : List ℕ) (j : ℕ) :
    sortedLt (imgs P.C P.D x j) = true :=
  sortedLt_fold_imgs P x j x [] rfl

private theorem imgs_nodup (x : List ℕ) (j : ℕ) : (imgs P.C P.D x j).Nodup :=
  sortedLt_nodup (imgs_sortedLt P x j)

private theorem pathsOK_spec {x : List ℕ} {j : ℕ} (h : pathsOK P.C P.D x j = true) {q : ℕ}
    (hq : q ∈ x) (ho : oid P.D q = j) :
    isS P.C (pathW P.C P.D 64 q []) = true ∧
      wordF P.C.L (pathW P.C P.D 64 q []) q = P.D.obase.getD j 0 := by
  have h1 := (List.all_eq_true.mp h) q hq
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · have h2 : Nat.beq (oid P.D q) j = false := by simpa using h1
    rw [ho, Nat.beq_refl] at h2
    exact absurd h2 (by simp)
  · rw [Bool.and_eq_true, Nat.beq_eq] at h1
    exact h1

private theorem act_pathW {x : List ℕ} (hx : ∀ p ∈ x, p < n) {j : ℕ}
    (h : pathsOK P.C P.D x j = true) {q : ℕ} (hq : q ∈ x) (ho : oid P.D q = j) :
    act n (evalElt P.els (pathW P.C P.D 64 q [])) q = P.D.obase.getD j 0 := by
  obtain ⟨his, hw⟩ := pathsOK_spec P h hq ho
  rw [P.act_wordF_eq (isS_lt P his) (hx q hq)]
  exact hw

private theorem isS_append {k π : List ℕ} (hk : isS P.C k = true) (hπ : isS P.C π = true) :
    isS P.C (k ++ π) = true := by
  unfold isS at *
  rw [List.all_append, Bool.and_eq_true]
  exact ⟨hk, hπ⟩

private theorem imgs_subset {x : List ℕ} {j : ℕ} (hj : j < P.D.obase.length)
    (hx : ∀ p ∈ x, p < n) (hpaths : pathsOK P.C P.D x j = true) :
    P.imgsF x j ⊆ (P.Sx x).filter (fun M => P.D.obase.getD j 0 ∈ M) := by
  intro M hM
  rw [mem_imgsF] at hM
  obtain ⟨q, hq, ho, k, hk, rfl⟩ := hM
  obtain ⟨his, hw⟩ := pathsOK_spec P hpaths hq ho
  have hkis : isS P.C k = true := K_isS P hj hk
  have hlab := labF_map_eq_lab P hx (isS_lt P hkis) (isS_lt P his)
  rw [Finset.mem_filter, hlab]
  constructor
  · rw [mem_Sx]
    exact ⟨_, evalElt_mem_S P (isS_spec P (isS_append P hkis his)), rfl⟩
  · rw [← List.mem_toFinset, lab_toFinset, Finset.mem_image]
    refine ⟨q, by rwa [List.mem_toFinset], ?_⟩
    rw [evalElt_append, act_mul _ _ (hx q hq), P.act_wordF_eq (isS_lt P his) (hx q hq), hw,
      P.act_wordF_eq (isS_lt P hkis) (obase_lt P hj), K_fixes_word P hj hk]

private theorem filter_subset_imgs {x : List ℕ} {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) (hx : ∀ p ∈ x, p < n)
    (hpaths : pathsOK P.C P.D x j = true) :
    (P.Sx x).filter (fun M => P.D.obase.getD j 0 ∈ M) ⊆ P.imgsF x j := by
  intro M hM
  rw [Finset.mem_filter, mem_Sx] at hM
  obtain ⟨⟨s, hs, rfl⟩, hbase⟩ := hM
  rw [← List.mem_toFinset, lab_toFinset, Finset.mem_image] at hbase
  obtain ⟨q, hq, hq'⟩ := hbase
  rw [List.mem_toFinset] at hq
  have hoq : oid P.D q = j := by
    have h1 := P.oid_inv hs (hx q hq)
    rw [hq', obase_oid P hj] at h1
    exact h1.symm
  obtain ⟨his, hw⟩ := pathsOK_spec P hpaths hq hoq
  have hgS : evalElt P.els (pathW P.C P.D 64 q []) ∈ P.S := evalElt_mem_S P (isS_spec P his)
  have hgfix : act n (evalElt P.els (pathW P.C P.D 64 q []))⁻¹ (P.D.obase.getD j 0) = q := by
    refine act_inj (g := evalElt P.els (pathW P.C P.D 64 q []))
      (act_lt _ (obase_lt P hj)) (hx q hq) ?_
    rw [← act_mul _ _ (obase_lt P hj), mul_inv_cancel, act_one (obase_lt P hj),
      P.act_wordF_eq (isS_lt P his) (hx q hq), hw]
  have hs'S : s * (evalElt P.els (pathW P.C P.D 64 q []))⁻¹ ∈ P.S :=
    P.S.mul_mem hs (P.S.inv_mem hgS)
  have hs'fix : act n (s * (evalElt P.els (pathW P.C P.D 64 q []))⁻¹) (P.D.obase.getD j 0) =
      P.D.obase.getD j 0 := by
    rw [act_mul _ _ (obase_lt P hj), hgfix, hq']
  obtain ⟨k, hk, hke⟩ := K_enum P hj h0 hs'S hs'fix
  refine (mem_imgsF P).mpr ⟨q, hq, hoq, k, hk, ?_⟩
  rw [labF_map_eq_lab P hx (isS_lt P (K_isS P hj hk)) (isS_lt P his)]
  have hseq : s = evalElt P.els k * evalElt P.els (pathW P.C P.D 64 q []) := by
    rw [hke]
    group
  rw [hseq, evalElt_append]

theorem imgsF_eq_filter {x : List ℕ} {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) (hx : ∀ p ∈ x, p < n)
    (hpaths : pathsOK P.C P.D x j = true) :
    P.imgsF x j = (P.Sx x).filter (fun M => P.D.obase.getD j 0 ∈ M) :=
  Finset.Subset.antisymm (imgs_subset P hj hx hpaths) (filter_subset_imgs P hj h0 hx hpaths)

theorem imgs_length {x : List ℕ} {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) (hx : ∀ p ∈ x, p < n)
    (hpaths : pathsOK P.C P.D x j = true) :
    (imgs P.C P.D x j).length = ((P.Sx x).filter (fun M => P.D.obase.getD j 0 ∈ M)).card := by
  rw [← List.toFinset_card_of_nodup (imgs_nodup P x j), imgs_toFinset P hj h0 hx hpaths,
    imgsF_eq_filter P hj h0 hx hpaths]

private theorem anyB_false_not_mem {t : List ℕ} :
    ∀ {U : List (List ℕ)}, anyB (fun M => M == t) U = false → t ∉ U
  | [], _ => by simp
  | a :: U, h => by
    rw [anyB, Bool.or_eq_false_iff] at h
    intro hm
    rcases List.mem_cons.mp hm with he | hm
    · subst he
      simp at h
    · exact anyB_false_not_mem h.2 hm

private theorem pushG_spec (gs : List (List ℕ)) (M : List ℕ) :
    ∀ (T V : List (List ℕ)), sortedLt V = true →
      sortedLt (pushG P.C gs M (T, V)).2 = true ∧
      (pushG P.C gs M (T, V)).2.toFinset =
        V.toFinset ∪ (gs.map fun g => labF (wordF P.C.L g) M).toFinset ∧
      (∀ N ∈ T, N ∈ (pushG P.C gs M (T, V)).1) ∧
      (∀ N ∈ (pushG P.C gs M (T, V)).1, N ∈ T ∨ ∃ g ∈ gs, N = labF (wordF P.C.L g) M) ∧
      (∀ N ∈ (pushG P.C gs M (T, V)).2, N ∈ V ∨ N ∈ (pushG P.C gs M (T, V)).1) ∧
      (pushG P.C gs M (T, V)).1.length + V.toFinset.card =
        T.length + (pushG P.C gs M (T, V)).2.toFinset.card := by
  induction gs with
  | nil =>
    intro T V hV
    refine ⟨hV, by simp [pushG], fun N hN => hN, fun N hN => Or.inl hN, fun N hN => Or.inl hN,
      rfl⟩
  | cons g gs ih =>
    intro T V hV
    have e : pushG P.C (g :: gs) M (T, V) = pushG P.C gs M
        (bif anyB (fun N => N == labF (wordF P.C.L g) M) V then (T, V)
          else (labF (wordF P.C.L g) M :: T, insU (labF (wordF P.C.L g) M) V)) := rfl
    rw [e]
    cases ha : anyB (fun N => N == labF (wordF P.C.L g) M) V with
    | true =>
      rw [Bool.cond_true]
      have hm := anyB_beq_mem ha
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih T V hV
      refine ⟨h1, ?_, h3, fun N hN => ?_, h5, h6⟩
      · rw [h2, List.map_cons, List.toFinset_cons, Finset.union_insert,
          Finset.insert_eq_of_mem (Finset.mem_union_left _ (List.mem_toFinset.mpr hm))]
      · rcases h4 N hN with h | ⟨g', hg', he⟩
        · exact Or.inl h
        · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', he⟩
    | false =>
      rw [Bool.cond_false]
      have hm := anyB_false_not_mem ha
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih _ _ (sortedLt_insU _ V hV)
      refine ⟨h1, ?_, fun N hN => h3 N (List.mem_cons_of_mem _ hN), fun N hN => ?_,
        fun N hN => ?_, ?_⟩
      · rw [h2, insU_toFinset, List.map_cons, List.toFinset_cons, Finset.union_insert,
          Finset.insert_union]
      · rcases h4 N hN with h | ⟨g', hg', he⟩
        · rcases List.mem_cons.mp h with h | h
          · exact Or.inr ⟨g, List.mem_cons_self .., h⟩
          · exact Or.inl h
        · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', he⟩
      · rcases h5 N hN with h | h
        · rw [← List.mem_toFinset, insU_toFinset, Finset.mem_insert, List.mem_toFinset] at h
          rcases h with h | h
          · exact Or.inr (h3 N (by rw [h]; exact List.mem_cons_self ..))
          · exact Or.inl h
        · exact Or.inr h
      · rw [List.length_cons, insU_toFinset,
          Finset.card_insert_of_notMem (fun h => hm (List.mem_toFinset.mp h))] at h6
        omega

private theorem closKG_spec (gs : List (List ℕ)) (y : List ℕ) (U F : Finset (List ℕ))
    (hF : ∀ M ∈ F, ∀ g ∈ gs, labF (wordF P.C.L g) M ∈ F)
    (hgen : ∀ S : Finset (List ℕ), y ∈ S →
      (∀ M ∈ S, M ∈ F → ∀ g ∈ gs, labF (wordF P.C.L g) M ∈ S) → F ⊆ S) :
    ∀ (f : ℕ) (T V : List (List ℕ)), sortedLt V = true → V.toFinset ⊆ U ∪ F →
      U ⊆ V.toFinset → y ∈ V → (∀ M ∈ T, M ∈ F) → (∀ M ∈ T, M ∈ V) →
      (∀ M ∈ V, M ∈ F → M ∉ T → ∀ g ∈ gs, labF (wordF P.C.L g) M ∈ V) →
      T.length + ((U ∪ F).card - V.toFinset.card) < f →
      sortedLt (closKG P.C gs f T V) = true ∧ (closKG P.C gs f T V).toFinset = U ∪ F
  | 0, _, _, _, _, _, _, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | f + 1, [], V, hs, hVs, hUV, hy, _, _, hcl, _ => by
    rw [closKG]
    refine ⟨hs, Finset.Subset.antisymm hVs (Finset.union_subset hUV ?_)⟩
    refine hgen V.toFinset (List.mem_toFinset.mpr hy) fun M hM hMF g hg => ?_
    exact List.mem_toFinset.mpr (hcl M (List.mem_toFinset.mp hM) hMF (by simp) g hg)
  | f + 1, M :: T, V, hs, hVs, hUV, hy, hTF, hTV, hcl, hf => by
    rw [closKG]
    have hMF : M ∈ F := hTF M List.mem_cons_self
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pushG_spec P gs M T V hs
    have himg : ∀ N ∈ (gs.map fun g => labF (wordF P.C.L g) M).toFinset, N ∈ F := by
      intro N hN
      rw [List.mem_toFinset, List.mem_map] at hN
      obtain ⟨g, hg, rfl⟩ := hN
      exact hF M hMF g hg
    have hsub : V.toFinset ⊆ (pushG P.C gs M (T, V)).2.toFinset := by
      rw [h2]
      exact Finset.subset_union_left
    have hVs' : (pushG P.C gs M (T, V)).2.toFinset ⊆ U ∪ F := by
      rw [h2]
      exact Finset.union_subset hVs fun N hN => Finset.mem_union_right _ (himg N hN)
    have hin : ∀ g ∈ gs, labF (wordF P.C.L g) M ∈ (pushG P.C gs M (T, V)).2 := by
      intro g hg
      apply List.mem_toFinset.mp
      rw [h2]
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨g, hg, rfl⟩))
    refine closKG_spec gs y U F hF hgen f _ _ h1 hVs' (hUV.trans hsub)
      (List.mem_toFinset.mp (hsub (List.mem_toFinset.mpr hy))) ?_ ?_ ?_ ?_
    · intro N hN
      rcases h4 N hN with h | ⟨g, hg, rfl⟩
      · exact hTF N (List.mem_cons_of_mem _ h)
      · exact hF M hMF g hg
    · intro N hN
      rcases h4 N hN with h | ⟨g, hg, rfl⟩
      · exact List.mem_toFinset.mp
          (hsub (List.mem_toFinset.mpr (hTV N (List.mem_cons_of_mem _ h))))
      · exact hin g hg
    · intro N hN hNF hNT g hg
      rcases h5 N hN with h | h
      · by_cases hNM : N = M
        · rw [hNM]
          exact hin g hg
        · have hNT' : N ∉ M :: T := by
            intro h'
            rcases List.mem_cons.mp h' with h' | h'
            · exact hNM h'
            · exact hNT (h3 N h')
          exact List.mem_toFinset.mp (hsub (List.mem_toFinset.mpr (hcl N h hNF hNT' g hg)))
      · exact absurd h hNT
    · have hc1 := Finset.card_le_card hVs'
      have hc2 := Finset.card_le_card hsub
      rw [List.length_cons] at hf
      omega

private theorem allIdx_get {α : Type} (f : ℕ → α → Bool) :
    ∀ (c : ℕ) (l : List α), allIdx f c l = true → ∀ i (hi : i < l.length), f (c + i) l[i] = true
  | _, [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | c, a :: l, h, i, hi => by
    rw [allIdx, Bool.and_eq_true] at h
    rcases i with _ | i
    · simpa using h.1
    · have h' := allIdx_get f (Nat.succ c) l h.2 i (by simpa using hi)
      have e : Nat.succ c + i = c + (i + 1) := by omega
      rw [e] at h'
      simpa using h'

private theorem K_sep_inj {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) {k₁ k₂ : List ℕ} (hk₁ : k₁ ∈ P.D.K.getD j [])
    (hk₂ : k₂ ∈ P.D.K.getD j [])
    (h : P.D.sep.map (wordF P.C.L k₁) = P.D.sep.map (wordF P.C.L k₂)) : k₁ = k₂ :=
  List.inj_on_of_nodup_map (sortedLt_nodup (K_sortedLt P hj h0)) hk₁ hk₂ h

private theorem sep_act {w : List ℕ} (hw : ∀ l ∈ w, l < 2 + P.C.ns) :
    P.D.sep.map (wordF P.C.L w) = P.D.sep.map (act n (evalElt P.els w)) :=
  List.map_congr_left fun _ hp => (P.act_wordF_eq hw (sep_lt P hp)).symm

private theorem dcKGens_sub {j : ℕ} (hG : ∀ i ∈ P.D.G.getD j [], i < (P.D.K.getD j []).length) :
    ∀ g ∈ dcKGens P.D j, g ∈ P.D.K.getD j [] := by
  intro g hg
  rw [dcKGens, List.mem_map] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  rw [List.getD_eq_getElem _ _ (hG i hi)]
  exact List.getElem_mem _

private theorem stabGenOK_G {j : ℕ} (hg : stabGenOK P.C P.D j = true) :
    ∀ i ∈ P.D.G.getD j [], i < (P.D.K.getD j []).length := by
  unfold stabGenOK at hg
  rw [Bool.and_eq_true, Bool.and_eq_true] at hg
  intro i hi
  have h := (List.all_eq_true.mp hg.1.1) i hi
  rwa [Nat.blt_eq] at h

private theorem K_mem_closure {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) (hg : stabGenOK P.C P.D j = true) {k : List ℕ}
    (hk : k ∈ P.D.K.getD j []) :
    evalElt P.els k ∈ Submonoid.closure {t | ∃ g ∈ dcKGens P.D j, evalElt P.els g = t} := by
  have hG := stabGenOK_G P hg
  unfold stabGenOK at hg
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq] at hg
  obtain ⟨⟨-, hlen⟩, hall⟩ := hg
  have hw := allIdx_get _ 0 _ hall
  have hK : ∀ {k}, k ∈ P.D.K.getD j [] → ∀ l ∈ k, l < 2 + P.C.ns :=
    fun hk => isS_lt P (K_isS P hj hk)
  have hb := obase_lt P hj
  have key : ∀ d i (hi : i < (P.D.Gw.getD j []).length), (P.D.Gw.getD j [])[i].2.2 ≤ d →
      evalElt P.els ((P.D.K.getD j []).getD i []) ∈
        Submonoid.closure {t | ∃ g ∈ dcKGens P.D j, evalElt P.els g = t} := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
    intro i hi hd
    have hiK : i < (P.D.K.getD j []).length := hlen ▸ hi
    have hki : (P.D.K.getD j []).getD i [] ∈ P.D.K.getD j [] := by
      rw [List.getD_eq_getElem _ _ hiK]
      exact List.getElem_mem hiK
    have hc := hw i hi
    rw [Nat.zero_add] at hc
    generalize he : (P.D.Gw.getD j [])[i] = e at hc hd
    obtain ⟨a, p, dd⟩ := e
    dsimp only at hc hd
    cases hba : Nat.blt a (P.D.G.getD j []).length with
    | false =>
      rw [hba, Bool.cond_false, beq_iff_eq] at hc
      obtain ⟨k0, hk0, he0⟩ := K_enum P hj h0 P.S.one_mem (act_one hb)
      have e1 : P.D.sep.map (wordF P.C.L k0) = P.D.sep := by
        rw [sep_act P (hK hk0), he0]
        exact (List.map_congr_left fun p hp => act_one (sep_lt P hp)).trans (List.map_id' _)
      rw [K_sep_inj P hj h0 hki hk0 (hc.trans e1.symm), he0]
      exact Submonoid.one_mem _
    | true =>
      rw [hba, Bool.cond_true, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq,
        beq_iff_eq] at hc
      obtain ⟨⟨hp, hdp⟩, hsep⟩ := hc
      rw [Nat.blt_eq] at hba
      have hpW : p < (P.D.Gw.getD j []).length := hlen ▸ hp
      rw [List.getD_eq_getElem _ _ hpW] at hdp
      have hkp : (P.D.K.getD j []).getD p [] ∈ P.D.K.getD j [] := by
        rw [List.getD_eq_getElem _ _ hp]
        exact List.getElem_mem hp
      have hgw : (dcKGens P.D j).getD a [] ∈ dcKGens P.D j := by
        have ha' : a < (dcKGens P.D j).length := by
          rw [dcKGens, List.length_map]
          exact hba
        rw [List.getD_eq_getElem _ _ ha']
        exact List.getElem_mem ha'
      have hgK := dcKGens_sub P hG _ hgw
      have hIH := ih _ (lt_of_lt_of_le hdp hd) p hpW le_rfl
      have hgS := evalElt_mem_S P (isS_spec P (K_isS P hj hgK))
      have hpS := evalElt_mem_S P (isS_spec P (K_isS P hj hkp))
      have hfix : ∀ {k}, k ∈ P.D.K.getD j [] →
          act n (evalElt P.els k) (P.D.obase.getD j 0) = P.D.obase.getD j 0 := fun hk => by
        rw [P.act_wordF_eq (hK hk) hb, K_fixes_word P hj hk]
      obtain ⟨k', hk', hk'e⟩ := K_enum P hj h0 (P.S.mul_mem hgS hpS)
        (by rw [act_mul _ _ hb, hfix hkp, hfix hgK])
      have e2 : P.D.sep.map (wordF P.C.L k') = P.D.sep.map (wordF P.C.L
          ((dcKGens P.D j).getD a [] ++ (P.D.K.getD j []).getD p [])) := by
        rw [sep_act P (hK hk'), sep_act P (letters_append P (hK hgK) (hK hkp)), evalElt_append,
          hk'e]
      rw [K_sep_inj P hj h0 hki hk' (hsep.symm.trans e2.symm), hk'e]
      exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨_, hgw, rfl⟩) hIH
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
  have hiW : i < (P.D.Gw.getD j []).length := hlen.symm ▸ hi
  have h := key _ i hiW le_rfl
  rwa [List.getD_eq_getElem _ _ hi] at h

private theorem extra_card_le {x : List ℕ} {j q : ℕ} :
    (P.imgsExtra x j q).card ≤ (P.D.K.getD j []).length := by
  unfold imgsExtra
  split
  · exact Finset.card_image_le.trans (List.toFinset_card_le _)
  · simp

private theorem stepKG {x : List ℕ} (hx : ∀ p ∈ x, p < n) {j : ℕ}
    (hj : j < P.D.obase.length) (h0 : 0 < (P.D.K.getD j []).length)
    (hpaths : pathsOK P.C P.D x j = true) (hg : stabGenOK P.C P.D j = true) {q : ℕ} (hq : q ∈ x)
    {U : List (List ℕ)} (hU : P.ExtraInv x j U.toFinset) (hUs : sortedLt U = true) :
    sortedLt (bif Nat.beq (oid P.D q) j then
        insKG P.C P.D j (insN (x.map (wordF P.C.L (pathW P.C P.D 64 q [])))) U
      else U) = true ∧
    (bif Nat.beq (oid P.D q) j then
        insKG P.C P.D j (insN (x.map (wordF P.C.L (pathW P.C P.D 64 q [])))) U
      else U).toFinset = U.toFinset ∪ P.imgsExtra x j q := by
  cases h : Nat.beq (oid P.D q) j with
  | false =>
    rw [Bool.cond_false, imgsExtra, ite_eq_right (by rw [h]; exact Bool.false_ne_true),
      Finset.union_empty]
    exact ⟨hUs, rfl⟩
  | true =>
    rw [Bool.cond_true, insKG]
    have ho : oid P.D q = j := by rwa [Nat.beq_eq] at h
    have his := pathsOK_spec' P hpaths hq ho
    have hK : ∀ {k}, k ∈ P.D.K.getD j [] → ∀ l ∈ k, l < 2 + P.C.ns :=
      fun hk => isS_lt P (K_isS P hj hk)
    have hb := obase_lt P hj
    have hfix : ∀ {k}, k ∈ P.D.K.getD j [] →
        act n (evalElt P.els k) (P.D.obase.getD j 0) = P.D.obase.getD j 0 := fun hk => by
      rw [P.act_wordF_eq (hK hk) hb, K_fixes_word P hj hk]
    have hmem : ∀ {k}, k ∈ P.D.K.getD j [] → evalElt P.els k ∈ P.S :=
      fun hk => evalElt_mem_S P (isS_spec P (K_isS P hj hk))
    have hy : insN (x.map (wordF P.C.L (pathW P.C P.D 64 q []))) =
        lab n ptLab x (evalElt P.els (pathW P.C P.D 64 q [])) := by
      have e := labF_map_eq_lab P hx (k := []) (fun l hl => absurd hl (by simp)) (isS_lt P his)
      rw [List.nil_append] at e
      rw [← e, labF]
      congr 1
      exact (List.map_id' _).symm
    have hyF : insN (x.map (wordF P.C.L (pathW P.C P.D 64 q []))) ∈ P.imgsExtra x j q := by
      obtain ⟨k0, hk0, he0⟩ := K_enum P hj h0 P.S.one_mem (act_one hb)
      rw [mem_imgsExtra]
      refine ⟨ho, k0, hk0, ?_⟩
      rw [labF_map_eq_lab P hx (hK hk0) (isS_lt P his), evalElt_append, he0, one_mul, hy]
    have hF' : ∀ M ∈ P.imgsExtra x j q, ∃ k ∈ P.D.K.getD j [],
        M = lab n ptLab x (evalElt P.els k * evalElt P.els (pathW P.C P.D 64 q [])) := by
      intro M hM
      rw [mem_imgsExtra] at hM
      obtain ⟨-, k, hk, rfl⟩ := hM
      exact ⟨k, hk, by rw [labF_map_eq_lab P hx (hK hk) (isS_lt P his), evalElt_append]⟩
    have hFof : ∀ {s : Γ}, s ∈ P.S → act n s (P.D.obase.getD j 0) = P.D.obase.getD j 0 →
        lab n ptLab x (s * evalElt P.els (pathW P.C P.D 64 q [])) ∈ P.imgsExtra x j q := by
      intro s hs hsf
      obtain ⟨k, hk, hke⟩ := K_enum P hj h0 hs hsf
      rw [mem_imgsExtra]
      refine ⟨ho, k, hk, ?_⟩
      rw [labF_map_eq_lab P hx (hK hk) (isS_lt P his), evalElt_append, hke]
    have hgen_lab : ∀ {g}, g ∈ P.D.K.getD j [] → ∀ (t : Γ),
        labF (wordF P.C.L g) (lab n ptLab x (t * evalElt P.els (pathW P.C P.D 64 q []))) =
          lab n ptLab x (evalElt P.els g * t * evalElt P.els (pathW P.C P.D 64 q [])) := by
      intro g hg t
      rw [labF_eq_lab_of P (lab_lt hx _) (hK hg), lab_lab' hx, mul_assoc]
    have hG := stabGenOK_G P hg
    have hFcl : ∀ M ∈ P.imgsExtra x j q, ∀ g ∈ dcKGens P.D j,
        labF (wordF P.C.L g) M ∈ P.imgsExtra x j q := by
      intro M hM g hg'
      obtain ⟨k, hk, rfl⟩ := hF' M hM
      have hgK := dcKGens_sub P hG g hg'
      rw [hgen_lab hgK]
      exact hFof (P.S.mul_mem (hmem hgK) (hmem hk))
        (by rw [act_mul _ _ hb, hfix hk, hfix hgK])
    have hgen : ∀ S : Finset (List ℕ), insN (x.map (wordF P.C.L (pathW P.C P.D 64 q []))) ∈ S →
        (∀ M ∈ S, M ∈ P.imgsExtra x j q → ∀ g ∈ dcKGens P.D j, labF (wordF P.C.L g) M ∈ S) →
        P.imgsExtra x j q ⊆ S := by
      intro S hyS hS M hM
      obtain ⟨k, hk, rfl⟩ := hF' M hM
      have hc := K_mem_closure P hj h0 hg hk
      have claim : ∀ t ∈ Submonoid.closure {t | ∃ g ∈ dcKGens P.D j, evalElt P.els g = t},
          lab n ptLab x (t * evalElt P.els (pathW P.C P.D 64 q [])) ∈ S ∧ t ∈ P.S ∧
            act n t (P.D.obase.getD j 0) = P.D.obase.getD j 0 := by
        intro t ht
        induction ht using Submonoid.closure_induction_left with
        | one => exact ⟨by rw [one_mul, ← hy]; exact hyS, P.S.one_mem, act_one hb⟩
        | mul_left a ha t _ iht =>
          obtain ⟨g, hg', rfl⟩ := ha
          have hgK := dcKGens_sub P hG g hg'
          obtain ⟨h1, h2, h3⟩ := iht
          refine ⟨?_, P.S.mul_mem (hmem hgK) h2, by rw [act_mul _ _ hb, h3, hfix hgK]⟩
          rw [← hgen_lab hgK]
          exact hS _ h1 (hFof h2 h3) g hg'
      exact (claim _ hc).1
    cases ha : anyB (fun M => M == insN (x.map (wordF P.C.L (pathW P.C P.D 64 q [])))) U with
    | true =>
      rw [Bool.cond_true]
      have ht := List.mem_toFinset.mpr (anyB_beq_mem ha)
      obtain ⟨q', hq', hM', hsub⟩ := hU _ ht
      exact ⟨hUs, (Finset.union_eq_left.mpr
        ((extra_sub P hx hj h0 hpaths hq hq' hyF hM').trans hsub)).symm⟩
    | false =>
      rw [Bool.cond_false]
      have hyU := anyB_false_not_mem ha
      have hdisj : ∀ M ∈ U, M ∈ P.imgsExtra x j q → False := by
        intro M hMU hMF
        obtain ⟨q', hq', hM', hsub⟩ := hU _ (List.mem_toFinset.mpr hMU)
        exact hyU (List.mem_toFinset.mp
          ((extra_sub P hx hj h0 hpaths hq hq' hMF hM').trans hsub hyF))
      have hyV : insN (x.map (wordF P.C.L (pathW P.C P.D 64 q []))) ∈
          insU (insN (x.map (wordF P.C.L (pathW P.C P.D 64 q [])))) U := by
        rw [← List.mem_toFinset, insU_toFinset]
        exact Finset.mem_insert_self _ _
      refine closKG_spec P (dcKGens P.D j) _ U.toFinset (P.imgsExtra x j q) hFcl hgen _ _ _
        (sortedLt_insU _ U hUs) ?_ ?_ hyV ?_ ?_ ?_ ?_
      · rw [insU_toFinset]
        exact Finset.insert_subset (Finset.mem_union_right _ hyF) Finset.subset_union_left
      · rw [insU_toFinset]
        exact Finset.subset_insert _ _
      · intro M hM
        rw [List.mem_singleton.mp hM]
        exact hyF
      · intro M hM
        rw [List.mem_singleton.mp hM]
        exact hyV
      · intro M hM hMF hMT
        rw [← List.mem_toFinset, insU_toFinset, Finset.mem_insert, List.mem_toFinset] at hM
        rcases hM with hM | hM
        · exact absurd (List.mem_singleton.mpr hM) hMT
        · exact (hdisj M hM hMF).elim
      · rw [insU_toFinset, Finset.card_insert_of_notMem (fun h => hyU (List.mem_toFinset.mp h)),
          List.length_singleton]
        have h1 := Finset.card_union_le U.toFinset (P.imgsExtra x j q)
        have h2 := extra_card_le P (x := x) (j := j) (q := q)
        omega

private theorem fold_imgsC {x : List ℕ} (hx : ∀ p ∈ x, p < n) {j : ℕ}
    (hj : j < P.D.obase.length) (h0 : 0 < (P.D.K.getD j []).length)
    (hpaths : pathsOK P.C P.D x j = true) (hg : stabGenOK P.C P.D j = true) :
    ∀ (l : List ℕ), (∀ q ∈ l, q ∈ x) → ∀ (U : List (List ℕ)), P.ExtraInv x j U.toFinset →
      sortedLt U = true →
      sortedLt (l.foldl (fun U q => bif Nat.beq (oid P.D q) j then
          insKG P.C P.D j (insN (x.map (wordF P.C.L (pathW P.C P.D 64 q [])))) U
        else U) U) = true ∧
      (l.foldl (fun U q => bif Nat.beq (oid P.D q) j then
          insKG P.C P.D j (insN (x.map (wordF P.C.L (pathW P.C P.D 64 q [])))) U
        else U) U).toFinset = l.foldl (fun U q => U ∪ P.imgsExtra x j q) U.toFinset
  | [], _, U, _, hs => ⟨hs, rfl⟩
  | a :: l, hl, U, hU, hs => by
    rw [List.foldl_cons, List.foldl_cons]
    have ha : a ∈ x := hl a List.mem_cons_self
    obtain ⟨e1, e⟩ := stepKG P hx hj h0 hpaths hg ha hU hs
    rw [← e]
    refine fold_imgsC hx hj h0 hpaths hg l (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ ?_ e1
    rw [e]
    intro M hM
    rcases Finset.mem_union.mp hM with hM | hM
    · obtain ⟨q', hq', h1, h2⟩ := hU M hM
      exact ⟨q', hq', h1, h2.trans Finset.subset_union_left⟩
    · exact ⟨a, ha, hM, Finset.subset_union_right⟩

private theorem sortedLt_eq {l l' : List (List ℕ)} (hl : sortedLt l = true)
    (hl' : sortedLt l' = true) (h : l.toFinset = l'.toFinset) : l = l' := by
  refine List.Perm.eq_of_pairwise (le := (· < ·)) (fun a b _ _ hab hba => ?_)
    ((sortedLt_iff_pairwise l).1 hl) ((sortedLt_iff_pairwise l').1 hl')
    (List.perm_of_nodup_nodup_toFinset_eq (sortedLt_nodup hl) (sortedLt_nodup hl') h)
  have := lexLt_trans ((lexLt_iff_lt a b).2 hab) ((lexLt_iff_lt b a).2 hba)
  rw [lexLt_irrefl] at this
  exact absurd this Bool.false_ne_true

theorem imgsG_eq {x : List ℕ} {j : ℕ} (hj : j < P.D.obase.length)
    (h0 : 0 < (P.D.K.getD j []).length) (hx : ∀ p ∈ x, p < n)
    (hpaths : pathsOK P.C P.D x j = true) (m : ℕ) :
    imgsG P.C P.D x j m = imgs P.C P.D x j := by
  unfold imgsG
  cases hu : useG P.D x j m with
  | false => rfl
  | true =>
    rw [Bool.cond_true]
    have hG : 0 < (P.D.G.getD j []).length := by
      unfold useG at hu
      rw [Bool.and_eq_true, Nat.blt_eq] at hu
      exact hu.1
    have hg := stabGenOK_of P hj h0 hG
    obtain ⟨hs, he⟩ := fold_imgsC P hx hj h0 hpaths hg x (fun _ hq => hq) []
      (by intro M hM; simp at hM) rfl
    refine sortedLt_eq hs (imgs_sortedLt P x j) ?_
    rw [imgsC, he, imgs_toFinset P hj h0 hx hpaths]
    rfl

end DcSoundCtx

end CFSG.KC.SLDc

end
