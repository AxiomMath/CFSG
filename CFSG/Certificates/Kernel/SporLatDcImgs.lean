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

private theorem fold_toFinset (step : List (List ℕ) → ℕ → List (List ℕ))
    (stepF : Finset (List ℕ) → ℕ → Finset (List ℕ))
    (h : ∀ (U : List (List ℕ)) (q : ℕ), (step U q).toFinset = stepF U.toFinset q) :
    ∀ (l : List ℕ) (U : List (List ℕ)), (l.foldl step U).toFinset = l.foldl stepF U.toFinset
  | [], U => rfl
  | a :: l, U => by
    rw [List.foldl_cons, List.foldl_cons, fold_toFinset step stepF h l (step U a), h]

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

theorem imgs_toFinset (x : List ℕ) (j : ℕ) :
    (imgs P.C P.D x j).toFinset = P.imgsF x j := by
  rw [imgsF]
  refine fold_toFinset _ _ ?_ x []
  intro U q
  cases h : Nat.beq (oid P.D q) j with
  | true =>
    rw [cond_true, insK_toFinset, imgsExtra, if_pos h]
  | false =>
    rw [cond_false, imgsExtra, if_neg (by rw [h]; exact Bool.false_ne_true), Finset.union_empty]

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
        insK P.C (P.D.K.getD j []) (x.map (wordF P.C.L (pathW P.C P.D 64 q []))) U else U) U) = true
  | [], U, hU => hU
  | a :: l, U, hU => by
    rw [List.foldl_cons]
    cases h : Nat.beq (oid P.D a) j with
    | true =>
      rw [cond_true]
      exact sortedLt_fold_imgs x j l _ (sortedLt_insK P.C _ _ U hU)
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
  rw [← List.toFinset_card_of_nodup (imgs_nodup P x j), imgs_toFinset,
    imgsF_eq_filter P hj h0 hx hpaths]

end DcSoundCtx

end CFSG.KC.SLDc

end
