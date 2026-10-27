module

public import CFSG.Certificates.Kernel.SporLatDcKeys

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

namespace DcSoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

variable (P : DcSoundCtx Γ n)

@[expose] def recs : List Rep := P.D.Rc.flatten

theorem mem_recs_repOK {r : Rep} (hr : r ∈ P.recs) : repOK P.C P.D r = true := by
  unfold recs at hr
  rw [List.mem_flatten] at hr
  obtain ⟨c, hc, hrc⟩ := hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have hck := chunkOK_of_lt P hi
  unfold chunkOK at hck
  rw [List.getD_eq_getElem _ _ hi, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at hck
  exact (List.all_eq_true.mp hck.1.1.1.1) r hrc

private theorem recs_lab_valid {r : Rep} (hr : r ∈ P.recs) : PtValid n r.lab :=
  rep_lab_valid P (mem_recs_repOK P hr)

private theorem recs_lab_nodup {r : Rep} (hr : r ∈ P.recs) : r.lab.Nodup :=
  rep_lab_nodup P (mem_recs_repOK P hr)

theorem recs_lab_eq {r : Rep} (hr : r ∈ P.recs) : r.lab = lab n ptLab P.C.Δ (evalElt P.els r.w) :=
  rep_lab_eq P (mem_recs_repOK P hr)

private theorem chunkOK_parts {i : ℕ} (hi : i < P.D.Rc.length) :
    (P.D.Rc.getD i []).all (repOK P.C P.D) = true ∧
    0 < (P.D.Rc.getD i []).length ∧
    sortedLt ((P.D.Rc.getD i []).map Rep.key) = true ∧
    (¬ (Nat.succ i < P.D.Rc.length) ∨
      ((P.D.Rc.getD i []).length = P.D.csz ∧
        lexLt (lastL ((P.D.Rc.getD i []).map Rep.key))
          (headL ((P.D.Rc.getD (Nat.succ i) []).map Rep.key)) = true)) ∧
    sumN ((P.D.Rc.getD i []).map Rep.m) = P.D.msum.getD i 0 := by
  have h := chunkOK_of_lt P hi
  unfold chunkOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, by rwa [Nat.blt_eq] at h2, h3, ?_, by rwa [Nat.beq_eq] at h5⟩
  rw [Bool.or_eq_true] at h4
  rcases h4 with h4 | h4
  · left
    have h4' : Nat.blt (Nat.succ i) P.D.Rc.length = false := by simpa using h4
    rw [← Nat.blt_eq, h4']
    exact Bool.false_ne_true
  · right
    rw [Bool.and_eq_true, Nat.beq_eq] at h4
    exact h4

private theorem headL_append {a b : List (List ℕ)} (ha : a ≠ []) : headL (a ++ b) = headL a := by
  cases a with
  | nil => exact absurd rfl ha
  | cons x a => rfl

private theorem sortedLt_append {a b : List (List ℕ)} (ha : sortedLt a = true)
    (hb : sortedLt b = true)
    (hbne : b ≠ []) (h : lexLt (lastL a) (headL b) = true) : sortedLt (a ++ b) = true := by
  rw [sortedLt_iff_pairwise] at ha hb ⊢
  rw [List.pairwise_append]
  refine ⟨ha, hb, fun x hx y hy => ?_⟩
  rw [← lexLt_iff_lt]
  rcases lastL_max a ((sortedLt_iff_pairwise a).mpr ha) x hx with h1 | h1
  · rcases headL_min ((sortedLt_iff_pairwise b).mpr hb) hy with h2 | h2
    · rw [h1, h2]; exact h
    · rw [h1]; exact lexLt_trans h h2
  · rcases headL_min ((sortedLt_iff_pairwise b).mpr hb) hy with h2 | h2
    · rw [h2]; exact lexLt_trans h1 h
    · exact lexLt_trans h1 (lexLt_trans h h2)

private theorem chunk_keys_data {i : ℕ} (hi : i < P.D.Rc.length) {c : List Rep}
    (hget0 : P.D.Rc.getD i [] = c) :
    0 < c.length ∧ sortedLt (c.map Rep.key) = true := by
  have hcpos : 0 < c.length := by
    have h1 := (chunkOK_parts P hi).2.1
    rwa [hget0] at h1
  have hckeys : sortedLt (c.map Rep.key) = true := by
    have h1 := (chunkOK_parts P hi).2.2.1
    rwa [hget0] at h1
  exact ⟨hcpos, hckeys⟩

private theorem sortedLt_flatten_cons_cons {c c' : List Rep} {cs' : List (List Rep)}
    (hckeys : sortedLt (c.map Rep.key) = true)
    (hih : sortedLt ((c' :: cs').flatten.map Rep.key) = true)
    (hc'ne : c'.map Rep.key ≠ [])
    (hcross : lexLt (lastL (c.map Rep.key)) (headL (c'.map Rep.key)) = true) :
    sortedLt ((c :: c' :: cs').flatten.map Rep.key) = true := by
  have hfl : (c :: c' :: cs').flatten = c ++ (c' :: cs').flatten := rfl
  have hfl' : (c' :: cs').flatten = c' ++ cs'.flatten := rfl
  have hbne : (c' :: cs').flatten.map Rep.key ≠ [] := by
    intro h
    have h1 : (c' :: cs').flatten = [] := List.map_eq_nil_iff.mp h
    rw [hfl'] at h1
    exact hc'ne (by rw [(List.append_eq_nil_iff.mp h1).1, List.map_nil])
  have hhead : headL ((c' :: cs').flatten.map Rep.key) = headL (c'.map Rep.key) := by
    rw [hfl', List.map_append, headL_append hc'ne]
  rw [hfl, List.map_append]
  exact sortedLt_append hckeys hih hbne (by rw [hhead]; exact hcross)

private theorem sortedLt_flatten_aux : ∀ (cs : List (List Rep)) (i : ℕ),
    i + cs.length ≤ P.D.Rc.length →
    (∀ j, j < cs.length → P.D.Rc.getD (i + j) [] = cs.getD j []) →
    sortedLt (cs.flatten.map Rep.key) = true := by
  intro cs
  induction cs with
  | nil => intro i _ _; simp only [List.flatten_nil, List.map_nil, sortedLt]
  | cons c cs ih =>
    intro i hlen hget
    have hi : i < P.D.Rc.length :=
      Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (List.length_pos_iff.mpr (by simp))) hlen
    have hget0 : P.D.Rc.getD i [] = c := by
      have := hget 0 (Nat.succ_pos _)
      simpa using this
    obtain ⟨-, hckeys⟩ := chunk_keys_data P hi hget0
    rcases cs with _ | ⟨c', cs'⟩
    · simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append,
        List.map_nil, List.append_nil]
      exact hckeys
    · have hi' : i + 1 < P.D.Rc.length :=
        Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left (Nat.succ_lt_succ (Nat.succ_pos _)) i) hlen
      have hget1 : P.D.Rc.getD (i + 1) [] = c' := by
        have := hget 1 (by simp)
        simpa using this
      obtain ⟨hc'pos, -⟩ := chunk_keys_data P hi' hget1
      have hc'ne : c'.map Rep.key ≠ [] := by
        intro h
        exact (List.length_pos_iff.mp hc'pos) (List.map_eq_nil_iff.mp h)
      have hcross : lexLt (lastL (c.map Rep.key)) (headL (c'.map Rep.key)) = true := by
        have h4 := (chunkOK_parts P hi).2.2.2.1
        rw [hget0, hget1] at h4
        rcases h4 with h4 | h4
        · omega
        · exact h4.2
      have hih : sortedLt ((c' :: cs').flatten.map Rep.key) = true := by
        refine ih (i + 1) ?_ ?_
        · rw [Nat.add_assoc, Nat.add_comm 1]
          exact hlen
        · intro j hj
          have h := hget (j + 1) (by simpa using hj)
          rw [show i + 1 + j = i + (j + 1) from by omega]
          simpa using h
      exact sortedLt_flatten_cons_cons hckeys hih hc'ne hcross

private theorem sortedLt_recs_keys : sortedLt (P.recs.map Rep.key) = true := by
  have h := sortedLt_flatten_aux P P.D.Rc 0 (by simp) (by
    intro j hj
    simpa using rfl)
  simpa [recs] using h

private theorem key_eq_of_mem_recs {r r' : Rep} (hr : r ∈ P.recs) (hr' : r' ∈ P.recs)
    (h : Rep.key r = Rep.key r') : r = r' := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr'
  have hi' : i < (P.recs.map Rep.key).length := by simpa using hi
  have hj' : j < (P.recs.map Rep.key).length := by simpa using hj
  have hk : (P.recs.map Rep.key)[i]'hi' = (P.recs.map Rep.key)[j]'hj' := by
    simp only [List.getElem_map]
    exact h
  have hij : i = j :=
    (List.Nodup.getElem_inj_iff (sortedLt_nodup (sortedLt_recs_keys P)) (hi := hi')
      (hj := hj')).mp hk
  subst hij
  rfl

private theorem recs_nodup : P.recs.Nodup :=
  List.Nodup.of_map Rep.key (sortedLt_nodup (sortedLt_recs_keys P))

private theorem Sx_lab {x : List ℕ} (hx : PtValid n x) {s : Γ} (hs : s ∈ P.S) :
    P.Sx (lab n ptLab x s) = P.Sx x := by
  ext M
  rw [mem_Sx, mem_Sx]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t * s, P.S.mul_mem ht hs, lab_lab hx t s⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * s⁻¹, P.S.mul_mem ht (P.S.inv_mem hs), ?_⟩
    rw [lab_lab hx (t * s⁻¹) s, mul_assoc, inv_mul_cancel, mul_one]

private theorem Sx_disjoint {r r' : Rep} (hr : r ∈ P.recs) (hr' : r' ∈ P.recs) (hne : r ≠ r') :
    Disjoint (P.Sx r.lab) (P.Sx r'.lab) := by
  rw [Finset.disjoint_left]
  intro M hM hM'
  have h1 : P.Sx M = P.Sx r.lab := by
    rw [mem_Sx] at hM
    obtain ⟨s, hs, rfl⟩ := hM
    exact Sx_lab P (recs_lab_valid P hr) hs
  have h2 : P.Sx M = P.Sx r'.lab := by
    rw [mem_Sx] at hM'
    obtain ⟨s, hs, rfl⟩ := hM'
    exact Sx_lab P (recs_lab_valid P hr') hs
  have hSx : P.Sx r.lab = P.Sx r'.lab := h1.symm.trans h2
  exact hne (key_eq_of_mem_recs P hr hr' (key_eq_of_Sx_eq P (mem_recs_repOK P hr)
    (mem_recs_repOK P hr') hSx))

private theorem sumN_eq_sum : ∀ (l : List ℕ), sumN l = l.sum
  | [] => rfl
  | a :: l => by rw [sumN, sumN_eq_sum l, List.sum_cons]; rfl

private theorem sumN_eq_sum_map : ∀ (l : List (List Rep)),
    sumN ((l.map (List.map Rep.m)).flatten) =
      sumN (l.map (fun c : List Rep => sumN (c.map Rep.m))) := by
  intro l
  have h1 : sumN ((l.map (List.map Rep.m)).flatten) =
      ((l.map (List.map Rep.m)).flatten).sum := sumN_eq_sum _
  have h2 : sumN (l.map (fun c : List Rep => sumN (c.map Rep.m))) =
      (l.map (fun c : List Rep => sumN (c.map Rep.m))).sum := sumN_eq_sum _
  rw [h1, h2, List.sum_flatten]
  congr 1
  rw [List.map_map]
  exact List.map_congr_left (fun (c : List Rep) _ => (sumN_eq_sum (c.map Rep.m)).symm)

private theorem msum_eq : P.D.msum = P.D.Rc.map (fun c : List Rep => sumN (c.map Rep.m)) := by
  have hlen : P.D.msum.length = (P.D.Rc.map (fun c : List Rep => sumN (c.map Rep.m))).length := by
    rw [msum_length P]
    simp
  apply List.ext_getElem hlen
  intro i hi1 hi2
  have hi : i < P.D.Rc.length := by
    rw [msum_length P] at hi1
    exact hi1
  have h := (chunkOK_parts P hi).2.2.2.2
  calc P.D.msum[i] = P.D.msum.getD i 0 := (List.getD_eq_getElem _ _ hi1).symm
    _ = sumN ((P.D.Rc.getD i []).map Rep.m) := h.symm
    _ = sumN ((P.D.Rc[i]).map Rep.m) := by rw [List.getD_eq_getElem _ _ hi]
    _ = (P.D.Rc.map (fun c : List Rep => sumN (c.map Rep.m)))[i] := by
        rw [List.getElem_map]

private theorem sum_m_recs : sumN (P.recs.map Rep.m) = P.C.N := by
  rw [recs, List.map_flatten]
  rw [sumN_eq_sum_map]
  rw [← msum_eq P, sum_msum P]

private theorem mem_foldr_union : ∀ (l : List Rep) (M : List ℕ),
    M ∈ l.foldr (fun r U => P.Sx r.lab ∪ U) ∅ ↔ ∃ r ∈ l, M ∈ P.Sx r.lab := by
  intro l
  induction l with
  | nil => intro M; simp
  | cons r l ih =>
    intro M
    rw [List.foldr_cons, Finset.mem_union, ih M]
    constructor
    · rintro (h | ⟨r', hr', hM⟩)
      · exact ⟨r, List.mem_cons_self .., h⟩
      · exact ⟨r', List.mem_cons_of_mem _ hr', hM⟩
    · rintro ⟨r', hr', hM⟩
      rw [List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · exact Or.inl hM
      · exact Or.inr ⟨r', hr', hM⟩

@[expose] noncomputable def unionSx : Finset (List ℕ) :=
  P.recs.foldr (fun r U => P.Sx r.lab ∪ U) ∅

theorem mem_unionSx {M : List ℕ} :
    M ∈ P.unionSx ↔ ∃ r ∈ P.recs, M ∈ P.Sx r.lab := by
  unfold unionSx
  exact mem_foldr_union P P.recs M

private theorem card_fold_union : ∀ (l : List Rep), (∀ r ∈ l, r ∈ P.recs) → l.Nodup →
    (l.foldr (fun r U => P.Sx r.lab ∪ U) ∅).card = sumN (l.map Rep.m)
  | [], _, _ => rfl
  | r :: l, hsub, hnod => by
    rw [List.foldr_cons]
    have hr : r ∈ P.recs := hsub r (List.mem_cons_self ..)
    have hdisj : Disjoint (P.Sx r.lab) (l.foldr (fun r U => P.Sx r.lab ∪ U) ∅) := by
      rw [Finset.disjoint_left]
      intro M hM hM'
      rw [mem_foldr_union] at hM'
      obtain ⟨r', hr', hM'⟩ := hM'
      have hne : r ≠ r' := by
        rintro rfl
        exact (List.nodup_cons.mp hnod).1 hr'
      exact (Finset.disjoint_left.mp
        (Sx_disjoint P hr (hsub r' (List.mem_cons_of_mem _ hr')) hne)) hM hM'
    rw [Finset.card_union_of_disjoint hdisj]
    rw [card_fold_union l (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
      (List.nodup_cons.mp hnod).2]
    rw [List.map_cons, sumN, ← m_eq_card P (mem_recs_repOK P hr)]
    rfl

theorem card_unionSx : P.unionSx.card = P.C.N := by
  unfold unionSx
  rw [card_fold_union P P.recs (fun r hr => hr) (recs_nodup P), sum_m_recs P]

@[expose] noncomputable def GOrb : Finset (List ℕ) :=
  letI : Fintype Γ := Fintype.ofFinite Γ
  Finset.univ.image (fun g : Γ => lab n ptLab P.C.Δ g)

theorem mem_GOrb {M : List ℕ} :
    M ∈ P.GOrb ↔ ∃ g : Γ, lab n ptLab P.C.Δ g = M := by
  classical
  letI : Fintype Γ := Fintype.ofFinite Γ
  show M ∈ Finset.univ.image (fun g : Γ => lab n ptLab P.C.Δ g) ↔
    ∃ g : Γ, lab n ptLab P.C.Δ g = M
  rw [Finset.mem_image]
  exact ⟨fun ⟨g, _, h⟩ => ⟨g, h⟩, fun ⟨g, h⟩ => ⟨g, Finset.mem_univ _, h⟩⟩

theorem unionSx_subset_GOrb : P.unionSx ⊆ P.GOrb := by
  intro M hM
  rw [mem_unionSx] at hM
  obtain ⟨r, hr, hM⟩ := hM
  rw [mem_Sx] at hM
  obtain ⟨s, hs, rfl⟩ := hM
  refine (mem_GOrb P).mpr ⟨s * evalElt P.els r.w, ?_⟩
  rw [recs_lab_eq P hr]
  exact (lab_lab P.hΔ s (evalElt P.els r.w)).symm

end DcSoundCtx

end CFSG.KC.SLDc

end
