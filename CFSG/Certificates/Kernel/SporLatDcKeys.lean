module

public import CFSG.Certificates.Kernel.SporLatDcCount

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

namespace DcSoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

variable (P : DcSoundCtx Γ n)

private theorem cntB_pos {α : Type} {f : α → Bool} {l : List α} (h : 0 < cntB f l) :
    ∃ a ∈ l, f a = true := by
  have hne : l.filter f ≠ [] := List.ne_nil_of_length_pos (by
    rwa [← cntB_eq_length_filter])
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
  exact ⟨a, (List.mem_filter.mp ha).1, (List.mem_filter.mp ha).2⟩

private theorem cntO_pos {x : List ℕ} {q : ℕ} (hq : q ∈ x) : 0 < cntO P.D x (oid P.D q) := by
  rw [cntO, cntB_eq_length_filter]
  exact List.length_pos_iff.mpr
    (List.ne_nil_of_mem (List.mem_filter.mpr ⟨hq, Nat.beq_refl _⟩))

private theorem argOK_iff {x : List ℕ} {j : ℕ} :
    argOK P.D x j = true ↔
      0 < (P.D.K.getD j []).length ∧
      ∀ k, 0 < cntO P.D x k →
        (P.D.K.getD k []).length = 0 ∨ costO P.D x j < costO P.D x k ∨
          (costO P.D x j = costO P.D x k ∧ j ≤ k) := by
  unfold argOK
  rw [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hK, hc⟩
    refine ⟨by rwa [Nat.blt_eq] at hK, fun k hk => ?_⟩
    have hk' : 0 < cntB (fun q => Nat.beq (oid P.D q) k) x := by
      rwa [cntO] at hk
    obtain ⟨q, hq, hqk⟩ := cntB_pos hk'
    rw [Nat.beq_eq] at hqk
    have h1 := hc q hq
    rw [← hqk]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq] at h1 ⊢
    tauto
  · rintro ⟨hK, hc⟩
    refine ⟨by rwa [Nat.blt_eq], fun q hq => ?_⟩
    have h1 := hc (oid P.D q) (cntO_pos P hq)
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq] at h1 ⊢
    tauto

private theorem argOK_unique {x : List ℕ} {j j' : ℕ} (h : argOK P.D x j = true)
    (h' : argOK P.D x j' = true) (hj : 0 < cntO P.D x j) (hj' : 0 < cntO P.D x j') :
    j = j' := by
  rw [argOK_iff] at h h'
  obtain ⟨hK, hc⟩ := h
  obtain ⟨hK', hc'⟩ := h'
  have h1 := hc j' hj'
  have h2 := hc' j hj
  rcases h1 with h1 | h1 | ⟨h1, h1'⟩
  · omega
  · rcases h2 with h2 | h2 | ⟨h2, h2'⟩
    · omega
    · omega
    · omega
  · rcases h2 with h2 | h2 | ⟨h2, h2'⟩
    · omega
    · omega
    · omega

private theorem argOK_congr {x x' : List ℕ} {j : ℕ} (hcnt : ∀ k, cntO P.D x k = cntO P.D x' k) :
    argOK P.D x j = true ↔ argOK P.D x' j = true := by
  have hcost : ∀ k, costO P.D x k = costO P.D x' k := by
    intro k
    rw [costO, costO, hcnt k]
  rw [argOK_iff, argOK_iff]
  constructor
  · rintro ⟨hK, hc⟩
    refine ⟨hK, fun k hk => ?_⟩
    rw [← hcnt k] at hk
    rcases hc k hk with h1 | h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · refine Or.inr (Or.inl ?_)
      rw [← hcost j, ← hcost k]
      exact h1
    · refine Or.inr (Or.inr ⟨?_, h2⟩)
      rw [← hcost j, ← hcost k]
      exact h1
  · rintro ⟨hK, hc⟩
    refine ⟨hK, fun k hk => ?_⟩
    rw [hcnt k] at hk
    rcases hc k hk with h1 | h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · refine Or.inr (Or.inl ?_)
      rw [hcost j, hcost k]
      exact h1
    · refine Or.inr (Or.inr ⟨?_, h2⟩)
      rw [hcost j, hcost k]
      exact h1

private theorem cntO_shift {x : List ℕ} (hx : PtValid n x) (hnd : x.Nodup) {s : Γ} (hs : s ∈ P.S)
    (j : ℕ) : cntO P.D (lab n ptLab x s) j = cntO P.D x j := by
  rw [← filter_card_eq_cntO P (lab_nodup hx.2 hnd s),
    filter_eq_inter_Oj P hx (M := lab n ptLab x s) (by rw [mem_Sx]; exact ⟨s, hs, rfl⟩) j,
    card_inter_Oj P (fun p hp => hx.2 p hp) hnd hs j,
    filter_card_eq_cntO P hnd]

private theorem cntO_mem_Sx {x : List ℕ} (hx : PtValid n x) (hnd : x.Nodup) {M : List ℕ}
    (hM : M ∈ P.Sx x) (j : ℕ) : cntO P.D M j = cntO P.D x j := by
  rw [mem_Sx] at hM
  obtain ⟨s, hs, rfl⟩ := hM
  exact cntO_shift P hx hnd hs j

private theorem headL_eq_of_toFinset_eq {l l' : List (List ℕ)} (hl : sortedLt l = true)
    (hl' : sortedLt l' = true) (h : l.toFinset = l'.toFinset) : headL l = headL l' := by
  rcases l with _ | ⟨a, l⟩
  · have h0 : l' = [] := (List.toFinset_eq_empty_iff l').mp (by rw [← h]; rfl)
    rw [h0]
  · rcases l' with _ | ⟨a', l'⟩
    · have h0 : a :: l = [] := (List.toFinset_eq_empty_iff (a :: l)).mp (by rw [h]; rfl)
      exact absurd h0 (by simp)
    · have ha' : a' ∈ a :: l := by
        rw [← List.mem_toFinset, h]
        exact List.mem_toFinset.mpr (List.mem_cons_self ..)
      have ha : a ∈ a' :: l' := by
        rw [← List.mem_toFinset, ← h]
        exact List.mem_toFinset.mpr (List.mem_cons_self ..)
      rcases headL_min hl ha' with h1 | h1
      · exact h1.symm
      · rcases headL_min hl' ha with h2 | h2
        · exact h2
        · have h3 : lexLt (headL (a :: l)) a = true := lexLt_trans h1 h2
          rw [show headL (a :: l) = a from rfl] at h3
          rw [lexLt_irrefl] at h3
          exact (Bool.false_ne_true h3).elim

private theorem orbR_parts {r : Rep} (hr : repOK P.C P.D r) :
    Rep.j r < P.D.obase.length ∧ 0 < cntO P.D r.lab (Rep.j r) ∧
    argOK P.D r.lab (Rep.j r) = true ∧ pathsOK P.C P.D r.lab (Rep.j r) = true ∧
    0 < (P.D.K.getD (Rep.j r) []).length ∧ 0 < Rep.m r ∧
    Rep.key r = Rep.j r :: headL (imgs P.C P.D r.lab (Rep.j r)) := by
  unfold repOK at hr
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hr
  have horb := hr.1.2
  unfold orbR at horb
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true] at horb
  obtain ⟨⟨⟨⟨⟨hj, hcnt⟩, harg⟩, hpaths⟩, hm⟩, hsize⟩ := horb
  unfold sizeKey at hsize
  rw [Bool.and_eq_true] at hsize
  have hkey : Rep.key r = Rep.j r :: headL (imgs P.C P.D r.lab (Rep.j r)) := by
    have h := hsize.2
    rwa [beq_iff_eq] at h
  have hargOK : argOK P.D r.lab (Rep.j r) = true := harg
  unfold argOK at harg
  rw [Bool.and_eq_true] at harg
  have hK0 : 0 < (P.D.K.getD (Rep.j r) []).length := by
    have h := harg.1
    rwa [Nat.blt_eq] at h
  exact ⟨by rwa [Nat.blt_eq] at hj, by rwa [Nat.blt_eq] at hcnt, hargOK, hpaths, hK0,
    by rwa [Nat.blt_eq] at hm, hkey⟩

theorem key_eq_of_Sx_eq {r r' : Rep} (hr : repOK P.C P.D r) (hr' : repOK P.C P.D r')
    (hSx : P.Sx r.lab = P.Sx r'.lab) : Rep.key r = Rep.key r' := by
  obtain ⟨hj, hcnt, harg, hpaths, hK0, hm, hkey⟩ := orbR_parts P hr
  obtain ⟨hj', hcnt', harg', hpaths', hK0', hm', hkey'⟩ := orbR_parts P hr'
  have hvalid := rep_lab_valid P hr
  have hvalid' := rep_lab_valid P hr'
  have hnd := rep_lab_nodup P hr
  have hnd' := rep_lab_nodup P hr'
  have hmem' : r'.lab ∈ P.Sx r.lab := by
    rw [hSx]
    exact (mem_Sx (P := P)).mpr ⟨1, P.S.one_mem, (lab_one hlaw hvalid').symm⟩
  have hcnt_eq : ∀ k, cntO P.D r.lab k = cntO P.D r'.lab k := by
    intro k
    rw [cntO_mem_Sx P hvalid hnd hmem' k]
  have harg' : argOK P.D r.lab (Rep.j r') = true :=
    (argOK_congr P hcnt_eq).mpr harg'
  have hj_eq : Rep.j r = Rep.j r' :=
    argOK_unique P harg harg' hcnt (hcnt_eq (Rep.j r') ▸ hcnt')
  have hhead : headL (imgs P.C P.D r.lab (Rep.j r)) =
      headL (imgs P.C P.D r'.lab (Rep.j r')) := by
    refine headL_eq_of_toFinset_eq (imgs_sortedLt P _ _) (imgs_sortedLt P _ _) ?_
    rw [imgs_toFinset, imgs_toFinset,
      imgsF_eq_filter P hj hK0 (fun p hp => hvalid.2 p hp) hpaths,
      imgsF_eq_filter P hj' hK0' (fun p hp => hvalid'.2 p hp) hpaths', hj_eq, hSx]
  rw [hkey, hkey', hhead, hj_eq]

end DcSoundCtx

end CFSG.KC.SLDc

end
