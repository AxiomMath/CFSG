module

public import Certificates.Data.Kernel.J4TreeColPair
public import Certificates.Data.Kernel.J4TreeColCov
import CFSG.Certificates.Kernel.J4Q.RepQT2B

public section

namespace CFSG.KC.J4TreeCol

open CFSG.KC.J4Q CFSG.KC.Loop CFSG.J4Tree.Native

theorem pIdx_eq (n i j : Nat) : pIdx n i j = pIdx n i i + (j - i) := by
  simp [pIdx]

theorem tri_succ (i : Nat) : (i + 1) * i / 2 = i * (i - 1) / 2 + i := by
  rcases i with _ | m
  · rfl
  · have e : (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) := by ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num)]
    simp

theorem tri_le {i n : Nat} (h : i ≤ n) : i * (i - 1) / 2 ≤ i * n :=
  (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (by omega))

theorem pIdx_diag_succ {n i : Nat} (h : i < n) :
    pIdx n (i + 1) (i + 1) = pIdx n i i + (n - i) := by
  have h1 := tri_succ i
  have h2 := tri_le h.le
  simp only [pIdx, Nat.sub_self, Nat.add_zero, Nat.add_sub_cancel]
  rw [h1, Nat.succ_mul]
  generalize i * n = A at *
  generalize i * (i - 1) / 2 = B at *
  omega

theorem pIdx_diag_mono {n a : Nat} :
    ∀ {b : Nat}, a < b → b ≤ n → pIdx n (a + 1) (a + 1) ≤ pIdx n b b
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | b + 1, h, hb => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · have h1 := pIdx_diag_mono h' (Nat.le_of_succ_le hb)
      rw [pIdx_diag_succ (by omega : b < n)]
      omega
    · exact le_rfl

theorem pIdx_lt_succ {n i j : Nat} (hij : i ≤ j) (hj : j < n) :
    pIdx n i j < pIdx n (i + 1) (i + 1) := by
  rw [pIdx_eq n i j, pIdx_diag_succ (by omega : i < n)]
  omega

theorem pIdx_diag_n (n : Nat) : pIdx n n n = n * (n + 1) / 2 := by
  have h1 : n * (n + 1) / 2 = n * (n - 1) / 2 + n := by rw [Nat.mul_comm n (n + 1), tri_succ]
  have h2 : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have h3 : n * (n - 1) + n = n * n := by
    rcases n with _ | m
    · rfl
    · simp only [Nat.add_sub_cancel]
      ring
  simp only [pIdx, Nat.sub_self, Nat.add_zero]
  rw [h1]
  generalize n * (n - 1) / 2 = B at *
  generalize n * (n - 1) = C at *
  generalize n * n = D at *
  omega

theorem pIdx_lt_total {n a b : Nat} (hab : a ≤ b) (hb : b < n) : pIdx n a b < n * (n + 1) / 2 := by
  have h1 := pIdx_lt_succ hab hb
  have h2 := pIdx_diag_mono (by omega : a < n) (le_refl n)
  rw [pIdx_diag_n] at h2
  omega

theorem pIdx_inj {n a b a' b' : Nat} (hab : a ≤ b) (hb : b < n) (hab' : a' ≤ b') (hb' : b' < n)
    (h : pIdx n a b = pIdx n a' b') : a = a' ∧ b = b' := by
  have key : ∀ {a b a' b' : Nat}, a ≤ b → b < n → a' ≤ b' → b' < n → a < a' →
      pIdx n a b ≠ pIdx n a' b' := by
    intro a b a' b' hab hb hab' hb' hlt he
    have h1 := pIdx_lt_succ hab hb
    have h2 := pIdx_diag_mono hlt (by omega : a' ≤ n)
    have h3 : pIdx n a' a' ≤ pIdx n a' b' := by
      rw [pIdx_eq n a' b']
      omega
    omega
  rcases lt_trichotomy a a' with hlt | rfl | hlt
  · exact absurd h (key hab hb hab' hb' hlt)
  · refine ⟨rfl, ?_⟩
    rw [pIdx_eq n a b, pIdx_eq n a b'] at h
    omega
  · exact absurd h.symm (key hab' hb' hab hb hlt)

@[expose] noncomputable def rowAux (n t k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ i)
      (Nat.ble (pIdx n (Nat.succ i) (Nat.succ i)) t)) k

theorem rowOfP_eq (n t : Nat) : rowOfP n t = rowAux n t (n - 1) := rfl

theorem rowAux_spec (n t : Nat) : ∀ k, rowAux n t k ≤ k ∧
    pIdx n (rowAux n t k) (rowAux n t k) ≤ t ∧ ∀ i, rowAux n t k < i → i ≤ k → t < pIdx n i i
  | 0 => by
    have e : rowAux n t 0 = 0 := rfl
    rw [e]
    exact ⟨le_rfl, by simp [pIdx], fun i h1 h2 => absurd h2 (by omega)⟩
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := rowAux_spec n t k
    have e : rowAux n t (k + 1) = Bool.rec (motive := fun _ => Nat) (rowAux n t k) (k + 1)
        (Nat.ble (pIdx n (k + 1) (k + 1)) t) := rfl
    cases hb : Nat.ble (pIdx n (k + 1) (k + 1)) t
    · have e' : rowAux n t (k + 1) = rowAux n t k := by rw [e, hb]
      have hlt : t < pIdx n (k + 1) (k + 1) := Nat.lt_of_not_le fun h => by
        rw [Nat.ble_eq_true_of_le h] at hb
        cases hb
      rw [e']
      refine ⟨by omega, h2, fun i hi1 hi2 => ?_⟩
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · exact h3 i hi1 (by omega)
      · obtain rfl : i = k + 1 := by omega
        exact hlt
    · have e' : rowAux n t (k + 1) = k + 1 := by rw [e, hb]
      rw [e']
      exact ⟨le_rfl, Nat.le_of_ble_eq_true hb, fun i hi1 hi2 => absurd hi2 (by omega)⟩

theorem rowOfP_spec {n t : Nat} (ht : t < n * (n + 1) / 2) :
    rowOfP n t < n ∧ pIdx n (rowOfP n t) (rowOfP n t) ≤ t ∧
      t < pIdx n (rowOfP n t + 1) (rowOfP n t + 1) := by
  rw [rowOfP_eq]
  obtain ⟨h1, h2, h3⟩ := rowAux_spec n t (n - 1)
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at ht
    · exact h
  refine ⟨by omega, h2, ?_⟩
  rcases Nat.lt_or_ge (rowAux n t (n - 1) + 1) n with h | h
  · exact h3 _ (by omega) (by omega)
  · have e : rowAux n t (n - 1) + 1 = n := by omega
    rw [e, pIdx_diag_n]
    exact ht

@[expose] noncomputable def pairP (G : Mats) (P i j : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (getP P (Nat.xor i j)) (getP P i)) (getP P j)) G.one

theorem pairRunP_succ (G : Mats) (P qp n c i j t : Nat) :
    pairRunP G P qp n (c + 1) i j t =
      (Nat.beq (fld qp 7 t + gRank G (pairP G P i j)) 112 &&
        if j + 1 < n then pairRunP G P qp n c i (j + 1) (t + 1)
        else pairRunP G P qp n c (i + 1) (i + 1) (t + 1)) := by
  have e : pairRunP G P qp n (c + 1) i j t =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool)
          (strictB (Nat.succ i) fun i' => strictB (Nat.succ t) fun t' => pairRunP G P qp n c i' i' t')
          (strictB (Nat.succ j) fun j' => strictB (Nat.succ t) fun t' => pairRunP G P qp n c i j' t')
          (Nat.blt (Nat.succ j) n))
        (Nat.beq (fld qp 7 t + gRank G (pairP G P i j)) 112) := rfl
  rw [e, strictB_eq, strictB_eq, strictB_eq, strictB_eq]
  by_cases h : j + 1 < n
  · have hb : Nat.blt (Nat.succ j) n = true := by
      rw [Nat.blt_eq]
      exact h
    rw [hb, if_pos h]
    cases Nat.beq (fld qp 7 t + gRank G (pairP G P i j)) 112 <;> rfl
  · have hb : Nat.blt (Nat.succ j) n = false := by
      cases hb' : Nat.blt (Nat.succ j) n
      · rfl
      · rw [Nat.blt_eq] at hb'
        exact absurd hb' h
    rw [hb, if_neg h]
    cases Nat.beq (fld qp 7 t + gRank G (pairP G P i j)) 112 <;> rfl

theorem pairRunP_spec (G : Mats) (P qp n : Nat) : ∀ (c i j t : Nat),
    pairRunP G P qp n c i j t = true → i ≤ j → (c ≠ 0 → j < n) → pIdx n i j = t →
    t + c ≤ n * (n + 1) / 2 →
    ∀ a b, a ≤ b → b < n → t ≤ pIdx n a b → pIdx n a b < t + c →
      fld qp 7 (pIdx n a b) + gRank G (pairP G P a b) = 112
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2 => absurd h2 (by omega)
  | c + 1, i, j, t, h, hij, hjn, hp, hc, a, b, hab, hb, h1, h2 => by
    have hj : j < n := hjn (by omega)
    rw [pairRunP_succ, Bool.and_eq_true] at h
    obtain ⟨hq, hr⟩ := h
    rcases Nat.lt_or_ge t (pIdx n a b) with hlt | hge
    · by_cases hjn' : j + 1 < n
      · rw [if_pos hjn'] at hr
        refine pairRunP_spec G P qp n c i (j + 1) (t + 1) hr (by omega) (fun _ => hjn') ?_
          (by omega) a b hab hb (by omega) (by omega)
        rw [pIdx_eq] at hp ⊢
        omega
      · rw [if_neg hjn'] at hr
        have hd := pIdx_diag_succ (by omega : i < n)
        have hp' := hp
        rw [pIdx_eq n i j] at hp'
        refine pairRunP_spec G P qp n c (i + 1) (i + 1) (t + 1) hr le_rfl (fun hc0 => ?_)
          (by omega) (by omega) a b hab hb (by omega) (by omega)
        by_contra hcon
        have e : i + 1 = n := by omega
        rw [e, pIdx_diag_n] at hd
        generalize n * (n + 1) / 2 = N at *
        omega
    · have e : pIdx n a b = t := by omega
      obtain ⟨rfl, rfl⟩ := pIdx_inj hab hb hij hj (e.trans hp.symm)
      rw [e]
      exact Nat.eq_of_beq_eq_true hq

theorem pairsOKP_spec {G : Mats} {D : CRec} {t0 cnt : Nat} (h : pairsOKP G D t0 cnt = true) :
    D.mode = 1 ∧ ∀ a b, a ≤ b → b < 2 ^ (treeWv D.k).length →
      t0 ≤ pIdx (2 ^ (treeWv D.k).length) a b → pIdx (2 ^ (treeWv D.k).length) a b < t0 + cnt →
      fld D.qp 7 (pIdx (2 ^ (treeWv D.k).length) a b) +
        gRank G (pairP G (packMs (matsOf G (treeWv D.k))) a b) = 112 := by
  unfold pairsOKP at h
  dsimp only at h
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hm, hle⟩, hr⟩ := h
  rw [strictB_eq, strictB_eq, strictB_eq, strictB_eq] at hr
  refine ⟨hm, ?_⟩
  generalize 2 ^ (treeWv D.k).length = n at hle hr ⊢
  have hle' := Nat.le_of_ble_eq_true hle
  intro a b hab hb h1 h2
  have ht0 : t0 < n * (n + 1) / 2 := by
    have := pIdx_lt_total hab hb
    omega
  obtain ⟨hi, hlo, hhi⟩ := rowOfP_spec ht0
  have hd := pIdx_diag_succ hi
  refine pairRunP_spec G _ D.qp n cnt _ _ t0 hr (by omega) (fun _ => by omega) ?_ hle' a b hab hb
    h1 h2
  rw [pIdx_eq]
  omega

theorem tileOK_spec : ∀ (l : List (Nat × Nat)) (t N : Nat), tileOK l t N = true →
    ∀ s, t ≤ s → s < N → ∃ q ∈ l, q.1 ≤ s ∧ s < q.1 + q.2
  | [], t, N, h, s, h1, h2 => by
    simp only [tileOK, beq_iff_eq] at h
    omega
  | q :: l, t, N, h, s, h1, h2 => by
    simp only [tileOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hq, hl⟩ := h
    rcases Nat.lt_or_ge s (t + q.2) with hs | hs
    · exact ⟨q, List.mem_cons_self .., by omega, by omega⟩
    · obtain ⟨q', hq', h⟩ := tileOK_spec l (t + q.2) N hl s hs h2
      exact ⟨q', List.mem_cons_of_mem _ hq', h⟩

theorem covOK_spec {R : Nat → CRec} {it : Nat → List Nat} {np nn : Nat}
    (h : covOK R it np nn = true) {j : Nat} (hj : j < nn) (hm : (R j).mode = 1) {s : Nat}
    (hs : s < nPairs (R j)) :
    ∃ p < np, (it p).getD 0 0 = j ∧ (it p).getD 1 0 ≤ s ∧
      s < (it p).getD 1 0 + (it p).getD 2 0 := by
  unfold covOK at h
  rw [List.all_eq_true] at h
  have h1 := h j (List.mem_range.2 hj)
  rw [hm, bne_self_eq_false, Bool.false_or] at h1
  obtain ⟨q, hq, hq1, hq2⟩ := tileOK_spec _ 0 _ h1 s (Nat.zero_le _) hs
  unfold itemsOf at hq
  obtain ⟨x, hx, hfx⟩ := List.mem_filterMap.1 hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  by_cases hxj : (it p).getD 0 0 = j
  · rw [if_pos hxj] at hfx
    obtain rfl := Option.some.inj hfx
    exact ⟨p, List.mem_range.1 hp, hxj, hq1, hq2⟩
  · rw [if_neg hxj] at hfx
    cases hfx

theorem pairs_sound {G : Mats} {R : Nat → CRec} {it : Nat → List Nat} {np nn : Nat}
    (hc : covOK R it np nn = true)
    (hp : ∀ p < np, pairsOKP G (R ((it p).getD 0 0)) ((it p).getD 1 0) ((it p).getD 2 0) = true)
    {j : Nat} (hj : j < nn) (hm : (R j).mode = 1) {a b : Nat} (hab : a ≤ b)
    (hb : b < 2 ^ (treeWv (R j).k).length) :
    fld (R j).qp 7 (pIdx (2 ^ (treeWv (R j).k).length) a b) +
      gRank G (pairP G (packMs (matsOf G (treeWv (R j).k))) a b) = 112 := by
  have hs : pIdx (2 ^ (treeWv (R j).k).length) a b < nPairs (R j) := pIdx_lt_total hab hb
  obtain ⟨p, hpn, hpj, h1, h2⟩ := covOK_spec hc hj hm hs
  have h := hp p hpn
  rw [hpj] at h
  exact (pairsOKP_spec h).2 a b hab hb h1 h2

end CFSG.KC.J4TreeCol

end
