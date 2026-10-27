module

public import CFSG.Certificates.Kernel.LocalQTR9CodeSound
public import CFSG.Certificates.Kernel.LocalQTSmallSound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Words

public section

namespace CFSG.KC.LQT.R

open CFSG.QuasithinUnique.Unc25K1 CFSG.KC.Ord

theorem rr_mul (x y : S3) : rr (x * y) = rmul (rr x) (rr y) := by
  simp [rr, rmul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem rr_one : rr 1 = rone := by
  simp [rr, rone]

theorem rr_inj {x y : S3} (h : rr x = rr y) : x = y := by
  simp only [rr, R9.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem rr_eq_iff {x y : S3} : rr x = rr y ↔ x = y := ⟨rr_inj, fun h => h ▸ rfl⟩

open CFSG.QuasithinUnique.Unc25L33 in
theorem rr_pow (x : S3) (n : ℕ) : rr (x ^ n) = rpw (rr x) n := by
  induction n with
  | zero => rw [pow_zero, rr_one]; rfl
  | succ n ih => rw [pow_succ', rr_mul, ih]; rfl

theorem evBK_rr (a b : S3) (w : List Bool) :
    evBK (codeR (rr a)) (codeR (rr b)) w = codeR (rr (evB a b w)) := by
  induction w with
  | nil => rw [evB, rr_one, ← oneK_eq]; rfl
  | cons c w ih =>
    cases c
    · change mulK (codeR (rr a)) (evBK _ _ w) = _
      rw [ih, mulK_codeR, evB, rr_mul]
    · change mulK (codeR (rr b)) (evBK _ _ w) = _
      rw [ih, mulK_codeR, evB, rr_mul]

theorem card_S3k : Fintype.card S3 = 5616 := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_SL_field]
  simp [Fin.prod_univ_three, ZMod.card]

theorem iffB_iff' {a b : Bool} : S.iffB a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp [S.iffB, notB]

theorem anyW_iff (l : List (List Bool)) (f : List Bool → Bool) :
    anyW l f = true ↔ ∃ x ∈ l, f x = true := by
  induction l with
  | nil => simp [anyW]
  | cons x l ih =>
    change orB (f x) (anyW l f) = true ↔ _
    rw [P.orB_iff, ih]
    simp

theorem cnt_inner {α : Type*} (c : α → ℕ) (B : ℕ → ℕ → Bool) (P : α → α → Bool) (a : α)
    (N : List α) (h : ∀ b ∈ N, B (c a) (c b) = P a b) :
    List.rec (motive := fun _ => ℕ) 0 (fun q _ ih2 => Nat.add ih2
      (Bool.rec (motive := fun _ => ℕ) 0 1 (B (c a) q))) (N.map c) =
    ((N.map (Prod.mk a)).filter fun p => P p.1 p.2).length := by
  induction N with
  | nil => rfl
  | cons b N ih =>
    simp only [List.map_cons, List.filter_cons]
    rw [ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb')), h b (by simp)]
    cases P a b <;> simp

theorem cnt_eq {α : Type*} (c : α → ℕ) (B : ℕ → ℕ → Bool) (P : α → α → Bool) (M N : List α)
    (h : ∀ a ∈ M, ∀ b ∈ N, B (c a) (c b) = P a b) :
    List.rec (motive := fun _ => ℕ) 0 (fun p _ ih => Nat.add ih
      (List.rec (motive := fun _ => ℕ) 0 (fun q _ ih2 => Nat.add ih2
        (Bool.rec (motive := fun _ => ℕ) 0 1 (B p q))) (N.map c))) (M.map c) =
    ((M.product N).filter fun p => P p.1 p.2).length := by
  induction M with
  | nil => rfl
  | cons a M ih =>
    simp only [List.map_cons]
    rw [ih (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')),
      cnt_inner c B P a N (h a (by simp))]
    change _ = ((N.map (Prod.mk a) ++ M.product N).filter _).length
    rw [List.filter_append, List.length_append]
    exact Nat.add_comm _ _

theorem s4145k (L : List R9) (hL : ∀ r, r ∈ L ↔ rdet r = 1) (u0 a b : S3) (Tl : List S3)
    (Ws : List (List Bool)) {U0 A B : ℕ}
    {TL wu : List ℕ} (hu : codeR (rr u0) = U0) (ha : codeR (rr a) = A) (hb : codeR (rr b) = B)
    (ht : (Tl.map rr).map codeR = TL)
    (hk : c4145 U0 A B TL Ws wu = true) (hs : ∀ c < 20, allSLc c (sl4145 U0 TL wu) = true) :
    (u0 ≠ 1)
    ∧ (u0 ^ 2 = 1)
    ∧ (Fintype.card S3 = 5616)
    ∧ (∀ r ∈ L,
          (((rmul r (rr u0) = rmul (rr u0) r ∧ rmul r (rmul r r) = rone) ↔ r ∈ Tl.map rr) ∧
            (rmul r (rr u0) = rmul (rr u0) r → (∀ t ∈ Tl.map rr, rmul t r = rmul r t) →
              r = rone ∨ r = rr u0) ∧
            ((∀ t ∈ Tl.map rr, rmul r t = rmul t r) → r = rone ∨ r = rr u0)))
    ∧ (∀ u ∈ L, u ≠ rone → rmul u u = rone →
          ∃ g ∈ L, rmul g (rr u0) = rmul u g)
    ∧ (∀ t ∈ Tl, ∃ w ∈ Ws, t = evB a b w)
    ∧ (u0 = evB a b [true, false, true, false])
    ∧ (a ≠ 1 ∧ b ≠ 1 ∧ (a * b) ^ 2 ≠ 1 ∧ (a * b) ^ 4 = 1)
    ∧ (((Tl.product Tl).filter
          (fun p => decide (p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ (p.1 * p.2) ^ 2 ≠ 1 ∧ (p.1 * p.2) ^ 4 = 1))).length
        ≤ 24) := by
  subst hu ha hb ht
  have hr : ∀ r ∈ L, sl4145 (codeR (rr u0)) ((Tl.map rr).map codeR) wu (codeR r) = true :=
    fun r h => allSLc_sound hs r ((hL r).1 h)
  simp only [sl4145, S.allBs_cons, S.allBs_nil, P.andB_iff, and_true] at hr
  simp only [iffB_iff', P.impB_iff, P.anyL_iff, P.orB_iff, P.beq_iff, S.memL_iff,
    mulK_codeR, oneK_eq, codeR_eq_iff, invoK_codeR, commK_codeR, allL_mapR, mem_mapR,
    P.andB_iff] at hr
  simp only [c4145, S.allBs_cons, S.allBs_nil, P.andB_iff, and_true] at hk
  obtain ⟨k1, k2, -, k4, k5, k6, k7, k8, k9, k10, k11⟩ := hk
  have hc := cnt_eq (codeR ∘ rr) (fun p q => S.allBs [notB (Nat.beq p oneK),
    notB (Nat.beq q oneK), notB (Nat.beq (pwK (mulK p q) 2) oneK),
    Nat.beq (pwK (mulK p q) 4) oneK])
    (fun x y => decide (x ≠ 1 ∧ y ≠ 1 ∧ (x * y) ^ 2 ≠ 1 ∧ (x * y) ^ 4 = 1)) Tl Tl
    (fun x _ y _ => by
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      simp only [Function.comp, S.allBs_cons, S.allBs_nil, P.andB_iff, and_true, P.notB_iff,
        P.beq_iff, oneK_eq, mulK_codeR, ← rr_mul, pwK_codeR, ← rr_pow, ← rr_one, codeR_eq_iff,
        rr_eq_iff])
  rw [List.map_map] at k11
  have hcnt := hc.symm.trans_le (Nat.le_of_ble_eq_true k11)
  simp only [P.notB_iff, P.beq_iff, oneK_eq, mulK_codeR, ← rr_mul, pwK_codeR, ← rr_pow,
    ← rr_one, codeR_eq_iff, rr_eq_iff, evBK_rr] at k1 k2 k6 k7 k8 k9 k10
  simp only [P.allL_iff, P.andB_iff, P.beq_iff] at k4
  simp only [allL_mapR, anyW_iff, P.beq_iff, evBK_rr, codeR_eq_iff, List.forall_mem_map,
    rr_eq_iff] at k5
  refine ⟨k1, by rw [sq]; exact k2, card_S3k, fun r h => ⟨(hr r h).1, (hr r h).2.1,
    (hr r h).2.2.1⟩, ?_, k5, k6, ⟨k7, k8, k9, k10⟩, hcnt⟩
  intro u hu hne hsq
  obtain ⟨w, hw, hwu⟩ := (hr u hu).2.2.2 ⟨hne, hsq⟩
  obtain ⟨hsl, hm⟩ := k4 w hw
  obtain ⟨g, hg, hdg⟩ := exists_of_slOK hsl
  rw [← hg, hwu, mulK_codeR, mulK_codeR, codeR_eq_iff] at hm
  exact ⟨g, (hL g).2 hdg, hm⟩

end CFSG.KC.LQT.R

end
