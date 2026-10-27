module

public import Certificates.Data.Kernel.SUSmall.Defs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallClassRules
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallClassKeysAux

public section

namespace CFSG.KC.SUSmall

open Certificates.SUSmall CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

def ZH (pos : ℕ) (sup : List ℕ) (c : List ℕ) : Prop :=
  ∀ i, c.getD i 0 ≠ 0 → (∀ s ∈ sup, zt s (pos + i) = true) ∧
    ∀ j < i, c.getD j 0 ≠ 0 → zt (pos + j) (pos + i) = true

theorem zh_tail {pos : ℕ} {sup : List ℕ} {x : ℕ} {c : List ℕ} (h : ZH pos sup (x :: c)) :
    ∀ i, c.getD i 0 ≠ 0 → (∀ s ∈ sup, zt s (pos + 1 + i) = true) ∧
      ∀ j < i, c.getD j 0 ≠ 0 → zt (pos + 1 + j) (pos + 1 + i) = true := by
  intro i hi
  have h1 := h (i + 1) (by rwa [List.getD_cons_succ])
  rw [show pos + (i + 1) = pos + 1 + i by omega] at h1
  refine ⟨h1.1, fun j hj hcj => ?_⟩
  have h2 := h1.2 (j + 1) (by omega) (by rwa [List.getD_cons_succ])
  rwa [show pos + (j + 1) = pos + 1 + j by omega] at h2

theorem allCompsZ_sound (P : List ℕ → Bool) :
    ∀ (k n pos : ℕ) (sup acc c : List ℕ), allCompsZ P n pos k sup acc = true →
      c.length = k → c.sum = n → ZH pos sup c → P (acc.reverse ++ c) = true := by
  intro k
  induction k with
  | zero =>
    intro n pos sup acc c h hl hs _
    rw [List.length_eq_zero_iff] at hl
    subst hl
    simp only [List.sum_nil] at hs
    subst hs
    simpa [allCompsZ] using h
  | succ k ih =>
    intro n pos sup acc c h hl hs hz
    obtain ⟨x, c, rfl⟩ : ∃ x c', c = x :: c' := by
      cases c with
      | nil => simp at hl
      | cons x c' => exact ⟨x, c', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [List.sum_cons] at hs
    rw [allCompsZ, Bool.and_eq_true] at h
    have ht := zh_tail hz
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx
      have := ih n (pos + 1) sup (0 :: acc) c h.1 hl (by omega) ht
      simpa using this
    · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
      have h0 := hz 0 (by simp)
      have hsup : (sup.all fun s => zt s pos) = true := by
        rw [List.all_eq_true]
        intro s hs'
        simpa using h0.1 s hs'
      rw [hsup, Bool.not_true, Bool.false_or, List.all_eq_true] at h
      have hr := h.2 a (List.mem_range.mpr (by omega))
      have hz' : ZH (pos + 1) (pos :: sup) c := by
        intro i hi
        refine ⟨fun s hs' => ?_, (ht i hi).2⟩
        rcases List.mem_cons.mp hs' with rfl | hs'
        · have := (hz (i + 1) (by rwa [List.getD_cons_succ])).2 0 (by omega) (by simp)
          rwa [show s + (i + 1) = s + 1 + i by omega, Nat.add_zero] at this
        · exact (ht i hi).1 s hs'
      have := ih (n - (a + 1)) (pos + 1) (pos :: sup) ((a + 1) :: acc) c hr hl (by omega) hz'
      simpa using this

theorem zt_eq : ∀ k l : Fin 9, ((uOf k == uOf l) == (phiOf k == phiOf l)) = zt k.val l.val := by
  decide

theorem zh_of_zCount {c : List ℕ} (hc : c.length = 9) (h : zCount c = true) : ZH 0 [] c := by
  intro i hi
  refine ⟨fun s hs => absurd hs List.not_mem_nil, fun j hj hcj => ?_⟩
  have hi9 : i < 9 := by
    by_contra hge
    exact hi (List.getD_eq_default _ _ (by omega))
  rw [zCount, List.all_eq_true] at h
  have h1 := List.all_eq_true.mp (h ⟨j, by omega⟩ (List.mem_finRange _)) ⟨i, hi9⟩
    (List.mem_finRange _)
  rw [zt_eq, Bool.or_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h1
  rcases h1 with (h | h) | h
  · exact absurd h hcj
  · exact absurd h hi
  · simpa using h

theorem cover_sound {m : ℕ} {K : List (List ℕ)} (h : coverOK m K = true) (p : Pair m)
    (hz : zeroPairZ p = true) (hd : smDot p.2 p.1 = 2) : ckey p ∈ K := by
  have hv : validCount (key p) = true := validCount_key p hz hd
  have hzc : zCount (key p) = true := by
    rw [validCount, Bool.and_eq_true] at hv
    exact hv.1
  have := allCompsZ_sound _ 9 m 0 [] [] (key p) h (hdRo7SmKeysAux_key_length p)
    (hdRo7SmKeysAux_key_sum p) (zh_of_zCount (hdRo7SmKeysAux_key_length p) hzc)
  simp only [List.reverse_nil, List.nil_append, hv, Bool.not_true, Bool.false_or,
    List.contains_iff_mem] at this
  rwa [ckeyOfList_key] at this

theorem derivGo_sound (NW : List (ℕ × ℕ × List ℕ)) (OW : List (ℕ × ℕ × ℕ × List ℕ))
    (Ks : Set ℕ) (hN : ∀ x y, cellNone NW x y = true → x ∈ Ks → y ∈ Ks → False)
    (hO : ∀ x y c, cellOut OW x y c = true → x ∈ Ks → y ∈ Ks → c ∈ Ks) :
    ∀ (st : List (ℕ × ℕ × ℕ)) (S : List ℕ) (f : ℕ × ℕ), (∀ s ∈ S, s ∈ Ks) →
      derivGo NW OW S st f = true → False := by
  intro st
  induction st with
  | nil =>
    intro S f hS h
    simp only [derivGo, Bool.and_eq_true, List.contains_iff_mem] at h
    exact hN _ _ h.2 (hS _ h.1.1) (hS _ h.1.2)
  | cons s t ih =>
    intro S f hS h
    simp only [derivGo, Bool.and_eq_true, List.contains_iff_mem] at h
    refine ih (s.2.2 :: S) f ?_ h.2
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hO _ _ _ h.1.2 (hS _ h.1.1.1) (hS _ h.1.1.2)
    · exact hS x hx

theorem allSubs_sound (P : List ℕ → Bool) :
    ∀ (L acc l : List ℕ), allSubs P acc L = true → l.Sublist L → P (acc.reverse ++ l) = true := by
  intro L
  induction L with
  | nil =>
    intro acc l h hl
    rw [List.sublist_nil] at hl
    subst hl
    simpa [allSubs] using h
  | cons x xs ih =>
    intro acc l h hl
    rw [allSubs, Bool.and_eq_true] at h
    rcases List.sublist_cons_iff.mp hl with hl | ⟨r, rfl, hr⟩
    · exact ih acc l h.1 hl
    · simpa using ih (x :: acc) r h.2 hr

theorem perm_single {m : ℕ} (π : Equiv.Perm (Fin m)) (i j k : Fin m) :
    (Pi.single i (1 : ZMod 3) : SMV m) (π k) - (Pi.single j (1 : ZMod 3) : SMV m) (π k) =
      (Pi.single (π.symm i) (1 : ZMod 3) : SMV m) k -
        (Pi.single (π.symm j) (1 : ZMod 3) : SMV m) k := by
  simp only [Pi.single_apply]
  have h1 : ∀ y : Fin m,
      (if π k = y then (1 : ZMod 3) else 0) = (if k = π.symm y then 1 else 0) := by
    intro y
    by_cases h : π k = y
    · rw [if_pos h, if_pos ((Equiv.apply_eq_iff_eq_symm_apply π).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((Equiv.apply_eq_iff_eq_symm_apply π).mpr hh))]
  rw [h1 i, h1 j]

theorem smtClass_of_smClass {m : ℕ} {p q : Pair m} (h : SMClass p q) (hq : SMTClass q) :
    SMTClass p := by
  obtain ⟨π, u, hu, hpq⟩ := h
  obtain ⟨i, j, t, hij, ht, hq1, hq2⟩ := hq
  refine ⟨π.symm i, π.symm j, u * t, ?_, ?_, ?_, ?_⟩
  · intro he
    exact hij (by rw [← Equiv.apply_symm_apply π i, he, Equiv.apply_symm_apply π j])
  · rcases hu with rfl | rfl <;> rcases ht with rfl | rfl <;> decide
  · funext k
    rw [(hpq k).1, hq1]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [perm_single π i j k]; ring
  · funext k
    rw [(hpq k).2, hq2]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [perm_single π i j k]; ring

theorem class_sound_wit {m : ℕ} (hm : m ≤ 9) (cat : List (Pair m)) (K : List (List ℕ)) (N : ℕ)
    (NW : List (ℕ × ℕ × List ℕ)) (OW : List (ℕ × ℕ × ℕ × List ℕ)) (SV : List ℕ)
    (DV : List (ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ)) (AL : List (List ℕ)) (Xs : List (List (Pair m)))
    (hcat : catOK cat K N = true) (hnone : NW.all (noneOK cat K N) = true)
    (hout : OW.all (outOK cat K N) = true) (hsurv : survOK N SV DV NW OW = true)
    (hsubs : subsOK SV AL NW OW = true) (hal : alOK K N AL Xs = true)
    (hcov : coverOK m K = true) {R : Set (SMV m × SMV m)} (hR : SMRCl R) :
    ∃ X ∈ Xs, ∀ p, p ∈ R ↔ (SMTClass p ∨ ∃ q ∈ X, SMClass p q) := by
  classical
  simp only [catOK, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at hcat
  obtain ⟨⟨⟨hlen, h2⟩, hT2⟩, hK⟩ := hcat
  have hKg : ∀ i < N, K.getD i [] = ckey (cat.getD i 0) := by
    intro i hi
    rw [← hK, List.getD_eq_getElem _ _ (by rw [List.length_map]; omega),
      List.getD_eq_getElem _ _ (by omega), List.getElem_map]
  have hcls : ∀ s i, i < N → ckey s = K.getD i [] → SMClass s (cat.getD i 0) := by
    intro s i hi he
    rw [smClass_iff_ckey_eq hm, he, hKg i hi]
  have hRT : ∀ p : Pair m, SMTClass p → p ∈ R := by
    rw [SMRCl] at hR
    exact hR.2.2.2.2.1
  let Ks : Set ℕ := {i | i < N ∧ cat.getD i 0 ∈ R}
  have h2K : (2 : ℕ) ∈ Ks := ⟨h2, hRT _ ((isTranspositionPair_iff _).mp hT2)⟩
  have hN : ∀ x y, cellNone NW x y = true → x ∈ Ks → y ∈ Ks → False := by
    intro x y h hx hy
    simp only [cellNone, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨w, hw, rfl, rfl⟩ := h
    have hw' := List.all_eq_true.mp hnone w hw
    simp only [noneOK, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at hw'
    obtain ⟨⟨hb, hk⟩, hbad⟩ := hw'
    have hs : pairOf m w.2.2 ∈ R := smRCl_class_closed hR hy.2 (hcls _ _ hb hk)
    rw [smRCl_not_badPair hR hx.2 hs] at hbad
    exact Bool.false_ne_true hbad
  have hO : ∀ x y c, (∃ w ∈ OW, w.1 = x ∧ w.2.1 = y ∧ w.2.2.1 = c) → x ∈ Ks → y ∈ Ks →
      c ∈ Ks := by
    rintro x y c ⟨w, hw, rfl, rfl, rfl⟩ hx hy
    have hw' := List.all_eq_true.mp hout w hw
    simp only [outOK, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at hw'
    obtain ⟨⟨⟨hb, hc⟩, hk⟩, hkc⟩ := hw'
    have hs : pairOf m w.2.2.2 ∈ R := smRCl_class_closed hR hy.2 (hcls _ _ hb hk)
    have hcj := smRCl_conj_mem hR hx.2 hs
    refine ⟨hc, smRCl_class_closed hR hcj ?_⟩
    rw [smClass_iff_ckey_eq hm, hkc, hKg _ hc]
  have hO' : ∀ x y c, cellOut OW x y c = true → x ∈ Ks → y ∈ Ks → c ∈ Ks := by
    intro x y c h
    simp only [cellOut, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨w, hw, ⟨h1, h2⟩, h3⟩ := h
    exact hO x y c ⟨w, hw, h1, h2, h3⟩
  have hKSV : ∀ a ∈ Ks, a ∈ SV := by
    intro a ha
    have h := List.all_eq_true.mp hsurv a (List.mem_range.mpr ha.1)
    simp only [Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq] at h
    rcases h with h | ⟨d, -, rfl, hd⟩
    · exact h
    · refine (derivGo_sound NW OW Ks hN hO' _ _ _ ?_ hd).elim
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact h2K
      · rw [List.mem_singleton] at hs
        rw [hs]
        exact ha
  let L : List ℕ := SV.filter fun a => decide (a ∈ Ks)
  have hLK : ∀ a, a ∈ L ↔ a ∈ Ks := by
    intro a
    simp only [L, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hKSV a h, h⟩⟩
  have hadm : admOK NW OW L = true := by
    simp only [admOK, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true]
    refine ⟨(hLK 2).mpr h2K, fun i hi j hj => ⟨?_, fun c hc => ?_⟩⟩
    · rw [Bool.not_eq_true']
      by_contra hc
      exact hN i j (by simpa using hc) ((hLK i).mp hi) ((hLK j).mp hj)
    · refine (hLK c).mpr (hO i j c ?_ ((hLK i).mp hi) ((hLK j).mp hj))
      simp only [outsOf, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨w, ⟨hw, h1, h2⟩, h3⟩ := hc
      exact ⟨w, hw, h1, h2, h3⟩
  have hLAL : L ∈ AL := by
    have h := allSubs_sound _ SV [] L hsubs List.filter_sublist
    simp only [List.reverse_nil, List.nil_append, hadm, Bool.not_true, Bool.false_or,
      List.contains_iff_mem] at h
    exact h
  obtain ⟨X, hX, hm'⟩ : ∃ X ∈ Xs, matchOK K N L X = true := by
    have h := List.all_eq_true.mp hal L hLAL
    simpa only [List.any_eq_true] using h
  simp only [matchOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true, Nat.blt_eq] at hm'
  obtain ⟨hm1, hm2⟩ := hm'
  refine ⟨X, hX, fun p => ⟨fun hp => ?_, fun hp => ?_⟩⟩
  · have hkp := cover_sound hcov p (smRCl_zeroPairZ hR hp) (by rw [SMRCl] at hR; exact hR.1 p hp)
    obtain ⟨i, hi, hiK⟩ := List.getElem_of_mem hkp
    have hiN : i < N := by rw [← hK, List.length_map] at hi; omega
    have hgi : K.getD i [] = ckey p := by rw [List.getD_eq_getElem _ _ hi, hiK]
    have hpc : SMClass p (cat.getD i 0) := hcls p i hiN hgi.symm
    have hiKs : i ∈ Ks := ⟨hiN, smRCl_class_closed hR hp
      ((smClass_iff_ckey_eq hm _ _).mpr ((smClass_iff_ckey_eq hm _ _).mp hpc).symm)⟩
    rcases hm1 i ((hLK i).mpr hiKs) with rfl | ⟨q, hq, hqk⟩
    · exact Or.inl (smtClass_of_smClass hpc ((isTranspositionPair_iff _).mp hT2))
    · exact Or.inr ⟨q, hq, (smClass_iff_ckey_eq hm _ _).mpr (by rw [hqk, hgi])⟩
  · rcases hp with hp | ⟨q, hq, hpq⟩
    · exact hRT p hp
    · obtain ⟨c, hc, hcN, hqk⟩ := hm2 q hq
      have hqR : q ∈ R := smRCl_class_closed hR ((hLK c).mp hc).2 (hcls q c hcN hqk)
      exact smRCl_class_closed hR hqR hpq

end CFSG.KC.SUSmall

end
