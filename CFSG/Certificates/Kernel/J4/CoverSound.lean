module

public import CFSG.Certificates.Kernel.J4.KRouteSound
public import CFSG.Certificates.Kernel.J4.TStructSound
public import CFSG.Certificates.Kernel.DceTwStab
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.GetD

public section

namespace CFSG.KJ4.Cover

open CFSG.KJ4 CFSG.KJ4.S CFSG.KJ4.R CFSG.KJ4.Mat CFSG.KJ4.Models CFSG.KJ4.KRoute CFSG.KJ4.TStruct
  CFSG.KC.Loop
open CFSG.Certificates.DceTwS (Cov cov_mul_N N_mul_cov mem_cov)

@[expose] noncomputable def eI (e : ℕ) : ℕ := Nat.land (Nat.shiftRight e (nat_lit 1)) (nat_lit 32767)
@[expose] noncomputable def eR (e : ℕ) : ℕ := Nat.land (Nat.shiftRight e (nat_lit 16)) (nat_lit 65535)
@[expose] noncomputable def eG (e : ℕ) : ℕ := Nat.shiftRight (eR e) (nat_lit 1)
@[expose] noncomputable def eS (e : ℕ) : ℕ := Nat.land (Nat.shiftRight e (nat_lit 32)) (nat_lit 65535)
@[expose] noncomputable def eP (e : ℕ) : ℕ := Nat.land (Nat.shiftRight e (nat_lit 16)) (nat_lit 32767)

@[expose] noncomputable def coverB (FT PT OT : ℕ → ℕ) (ND D e : ℕ) : Bool :=
  letB (FT (eG e)) (fun F => andB (Nat.beq (oJ (OT (eI e))) (Nat.succ (eI e))) (
    Bool.rec (motive := fun _ => Bool)
      (andB (Nat.beq (fD F) D) (andB (Nat.beq (fJ F) (Nat.succ (eI e))) (Nat.blt (fDp F) ND)))
      (andB (Nat.beq (fDp F) D) (andB (Nat.blt (nat_lit 0) (fJ F)) (andB (Nat.blt (fD F) ND)
        (chkPtF (PT (eI e)) (fPi F) (PT (Nat.sub (fJ F) (nat_lit 1)))
          (Nat.land (Nat.shiftRight e (nat_lit 32)) (nat_lit 7))))))
      (Nat.beq (Nat.land (eR e) (nat_lit 1)) (nat_lit 1))))

@[expose] noncomputable def stabB (FT PT : ℕ → ℕ) (D e BM : ℕ) : Bool :=
  letB (FT (eS e)) (fun F =>
    andB (Nat.beq (fD F) D) (andB (Nat.beq (fDp F) D) (andB (Nat.beq (fJ F) (nat_lit 0))
    (andB (Nat.blt (nat_lit 0) (Nat.land BM (Nat.shiftLeft (nat_lit 1) (eP e))))
      (chkPtF (PT (eP e)) (fPi F) (PT (eI e)) (Nat.land (Nat.shiftRight e (nat_lit 48)) (nat_lit 7)))))))

theorem forStep_eq (FT PT OT : ℕ → ℕ) (ND NOM D e BM : ℕ) :
    forStep FT PT OT ND NOM D e BM = Bool.rec (motive := fun _ => ℕ) (Nat.lor BM (Nat.shiftLeft 1 NOM))
      (Nat.lor BM (Nat.shiftLeft 1 (eI e)))
      (andB (Nat.blt (eI e) NOM) (andB (Nat.beq (Nat.land BM (Nat.shiftLeft 1 (eI e))) 0)
        (Bool.rec (motive := fun _ => Bool) (coverB FT PT OT ND D e) (stabB FT PT D e BM)
          (Nat.beq (Nat.land e 1) 1)))) := by
  unfold forStep
  rw [strictN_eq]
  rfl

theorem forStep_cases (FT PT OT : ℕ → ℕ) (ND NOM D e BM : ℕ) :
    forStep FT PT OT ND NOM D e BM = Nat.lor BM (Nat.shiftLeft 1 NOM) ∨
    (eI e < NOM ∧ Nat.land BM (Nat.shiftLeft 1 (eI e)) = 0 ∧
      forStep FT PT OT ND NOM D e BM = Nat.lor BM (Nat.shiftLeft 1 (eI e)) ∧
      ((Nat.land e 1 ≠ 1 ∧ coverB FT PT OT ND D e = true) ∨
        (Nat.land e 1 = 1 ∧ stabB FT PT D e BM = true))) := by
  rw [forStep_eq]
  cases hc : andB (Nat.blt (eI e) NOM) (andB (Nat.beq (Nat.land BM (Nat.shiftLeft 1 (eI e))) 0)
      (Bool.rec (motive := fun _ => Bool) (coverB FT PT OT ND D e) (stabB FT PT D e BM)
        (Nat.beq (Nat.land e 1) 1)))
  · exact Or.inl rfl
  · right
    obtain ⟨h1, h23⟩ := andB_eq_true.1 hc
    obtain ⟨h2, h3⟩ := andB_eq_true.1 h23
    refine ⟨blt_eq_true.1 h1, beq_eq_true.1 h2, rfl, ?_⟩
    cases hb : Nat.beq (Nat.land e 1) 1
    · rw [hb] at h3
      exact Or.inl ⟨Nat.ne_of_beq_eq_false hb, h3⟩
    · rw [hb] at h3
      exact Or.inr ⟨Nat.eq_of_beq_eq_true hb, h3⟩

theorem coverB_spec {FT PT OT : ℕ → ℕ} {ND D e : ℕ} (h : coverB FT PT OT ND D e = true) :
    oJ (OT (eI e)) = eI e + 1 ∧
    ((fD (FT (eG e)) = D ∧ fJ (FT (eG e)) = eI e + 1 ∧ fDp (FT (eG e)) < ND) ∨
     (fDp (FT (eG e)) = D ∧ 0 < fJ (FT (eG e)) ∧ fD (FT (eG e)) < ND ∧
       ∃ hh, chkPt (PT (eI e)) (fPi (FT (eG e))) (PT (fJ (FT (eG e)) - 1)) hh = true)) := by
  unfold coverB at h
  rw [KRoute.letB_eq] at h
  obtain ⟨h1, h2⟩ := andB_eq_true.1 h
  refine ⟨beq_eq_true.1 h1, ?_⟩
  cases hb : Nat.beq (Nat.land (eR e) 1) 1
  · rw [hb] at h2
    obtain ⟨a, b⟩ := andB_eq_true.1 h2
    obtain ⟨b, c⟩ := andB_eq_true.1 b
    exact Or.inl ⟨beq_eq_true.1 a, beq_eq_true.1 b, blt_eq_true.1 c⟩
  · rw [hb] at h2
    obtain ⟨a, b⟩ := andB_eq_true.1 h2
    obtain ⟨b, c⟩ := andB_eq_true.1 b
    obtain ⟨c, d⟩ := andB_eq_true.1 c
    refine Or.inr ⟨beq_eq_true.1 a, blt_eq_true.1 b, blt_eq_true.1 c,
      Nat.land (Nat.shiftRight e 32) 7, ?_⟩
    rw [← chkPtF_eq]
    exact d

theorem testBit_of_land {BM p : ℕ} (h : 0 < Nat.land BM (Nat.shiftLeft 1 p)) : BM.testBit p = true := by
  by_contra hb
  simp only [Bool.not_eq_true] at hb
  have e : Nat.land BM (Nat.shiftLeft 1 p) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    change (BM &&& 1 <<< p).testBit j = _
    rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hj : p = j
    · subst hj
      simp [hb]
    · simp [hj]
  omega

theorem testBit_lor_shl (BM i j : ℕ) :
    (Nat.lor BM (Nat.shiftLeft 1 i)).testBit j = (BM.testBit j || decide (i = j)) := by
  change (BM ||| 1 <<< i).testBit j = _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem stabB_spec {FT PT : ℕ → ℕ} {D e BM : ℕ} (h : stabB FT PT D e BM = true) :
    fD (FT (eS e)) = D ∧ fDp (FT (eS e)) = D ∧ fJ (FT (eS e)) = 0 ∧ BM.testBit (eP e) = true ∧
      ∃ hh, chkPt (PT (eP e)) (fPi (FT (eS e))) (PT (eI e)) hh = true := by
  unfold stabB at h
  rw [KRoute.letB_eq] at h
  obtain ⟨a, h⟩ := andB_eq_true.1 h
  obtain ⟨b, h⟩ := andB_eq_true.1 h
  obtain ⟨c, h⟩ := andB_eq_true.1 h
  obtain ⟨d, h⟩ := andB_eq_true.1 h
  refine ⟨beq_eq_true.1 a, beq_eq_true.1 b, beq_eq_true.1 c, testBit_of_land (blt_eq_true.1 d),
    Nat.land (Nat.shiftRight e 48) 7, ?_⟩
  rw [← chkPtF_eq]
  exact h

@[expose] def FInv (NOM : ℕ) (P : ℕ → Prop) (BM : ℕ) : Prop :=
  BM.testBit NOM = true ∨ ∀ j, BM.testBit j = true → j < NOM ∧ P j

structure FHyp (FT PT OT : ℕ → ℕ) (ND NOM NF D : ℕ) (P : ℕ → Prop) : Prop where
  c0 : ∀ i g, i < NOM → g < NF → oJ (OT i) = i + 1 → fD (FT g) = D → fJ (FT g) = i + 1 →
    fDp (FT g) < ND → P i
  c1 : ∀ i g hh, i < NOM → g < NF → fDp (FT g) = D → 0 < fJ (FT g) → fD (FT g) < ND →
    chkPt (PT i) (fPi (FT g)) (PT (fJ (FT g) - 1)) hh = true → P i
  st : ∀ i p g hh, i < NOM → p < NOM → P p → g < NF → fD (FT g) = D → fDp (FT g) = D →
    fJ (FT g) = 0 → chkPt (PT p) (fPi (FT g)) (PT i) hh = true → P i

theorem forStep_inv {FT PT OT : ℕ → ℕ} {ND NOM NF D : ℕ} {P : ℕ → Prop}
    (H : FHyp FT PT OT ND NOM NF D P) {e BM : ℕ} (hI : FInv NOM P BM) (hfx : fixEnt NF e = true) :
    FInv NOM P (forStep FT PT OT ND NOM D e BM) := by
  rcases forStep_cases FT PT OT ND NOM D e BM with hf | ⟨hi, -, hr, hcase⟩
  · rw [hf]
    left
    rw [testBit_lor_shl]
    simp
  · rw [hr]
    rcases hI with hI | hI
    · left
      rw [testBit_lor_shl, hI]
      rfl
    · have hPi : P (eI e) := by
        unfold fixEnt at hfx
        rcases hcase with ⟨hb, hcv⟩ | ⟨hb, hst⟩
        · have hg : eG e < NF := by
            cases hbb : Nat.beq (Nat.land e 1) 1
            · rw [hbb] at hfx
              exact blt_eq_true.1 hfx
            · exact absurd (Nat.eq_of_beq_eq_true hbb) hb
          obtain ⟨hoj, hc | ⟨h1, h2, h3, hh, h4⟩⟩ := coverB_spec hcv
          · exact H.c0 _ _ hi hg hoj hc.1 hc.2.1 hc.2.2
          · exact H.c1 _ _ hh hi hg h1 h2 h3 h4
        · have hg : eS e < NF := by
            have hbb : Nat.beq (Nat.land e 1) 1 = true := by rw [hb]; rfl
            rw [hbb] at hfx
            exact blt_eq_true.1 hfx
          obtain ⟨h1, h2, h3, hp, hh, h4⟩ := stabB_spec hst
          have hpP := hI _ hp
          exact H.st _ _ _ hh hi hpP.1 hpP.2 hg h1 h2 h3 h4
      right
      intro j hj
      rw [testBit_lor_shl] at hj
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hj
      rcases hj with hj | rfl
      · exact hI j hj
      · exact ⟨hi, hPi⟩

theorem forRun_succ (FT PT OT : ℕ → ℕ) (ND NOM D C m BM : ℕ) :
    forRun FT PT OT ND NOM D C (m + 1) BM = forRun FT PT OT ND NOM D (Nat.shiftRight C 64) m
      (forStep FT PT OT ND NOM D (Nat.land C 18446744073709551615) BM) := by
  change strictN C (fun C' => strictN (Nat.land C' (nat_lit 18446744073709551615)) (fun e =>
      strictN (forStep FT PT OT ND NOM D e BM)
        (fun B => forRun FT PT OT ND NOM D (Nat.shiftRight C' (nat_lit 64)) m B))) = _
  simp only [strictN_eq]

theorem fixRun_succ (NF m C : ℕ) :
    fixRun NF (m + 1) C = andB (fixEnt NF (Nat.land C 18446744073709551615)) (fixRun NF m (Nat.shiftRight C 64)) := by
  change letB C (fun C' => andB (fixEnt NF (Nat.land C' (nat_lit 18446744073709551615)))
    (fixRun NF m (Nat.shiftRight C' (nat_lit 64)))) = _
  rw [KRoute.letB_eq]

theorem forRun_inv {FT PT OT : ℕ → ℕ} {ND NOM NF D : ℕ} {P : ℕ → Prop}
    (H : FHyp FT PT OT ND NOM NF D P) :
    ∀ m C BM, FInv NOM P BM → fixRun NF m C = true → FInv NOM P (forRun FT PT OT ND NOM D C m BM)
  | 0, _, _, hI, _ => hI
  | m + 1, C, BM, hI, hf => by
    rw [fixRun_succ] at hf
    obtain ⟨h1, h2⟩ := andB_eq_true.1 hf
    rw [forRun_succ]
    exact forRun_inv H m _ _ (forStep_inv H hI h1) h2

theorem runF_cons (k : KD) (D C : ℕ) (l : List ℕ) (x : ℕ) :
    runF k D (C :: l) x =
      runF k D l (forRun k.FT k.PT k.OT k.ND k.NOM D (Nat.shiftRight C 12) (Nat.land C 4095) x) := by
  change strictN (forRun k.FT k.PT k.OT k.ND k.NOM D (Nat.shiftRight C (nat_lit 12))
    (Nat.land C (nat_lit 4095)) x) (runF k D l) = _
  rw [strictN_eq]

theorem runF_inv {k : KD} {D : ℕ} {P : ℕ → Prop} (H : FHyp k.FT k.PT k.OT k.ND k.NOM k.NF D P) :
    ∀ (l : List ℕ) (x : ℕ), FInv k.NOM P x → fixL k.NF l = true → FInv k.NOM P (runF k D l x)
  | [], _, hI, _ => hI
  | C :: l, x, hI, hf => by
    obtain ⟨h1, h2⟩ := andB_eq_true.1 hf
    rw [runF_cons]
    exact runF_inv H l _ (forRun_inv H _ _ _ hI h1) h2

theorem fullOf_eq (k : KD) : fullOf k = 2 ^ k.NOM - 1 := by
  unfold fullOf
  change (1 <<< k.NOM) - 1 = _
  rw [Nat.one_shiftLeft]

theorem forest_all {k : KD} {D : ℕ} {P : ℕ → Prop} (H : FHyp k.FT k.PT k.OT k.ND k.NOM k.NF D P)
    {L : List ℕ} (hL : runF k D L 0 = fullOf k) (hf : fixL k.NF L = true) : ∀ j < k.NOM, P j := by
  have h0 : FInv k.NOM P 0 := Or.inr fun j hj => by rw [Nat.zero_testBit] at hj; cases hj
  have h := runF_inv H L 0 h0 hf
  rw [hL, fullOf_eq] at h
  rcases h with h | h
  · rw [Nat.testBit_two_pow_sub_one] at h
    simp at h
  · intro j hj
    exact (h j (by rw [Nat.testBit_two_pow_sub_one]; simpa using hj)).2

theorem forAll_get (k : KD) : ∀ (Ls : List (List ℕ)) (D₁ : ℕ), forAll k Ls D₁ = true →
    ∀ i (hi : i < Ls.length), runF k (D₁ + i) Ls[i] 0 = fullOf k
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | L :: Ls, D₁, h, i, hi => by
    rw [forAll_cons] at h
    obtain ⟨h1, h2⟩ := andB_eq_true.1 h
    cases i with
    | zero => exact beq_eq_true.1 h1
    | succ i =>
      have e : D₁ + (i + 1) = Nat.succ D₁ + i := by omega
      rw [e]
      exact forAll_get k Ls (Nat.succ D₁) h2 i (by simpa using hi)

theorem fixLs_get (NF : ℕ) : ∀ (Ls : List (List ℕ)), fixLs NF Ls = true →
    ∀ i (hi : i < Ls.length), fixL NF Ls[i] = true
  | [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | L :: Ls, h, i, hi => by
    obtain ⟨h1, h2⟩ := andB_eq_true.1 h
    cases i with
    | zero => exact h1
    | succ i => exact fixLs_get NF Ls h2 i (by simpa using hi)

theorem chAll_get (k : KD) : ∀ (Ls : List ((ℕ → ℕ) × (ℕ × (List ℕ × ℕ)))) (D₁ : ℕ), chAll k Ls D₁ = true →
    ∀ i (hi : i < Ls.length),
      chainRun k.FT Ls[i].1 k.LET k.W0 k.TR1 (D₁ + i) 256 Ls[i].2.1 Ls[i].2.2.1 = Ls[i].2.2.2 ∧
        0 < Ls[i].2.2.2
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | ⟨E, ne, lv, bd⟩ :: Ls, D₁, h, i, hi => by
    change andB _ _ = true at h
    obtain ⟨h1, h2⟩ := andB_eq_true.1 h
    cases i with
    | zero =>
      obtain ⟨a, b⟩ := andB_eq_true.1 h1
      exact ⟨beq_eq_true.1 a, blt_eq_true.1 (andB_eq_true.1 b).1⟩
    | succ i =>
      have e : D₁ + (i + 1) = Nat.succ D₁ + i := by omega
      rw [e]
      exact chAll_get k Ls (Nat.succ D₁) h2 i (by simpa using hi)

theorem fixDch_get (NF : ℕ) : ∀ (Ls : List ((ℕ → ℕ) × (ℕ × (List ℕ × ℕ)))), fixDch NF Ls = true →
    ∀ i (hi : i < Ls.length), allIn 0 Ls[i].2.1 (fixEt NF Ls[i].1) = true
  | [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | ⟨E, ne, lv, bd⟩ :: Ls, h, i, hi => by
    change andB _ _ = true at h
    obtain ⟨h1, h2⟩ := andB_eq_true.1 h
    cases i with
    | zero => exact h1
    | succ i => exact fixDch_get NF Ls h2 i (by simpa using hi)

theorem fixEt_spec {NF : ℕ} {ET : ℕ → ℕ} {e : ℕ} (h : fixEt NF ET e = true) (h1 : eK (ET e) = 1) :
    eA (ET e) < NF := by
  unfold fixEt at h
  rw [KRoute.letB_eq] at h
  have hb : Nat.beq (eK (ET e)) 1 = true := by rw [h1]; rfl
  rw [hb] at h
  exact blt_eq_true.1 h

@[expose] noncomputable def bdAt (k : KD) (D : ℕ) : ℕ := (k.DCH.map fun c => c.2.2.2).getD (D - 1) 1

theorem listSum_eq (B : ℕ) : ∀ L : List ((ℕ → ℕ) × (ℕ × (List ℕ × ℕ))),
    List.rec (motive := fun _ => ℕ) (nat_lit 1) (fun c _ ih => Nat.add ih (Nat.div B c.2.2.2)) L =
      1 + ∑ i ∈ Finset.range L.length, B / (L.map fun c => c.2.2.2).getD i 1
  | [] => by simp
  | c :: L => by
    change List.rec (motive := fun _ => ℕ) (nat_lit 1) (fun c _ ih => Nat.add ih (Nat.div B c.2.2.2)) L +
      B / c.2.2.2 = _
    rw [listSum_eq B L, List.length_cons, Finset.sum_range_succ']
    simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
    omega

theorem sum_erase_zero (n : ℕ) (f : ℕ → ℕ) :
    ∑ D ∈ (Finset.range (n + 1)).erase 0, f (D - 1) = ∑ i ∈ Finset.range n, f i := by
  have h := Finset.add_sum_erase (Finset.range (n + 1)) (fun D => f (D - 1))
    (Finset.mem_range.2 (Nat.succ_pos n))
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.add_sub_cancel] at h
  omega

theorem idxSum_eq {k : KD} (hl : k.DCH.length = k.ND - 1) (hnd : 0 < k.ND) :
    1 + ∑ D ∈ (Finset.range k.ND).erase 0, k.BK / bdAt k D = idxSum k := by
  unfold idxSum
  rw [listSum_eq k.BK k.DCH, hl]
  obtain ⟨n, hn⟩ : ∃ n, k.ND = n + 1 := ⟨k.ND - 1, by omega⟩
  rw [hn, Nat.add_sub_cancel]
  unfold bdAt
  rw [sum_erase_zero n (fun i => k.BK / (k.DCH.map fun c => c.2.2.2).getD i 1)]

theorem j4Ok_forest {k : KD} {d : MD} {KW MW MT : List ℕ} {FLs : List (List ℕ)}
    (h : j4Ok k d KW MW MT FLs = true) : FLs.length = k.ND - 1 ∧ forAll k FLs 1 = true := by
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨hl, h⟩ := andB_eq_true.1 h
  obtain ⟨hf, -⟩ := andB_eq_true.1 h
  exact ⟨beq_eq_true.1 hl, hf⟩

theorem kChains_dch {k : KD} (h : kChains k = true) :
    k.DCH.length = k.ND - 1 ∧ chAll k k.DCH 1 = true := by
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨hl, h⟩ := andB_eq_true.1 h
  obtain ⟨hc, -⟩ := andB_eq_true.1 h
  exact ⟨beq_eq_true.1 hl, hc⟩

theorem kRange_cov {k : KD} (h : kRange k = true) : 0 < k.ND ∧ cov0 k.FT k.ND k.cv = true := by
  obtain ⟨h0, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨hc, -⟩ := andB_eq_true.1 h
  exact ⟨blt_eq_true.1 h0, hc⟩

theorem j4Fix_refs {k : KD} {FLs : List (List ℕ)} (h : j4Fix k FLs = true) :
    k.cv < k.NF ∧ fixDch k.NF k.DCH = true ∧ fixLs k.NF FLs = true := by
  obtain ⟨h0, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨h1, h2⟩ := andB_eq_true.1 h
  exact ⟨blt_eq_true.1 h0, h1, h2⟩

theorem cov0_spec {FT : ℕ → ℕ} {ND g : ℕ} (h : cov0 FT ND g = true) :
    fD (FT g) = 0 ∧ 0 < fJ (FT g) ∧ fDp (FT g) < ND := by
  unfold cov0 at h
  rw [KRoute.letB_eq] at h
  obtain ⟨a, h⟩ := andB_eq_true.1 h
  obtain ⟨b, c⟩ := andB_eq_true.1 h
  exact ⟨beq_eq_true.1 a, blt_eq_true.1 b, blt_eq_true.1 c⟩

theorem ptOK_pt {k : KD} (o : Ok k) {i : ℕ} (hi : i < k.NOM) : ptOK (k.PT i) = true :=
  (andB_eq_true.1 ((kPts_parts o.hP).1 i hi)).1

section Group

variable {k : KD} {G : Type*} [Group G] (φ : Khat k.LET →* G) (t : G)

@[expose] noncomputable def uC (c : Khat k.LET) : G := (φ c)⁻¹ * t * φ c

theorem mr (x : Khat k.LET) : φ x ∈ φ.range := MonoidHom.mem_range.2 ⟨x, rfl⟩

variable {φ t}

theorem ev_exists (X : ℕ) : ∃ c : Khat k.LET, ev φ X = φ c := by
  unfold ev
  split_ifs with h
  · exact ⟨_, rfl⟩
  · exact ⟨1, (map_one φ).symm⟩

theorem tJ_exists {J : ℕ} (hJ : J ≠ 0) : ∃ c : Khat k.LET, tJ k φ t J = uC φ t c := by
  unfold tJ
  rw [ite_eq_right hJ]
  obtain ⟨c, hc⟩ := ev_exists (φ := φ) (oG (k.OT (J - 1)))
  rw [hc]
  exact ⟨c, rfl⟩

theorem tJ_om (o : Ok k) {j : ℕ} (hj : j < k.NOM) (hO : k.OT j ≠ 0) :
    ∃ c : Khat k.LET, actS.act (thV k) (c : GLm) = ptVecs (k.PT j) ∧ tJ k φ t (j + 1) = uC φ t c := by
  obtain ⟨-, -, c, hc, -, hact⟩ := om_spec o hj hO
  refine ⟨c, hact, ?_⟩
  unfold tJ
  rw [ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel, ev_eq φ c hc]
  rfl

theorem uC_mul (c q : Khat k.LET) : uC φ t (c * q) = (φ q)⁻¹ * uC φ t c * φ q := by
  unfold uC
  rw [map_mul]
  group

theorem uC_sq (ht : t * t = 1) (c : Khat k.LET) : uC φ t c * uC φ t c = 1 := by
  unfold uC
  calc (φ c)⁻¹ * t * φ c * ((φ c)⁻¹ * t * φ c) = (φ c)⁻¹ * (t * t) * φ c := by group
    _ = 1 := by rw [ht]; group

theorem act_inv_cancel {P : Set Vec} {a b : GLm} (h : actS.act P (b * a) = actS.act P a) :
    actS.act P b = P := by
  calc actS.act P b = actS.act (actS.act (actS.act P b) a) a⁻¹ := by
        rw [← actS.act_mul, mul_inv_cancel, actS.act_one]
    _ = P := by rw [← actS.act_mul P b a, h, ← actS.act_mul, mul_inv_cancel, actS.act_one]

@[expose] def TConj (k : KD) (φ : Khat k.LET →* G) (t : G) : Prop :=
  ∀ s : Khat k.LET, actS.act (thV k) (s : GLm) = thV k → t * φ s * t ∈ φ.range

theorem uC_rel (ht : t * t = 1) (hT : TConj k φ t) {a b : Khat k.LET}
    (hab : actS.act (thV k) (a : GLm) = actS.act (thV k) (b : GLm)) :
    (uC φ t a)⁻¹ * uC φ t b ∈ φ.range := by
  obtain ⟨s, rfl⟩ : ∃ s, b = s * a := ⟨b * a⁻¹, by group⟩
  have hs : actS.act (thV k) (s : GLm) = thV k :=
    act_inv_cancel (a := (a : GLm)) (by rw [← Subgroup.coe_mul, ← hab])
  have hs' : actS.act (thV k) ((s⁻¹ : Khat k.LET) : GLm) = thV k := by
    rw [Subgroup.coe_inv]
    calc actS.act (thV k) (s : GLm)⁻¹ = actS.act (actS.act (thV k) (s : GLm)) (s : GLm)⁻¹ := by rw [hs]
      _ = thV k := by rw [← actS.act_mul, mul_inv_cancel, actS.act_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have key : (uC φ t a)⁻¹ * uC φ t (s * a) = (φ a)⁻¹ * (t⁻¹ * φ s⁻¹ * t) * φ s * φ a := by
    unfold uC
    rw [map_mul, map_inv]
    group
  rw [key, hti]
  exact φ.range.mul_mem (φ.range.mul_mem (φ.range.mul_mem (φ.range.inv_mem (mr φ a))
    (hT _ hs')) (mr φ s)) (mr φ a)

theorem tconj (o : Ok k) (hO : Orb k) {x y z : G} (gh : GHyp k φ x y t z) {ps : Khat k.LET}
    (hps : ((ps : GLm) : Mat12) = toMat k.PS1)
    (hψ : ∀ g : Khat k.LET, ((g : GLm) : Mat12) = toMat k.TR1 → t * φ g * t = φ ps) :
    TConj k φ t := by
  intro s hs
  have hsT : (s : GLm) ∈ Tg k := ⟨TStruct.mem_Stab.2 (by rw [← TStruct.act_eq]; exact hs), s.2⟩
  obtain ⟨e, he, l, hl, hsl⟩ := T_decomp o hO hsT
  obtain ⟨v, -, hv⟩ := lam_psi o hO gh hps hψ e he
  have e1 : s = ⟨trG k e, lam_mem o e he⟩ * ⟨l, T0_le_Khat o hl⟩ := Subtype.ext hsl
  have hc := T0_comm o gh ⟨l, T0_le_Khat o hl⟩ hl
  refine MonoidHom.mem_range.2 ⟨v * ⟨l, T0_le_Khat o hl⟩, ?_⟩
  rw [map_mul, e1, map_mul, ← hv ⟨trG k e, lam_mem o e he⟩ rfl]
  calc t * φ ⟨trG k e, lam_mem o e he⟩ * t * φ ⟨l, T0_le_Khat o hl⟩ =
      t * φ ⟨trG k e, lam_mem o e he⟩ * (t * φ ⟨l, T0_le_Khat o hl⟩) := by group
    _ = t * (φ ⟨trG k e, lam_mem o e he⟩ * φ ⟨l, T0_le_Khat o hl⟩) * t := by rw [hc.eq]; group

variable {w : ℕ → G}

theorem frel_mem (hw : ∀ g < k.NF, FRel k φ t w g) {g : ℕ} (hg : g < k.NF) :
    w (fD (k.FT g)) * tJ k φ t (fJ (k.FT g)) * (w (fDp (k.FT g)) * ev φ (fPi (k.FT g)))⁻¹ ∈ φ.range :=
  hw g hg

theorem cov_of_rel {y : G} {D : ℕ} (hD : D < k.ND) {b : G} (hb : b ∈ φ.range)
    (h : y * (w D * b)⁻¹ ∈ φ.range) : y ∈ Cov φ.range w (Finset.range k.ND) := by
  have e : y = y * (w D * b)⁻¹ * w D * b := by group
  rw [e]
  exact mem_cov (Finset.mem_range.2 hD) h hb

theorem cov_transfer (ht : t * t = 1) (hT : TConj k φ t) {y : G} {a b : Khat k.LET}
    (hab : actS.act (thV k) (a : GLm) = actS.act (thV k) (b : GLm))
    (h : y * uC φ t a ∈ Cov φ.range w (Finset.range k.ND)) :
    y * uC φ t b ∈ Cov φ.range w (Finset.range k.ND) := by
  have e : y * uC φ t b = y * uC φ t a * ((uC φ t a)⁻¹ * uC φ t b) := by group
  rw [e]
  exact cov_mul_N h (uC_rel ht hT hab)

@[expose] noncomputable def gO {k : KD} (hO : Orb k) (j : ℕ) : Khat k.LET :=
  if h : j < k.NOM then ⟨(hO j h).choose, (hO j h).choose_spec.1⟩ else 1

theorem gO_act {k : KD} (hO : Orb k) {j : ℕ} (hj : j < k.NOM) :
    actS.act (thV k) (gO hO j : GLm) = ptVecs (k.PT j) := by
  unfold gO
  simp only [dite_eq_left hj]
  exact (hO j hj).choose_spec.2

theorem act_mul_khat (a q : Khat k.LET) {P Q : Set Vec} (ha : actS.act (thV k) (a : GLm) = P)
    (hq : actS.act P (q : GLm) = Q) : actS.act (thV k) ((a * q : Khat k.LET) : GLm) = Q := by
  rw [Subgroup.coe_mul, actS.act_mul, ha, hq]

theorem act_of_chkPt (o : Ok k) {p i π hh : ℕ} (hp : p < k.NOM) (hi : i < k.NOM) {q : Khat k.LET}
    (hq : ((q : GLm) : Mat12) = toMat π) (hc : chkPt (k.PT p) π (k.PT i) hh = true) :
    actS.act (ptVecs (k.PT p)) (q : GLm) = ptVecs (k.PT i) := by
  rw [TStruct.act_eq, hq]
  exact chkPt_image (ptOK_pt o hp) (ptOK_pt o hi) hc

structure CHyp (k : KD) (φ : Khat k.LET →* G) (t : G) (w : ℕ → G) : Prop where
  ht : t * t = 1
  hT : TConj k φ t
  hF : FOK k k.NF
  hw0 : w 0 = 1
  hw : ∀ g < k.NF, FRel k φ t w g
  hOJ : ∀ g < k.NF, 0 < fJ (k.FT g) → k.OT (fJ (k.FT g) - 1) ≠ 0

theorem cover_D (o : Ok k) (hO : Orb k) (H : CHyp k φ t w) {D : ℕ} {L : List ℕ}
    (hL : runF k D L 0 = fullOf k) (hf : fixL k.NF L = true) :
    ∀ j < k.NOM, w D * uC φ t (gO hO j) ∈ Cov φ.range w (Finset.range k.ND) := by
  refine forest_all ⟨?_, ?_, ?_⟩ hL hf
  ·
    intro i g hi hg hoj hD hJ hD'
    have hOT : k.OT i ≠ 0 := by
      intro h0
      rw [h0] at hoj
      exact absurd hoj (by simp [oJ])
    obtain ⟨c, hc, htc⟩ := tJ_om (φ := φ) (t := t) o hi hOT
    have hr := frel_mem H.hw hg
    rw [hD, hJ, htc] at hr
    obtain ⟨b, hb⟩ := ev_exists (φ := φ) (fPi (k.FT g))
    rw [hb] at hr
    exact cov_transfer H.ht H.hT (hc.trans (gO_act hO hi).symm) (cov_of_rel hD' ((mr φ) b) hr)
  ·
    intro i g hh hi hg hDp hJ hD0 hpt
    have hJn : fJ (k.FT g) ≤ k.NOM := (recOK_spec (H.hF g hg).1).2.2.2.1
    have hj1 : fJ (k.FT g) - 1 < k.NOM := by omega
    obtain ⟨c, hc, htc⟩ := tJ_om (φ := φ) (t := t) o hj1 (H.hOJ g hg hJ)
    rw [Nat.sub_add_cancel hJ] at htc
    obtain ⟨q, hq⟩ := (H.hF g hg).2
    have hr := frel_mem H.hw hg
    rw [hDp, htc, ev_eq φ q hq] at hr
    obtain ⟨n, hn, hn'⟩ : ∃ n ∈ φ.range,
        w (fD (k.FT g)) * uC φ t c * (w D * φ q)⁻¹ = n := ⟨_, hr, rfl⟩
    have hwD : w D = n⁻¹ * w (fD (k.FT g)) * uC φ t c * (φ q)⁻¹ := by
      rw [← hn']
      group
    have hb := act_mul_khat (gO hO i) q (gO_act hO hi) (act_of_chkPt o hi hj1 hq hpt)
    have hcb := uC_rel H.ht H.hT (hc.trans hb.symm)
    have hinv : uC φ t c = (uC φ t c)⁻¹ := eq_inv_of_mul_eq_one_left (uC_sq H.ht c)
    have e : w D * uC φ t (gO hO i) =
        n⁻¹ * w (fD (k.FT g)) * ((uC φ t c)⁻¹ * uC φ t (gO hO i * q) * (φ q)⁻¹) := by
      rw [hwD, uC_mul, ← hinv]
      group
    rw [e]
    exact mem_cov (Finset.mem_range.2 hD0) (φ.range.inv_mem hn)
      (φ.range.mul_mem hcb (φ.range.inv_mem ((mr φ) q)))
  ·
    intro i p g hh hi hp hP hg hD hDp hJ0 hpt
    obtain ⟨q, hq⟩ := (H.hF g hg).2
    have hr := frel_mem H.hw hg
    rw [hD, hDp, hJ0, tJ_zero, mul_one, ev_eq φ q hq] at hr
    have hb := act_mul_khat (gO hO p) q (gO_act hO hp) (act_of_chkPt o hp hi hq hpt)
    have e : w D * uC φ t (gO hO p * q) = w D * (w D * φ q)⁻¹ * (w D * uC φ t (gO hO p)) * φ q := by
      rw [uC_mul]
      group
    have h1 : w D * uC φ t (gO hO p * q) ∈ Cov φ.range w (Finset.range k.ND) := by
      rw [e]
      exact cov_mul_N (N_mul_cov hP hr) ((mr φ) q)
    exact cov_transfer H.ht H.hT (hb.trans (gO_act hO hi).symm) h1

theorem cover_zero (H : CHyp k φ t w) (hcv : k.cv < k.NF) (hc0 : cov0 k.FT k.ND k.cv = true)
    (c : Khat k.LET) : w 0 * uC φ t c ∈ Cov φ.range w (Finset.range k.ND) := by
  obtain ⟨h0, hJ, hD'⟩ := cov0_spec hc0
  obtain ⟨c', hc'⟩ := tJ_exists (φ := φ) (t := t) (Nat.pos_iff_ne_zero.1 hJ)
  obtain ⟨b, hb⟩ := ev_exists (φ := φ) (fPi (k.FT k.cv))
  have hr := frel_mem H.hw hcv
  rw [h0, H.hw0, one_mul, hc', hb] at hr
  have h1 := cov_of_rel hD' ((mr φ) b) hr
  have e : w 0 * uC φ t c = (φ c)⁻¹ * φ c' * uC φ t c' * ((φ c')⁻¹ * φ c) := by
    rw [H.hw0, one_mul]
    unfold uC
    group
  rw [e]
  exact cov_mul_N (N_mul_cov h1 (φ.range.mul_mem (φ.range.inv_mem ((mr φ) c))
    ((mr φ) c'))) (φ.range.mul_mem (φ.range.inv_mem ((mr φ) c'))
    ((mr φ) c))

@[expose] noncomputable def stabH (φ : Khat k.LET →* G) (w : ℕ → G) (D : ℕ) : Subgroup (Khat k.LET) :=
  (φ.range.comap (MulAut.conj (w D)).toMonoidHom).comap φ

theorem mem_stabH {D : ℕ} {m : Khat k.LET} : m ∈ stabH φ w D ↔ w D * φ m * (w D)⁻¹ ∈ φ.range := by
  simp [stabH]

theorem stab_card (H : CHyp k φ t w) {D : ℕ} {ET : ℕ → ℕ} {ne : ℕ} (lv : List ℕ)
    (hfx : ∀ e < ne, fixEt k.NF ET e = true) :
    chainRun k.FT ET k.LET k.W0 k.TR1 D 256 ne lv ≤
      Nat.card {m : Khat k.LET // w D * φ m * (w D)⁻¹ ∈ φ.range} := by
  let S : Set GLm := ((stabH φ w D).map (Khat k.LET).subtype : Set GLm)
  have hG : CFSG.Certificates.J4Chain.GivensIn pm S k.FT ET k.LET k.W0 k.TR1 D 256 ne := by
    refine ⟨fun l hl hg => ?_, fun e he h1 _ hD hDp hJ => ?_, fun hg => ?_, fun hg => ?_⟩
    · interval_cases l <;> exact (gm_false (by decide +kernel) hg).elim
    · have hg := fixEt_spec (hfx e he) h1
      obtain ⟨q, hq⟩ := (H.hF _ hg).2
      have hr := frel_mem H.hw hg
      rw [hD, hDp, hJ, tJ_zero, mul_one, ev_eq φ q hq] at hr
      refine ⟨q, ⟨q, mem_stabH.2 ?_, rfl⟩, hq⟩
      have e : w D * φ q * (w D)⁻¹ = (w D * (w D * φ q)⁻¹)⁻¹ := by group
      rw [e]
      exact φ.range.inv_mem hr
    · exact (gm_false (by decide +kernel) hg).elim
    · exact (gm_false (by decide +kernel) hg).elim
  have h1 := CFSG.Certificates.J4Chain.chainRun_le pm lv hG
  rw [Subgroup.closure_eq, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h1
  exact h1.trans (Nat.card_congr (Equiv.subtypeEquivRight fun m => mem_stabH (φ := φ) (w := w))).le

theorem cover_hyp {d : MD} {KW MW MT : List ℕ} {FLs : List (List ℕ)} (o : Ok k) (hO : Orb k)
    (hj : j4Ok k d KW MW MT FLs = true) (hfix : j4Fix k FLs = true) (H : CHyp k φ t w) :
    CFSG.Certificates.DceTwS.Hyp φ.range t (Khat k.LET) φ k.BK (Set Vec) actS.act (thV k)
      (fun j => ptVecs (k.PT j)) (gO hO) k.NOM w (Finset.range k.ND) (bdAt k) := by
  obtain ⟨hFL, hfa⟩ := j4Ok_forest hj
  obtain ⟨hDl, hch⟩ := kChains_dch o.hC
  obtain ⟨hnd, hc0⟩ := kRange_cov o.hR
  obtain ⟨hcv, hdch, hfls⟩ := j4Fix_refs hfix
  · refine
      { φN := (mr φ)
        Nφ := fun n hn => MonoidHom.mem_range.1 hn
        finM := inferInstance
        cardM := (card_khat o.hS o.hR o.hC o.hW o.hN).le
        act_one := actS.act_one
        act_mul := fun p a b => (actS.act_mul p a b).symm
        orbit := fun j hj => gO_act hO hj
        onto := fun m => orbit_pts o hO m.2
        usq := H.ht
        conj := H.hT
        zero_mem := Finset.mem_range.2 hnd
        w_zero := H.hw0
        cover := ?_
        stabD := ?_ }
    · intro D hD j hj
      rcases Nat.eq_zero_or_pos D with rfl | hpos
      · exact cover_zero H hcv hc0 _
      · have hi : D - 1 < FLs.length := by rw [hFL]; have := Finset.mem_range.1 hD; omega
        have hL := forAll_get k FLs 1 hfa (D - 1) hi
        have e : 1 + (D - 1) = D := by omega
        rw [e] at hL
        exact cover_D o hO H hL (fixLs_get k.NF FLs hfls (D - 1) hi) j hj
    · intro D hD hD0
      have hi : D - 1 < k.DCH.length := by rw [hDl]; have := Finset.mem_range.1 hD; omega
      obtain ⟨hrun, hpos⟩ := chAll_get k k.DCH 1 hch (D - 1) hi
      have e : 1 + (D - 1) = D := by omega
      rw [e] at hrun
      have hbd : bdAt k D = k.DCH[D - 1].2.2.2 := by
        unfold bdAt
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map]
      rw [hbd]
      refine ⟨hpos, ?_⟩
      rw [← hrun]
      exact stab_card H _ fun e he => allIn_spec (fixDch_get k.NF k.DCH hdch (D - 1) hi) he

theorem cover_bound {d : MD} {KW MW MT : List ℕ} {FLs : List (List ℕ)} (o : Ok k) (hO : Orb k)
    (hj : j4Ok k d KW MW MT FLs = true) (hfix : j4Fix k FLs = true) (H : CHyp k φ t w)
    (X : Set G) (hX : ∀ x ∈ X, x ∈ φ.range ∨ x = t) :
    Finite (Subgroup.closure X) ∧ Nat.card (Subgroup.closure X) ≤ k.BK * idxSum k := by
  have hb := CFSG.Certificates.DceTwS.bound (cover_hyp o hO hj hfix H) X
    fun x hx => (hX x hx).imp id Or.inl
  rw [idxSum_eq (kChains_dch o.hC).1 (kRange_cov o.hR).1] at hb
  exact hb

theorem card_xyt {d : MD} {KW MW MT : List ℕ} {FLs : List (List ℕ)} (o : Ok k) (hO : Orb k)
    (hj : j4Ok k d KW MW MT FLs = true) (hfix : j4Fix k FLs = true) (H : CHyp k φ t w) {x y : G}
    (hx : ∀ g : Khat k.LET, (g : GLm) = xh k.LET → φ g = x)
    (hy : ∀ g : Khat k.LET, (g : GLm) = yh k.LET → φ g = y) :
    Finite (Subgroup.closure ({x, y, t} : Set G)) ∧
      Nat.card (Subgroup.closure ({x, y, t} : Set G)) ≤ k.BK * idxSum k := by
  refine cover_bound o hO hj hfix H _ fun a ha => ?_
  rcases ha with rfl | rfl | rfl
  · exact Or.inl ⟨xK k.LET, hx _ rfl⟩
  · exact Or.inl ⟨yK k.LET, hy _ rfl⟩
  · exact Or.inr rfl

end Group

end CFSG.KJ4.Cover

end
