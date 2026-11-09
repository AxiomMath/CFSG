module

public import CFSG.Certificates.Kernel.Spor.RawSch3GSound
public import CFSG.Certificates.Kernel.Spor.RawSch4OSound
import all CFSG.Certificates.Kernel.Spor.RawSch3GSound
public import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def wvKC (n w m idn : Nat) (S SI : Nat → Nat) (kS TJ : Nat)
    (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idn
    (fun a _ ih => strictN ih (fun T => pcompC n w m (letterK S SI kS (stAt TJ a)) T)) wd

@[expose] noncomputable def wdOneK (n w m idn : Nat) (S SI : Nat → Nat) (kS TJ : Nat)
    (W : List (List Nat)) (j i : Nat) : Bool :=
  bAnd(wlK kS TJ (W.getD i []),
    Nat.beq (S (Nat.add j i)) (wvKC n w m idn S SI kS TJ (W.getD i [])))

@[expose] noncomputable def wordKC (n w m idn : Nat) (S SI : Nat → Nat) (wd : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) idn
    (fun z _ ih => strictN ih (fun T => strictN (icode z) (fun c =>
      pcompC n w m (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
        S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
        SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T))) wd

@[expose] noncomputable def derOneK (n w m idn : Nat) (S SI : Nat → Nat) (kO : Nat)
    (D : List (List Int)) (i : Nat) : Bool :=
  strictB (S (Nat.add kO i)) (fun sj => bAnd(lettersK (Nat.add kO i) (dword D kO (Nat.add kO i)),
    Nat.beq sj (wordKC n w m idn S SI (dword D kO (Nat.add kO i)))))

@[expose] noncomputable def headRK (n w m idn : Nat) (S : Nat → Nat) (kS kO : Nat)
    (D : List (List Int)) (nb BP : Nat) : Bool :=
  bAnd(szOK n w, bAnd(Nat.blt kS (nat_lit 128), bAnd(Nat.ble kO kS,
  bAnd(Nat.beq (Nat.add (lenW D) kO) kS,
  bAnd(allN kS (fun j => bIf(allN nb (fun t => strictB (pg w m BP t) (fun b =>
      Nat.beq (pg w m (S j) b) b)), Nat.beq (S j) idn, true)),
  allN nb (fun t => Nat.blt (pg w m BP t) n))))))

end CFSG.KS.Raw

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2 CFSG.Certificates.Native

theorem wvKC_eq (n w idn : Nat) (S SI : Nat → Nat) (kS TJ : Nat) :
    ∀ wd : List Nat, wvKC n w (mask w) idn S SI kS TJ wd = wvK n w (mask w) idn S SI kS TJ wd
  | [] => rfl
  | a :: wd => by
    have e1 : wvKC n w (mask w) idn S SI kS TJ (a :: wd) = pcompC n w (mask w)
        (letterK S SI kS (stAt TJ a)) (wvKC n w (mask w) idn S SI kS TJ wd) := by
      change strictN _ _ = _
      rw [strictN_eq]
      rfl
    have e2 : wvK n w (mask w) idn S SI kS TJ (a :: wd) = pcomp n w (mask w)
        (letterK S SI kS (stAt TJ a)) (wvK n w (mask w) idn S SI kS TJ wd) := by
      change strictN _ _ = _
      rw [strictN_eq]
      rfl
    rw [e1, e2, CFSG.KS.PK.pcompC_eq, wvKC_eq n w idn S SI kS TJ wd]

theorem wordKC_eq (n w idn : Nat) (S SI : Nat → Nat) :
    ∀ wd : List Int, wordKC n w (mask w) idn S SI wd = wordK n w (mask w) idn S SI wd
  | [] => rfl
  | z :: wd => by
    have e1 : wordKC n w (mask w) idn S SI (z :: wd) = strictN (wordKC n w (mask w) idn S SI wd)
        (fun T => strictN (icode z) (fun c => pcompC n w (mask w)
          (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
            S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
            SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T)) := rfl
    have e2 : wordK n w (mask w) idn S SI (z :: wd) = strictN (wordK n w (mask w) idn S SI wd)
        (fun T => strictN (icode z) (fun c => pcomp n w (mask w)
          (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
            S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
            SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T)) := rfl
    rw [e1, e2, strictN_eq, strictN_eq, strictN_eq, strictN_eq, CFSG.KS.PK.pcompC_eq,
      wordKC_eq n w idn S SI wd]

theorem headK_of_parts {n w kS kO nb BP : Nat} {S SI : Nat → Nat} {D : List (List Int)}
    (hr : headRK n w (mask w) (pidn n w) S kS kO D nb BP = true)
    (hp : ∀ j < kS, permOK n w (mask w) (n * w) (S j) (SI j) = true) (N : Nat) (hN : kO + N = kS)
    (hd : ∀ i < N, derOneK n w (mask w) (pidn n w) S SI kO D i = true) :
    headK n w (mask w) (n * w) (pidn n w) S SI kS kO D nb BP = true := by
  unfold headRK at hr
  rw [bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  unfold headK
  rw [bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff]
  refine ⟨h1, h2, h3, h4, allN_iff.2 hp, allN_iff.2 fun j hj => ?_, h5, h6⟩
  cases hc : Nat.blt j kO with
  | true => rfl
  | false =>
    have hk : kO ≤ j := Nat.not_lt.mp fun h => by rw [Nat.blt_eq.mpr h] at hc; cases hc
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
    have h := hd i (by omega)
    unfold derOneK at h
    rw [wordKC_eq] at h
    exact h

theorem wdsK_of_one {n w kS TJ : Nat} {S SI : Nat → Nat} {idn : Nat} :
    ∀ (W : List (List Nat)) (j N : Nat), W.length = N → j + N = kS →
      (∀ i < N, wdOneK n w (mask w) idn S SI kS TJ W j i = true) →
      wdsK n w (mask w) idn S SI kS TJ W j = true
  | [], j, N, hN, hk, _ => by
    have hj : j = kS := by simp at hN; omega
    subst hj
    exact Nat.beq_refl j
  | wd :: W, j, N, hN, hk, h => by
    have hN' : N = W.length + 1 := by simp at hN; omega
    subst hN'
    have e : wdsK n w (mask w) idn S SI kS TJ (wd :: W) j = bAnd(wlK kS TJ wd,
        bAnd(Nat.beq (S j) (wvK n w (mask w) idn S SI kS TJ wd),
          wdsK n w (mask w) idn S SI kS TJ W (Nat.succ j))) := rfl
    have h0 := h 0 (by omega)
    unfold wdOneK at h0
    simp only [List.getD_cons_zero, Nat.add_eq, Nat.add_zero, bAnd_iff, wvKC_eq] at h0
    rw [e, bAnd_iff, bAnd_iff]
    refine ⟨h0.1, h0.2, wdsK_of_one W (Nat.succ j) W.length rfl (by omega) fun i hi => ?_⟩
    have hi' := h (i + 1) (by omega)
    unfold wdOneK at hi' ⊢
    have ea : Nat.add j (i + 1) = Nat.add (Nat.succ j) i := by simp only [Nat.add_eq]; omega
    rwa [List.getD_cons_succ, ea] at hi'

theorem wordEqK_of_headK {n w kS kO nb BP : Nat} {S SI : Nat → Nat} {D : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO D nb BP = true) {j : Nat}
    (hj1 : kO ≤ j) (hj2 : j < kS) :
    CFSG.KS.Prim.wordEqK n w (mask w) (pidn n w) S SI j (dword D kO j) (S j) = true := by
  unfold headK at hh
  rw [bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff] at hh
  obtain ⟨hsz, -, -, -, -, hd, -⟩ := hh
  have h : bIf(Nat.blt j kO, true, strictB (S j) (fun sj => bAnd(lettersK j (dword D kO j),
      Nat.beq sj (wordK n w (mask w) (pidn n w) S SI (dword D kO j))))) = true :=
    allN_iff.1 hd j hj2
  cases hc : Nat.blt j kO with
  | true => exact absurd (Nat.blt_eq.mp hc) (by omega)
  | false =>
    rw [hc] at h
    have es : ∀ y (k : Nat → Bool), strictB y k = k y := fun y k => by cases y <;> rfl
    change strictB (S j) (fun sj => bAnd(lettersK j (dword D kO j),
      Nat.beq sj (wordK n w (mask w) (pidn n w) S SI (dword D kO j)))) = true at h
    rw [es, bAnd_iff] at h
    unfold CFSG.KS.Prim.wordEqK
    rw [bAnd_iff, bAnd_iff, Nat.eq_of_beq_eq_true h.2]
    exact ⟨hsz, h.1, Nat.beq_refl _⟩

theorem gensJ_mem {n w kS kO nb BP TJ : Nat} {S SI : Nat → Nat} {D : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO D nb BP = true)
    (hJ : allN kO (fun j => anyLt (Nat.shiftRight (stCnt TJ) (nat_lit 1))
      (fun a => Nat.beq (stAt TJ a) j)) = true) :
    ∀ j', 0 ≤ j' → j' < kS → pp n w (S j') ∈ Submonoid.closure (LJ n w S kS TJ) := by
  unfold headK at hh
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  obtain ⟨hsz, _, _, _, hperm, hder, _, _⟩ := hh
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hinvM : ∀ g ∈ Submonoid.closure (LJ n w S kS TJ), g⁻¹ ∈ Submonoid.closure (LJ n w S kS TJ) :=
    fun g hg => inv_mem_closure hg
  intro j _
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjk : j < kO
    · obtain ⟨a, ha, e⟩ := anyLt_spec (allN_iff.1 hJ j hjk)
      have ea := Nat.eq_of_beq_eq_true e
      apply Submonoid.subset_closure
      refine ⟨a, ha, by rw [ea]; exact hj, ?_⟩
      unfold lp
      rw [ea, if_pos hj]
    · have := allN_iff.1 hder j hj
      rw [bIf_eq, ite_eq_right (by rw [blt_dec]; simpa using hjk), strictB_eq, Bool.and_eq_true,
        beq_dec, decide_eq_true_iff] at this
      obtain ⟨hl, he⟩ := this
      obtain ⟨g, hg, hgm⟩ := wordK_mem hn24 hw (j := j) (M := Submonoid.closure (LJ n w S kS TJ))
        (fun h hh' => ⟨pp n w (S h), (prep_pp (allN_iff.1 hperm h (by omega))).1,
          (prep_pp (allN_iff.1 hperm h (by omega))).2, ih h hh' (Nat.zero_le _) (by omega)⟩)
          hinvM _ hl
      have hSj : PRep n w (wordK n w (mask w) (pidn n w) S SI (dword D kO j)) (pp n w (S j)) := by
        rw [← he]
        exact (prep_pp (allN_iff.1 hperm j hj)).1
      rw [prep_unique hSj hg]
      exact hgm

theorem schK_of_sch3GLJ {n w kS kO BP i D NSi N1 N2 CH TJ : Nat} {S SI LR TR TRI U : Nat → Nat}
    {W : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO W (i + 3) BP = true)
    (hl : LevelsOK n w S SI LR TR TRI kS (i + 3) BP)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (h12 : lv12K w (mask w) S SI kS BP i (stepsAt n w S kS BP (i + 1))
      (stepsAt n w S kS BP (i + 1 + 1)) = true)
    (hU : utabF n w (mask w) (n * w) LR TR U i D = true)
    (hJ : allN kO (fun j => anyLt (Nat.shiftRight (stCnt TJ) (nat_lit 1))
      (fun a => Nat.beq (stAt TJ a) j)) = true)
    (hc : rcnt (LR i) ≤ NSi * CH)
    (hs : ∀ s < NSi, sch3F n w (mask w) (n * w) S SI LR TR TRI U kS BP i TJ D (s * CH) CH = true)
    (hc1 : rcnt (LR (i + 1)) ≤ N1 * CH)
    (hs1 : ∀ s < N1, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 3) (i + 1)
      (stepsAt n w S kS BP (i + 1)) (s * CH) CH = true)
    (hc2 : rcnt (LR (i + 1 + 1)) ≤ N2 * CH)
    (hs2 : ∀ s < N2, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 3) (i + 1 + 1)
      (stepsAt n w S kS BP (i + 1 + 1)) (s * CH) CH = true)
    (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 3) i
      (stepsAt n w S kS BP i) h₀ cnt = true :=
  schK_of_sch3GLM hh hl hinv h12 hU (gensJ_mem hh hJ) hc hs hc1 hs1 hc2 hs2 h₀ cnt

end CFSG.KS.Raw.Orb

end
