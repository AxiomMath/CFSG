module

public import Certificates.Data.Kernel.LocalQT.LatE
public import Certificates.Data.Kernel.LocalQT.ChainInj
public import CFSG.Certificates.Kernel.LocalQTLatSound
import CFSG.Certificates.Kernel.LocalQTDiagExtSound
import CFSG.Certificates.Kernel.LocalQTLatSixCSound
import CFSG.Certificates.Kernel.LocalQTChainMSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExtCheck

public section

namespace CFSG.KC.LQT.L

open Equiv CFSG.KC.Ord CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

theorem diagExtC_sound {n₁ n₂ : ℕ} (h : n₁ + n₂ ≤ 32) {d N M : ℕ}
    (A : List (Perm (Fin n₁))) (B : List (Perm (Fin n₂))) (CA : List Lvl)
    (WA : List (List (List ℕ))) (CB : List Lvl) (WB : List (List (List ℕ))) (CD : List Lvl)
    (WD : List (List (List ℕ))) (hIA : chainInj n₁ CA = true) (hIB : chainInj n₂ CB = true)
    (hID : chainInj (n₁ + n₂) CD = true)
    (hc : diagExtC n₁ n₂ d (A.map code) (B.map code) N M CA WA CB WB CD WD = true) :
    diagExtOK (RN.enc : Perm (Fin n₁) → RN n₁)
      (RN.enc : Perm (Fin n₂) → RN n₂) d A B N M = true :=
  CFSG.KC.LQT.CM.diagExtC_sound h A B CA WA CB WB CD WD hIA hIB hID hc

theorem perf_sound {n : ℕ} (hn : n ≤ 32) (G : List (Perm (Fin n))) (P : List (List CommWord))
    (h : perfK n (G.map code) P = true) : perfOK (RN.enc : Perm (Fin n) → RN n) G P = true :=
  CFSG.KC.LQT.CM.perf_sound hn G P h

theorem latG_intro {n d msz k L K : ℕ} {C : List Lvl} {MG TG sizes lab : List ℕ}
    {lat : List (List ℕ)} {MW : List (List (List ℕ))} {T : List (List ℕ)} {ms : List MemG}
    {reps : List (ℕ × ℕ × List (List ℕ))} {joins : List (ℕ × ℕ × ℕ × List (List ℕ))}
    (h0 : memsOKG TG lat ms = true) (h1 : chainOK n C = true)
    (h2 : grpT n C (chainF C) MG MW k T L d = true) (h3 : allA ms (closedMG n d) = true)
    (h4 : Option.rec (motive := fun _ => Bool) false
      (fun Tm => coverG n C (chainF C) Tm K lab reps) (getO ms 0) = true)
    (h5 : repsG n TG ms reps = true) (h6 : joinsG n ms joins = true)
    (h7 : sizesG (chainF C) ms sizes msz = true) (h8 : tleC n C (chainF C) TG = true) :
    latG n C d MG MW k T L TG lat ms K lab reps joins sizes msz = true := by
  rw [latG, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  rfl

theorem coverG_intro {n F K : ℕ} {C : List Lvl} {Tm : MemG} {lab : List ℕ}
    {reps : List (ℕ × ℕ × List (List ℕ))} (ha : coverA n C F Tm K lab reps = true)
    (hd : coverD n Tm K lab reps = true) (hc : coverN n F Tm reps = true) :
    coverG n C F Tm K lab reps = true := by
  rw [coverG, ha, hd, hc]
  rfl

@[expose] noncomputable def coverPt (n : Nat) (C : List Lvl) (a t b : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun lv _ _ =>
    orB (notB (andB (Nat.blt lv.1 n) (Nat.blt (P.img b lv.1) n)))
      (notB (Nat.beq (getK lv.2.1 (P.img a (P.img t (P.img b lv.1)))) 0))) C

@[expose] noncomputable def coverDQ (n : Nat) (A : (Nat → Bool) → Bool) (Tm : MemG) (K : Nat)
    (lab : List Nat) (reps : List (Nat × Nat × List (List Nat))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r rs ih => andB
    (P.letB (P.inv n r.1) fun a => P.letB (incK n K lab r.1) fun kr =>
      allA rs fun r' => orB (notB (Nat.beq kr (incK n K lab r'.1)))
        (A fun t => notB (andB (coverPt n Tm.2.1 a t r'.1)
          (memG n Tm (P.mul n (P.mul n a t) r'.1))))) ih) reps

@[expose] noncomputable def coverDL (n : Nat) (Tm : MemG) (TE : List Nat) (K : Nat)
    (lab : List Nat) (reps : List (Nat × Nat × List (List Nat))) : Bool :=
  andB (allChain n Tm.2.1 fun t => CFSG.KC.LQT.S.memL t TE) (coverDQ n (P.allL TE) Tm K lab reps)

@[expose] noncomputable def coverNP (n F : Nat) (Tm : MemG)
    (reps : List (Nat × Nat × List (List Nat))) : Bool :=
  Nat.beq (List.rec (motive := fun _ => Nat) 0 (fun r _ ih => Nat.add ih
    (CFSG.KC.Loop.strictN (P.inv n r.1) fun a => CFSG.KC.Loop.strictN
      (CFSG.KC.LQT.PH.cntFrom n Tm.2.1 (fun t => andB (coverPt n Tm.2.1 a t r.1)
        (memG n Tm (P.mul n (P.mul n a t) r.1))) (P.one n))
      fun k => Bool.rec (motive := fun _ => Nat) (Nat.add F 1)
        (Nat.div (Nat.mul (chainF Tm.2.1) (chainF Tm.2.1)) k)
        (Nat.beq (Nat.mod (Nat.mul (chainF Tm.2.1) (chainF Tm.2.1)) k) 0))) reps) F

theorem img_mul_lt {n s t i : ℕ} (hi : i < n) : P.img (P.mul n s t) i = P.img s (P.img t i) := by
  rw [P.img_eq, P.mul, P.ofFn_eq, P.E_digit (fun j _ => by rw [P.img_eq]; omega) hi]

theorem coverPt_of_memG {n : ℕ} {Tm : MemG} {a t b : ℕ}
    (h : memG n Tm (P.mul n (P.mul n a t) b) = true) : coverPt n Tm.2.1 a t b = true := by
  obtain ⟨G, C, W⟩ := Tm
  cases C with
  | nil => rfl
  | cons lv C =>
    change orB (notB (andB (Nat.blt lv.1 n) (Nat.blt (P.img b lv.1) n)))
      (notB (Nat.beq (getK lv.2.1 (P.img a (P.img t (P.img b lv.1)))) 0)) = true
    rw [P.orB_iff, P.notB_iff, P.notB_iff, P.andB_iff, P.blt_iff, P.blt_iff, P.beq_iff]
    by_cases hb : lv.1 < n ∧ P.img b lv.1 < n
    · refine Or.inr fun h0 => ?_
      have e : P.img (P.mul n (P.mul n a t) b) lv.1 = P.img a (P.img t (P.img b lv.1)) := by
        rw [img_mul_lt hb.1, img_mul_lt hb.2]
      change Nat.blt (idxM n (lv :: C) (chainF (lv :: C)) _) (chainF (lv :: C)) = true at h
      rw [CFSG.KC.LQT.CM.idxM_sift] at h
      simp [CFSG.KC.LQT.CM.sift, e, h0] at h
    · exact Or.inl hb

theorem andB_coverPt (n : ℕ) (Tm : MemG) (a t b : ℕ) :
    andB (coverPt n Tm.2.1 a t b) (memG n Tm (P.mul n (P.mul n a t) b)) =
      memG n Tm (P.mul n (P.mul n a t) b) := by
  cases h : memG n Tm (P.mul n (P.mul n a t) b)
  · cases coverPt n Tm.2.1 a t b <;> rfl
  · rw [coverPt_of_memG h]
    rfl

theorem coverDQ_eq (n : ℕ) (Tm : MemG) (K : ℕ) (lab : List ℕ)
    (reps : List (ℕ × ℕ × List (List ℕ))) :
    coverDQ n (allChain n Tm.2.1) Tm K lab reps = coverD n Tm K lab reps := by
  simp only [coverDQ, coverD, P.letB_eq, andB_coverPt]

theorem allA_mono {α : Type} {f g : α → Bool} (h : ∀ x, f x = true → g x = true) :
    ∀ l : List α, allA l f = true → allA l g = true
  | [], _ => rfl
  | x :: l, hl => by
    change andB (f x) (allA l f) = true at hl
    change andB (g x) (allA l g) = true
    rw [P.andB_iff] at hl ⊢
    exact ⟨h x hl.1, allA_mono h l hl.2⟩

theorem coverDQ_mono {n : ℕ} {A B : (ℕ → Bool) → Bool} (hAB : ∀ f, A f = true → B f = true)
    (Tm : MemG) (K : ℕ) (lab : List ℕ) :
    ∀ reps : List (ℕ × ℕ × List (List ℕ)),
      coverDQ n A Tm K lab reps = true → coverDQ n B Tm K lab reps = true
  | [], _ => rfl
  | r :: rs, h => by
    obtain ⟨h1, h2⟩ := P.andB_iff.1 h
    refine P.andB_iff.2 ⟨?_, coverDQ_mono (n := n) hAB Tm K lab rs h2⟩
    simp only [P.letB_eq] at h1 ⊢
    refine allA_mono (fun r' hr' => ?_) rs h1
    rw [P.orB_iff] at hr' ⊢
    exact hr'.imp id (hAB _)

theorem chainFrom_mono {n : ℕ} {f g : ℕ → Bool} (h : ∀ x, f x = true → g x = true) :
    ∀ (C : List Lvl) (p : ℕ), chainFrom n C f p = true → chainFrom n C g p = true
  | [], p, hf => h p hf
  | lv :: C, p, hf => by
    change P.allN n (fun j => P.impB (notB (Nat.beq (getK lv.2.1 j) 0))
      (P.letB (P.mul n p (getK lv.2.1 j)) (chainFrom n C f))) = true at hf
    change P.allN n (fun j => P.impB (notB (Nat.beq (getK lv.2.1 j) 0))
      (P.letB (P.mul n p (getK lv.2.1 j)) (chainFrom n C g))) = true
    rw [P.allN_iff] at hf ⊢
    intro j hj
    have hj' := hf j hj
    rw [P.impB_iff, P.letB_eq] at hj' ⊢
    exact fun hu => chainFrom_mono h C _ (hj' hu)

theorem memL_iff_mem (c : ℕ) : ∀ l : List ℕ, CFSG.KC.LQT.S.memL c l = true ↔ c ∈ l
  | [] => by simp [CFSG.KC.LQT.S.memL]
  | x :: l => by
    change orB (Nat.beq c x) (CFSG.KC.LQT.S.memL c l) = true ↔ _
    rw [P.orB_iff, Nat.beq_eq, memL_iff_mem c l, List.mem_cons]

theorem coverDL_sound {n : ℕ} {Tm : MemG} {TE : List ℕ} {K : ℕ} {lab : List ℕ}
    {reps : List (ℕ × ℕ × List (List ℕ))} (h : coverDL n Tm TE K lab reps = true) :
    coverD n Tm K lab reps = true := by
  rw [coverDL, P.andB_iff] at h
  rw [← coverDQ_eq]
  exact coverDQ_mono (fun f hf => chainFrom_mono (fun t ht =>
    (P.allL_iff TE f).1 hf t ((memL_iff_mem t TE).1 ht)) Tm.2.1 (P.one n) h.1) Tm K lab reps h.2

theorem coverNP_eq (n F : ℕ) (Tm : MemG) (reps : List (ℕ × ℕ × List (List ℕ))) :
    coverNP n F Tm reps = coverN n F Tm reps := by
  simp only [coverNP, coverN, CFSG.KC.LQT.CM.strictN_eq, andB_coverPt]

@[expose] def repsWith {n : ℕ} (cs : List ℕ) (reps : List (Perm (Fin n) × ℕ × List (List ℕ))) :
    List (ℕ × ℕ × List (List ℕ)) :=
  List.zipWith (fun k r => (k, r.2.1, r.2.2)) cs reps

@[expose] noncomputable def repsCodesOK {n : ℕ} : List ℕ → List (Perm (Fin n) × ℕ × List (List ℕ)) → Bool
  | [], [] => true
  | k :: cs, r :: reps => andB (Nat.beq (code r.1) k) (repsCodesOK cs reps)
  | _, _ => false

theorem repsCode_eq_with {n : ℕ} (c : LatCert (Perm (Fin n))) (cs : List ℕ)
    (h : repsCodesOK cs c.reps = true) : repsCode c = repsWith cs c.reps := by
  rw [repsCode, repsWith]
  generalize c.reps = l at h
  induction l generalizing cs with
  | nil => cases cs <;> simp_all [repsCodesOK]
  | cons r l ih =>
    cases cs with
    | nil => simp [repsCodesOK] at h
    | cons k cs =>
      rw [repsCodesOK, P.andB_iff, P.beq_iff] at h
      rw [List.map_cons, List.zipWith_cons_cons, h.1, ih cs h.2]

theorem latG_sound {n : ℕ} (hn : n ≤ 32) (C : List Lvl) (MW : List (List (List ℕ))) (k : ℕ)
    (T : List (List ℕ)) (L : ℕ) (ms : List MemG) (K : ℕ) (lab : List ℕ)
    (hI : chainInj n C = true) (hIm : allA ms (fun m => chainInj n m.2.1) = true)
    (c : LatCert (Perm (Fin n)))
    (h : latG n C c.depth (c.mGens.map code) MW k T L (c.tGens.map code)
      (c.lat.map (List.map code)) ms K lab (repsCode c) c.joins c.sizes c.msize = true) :
    c.check RN.enc = true :=
  CFSG.KC.LQT.CM.latG_sound hn C MW k T L ms K lab hI hIm c h

theorem containsG_sound {n : ℕ} (hn : n ≤ 32) (ms : List MemG)
    (hIm : allA ms (fun m => chainInj n m.2.1) = true) (c : LatCert (Perm (Fin n)))
    (A : List (Perm (Fin n))) {d k s : ℕ}
    (h : containsG n d (c.tGens.map code) (c.lat.map (List.map code)) ms c.sizes (A.map code) k
      s = true) :
    (List.range k).all (fun j => c.sizes.getD j 0 != s ||
      A.all fun g => (elts (RN.enc : Perm (Fin n) → RN n) d ((c.tGens :: c.lat).getD j [])).contains
        (RN.enc g)) = true :=
  CFSG.KC.LQT.CM.containsG_sound hn ms hIm c A h

end CFSG.KC.LQT.L

end
