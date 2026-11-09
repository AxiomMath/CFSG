module

public import CFSG.Certificates.Kernel.LceSP.HeLab
public import CFSG.Certificates.Kernel.Common.LabM
public import CFSG.Certificates.Kernel.LceSP.LabFLab
import CFSG.Certificates.Kernel.LceSP.Main
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.Certificates.LceP.LabFM

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop CFSG.KC.LabG CFSG.Certificates.LceP
  CFSG.Certificates.LceP.HeL CFSG.Certificates.LceP.LabFL CFSG.KC.LabM
open CFSG.KC.HeB hiding labInv lpush pushFwd pushInv pushLab labGo labWalk labStep labChunk runLab
  cycLab cycRed cycOK target hintsLt

@[expose] noncomputable def labOkM (blk WT RT ST LB MB : Nat → Nat)
    (INV INV8 L nC nCa nf m Hs nR nS K S0 S1 X0 X1 : Nat) (Cs : List Nat) : Bool :=
  andB (wordsOK WT RT ST INV INV8 m Hs)
  (andB (CFSG.KC.Bind.hintsOK WT m nR nS Hs)
  (andB (CFSG.Certificates.LCE.relsNorm RT nR)
  (andB (invOK INV INV8 L)
  (andB (Nat.beq nC nCa)
  (andB (Nat.ble nCa (nat_lit 1048576))
  (andB (Nat.blt nf (nat_lit 4294967296))
  (andB (Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)))
  (andB (Nat.beq S1 (mkS nf nCa))
  (andB (Nat.beq X0 (nat_lit 1))
  (andB (Nat.beq X1 (Nat.succ nf))
  (andB (CFSG.KC.LabF.hintsLt WT m K Hs)
  (andB (HeB.labsWF LB nf)
  (andB (Nat.beq (LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1))
  (andB (Nat.beq (runFacts blk WT INV nC L Cs S0) S1)
    (Nat.beq (runLabM WT LB MB Hs Cs X0) X1)))))))))))))))

theorem andB_introM {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true :=
  (andB_iff a b).2 ⟨ha, hb⟩

theorem labOkM_intro {blk WT RT ST LB MB : Nat → Nat}
    {INV INV8 L nC nCa nf m Hs nR nS K S0 S1 X0 X1 : Nat} {Cs : List Nat}
    (h1 : wordsOK WT RT ST INV INV8 m Hs = true)
    (h1a : CFSG.KC.Bind.hintsOK WT m nR nS Hs = true)
    (h1b : CFSG.Certificates.LCE.relsNorm RT nR = true) (h2 : invOK INV INV8 L = true)
    (h3 : Nat.beq nC nCa = true) (h4 : Nat.ble nCa (nat_lit 1048576) = true)
    (h5 : Nat.blt nf (nat_lit 4294967296) = true)
    (h6 : Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)) = true) (h7 : Nat.beq S1 (mkS nf nCa) = true)
    (h8 : Nat.beq X0 (nat_lit 1) = true) (h9 : Nat.beq X1 (Nat.succ nf) = true)
    (h10 : CFSG.KC.LabF.hintsLt WT m K Hs = true) (h11 : HeB.labsWF LB nf = true)
    (h12 : Nat.beq (LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1) = true)
    (h13 : Nat.beq (runFacts blk WT INV nC L Cs S0) S1 = true)
    (h14 : Nat.beq (runLabM WT LB MB Hs Cs X0) X1 = true) :
    labOkM blk WT RT ST LB MB INV INV8 L nC nCa nf m Hs nR nS K S0 S1 X0 X1 Cs = true :=
  andB_introM h1 (andB_introM h1a (andB_introM h1b (andB_introM h2 (andB_introM h3
    (andB_introM h4 (andB_introM h5 (andB_introM h6 (andB_introM h7 (andB_introM h8
    (andB_introM h9 (andB_introM h10 (andB_introM h11 (andB_introM h12
    (andB_introM h13 h14))))))))))))))

theorem readsM_succ (MB : ℕ → ℕ) (ft n k R : ℕ) :
    readsM MB ft n (k + 1) R =
      if Nat.beq (Nat.sub n (Nat.succ k)) ft = true then readsM MB ft n k R
      else andB (Nat.blt 0 (MB (Nat.shiftRight (Nat.land R 4294967295) 1)))
        (readsM MB ft n k (Nat.shiftRight R 32)) :=
  brec_eq _ _ _

theorem pos_of_bltM {a : ℕ} (h : Nat.blt 0 a = true) : 0 < a := by
  rwa [Nat.blt_eq] at h

variable {G : Type*} [Group G] (u : ℕ → G)

section Walks

variable (gen : ℕ → G)

@[expose] def RefsLM (blk LB MB : ℕ → ℕ) (rep : ℕ → G) (i : ℕ) : Prop :=
  ∀ h < i, (0 < MB h → el gen rep (fct blk h) = lab u (LB h)) ∧
    lv gen (fic (fct blk h)) = (lv gen (fc (fct blk h)))⁻¹ ∧ labWF (LB h) = true

theorem WL_refM {li : ℕ → ℕ} (hli : LIOk u li) {blk LB MB : ℕ → ℕ} {rep : ℕ → G}
    {s W ft p st acc i e : ℕ} {a b : G} (hI : WL u gen rep s W ft a b p st acc) (hp : p + 1 < 2048)
    (hpf : p ≠ ft) (hrefs : RefsLM u gen blk LB MB rep i) (hm : Nat.shiftRight e 1 < i → 0 < MB (Nat.shiftRight e 1)) :
    WL u gen rep s W ft a b (p + 1) (refStep blk i e st)
      (pushLab li (LB (Nat.shiftRight e 1)) (Nat.land e 1) acc) := by
  unfold refStep
  rw [brec_eq]
  split_ifs with hh
  · rw [Nat.blt_eq] at hh
    simp only [strictN_eq]
    obtain ⟨h1', h2, h3⟩ := hrefs _ hh
    have h1 := h1' (hm hh)
    have hpl := fun hcl hc => pushLab_spec u hli (dir := Nat.land e 1) (acc := acc) h3 hcl hc
    rw [brec_eq]
    split_ifs with hd
    · rw [Nat.beq_eq] at hd
      refine WL_sB u gen hI hp (l := (lab u (LB (Nat.shiftRight e 1)))⁻¹) (fun hcl hc => ?_) hpf
        (by rw [h1]) h2
      obtain ⟨c1, c2, c3⟩ := hpl hcl hc
      rw [ite_eq_left hd] at c3
      exact ⟨c1, c2, c3⟩
    · rw [Nat.beq_eq] at hd
      refine WL_sF u gen hI hp (l := lab u (LB (Nat.shiftRight e 1))) (fun hcl hc => ?_)
        (Or.inl ⟨hpf, h1⟩)
      obtain ⟨c1, c2, c3⟩ := hpl hcl hc
      rw [ite_eq_right hd] at c3
      exact ⟨c1, c2, c3⟩
  · exact Or.inl rfl

theorem walk_jointM {li : ℕ → ℕ} (hli : LIOk u li) {blk LB MB : ℕ → ℕ} {rep : ℕ → G}
    {s W ft i Ri Li n : ℕ} (hrefs : RefsLM u gen blk LB MB rep i) (hn : n < 1024)
    (hLi : labWF Li = true) :
    ∀ k ≤ n, ∀ J st acc, (readsM MB ft n k J = true ∨ ∀ h < i, 0 < MB h) →
      WL u gen rep s W ft (el gen rep Ri) (lab u Li) (n - k) st acc →
      WL u gen rep s W ft (el gen rep Ri) (lab u Li) n (walkGo blk i Ri ft n k J st)
        (labGo li LB Li ft n k J acc)
  | 0, _, J, st, acc, _, hI => by
    change WL u gen rep s W ft (el gen rep Ri) (lab u Li) n st acc
    simpa using hI
  | k + 1, hk, J, st, acc, hr, hI => by
    rw [walkGo_succ', labGo_succ']
    rw [readsM_succ] at hr
    have e : n - k = n - (k + 1) + 1 := by omega
    split_ifs at hr ⊢ with hp
    · rw [Nat.beq_eq] at hp
      refine walk_jointM hli hrefs hn hLi k (by omega) _ _ _ hr ?_
      rw [e]
      obtain ⟨hn', -⟩ := labWF_spec hLi
      refine WL_sF u gen hI (by omega) (fun hcl hc => ?_) (Or.inr ⟨hp, rfl, rfl⟩)
      obtain ⟨c1, c2, c3⟩ := pushFwd_spec u hli (L := Li) (acc := acc) hcl (by omega)
      exact ⟨c1, by omega, c3⟩
    · rw [Nat.beq_eq] at hp
      refine walk_jointM hli hrefs hn hLi k (by omega) _ _ _
        (hr.imp (fun h => ((andB_iff _ _).1 h).2) id) ?_
      rw [e]
      refine WL_refM u gen hli hI (by omega) hp hrefs (fun hh => ?_)
      rcases hr with h | h
      · exact pos_of_bltM ((andB_iff _ _).1 h).1
      · exact h _ hh

theorem cyc_jointM {li : ℕ → ℕ} (hli : LIOk u li) {blk LB MB : ℕ → ℕ} {rep : ℕ → G}
    {s W n nf : ℕ} (hrefs : RefsLM u gen blk LB MB rep nf) (hn : n < 1024) :
    ∀ k ≤ n, ∀ R st acc, readsM MB 2048 n k R = true → WL u gen rep s W n 1 1 (n - k) st acc →
      WL u gen rep s W n 1 1 n (cycWalk blk nf k R st) (cycLab li LB k R acc)
  | 0, _, R, st, acc, _, hI => by
    change WL u gen rep s W n 1 1 n st acc
    simpa using hI
  | k + 1, hk, R, st, acc, hr, hI => by
    rw [cycWalk_succ, cycLab_succ]
    rw [readsM_succ, if_neg (by rw [Nat.beq_eq]; change ¬ n - (k + 1) = 2048; omega)] at hr
    obtain ⟨hm, hr'⟩ := (andB_iff _ _).1 hr
    refine cyc_jointM hli hrefs hn k (by omega) _ _ _ hr' ?_
    rw [show n - k = n - (k + 1) + 1 by omega]
    exact WL_refM u gen hli hI (by omega) (by omega) hrefs (fun _ => pos_of_bltM hm)

theorem walk_factM {blk LB MB : ℕ → ℕ} {rep : ℕ → G}
    {INV nC i R w fs ft J hh : ℕ}
    (h : walkOK blk INV nC i R w fs ft J = true)
    (hl : LabF.labGo LB (LB i) ft (wLen w) (wLen w) (Nat.shiftRight J 53) 0 = LabF.target w hh)
    (hr : readsM MB ft (wLen w) (wLen w) (Nat.shiftRight J 53) = true ∨ ∀ h < i, 0 < MB h)
    (hfs : fs < 1048576) (hrefs : RefsLM u gen blk LB MB rep i) (hrep0 : rep 0 = 1)
    (hLi : labWF (LB i) = true)
    (h2 : wKind w = 2 → bv gen (wWord w) (wLen w) = 1)
    (h3 : wKind w = 3 → Clean (LabF.target w hh) →
      bv gen (wWord w) (wLen w) = lab u (LabF.target w hh)) :
    recOK INV nC R = true ∧ el gen rep R = lab u (LB i) := by
  rw [labGoF] at hl
  unfold walkOK at h
  simp only [andB_iff, orB_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at h
  obtain ⟨hrec, hft, hkind, hwalk⟩ := h
  refine ⟨hrec, ?_⟩
  have hn := wLen_lt w
  have h0 : WL u gen rep fs (wWord w) ft (el gen rep R) (lab u (LB i)) (wLen w - wLen w)
      (wStart fs (wWord w)) 0 := by
    rw [Nat.sub_self]
    exact WL_start u gen hfs
  have hW := walk_jointM u gen (xi_ok u) (Ri := R) hrefs hn hLi (wLen w) le_rfl
    (Nat.shiftRight J 53) _ _ hr h0
  rw [hwalk, hl] at hW
  rcases hW with hd | ⟨hcl, -, cur, hcur, hst, -, hX2⟩
  · omega
  · have hc : cur = fs := by omega
    rw [hc] at hX2
    obtain ⟨A, B, e1, e2⟩ := hX2 hft
    have hT : rep fs * bv gen (wWord w) (wLen w) * (rep fs)⁻¹ = lab u (LabF.target w hh) := by
      rcases hkind with hk | ⟨hk, hfs0⟩
      · have hb : Nat.beq (wKind w) 3 = false := by
          cases hq : Nat.beq (wKind w) 3
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hq) (by omega)
        have ht : LabF.target w hh = 0 := by
          unfold LabF.target
          rw [hb]
        rw [h2 hk, ht, lab_zero, mul_one, mul_inv_cancel]
      · rw [hfs0, hrep0, h3 hk hcl, one_mul, inv_one, mul_one]
    rw [hT, e2] at e1
    exact (mul_left_cancel (mul_right_cancel e1)).symm

@[expose] def LInvM (blk LB MB : ℕ → ℕ) (INV nC i N : ℕ) : Prop :=
  (∀ h < i, recOK INV nC (fct blk h) = true) ∧ ∃ rep : ℕ → G, rep 0 = 1 ∧
    ∀ rep' : ℕ → G, (∀ k < N, rep' k = rep k) → ∀ h < i, 0 < MB h →
      el gen rep' (fct blk h) = lab u (LB h)

@[expose] def GoodM (blk LB MB : ℕ → ℕ) (INV nC nf S X I : ℕ) : Prop :=
  S = 0 ∨ I = 0 ∨ X = 0 ∨ nf + 1 < X ∨
    (I = 1 ∧ ∃ i N, X = i + 1 ∧ i ≤ nf ∧ S = mkS i N ∧ 1 ≤ N ∧ LInvM u gen blk LB MB INV nC i N)

theorem good_deadM {blk LB MB : ℕ → ℕ} {INV nC nf S I X' : ℕ} (X : ℕ) (hX : nf + 1 ≤ X)
    (h : X' = 0 ∨ X' = X + 1) : GoodM u gen blk LB MB INV nC nf S X' I := by
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))

theorem labStepM_cases (LB MB : ℕ → ℕ) (Hs J X w : ℕ) :
    labStepM LB MB Hs J X w = 0 ∨ labStepM LB MB Hs J X w = X + 1 := by
  unfold labStepM
  simp only [brec_eq]
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem walk_stepM {blk WT LB MB : ℕ → ℕ} {INV INV8 L nC nf m Hs : ℕ}
    (hinv : invOK INV INV8 L = true) (hnf : nf < 4294967296)
    (hLB : ∀ h < nf, labWF (LB h) = true)
    (hWT : ∀ k < m, (wKind (WT k) = 2 → bv gen (wWord (WT k)) (wLen (WT k)) = 1) ∧
      (wKind (WT k) = 3 → Clean (LabF.target (WT k) (LabF.hint Hs k)) →
        bv gen (wWord (WT k)) (wLen (WT k)) = lab u (LabF.target (WT k) (LabF.hint Hs k))))
    (hM2 : ∀ i, MB i = 2 → ∀ h < i, 0 < MB h)
    {S X I J : ℕ} (hJ : Nat.land J 1 = 1) (hS : GoodM u gen blk LB MB INV nC nf S X I) :
    GoodM u gen blk LB MB INV nC nf
      (factStep blk INV nC L J S (fct blk (sI S)) (WT (Nat.land (Nat.shiftRight J 1) 65535)))
      (labStepM LB MB Hs J X (WT (Nat.land (Nat.shiftRight J 1) 65535)))
      (Bool.rec (motive := fun _ => ℕ) 0 I (Nat.blt (Nat.land (Nat.shiftRight J 1) 65535) m)) := by
  rcases hS with h0 | h0 | h0 | hd | ⟨hI1, i, N, hX, hi, hSd, hN, hrec, rep, hrep0, hfacts⟩
  · left
    rw [h0]
    rfl
  · right
    left
    rw [h0]
    cases Nat.blt (Nat.land (Nat.shiftRight J 1) 65535) m <;> rfl
  · right
    right
    left
    rw [h0]
    rfl
  · exact good_deadM u gen X (by omega) (labStepM_cases LB MB Hs J X _)
  have hi32 : i < 4294967296 := by omega
  rcases Nat.lt_or_ge i nf with hinf | hinf
  swap
  · exact good_deadM u gen X (by omega) (labStepM_cases LB MB Hs J X _)
  rcases Nat.lt_or_ge (Nat.land (Nat.shiftRight J 1) 65535) m with hidm | hidm
  swap
  · right
    left
    have : Nat.blt (Nat.land (Nat.shiftRight J 1) 65535) m = false := by
      cases hq : Nat.blt (Nat.land (Nat.shiftRight J 1) 65535) m
      · rfl
      · rw [Nat.blt_eq] at hq
        omega
    rw [this]
  have hI' : Bool.rec (motive := fun _ => ℕ) 0 I
      (Nat.blt (Nat.land (Nat.shiftRight J 1) 65535) m) = 1 := by
    have : Nat.blt (Nat.land (Nat.shiftRight J 1) 65535) m = true := by
      rw [Nat.blt_eq]
      exact hidm
    rw [this, hI1]
  rw [hI']
  have hsI : sI S = i := by
    rw [sI_eq, hSd, mkS_eq N hi32]
    omega
  have hsN : sN S = N := by
    rw [sN_eq, hSd, mkS_eq N hi32]
    omega
  have hS0 : Nat.blt 0 S = true := by
    rw [Nat.blt_eq, hSd, mkS_eq N hi32]
    omega
  have hX0 : Nat.blt 0 X = true := by
    rw [Nat.blt_eq]
    omega
  have hXi : Nat.sub X 1 = i := by
    change X - 1 = i
    omega
  have hJ' : Nat.beq (Nat.land J 1) 1 = true := by
    rw [Nat.beq_eq]
    exact hJ
  have hfS : factStep blk INV nC L J S (fct blk (sI S)) (WT (Nat.land (Nat.shiftRight J 1) 65535)) =
      Bool.rec (motive := fun _ => ℕ) 0 (mkS (Nat.succ i) N)
        (walkOK blk INV nC i (fct blk i) (WT (Nat.land (Nat.shiftRight J 1) 65535))
          (Nat.land (Nat.shiftRight J 17) 1048575) (Nat.land (Nat.shiftRight J 37) 65535) J) := by
    unfold factStep
    rw [hS0, hJ', hsI, hsN]
  have hlS : labStepM LB MB Hs J X (WT (Nat.land (Nat.shiftRight J 1) 65535)) =
      Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ)
          (Bool.rec (motive := fun _ => ℕ) 0 (Nat.succ X)
            (andB (LabF.labWalk LB i J (WT (Nat.land (Nat.shiftRight J 1) 65535))
                (LabF.hint Hs (Nat.land (Nat.shiftRight J 1) 65535)))
              (readsM MB (Nat.land (Nat.shiftRight J 37) 65535)
                (wLen (WT (Nat.land (Nat.shiftRight J 1) 65535)))
                (wLen (WT (Nat.land (Nat.shiftRight J 1) 65535))) (Nat.shiftRight J 53))))
          (Bool.rec (motive := fun _ => ℕ) 0 (Nat.succ X)
            (LabF.labWalk LB i J (WT (Nat.land (Nat.shiftRight J 1) 65535))
              (LabF.hint Hs (Nat.land (Nat.shiftRight J 1) 65535))))
          (Nat.beq (MB i) 2))
        (Nat.succ X)
        (Nat.beq (MB i) 0) := by
    unfold labStepM
    rw [hX0, hJ', hXi]
  rw [hfS, hlS]
  cases hw : walkOK blk INV nC i (fct blk i) (WT (Nat.land (Nat.shiftRight J 1) 65535))
      (Nat.land (Nat.shiftRight J 17) 1048575) (Nat.land (Nat.shiftRight J 37) 65535) J
  · exact Or.inl rfl
  have hrecI : recOK INV nC (fct blk i) = true := by
    have hw' := hw
    unfold walkOK at hw'
    simp only [andB_iff, orB_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at hw'
    exact hw'.1
  cases hm0 : Nat.beq (MB i) 0
  swap
  · have hmi' : MB i = 0 := Nat.eq_of_beq_eq_true hm0
    change GoodM u gen blk LB MB INV nC nf (mkS (Nat.succ i) N) (Nat.succ X) 1
    right
    right
    right
    right
    refine ⟨rfl, i + 1, N, by omega, by omega, rfl, hN, fun h hh => ?_, rep, hrep0,
      fun rep' hag h hh hm => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
      · exact hrec h hh
      · exact hrecI
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
      · exact hfacts rep' hag h hh hm
      · exact absurd hm (by omega)
  have tail : LabF.labWalk LB i J (WT (Nat.land (Nat.shiftRight J 1) 65535))
      (LabF.hint Hs (Nat.land (Nat.shiftRight J 1) 65535)) = true →
      (readsM MB (Nat.land (Nat.shiftRight J 37) 65535)
        (wLen (WT (Nat.land (Nat.shiftRight J 1) 65535)))
        (wLen (WT (Nat.land (Nat.shiftRight J 1) 65535))) (Nat.shiftRight J 53) = true ∨
        ∀ h < i, 0 < MB h) →
      GoodM u gen blk LB MB INV nC nf (mkS (Nat.succ i) N) (Nat.succ X) 1 := by
    intro hlw1 hlw2
    have hl := Nat.eq_of_beq_eq_true hlw1
    have hfs : Nat.land (Nat.shiftRight J 17) 1048575 < 1048576 := by
      rw [land20]
      omega
    obtain ⟨h2, h3⟩ := hWT _ hidm
    have hwf : ∀ rep' : ℕ → G, (∀ k < N, rep' k = rep k) →
        recOK INV nC (fct blk i) = true ∧ el gen rep' (fct blk i) = lab u (LB i) := by
      intro rep' hag
      refine walk_factM u gen hw hl hlw2 hfs (fun h hh => ⟨hfacts rep' hag h hh,
        (lv_fic gen blk hinv (hrec h hh)).1, hLB h (by omega)⟩) ?_ (hLB i hinf) h2 h3
      rw [hag 0 (by omega), hrep0]
    right
    right
    right
    right
    refine ⟨rfl, i + 1, N, by omega, by omega, rfl, hN, fun h hh => ?_, rep, hrep0,
      fun rep' hag h hh hm => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
      · exact hrec h hh
      · exact (hwf rep (fun _ _ => rfl)).1
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
      · exact hfacts rep' hag h hh hm
      · exact (hwf rep' hag).2
  cases hm2 : Nat.beq (MB i) 2
  · cases hlw : andB (LabF.labWalk LB i J (WT (Nat.land (Nat.shiftRight J 1) 65535))
        (LabF.hint Hs (Nat.land (Nat.shiftRight J 1) 65535)))
        (readsM MB (Nat.land (Nat.shiftRight J 37) 65535)
          (wLen (WT (Nat.land (Nat.shiftRight J 1) 65535)))
          (wLen (WT (Nat.land (Nat.shiftRight J 1) 65535))) (Nat.shiftRight J 53))
    · exact Or.inr (Or.inr (Or.inl rfl))
    obtain ⟨hlw1, hlw2⟩ := (andB_iff _ _).1 hlw
    exact tail hlw1 (Or.inl hlw2)
  · cases hlw : LabF.labWalk LB i J (WT (Nat.land (Nat.shiftRight J 1) 65535))
        (LabF.hint Hs (Nat.land (Nat.shiftRight J 1) 65535))
    · exact Or.inr (Or.inr (Or.inl rfl))
    exact tail hlw (Or.inr (hM2 i (Nat.eq_of_beq_eq_true hm2)))

theorem tree_stepM {blk LB MB : ℕ → ℕ} {INV nC nf L Hs : ℕ} (hnf : nf < 4294967296)
    {S X I J : ℕ} (hJ : ¬Nat.land J 1 = 1) (hS : GoodM u gen blk LB MB INV nC nf S X I) :
    GoodM u gen blk LB MB INV nC nf (factStep blk INV nC L J S (fct blk (sI S)) 0)
      (labStepM LB MB Hs J X 0) I := by
  rcases hS with h0 | h0 | h0 | hd | ⟨hI1, i, N, hX, hi, hSd, hN, hrec, rep, hrep0, hfacts⟩
  · left
    rw [h0]
    rfl
  · exact Or.inr (Or.inl h0)
  · right
    right
    left
    rw [h0]
    rfl
  · exact good_deadM u gen X (by omega) (labStepM_cases LB MB Hs J X _)
  have hi32 : i < 4294967296 := by omega
  rcases Nat.lt_or_ge i nf with hinf | hinf
  swap
  · exact good_deadM u gen X (by omega) (labStepM_cases LB MB Hs J X _)
  have hsI : sI S = i := by
    rw [sI_eq, hSd, mkS_eq N hi32]
    omega
  have hsN : sN S = N := by
    rw [sN_eq, hSd, mkS_eq N hi32]
    omega
  have hS0 : Nat.blt 0 S = true := by
    rw [Nat.blt_eq, hSd, mkS_eq N hi32]
    omega
  have hX0 : Nat.blt 0 X = true := by
    rw [Nat.blt_eq]
    omega
  have hXi : Nat.sub X 1 = i := by
    change X - 1 = i
    omega
  have hJ' : Nat.beq (Nat.land J 1) 1 = false := by
    cases hq : Nat.beq (Nat.land J 1) 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hq) hJ
  have hfS : factStep blk INV nC L J S (fct blk (sI S)) 0 =
      Bool.rec (motive := fun _ => ℕ) 0 (mkS (Nat.succ i) (Nat.succ N))
        (fTree INV nC L (fct blk i) N) := by
    unfold factStep
    rw [hS0, hJ', hsI, hsN]
  have hlS : labStepM LB MB Hs J X 0 =
      Bool.rec (motive := fun _ => ℕ) 0 (Nat.succ X) (Nat.beq (LB i) 0) := by
    unfold labStepM
    rw [hX0, hJ', hXi]
  rw [hfS, hlS]
  cases htree : fTree INV nC L (fct blk i) N
  · exact Or.inl rfl
  cases hlb : Nat.beq (LB i) 0
  · exact Or.inr (Or.inr (Or.inl rfl))
  have hLB0 := Nat.eq_of_beq_eq_true hlb
  unfold fTree at htree
  simp only [andB_iff, Nat.beq_eq, Nat.blt_eq] at htree
  obtain ⟨hrR, hfy, hfx, hfc⟩ := htree
  change GoodM u gen blk LB MB INV nC nf (mkS (Nat.succ i) (Nat.succ N)) (Nat.succ X) I
  right
  right
  right
  right
  refine ⟨hI1, i + 1, N + 1, by omega, by omega, rfl, by omega, fun h hh => ?_,
    Function.update rep N (rep (fx (fct blk i)) * lv gen (fc (fct blk i))), ?_,
    fun rep' hag h hh hm => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrec h hh
    · exact hrR
  · rw [Function.update_of_ne (show (0 : ℕ) ≠ N by omega)]
    exact hrep0
  · have hag' : ∀ k < N, rep' k = rep k := by
      intro k hk
      rw [hag k (by omega), Function.update_of_ne (show k ≠ N by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hfacts rep' hag' h hh hm
    · unfold el
      rw [hfy, hag N (by omega), Function.update_self, hag' _ hfx, mul_inv_cancel, hLB0, lab_zero]

@[expose] noncomputable def labRecM (WT LB MB : ℕ → ℕ) (Hs : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (strictN (labStepM LB MB Hs J S (nat_lit 0)) (ih (Nat.shiftRight J (nat_lit 1))))
      (strictN (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) WT) (fun w =>
        strictN (labStepM LB MB Hs J S w) (ih (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) k

theorem chunk_allM {blk WT LB MB : ℕ → ℕ} {INV INV8 L nC nf m Hs : ℕ}
    (hinv : invOK INV INV8 L = true) (hnf : nf < 4294967296)
    (hLB : ∀ h < nf, labWF (LB h) = true)
    (hWT : ∀ k < m, (wKind (WT k) = 2 → bv gen (wWord (WT k)) (wLen (WT k)) = 1) ∧
      (wKind (WT k) = 3 → Clean (LabF.target (WT k) (LabF.hint Hs k)) →
        bv gen (wWord (WT k)) (wLen (WT k)) = lab u (LabF.target (WT k) (LabF.hint Hs k))))
    (hM2 : ∀ i, MB i = 2 → ∀ h < i, 0 < MB h) :
    ∀ k J S X I, GoodM u gen blk LB MB INV nC nf S X I →
      GoodM u gen blk LB MB INV nC nf (chunkRec blk WT INV nC L k J S)
        (labRecM WT LB MB Hs k J X) (idsRec WT m k J I)
  | 0, _, _, _, _, h => h
  | k + 1, J, S, X, I, h => by
    change GoodM u gen blk LB MB INV nC nf
      (Bool.rec (motive := fun _ => Nat)
        (chunkRec blk WT INV nC L k (Nat.shiftRight J 1)
          (factStep blk INV nC L J S (fct blk (sI S)) 0))
        (strictN (strictN (Nat.land (Nat.shiftRight J 1) 65535) WT) (fun w =>
          chunkRec blk WT INV nC L k (Nat.shiftRight J (jLen J w))
            (factStep blk INV nC L J S (fct blk (sI S)) w)))
        (Nat.beq (Nat.land J 1) 1))
      (Bool.rec (motive := fun _ => Nat)
        (strictN (labStepM LB MB Hs J X 0) (labRecM WT LB MB Hs k (Nat.shiftRight J 1)))
        (strictN (strictN (Nat.land (Nat.shiftRight J 1) 65535) WT) (fun w =>
          strictN (labStepM LB MB Hs J X w)
            (labRecM WT LB MB Hs k (Nat.shiftRight J (jLen J w)))))
        (Nat.beq (Nat.land J 1) 1))
      (Bool.rec (motive := fun _ => Nat)
        (idsRec WT m k (Nat.shiftRight J 1) I)
        (strictN (Nat.land (Nat.shiftRight J 1) 65535) (fun id =>
          strictN (WT id) (fun w =>
            idsRec WT m k (Nat.shiftRight J (jLen J w))
              (Bool.rec (motive := fun _ => Nat) 0 I (Nat.blt id m)))))
        (Nat.beq (Nat.land J 1) 1))
    cases hJb : Nat.beq (Nat.land J 1) 1
    · simp only [strictN_eq]
      exact chunk_allM hinv hnf hLB hWT hM2 k _ _ _ _
        (tree_stepM u gen hnf (Nat.ne_of_beq_eq_false hJb) h)
    · simp only [strictN_eq]
      exact chunk_allM hinv hnf hLB hWT hM2 k _ _ _ _
        (walk_stepM u gen hinv hnf hLB hWT hM2 (Nat.eq_of_beq_eq_true hJb) h)

theorem runAll_goodM {blk WT LB MB : ℕ → ℕ} {INV INV8 L nC nf m Hs : ℕ}
    (hinv : invOK INV INV8 L = true) (hnf : nf < 4294967296)
    (hLB : ∀ h < nf, labWF (LB h) = true)
    (hWT : ∀ k < m, (wKind (WT k) = 2 → bv gen (wWord (WT k)) (wLen (WT k)) = 1) ∧
      (wKind (WT k) = 3 → Clean (LabF.target (WT k) (LabF.hint Hs k)) →
        bv gen (wWord (WT k)) (wLen (WT k)) = lab u (LabF.target (WT k) (LabF.hint Hs k))))
    (hM2 : ∀ i, MB i = 2 → ∀ h < i, 0 < MB h) :
    ∀ (Cs : List ℕ) S X I, GoodM u gen blk LB MB INV nC nf S X I →
      GoodM u gen blk LB MB INV nC nf (runFacts blk WT INV nC L Cs S) (runLabM WT LB MB Hs Cs X)
        (LceSR.runIds WT m Cs I)
  | [], _, _, _, h => h
  | C :: Cs, S, X, I, h => by
    change GoodM u gen blk LB MB INV nC nf (strictN (runChunk blk WT INV nC L C S)
      (runFacts blk WT INV nC L Cs))
      (strictN (labChunkM WT LB MB Hs C X) (runLabM WT LB MB Hs Cs))
      (strictN (LceSR.idsChunk WT m C I) (LceSR.runIds WT m Cs))
    simp only [strictN_eq]
    exact runAll_goodM hinv hnf hLB hWT hM2 Cs _ _ _
      (chunk_allM u gen hinv hnf hLB hWT hM2 (Nat.land C 255) (Nat.shiftRight C 8) S X I h)

end Walks

theorem labOkM_sound' (gen : ℕ → G) {blk WT RT ST LB MB : ℕ → ℕ}
    {INV INV8 L nC nCa nf m Hs nR nS K S0 S1 X0 X1 : ℕ} {Cs : List ℕ}
    (h : labOkM blk WT RT ST LB MB INV INV8 L nC nCa nf m Hs nR nS K S0 S1 X0 X1 Cs = true)
    (hRT : ∀ r < nR, bv gen (wWord (RT r)) (wLen (RT r)) = 1)
    (hST : ∀ j < K, bv gen (wWord (ST j)) (wLen (ST j)) = u j)
    {c wid R E : ℕ} (hc0 : c < 2 ^ 20) (hwid : wid < m)
    (hc : LabF.cycOK blk WT LB nf c wid R (LabF.entStk E) = true)
    (hcm : readsM MB 2048 (wLen (WT wid)) (wLen (WT wid)) R = true)
    (hM2 : ∀ i, MB i = 2 → ∀ h < i, 0 < MB h) :
    bv u (wWord E) (wLen E) = 1 := by
  unfold labOkM at h
  obtain ⟨hwords, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hhOK, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hnorm, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hinv, h⟩ := (andB_iff _ _).1 h
  obtain ⟨-, h⟩ := (andB_iff _ _).1 h
  obtain ⟨-, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hnf, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hS0, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hS1, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hX0, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hX1, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hhints, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hlabs, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hids, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hrunF, hrunL⟩ := (andB_iff _ _).1 h
  have hnf' : nf < 4294967296 := blt_true hnf
  have hS0' : S0 = mkS 0 1 := Nat.eq_of_beq_eq_true hS0
  have hS1' : S1 = mkS nf nCa := Nat.eq_of_beq_eq_true hS1
  have hX0' : X0 = 1 := Nat.eq_of_beq_eq_true hX0
  have hX1' : X1 = nf + 1 := Nat.eq_of_beq_eq_true hX1
  have hids' := Nat.eq_of_beq_eq_true hids
  have hrunF' := Nat.eq_of_beq_eq_true hrunF
  have hrunL' := Nat.eq_of_beq_eq_true hrunL
  have hLB : ∀ i < nf, labWF (LB i) = true := allBelow_spec' hlabs (by
    change nf ≤ 64 * ((nf >>> 6) + 1)
    rw [Nat.shiftRight_eq_div_pow]
    omega)
  have hWT : ∀ k < m, (wKind (WT k) = 2 → bv gen (wWord (WT k)) (wLen (WT k)) = 1) ∧
      (wKind (WT k) = 3 → Clean (LabF.target (WT k) (LabF.hint Hs k)) →
        bv gen (wWord (WT k)) (wLen (WT k)) = lab u (LabF.target (WT k) (LabF.hint Hs k))) := by
    intro k hk
    have hw := hintLoop (fun j H => (fun w r => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true
          (wSub INV (wWord w) (wLen w) (wWord (ST r)) (wLen (ST r)))
          (Nat.beq (wKind w) (nat_lit 3)))
        (wRel INV INV8 (wWord w) (wLen w) (wWord (RT r)) (wLen (RT r)))
        (Nat.beq (wKind w) (nat_lit 2))) (WT j) (Nat.land H (nat_lit 65535)))
      m (nat_lit 16) m le_rfl Hs hwords k hk
    have hh := hintLoop (fun j H => (fun w h => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true (Nat.blt h nS) (Nat.beq (wKind w) (nat_lit 3)))
        (Nat.blt h nR) (Nat.beq (wKind w) (nat_lit 2))) (WT j) (Nat.land H (nat_lit 65535)))
      m (nat_lit 16) m le_rfl Hs hhOK k hk
    rw [Nat.sub_self, Nat.zero_add] at hw hh
    obtain ⟨hw2, hw3⟩ := word_check hw
    obtain ⟨hh2, -⟩ := hint_check hh
    refine ⟨fun hk2 => ?_, fun hk3 hcl => ?_⟩
    · have hr := hh2 hk2
      have hn := relsNorm_spec hnorm _ hr
      rw [← two_pow_eight_mul] at hn
      exact wRel_sound gen hinv (hw2 hk2) hn (hRT _ hr)
    · have er : Nat.land (Hs >>> (16 * k)) 65535 = LabF.hint Hs k := rfl
      have hlt : LabF.hint Hs k < K := hintsLt_spec hhints k hk hk3
      rw [wSub_sound gen (hw3 hk3), er, lab_target3F u hk3 hcl]
      exact hST _ hlt
  have hG0 : GoodM u gen blk LB MB INV nC nf S0 X0 1 := by
    right
    right
    right
    right
    exact ⟨rfl, 0, 1, hX0', Nat.zero_le _, hS0', le_rfl,
      fun h hh => absurd hh (Nat.not_lt_zero h), fun _ => 1, rfl,
      fun _ _ h hh => absurd hh (Nat.not_lt_zero h)⟩
  have hG1 := runAll_goodM u gen hinv hnf' hLB hWT hM2 Cs S0 X0 1 hG0
  rw [hrunF', hrunL', hids', hS1', hX1'] at hG1
  have hF : ∃ rep : ℕ → G, RefsLM u gen blk LB MB rep nf := by
    rcases hG1 with h0 | h0 | h0 | hd | ⟨-, i, N, hX, -, -, -, hrec, rep, -, hfacts⟩
    · rw [mkS_eq nCa hnf'] at h0
      exact ⟨fun _ => 1, fun h hh => absurd hh (by omega)⟩
    · exact absurd h0 (by norm_num)
    · omega
    · omega
    · have hi' : i = nf := by omega
      subst hi'
      exact ⟨rep, fun h hh => ⟨hfacts rep (fun _ _ => rfl) h hh,
        (lv_fic gen blk hinv (hrec h hh)).1, hLB h hh⟩⟩
  obtain ⟨rep, hrefs⟩ := hF
  rw [cycOKF, entStkF] at hc
  unfold cycOK at hc
  rw [letB_eq] at hc
  simp only [andB_iff, Nat.beq_eq, Nat.add_eq] at hc
  obtain ⟨hk2, hwalk, hred⟩ := hc
  have hn := wLen_lt (WT wid)
  have h1 : bv gen (wWord (WT wid)) (wLen (WT wid)) = 1 := (hWT wid hwid).1 hk2
  have hc1 : c < 1048576 := lt_of_lt_of_eq hc0 (by norm_num)
  have h0 : WL u gen rep c (wWord (WT wid)) (wLen (WT wid)) 1 1 (wLen (WT wid) - wLen (WT wid))
      (wStart c (wWord (WT wid))) 0 := by
    rw [Nat.sub_self]
    exact WL_start u gen hc1
  have hW := cyc_jointM u gen (xi_ok u) hrefs hn (wLen (WT wid)) le_rfl R _ _ hcm h0
  rw [hwalk] at hW
  rcases hW with hd | ⟨hcl, -, cur, hcur, hst, hY, -⟩
  · omega
  · have hcc : cur = c := by omega
    have hlab := hY le_rfl
    rw [hcc, h1, mul_one, mul_inv_cancel] at hlab
    obtain ⟨r1, r2⟩ := cycRed_spec u (xi_ok u) hcl hlab.symm
    rw [hred] at r1 r2
    rw [← entStk_spec u r1]
    exact r2

end CFSG.Certificates.LceP.LabFM

end
