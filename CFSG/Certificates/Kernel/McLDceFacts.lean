module

public import CFSG.Certificates.Kernel.McLDceWalk
import CFSG.Certificates.Kernel.Co1DceCover
import Mathlib.Tactic.Group
public import CFSG.Certificates.Kernel.McLDceOrb

public section

namespace CFSG.Certificates.McLD

open CFSG.KC CFSG.KC.McL.Mat CFSG.Certificates.LCE

set_option exponentiation.threshold 700

@[expose] def FactRaw (FB HB GB TB WD : ℕ → ℕ) (LT TL NL ND NO nH nT nW i nx nx' : ℕ) : Prop :=
  McL.Dce.recOK ND NO (fR FB i) = true ∧
    (nx' = nx + 1 ∧ McL.Dce.treeOK nx (fR FB i) = true ∨
      nx' = nx ∧ (∃ Jf, McL.Dce.axiomOK HB nH Jf (fR FB i) = true) ∨
      nx' = nx ∧ ∃ Jf, McL.Dce.walkOK FB HB GB TB WD LT TL NL ND nH nT nW i Jf (fR FB i) = true)

theorem mkS_eq {i : ℕ} (nx : ℕ) (hi : i < 2 ^ 32) : McL.Dce.mkS i nx = i + nx * 2 ^ 32 :=
  Co1D.lor_shl hi

private theorem sI_eq (S : ℕ) : McL.Dce.sI S = S &&& 4294967295 := rfl
private theorem sX_eq (S : ℕ) : McL.Dce.sX S = S >>> 32 := rfl

theorem mkS_dec {i : ℕ} (nx : ℕ) (hi : i < 2 ^ 32) :
    McL.Dce.sI (McL.Dce.mkS i nx) = i ∧ McL.Dce.sX (McL.Dce.mkS i nx) = nx := by
  rw [mkS_eq nx hi]
  refine ⟨?_, ?_⟩
  · rw [sI_eq, show (4294967295 : ℕ) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  · rw [sX_eq, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 32),
      Nat.div_eq_of_lt hi, Nat.zero_add]

theorem mkS_wrap (nx : ℕ) : McL.Dce.mkS (2 ^ 32) nx = McL.Dce.mkS 0 (Nat.lor 1 nx) := by
  unfold McL.Dce.mkS
  change 2 ^ 32 ||| nx <<< 32 = 0 ||| (1 ||| nx) <<< 32
  rw [Nat.zero_or, Nat.shiftLeft_or_distrib, Nat.one_shiftLeft]

@[expose] def FInv (FB HB GB TB WD : ℕ → ℕ) (LT TL NL ND NO nH nT nW S : ℕ) : Prop :=
  S = 0 ∨ ∃ i nx, S = McL.Dce.mkS i nx ∧ i < 2 ^ 32 ∧ ∃ nxf : ℕ → ℕ, nxf i = nx ∧
    ∀ i' < i, FactRaw FB HB GB TB WD LT TL NL ND NO nH nT nW i' (nxf i') (nxf (i' + 1))

variable {FB HB GB TB WD : ℕ → ℕ} {LT TL NL ND NO nH nT nW : ℕ}

theorem factStep_inv {Jf S : ℕ} (h : FInv FB HB GB TB WD LT TL NL ND NO nH nT nW S) :
    FInv FB HB GB TB WD LT TL NL ND NO nH nT nW
      (McL.Dce.factStep FB HB GB TB WD LT TL NL ND NO nH nT nW Jf S) := by
  rcases h with rfl | ⟨i, nx, rfl, hi, nxf, hnx, hf⟩
  · exact Or.inl rfl
  obtain ⟨eI, eN⟩ := mkS_dec nx hi
  have key : McL.Dce.factStep FB HB GB TB WD LT TL NL ND NO nH nT nW Jf (McL.Dce.mkS i nx) = 0 ∨
      ∃ nx', McL.Dce.factStep FB HB GB TB WD LT TL NL ND NO nH nT nW Jf (McL.Dce.mkS i nx) =
        McL.Dce.mkS (i + 1) nx' ∧ FactRaw FB HB GB TB WD LT TL NL ND NO nH nT nW i nx nx' := by
    unfold McL.Dce.factStep
    simp only []
    rw [eI, eN]
    cases h1 : Th.andB (Nat.blt 0 (McL.Dce.mkS i nx))
        (McL.Dce.recOK ND NO (McL.Dce.rec FB 6 McL.Dce.RW i))
    · exact Or.inl rfl
    rw [andB_iff] at h1
    dsimp only
    cases h2 : Nat.beq (Nat.land Jf 3) 0
    · dsimp only
      cases h3 : Nat.beq (Nat.land Jf 3) 1
      · dsimp only
        cases h4 : Th.andB (Nat.beq (Nat.land Jf 3) 2)
            (McL.Dce.walkOK FB HB GB TB WD LT TL NL ND nH nT nW i Jf (McL.Dce.rec FB 6 McL.Dce.RW i))
        · exact Or.inl rfl
        · rw [andB_iff] at h4
          exact Or.inr ⟨_, rfl, h1.2, Or.inr (Or.inr ⟨rfl, Jf, h4.2⟩)⟩
      · dsimp only
        cases h4 : McL.Dce.axiomOK HB nH Jf (McL.Dce.rec FB 6 McL.Dce.RW i)
        · exact Or.inl rfl
        · exact Or.inr ⟨_, rfl, h1.2, Or.inr (Or.inl ⟨rfl, Jf, h4⟩)⟩
    · dsimp only
      cases h4 : McL.Dce.treeOK nx (McL.Dce.rec FB 6 McL.Dce.RW i)
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl, h1.2, Or.inl ⟨rfl, h4⟩⟩
  rcases key with hz | ⟨nx', e, hfr⟩
  · exact Or.inl hz
  rw [e]
  rcases Nat.lt_or_ge (i + 1) (2 ^ 32) with hlt | hge
  · refine Or.inr ⟨i + 1, nx', rfl, hlt, fun i' => if i' ≤ i then nxf i' else nx', by simp, ?_⟩
    intro i' hi'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
    · have h1 : i' ≤ i := by omega
      have h2 : i' + 1 ≤ i := by omega
      simp only [h1, h2, ↓reduceIte]
      exact hf i' hi'
    · simp only [le_refl, ↓reduceIte, Nat.not_succ_le_self]
      rw [hnx]
      exact hfr
  · have e2 : i + 1 = 2 ^ 32 := by omega
    rw [e2, mkS_wrap]
    exact Or.inr ⟨0, _, rfl, Nat.two_pow_pos 32, fun _ => Nat.lor 1 nx', rfl,
      fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩

theorem runChunk_inv : ∀ (n J S : ℕ), FInv FB HB GB TB WD LT TL NL ND NO nH nT nW S →
    FInv FB HB GB TB WD LT TL NL ND NO nH nT nW
      (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
        (fun _ ih J S => (fun L =>
          Loop.strictN (McL.Dce.factStep FB HB GB TB WD LT TL NL ND NO nH nT nW
              (McL.Dce.bits J (nat_lit 12) L) S)
            (ih (Nat.shiftRight J (Nat.add (nat_lit 12) L))))
          (Nat.land J (nat_lit 4095))) n J S)
  | 0, _, _, h => h
  | n + 1, J, S, h => by
    change FInv FB HB GB TB WD LT TL NL ND NO nH nT nW
      (Loop.strictN (McL.Dce.factStep FB HB GB TB WD LT TL NL ND NO nH nT nW
          (McL.Dce.bits J 12 (Nat.land J 4095)) S)
        (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
          (fun _ ih J S => (fun L =>
            Loop.strictN (McL.Dce.factStep FB HB GB TB WD LT TL NL ND NO nH nT nW
                (McL.Dce.bits J (nat_lit 12) L) S)
              (ih (Nat.shiftRight J (Nat.add (nat_lit 12) L))))
            (Nat.land J (nat_lit 4095))) n (Nat.shiftRight J (Nat.add 12 (Nat.land J 4095)))))
    rw [strictN_eq]
    exact runChunk_inv n _ _ (factStep_inv h)

theorem runFacts_inv : ∀ (Cs : List ℕ) (S : ℕ), FInv FB HB GB TB WD LT TL NL ND NO nH nT nW S →
    FInv FB HB GB TB WD LT TL NL ND NO nH nT nW
      (McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW Cs S)
  | [], _, h => h
  | C :: Cs, S, h => by
    change FInv FB HB GB TB WD LT TL NL ND NO nH nT nW
      (Loop.strictN (McL.Dce.runChunk FB HB GB TB WD LT TL NL ND NO nH nT nW C S)
        (McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW Cs))
    rw [strictN_eq]
    exact runFacts_inv Cs _ (runChunk_inv _ _ _ h)

public theorem runFacts_spec {Cf : List ℕ} {NF : ℕ} (hNF : NF < 2 ^ 20) (hND : 0 < ND)
    (h : Nat.beq (McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW Cf (McL.Dce.mkS 0 1))
      (McL.Dce.mkS NF ND) = true) :
    ∃ nxf : ℕ → ℕ, ∀ i < NF,
      FactRaw FB HB GB TB WD LT TL NL ND NO nH nT nW i (nxf i) (nxf (i + 1)) := by
  have hNF' : NF < 2 ^ 32 := by omega
  have h0 : FInv FB HB GB TB WD LT TL NL ND NO nH nT nW (McL.Dce.mkS 0 1) :=
    Or.inr ⟨0, 1, rfl, Nat.two_pow_pos 32, fun _ => 1, rfl, fun i' hi' => absurd hi' (by omega)⟩
  have h1 := runFacts_inv Cf _ h0
  rw [Nat.eq_of_beq_eq_true h] at h1
  rcases h1 with h1 | ⟨i, nx, e, hi, nxf, -, hf⟩
  · rw [mkS_eq ND hNF'] at h1
    have : 0 < ND * 2 ^ 32 := Nat.mul_pos hND (Nat.two_pow_pos 32)
    omega
  obtain ⟨d1, -⟩ := mkS_dec ND hNF'
  obtain ⟨d3, -⟩ := mkS_dec nx hi
  rw [e, d3] at d1
  subst d1
  exact ⟨nxf, hf⟩

theorem treeOK_spec {nx R : ℕ} (h : McL.Dce.treeOK nx R = true) :
    0 < McL.Dce.rJ R ∧ McL.Dce.rDp R = nx ∧ McL.Dce.rD R < nx ∧ McL.Dce.rPi R = ident ∧
      McL.Dce.rN R = ident := by
  unfold McL.Dce.treeOK at h
  simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem axiomOK_spec {nH Jf R : ℕ} (h : McL.Dce.axiomOK HB nH Jf R = true) :
    McL.Dce.rD R = 0 ∧ McL.Dce.rJ R = 0 ∧ McL.Dce.rDp R = 0 ∧ ∃ x < nH, ∃ b < nH,
      McL.Dce.rPi R = mul25 (McL.Dce.mat HB x) (McL.Dce.mat HB b) ∧
      McL.Dce.rN R = McL.Dce.rFI R := by
  unfold McL.Dce.axiomOK at h
  beta_reduce at h
  simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, _, h4, _, h5, h6, h7⟩

theorem tree_unique {nxf : ℕ → ℕ} {NF : ℕ}
    (hf : ∀ i < NF, FactRaw FB HB GB TB WD LT TL NL ND NO nH nT nW i (nxf i) (nxf (i + 1)))
    {i i' : ℕ} (hi : i < NF) (hi' : i' < NF) (ht : nxf (i + 1) = nxf i + 1)
    (ht' : nxf (i' + 1) = nxf i' + 1) (e : McL.Dce.rDp (fR FB i) = McL.Dce.rDp (fR FB i')) :
    i = i' := by
  have mono1 : ∀ k < NF, nxf k ≤ nxf (k + 1) := fun k hk => by
    rcases (hf k hk).2 with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> omega
  have mono : ∀ a b, a ≤ b → b ≤ NF → nxf a ≤ nxf b := by
    intro a b hab hb
    induction b with
    | zero => rw [Nat.le_zero.1 hab]
    | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hab) with h1 | h1
      · exact Nat.le_trans (ih (by omega) (by omega)) (mono1 k (by omega))
      · rw [h1]
  have tr : ∀ k < NF, nxf (k + 1) = nxf k + 1 → McL.Dce.rDp (fR FB k) = nxf k := fun k hk hk1 => by
    rcases (hf k hk).2 with ⟨-, h⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact (treeOK_spec h).2.1
    · omega
    · omega
  rw [tr i hi ht, tr i' hi' ht'] at e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h1 | h1
  · have := mono (i + 1) i' (by omega) (by omega)
    omega
  · have := mono (i' + 1) i (by omega) (by omega)
    omega

section Hold

variable {G : Type*} [Group G] {gen : ℕ → G} {LI : ℕ} (φ : Mg LT TL NL →* G)

public theorem hG_of (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    {OB : ℕ → ℕ} {I0 : ℕ} {Ch Cg : List ℕ}
    (hhdr : Nat.beq (McL.Dce.runHdr HB LT TL NL Ch 1) (nH + 1) = true)
    (hgom : Nat.beq (McL.Dce.runGom HB GB OB I0 nH Cg 1) (NO + 1) = true) :
    ∀ j < NO, InM LT TL NL (gL HB GB j) ∧ InM LT TL NL (gH HB GB j) ∧
      mul25 (gL HB GB j) (gH HB GB j) = ident := fun j hj =>
  ⟨(gE_mem hTL hNL hlet hhdr hgom j hj).1, (gE_mem hTL hNL hlet hhdr hgom j hj).2,
    (gomOK_spec (runGom_ok hgom j hj)).2.2.2⟩

public theorem hS_of (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    (hφ : ∀ c (hc : c < 3), φ ⟨Lf LT TL NL c, Lf_mem hc⟩ = gen c)
    {OB RR : ℕ → ℕ} {NR I0 hT : ℕ} {Ch Ct : List ℕ}
    (hhdr : Nat.beq (McL.Dce.runHdr HB LT TL NL Ch 1) (nH + 1) = true)
    (hpsi : Nat.beq (McL.Dce.runT HB TB OB RR LT TL NL NR nH nT I0 Ct 1) (nT + 1) = true)
    (htsq : McL.Dce.tsqOK RR TL NR hT = true) (hRRc : relsNorm RR NR = true)
    (hRR : ∀ r < NR, wv gen (LceS.wWord (RR r)) (LceS.wLen (RR r)) = 1) :
    ∀ e < nT, InM LT TL NL (McL.Dce.tSig HB TB e) ∧ InM LT TL NL (tPsi HB TB e) ∧
      gen TL * rc φ (McL.Dce.tSig HB TB e) * gen TL = rc φ (tPsi HB TB e) := fun e he =>
  ⟨(psi_mem hTL hNL hlet hhdr hpsi e he).1, (psi_mem hTL hNL hlet hhdr hpsi e he).2.1,
    psi_rc φ hφ hTL hNL hlet hhdr hpsi htsq hRRc hRR e he⟩

public theorem facts_hold (hTL : TL = 3) (hNL : NL = 4)
    (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    (hφ : ∀ c (hc : c < 3), φ ⟨Lf LT TL NL c, Lf_mem hc⟩ = gen c)
    (hH : ∀ h < nH, InM LT TL NL (McL.Dce.mat HB h))
    (hG : ∀ j < NO, InM LT TL NL (gL HB GB j) ∧ InM LT TL NL (gH HB GB j) ∧
      mul25 (gL HB GB j) (gH HB GB j) = ident)
    (hS : ∀ e < nT, InM LT TL NL (McL.Dce.tSig HB TB e) ∧ InM LT TL NL (tPsi HB TB e) ∧
      gen TL * rc φ (McL.Dce.tSig HB TB e) * gen TL = rc φ (tPsi HB TB e))
    (ht : gen TL * gen TL = 1) (hND : ND ≤ 256) (hND0 : 0 < ND)
    (hwords : ∀ w < nW, wv gen (LceS.wWord (WD w)) (LceS.wLen (WD w)) = 1)
    {Cf : List ℕ} {NF : ℕ} (hNF : NF < 2 ^ 20)
    (hfacts : Nat.beq (McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW Cf
      (McL.Dce.mkS 0 1)) (McL.Dce.mkS NF ND) = true) :
    ∃ w : ℕ → G, w 0 = 1 ∧ ∀ i < NF, FOK φ gen HB GB ND NO w (fR FB i) := by
  classical
  obtain ⟨nxf, hf⟩ := runFacts_spec hNF hND0 hfacts
  obtain ⟨w, hw0, hw⟩ := Co1D.exists_tree_w NF (fun i => nxf (i + 1) = nxf i + 1)
    (fun i => McL.Dce.rD (fR FB i)) (fun i => McL.Dce.rDp (fR FB i))
    (fun i => tvJ φ gen HB GB (McL.Dce.rJ (fR FB i)))
    (fun i hi hT => by
      rcases (hf i hi).2 with ⟨-, h⟩ | ⟨e, -⟩ | ⟨e, -⟩
      · obtain ⟨-, h2, h3, -⟩ := treeOK_spec h
        exact lt_of_lt_of_eq h3 h2.symm
      · omega
      · omega)
    (fun i hi i' hi' hT hT' e => tree_unique hf hi hi' hT hT' e)
  refine ⟨w, hw0, fun i => ?_⟩
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨hrec, ht' | ⟨-, Jf, ha⟩ | ⟨-, Jf, hW⟩⟩ := hf i hi
    · obtain ⟨e1, htr⟩ := ht'
      obtain ⟨-, -, h3, h4, h5⟩ := treeOK_spec htr
      refine ⟨hrec, by rw [h4]; exact InM_ident, by rw [h5]; exact InM_ident, ?_⟩
      unfold FM
      rw [h4, h5, rc_ident, one_mul, mul_one, hw i hi e1]
    · obtain ⟨h1, h2, h3, x, hx, b, hb, h4, h5⟩ := axiomOK_spec ha
      obtain ⟨-, -, -, hPF, -⟩ := recOK_spec hrec
      have hP : InM LT TL NL (McL.Dce.rPi (fR FB i)) := by
        rw [h4]
        exact InM_mul (hH x hx) (hH b hb)
      have hN : InM LT TL NL (McL.Dce.rN (fR FB i)) := by
        rw [h5]
        exact InM_inv hP hPF
      refine ⟨hrec, hP, hN, ?_⟩
      unfold FM tvJ
      rw [h1, h2, h3, ite_eq_left rfl, hw0, h5, rc_inv φ hP hPF]
      group
    · exact walk_mean φ hTL hNL hlet hφ hH hG hS ht hND hwords
        (fun h hh => ih h hh (by omega)) hrec hW

end Hold

end CFSG.Certificates.McLD

end
