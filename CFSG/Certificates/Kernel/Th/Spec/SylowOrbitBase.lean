
module

public import CFSG.Certificates.Kernel.Th.Spec.FwdRelBase
public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.SeedS
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Th.Spec.FwdSlp
import CFSG.Certificates.Kernel.Th.Spec.DceMat
import CFSG.Certificates.Kernel.DceLoops
import CFSG.Certificates.Kernel.J4.ChainSound
import CFSG.Certificates.Kernel.LceSP.Base

@[expose] public section

namespace CFSG.KC.Th.Spec.SylowOrbit

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}

def pcSub (J : Subgroup (GL (Fin 248) (ZMod 2))) (RB : ℕ → ℕ) (PR i n : ℕ) :
    Subgroup J :=
  Subgroup.closure {g | ∃ k, i ≤ k ∧ k < n ∧ 𝕄 g = pkMat (RB (regAt PR k))}

noncomputable def blkFr (BL b : ℕ) : ℕ := bitsN BL (Nat.mul (nat_lit 10) b) (nat_lit 5)

noncomputable def blkTo (BL b : ℕ) : ℕ :=
  bitsN BL (Nat.add (Nat.mul (nat_lit 10) b) (nat_lit 5)) (nat_lit 5)

def BlockOK (RB : ℕ → ℕ) (rm PR n p BL b : ℕ) : Prop :=
  ∃ PT : ℕ → ℕ, ∃ TC SC : List ℕ, ∃ SS : ℕ, PT 0 < 2 ^ 248 ∧
    baseFixed RB rm PR (PT 0) (blkTo BL b) n = true ∧
    runTree RB PT rm PR (blkFr BL b) (blkTo BL b) TC 2 = p ^ (blkTo BL b - blkFr BL b) + 1 ∧
    DceS.runSorted PT 11 (p ^ (blkTo BL b - blkFr BL b)) SC 1 = SS ∧
    DceS.sortedCount SS = p ^ (blkTo BL b - blkFr BL b)

private theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem regsIn_spec {L n r : ℕ} (h : regsIn L n r = true) :
    ∀ k < n, 0 < regAt L k ∧ regAt L k < r := by
  have hf := (CFSG.KC.Th.Spec.Dce.allB_iff (fun k => regBelow (regAt L k) r) n).1 h
  intro k hk
  obtain ⟨h1, h2⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 (hf k hk)
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2⟩

theorem exists_seedGroup (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {SA SB : ℕ} {LA LB : List Char} (hA : SeedS.decOK SA LA = true)
    (hB : SeedS.decOK SB LB = true) (hA2 : mulB c rm SA SA = ONE)
    (hB3 : mulB c rm (mulB c rm SB SB) SB = ONE) :
    ∃ J : Subgroup (GL (Fin 248) (ZMod 2)),
      Nat.card J = Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1
        (String.ofList LA) (String.ofList LB))ˣ ∧
      ∃ a b : J, 𝕄 a = pkMat SA ∧ 𝕄 b = pkMat SB := by
  let A : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
    CFSG.Blueprint.NativeSporadic.decode 2 248 1 (String.ofList LA)
  let B : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
    CFSG.Blueprint.NativeSporadic.decode 2 248 1 (String.ofList LB)
  have hAmat : pkMat SA = A := by
    rw [(decOK_sound hA).2, CFSG.Sporadic.Th.rowsMatrix_rowsOf]
  have hBmat : pkMat SB = B := by
    rw [(decOK_sound hB).2, CFSG.Sporadic.Th.rowsMatrix_rowsOf]
  have hA2' : A * A = 1 := by
    rw [← hAmat, ← pkMat_mulB hk, hA2, pkMat_one hk]
  have hB3' : B * B * B = 1 := by
    rw [← hBmat, ← pkMat_mulB hk, ← pkMat_mulB hk, hB3, pkMat_one hk]
  have hAdet : A.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hA2'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hBdet : B.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hB3'
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨Subgroup.closure {Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet,
      Matrix.GeneralLinearGroup.mkOfDetNeZero B hBdet}, ?_, ?_⟩
  · exact Nat.card_congr (CFSG.Blueprint.NativeSporadic.matrixSeedEquiv 2 248 (by norm_num)
      A B hAdet hBdet).symm.toEquiv
  · refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet,
        Subgroup.subset_closure (Set.mem_insert _ _)⟩,
      ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero B hBdet,
        Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩, ?_, ?_⟩
    · exact hAmat.symm
    · exact hBmat.symm

private def TreeGood (RB PT : ℕ → ℕ) (rm PR fr tb k : ℕ) : Prop :=
  ∃ par g, par < k ∧ fr < g ∧ g ≤ tb ∧
    PT k = vecB rm (PT par) (RB (regAt PR (g - 1)))

private def TreeInv (RB PT : ℕ → ℕ) (rm PR fr tb s : ℕ) : Prop :=
  s = 0 ∨ (2 ≤ s ∧ ∀ k, 1 ≤ k → k + 1 < s → TreeGood RB PT rm PR fr tb k)

private noncomputable def treeChunk (RB PT : ℕ → ℕ) (rm PR fr tb : ℕ) :
    ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
    (fun _ ih2 J S => (fun k par g => CFSG.KC.Loop.strictN
        (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (Nat.succ S)
          (andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt par k)
            (andB (Nat.blt fr g) (andB (Nat.ble g tb)
              (Nat.beq (PT k) (vecB rm (PT par) (RB (regAt PR (Nat.sub g (nat_lit 1)))))))))))
        (ih2 (Nat.shiftRight J (nat_lit 17))))
      (Nat.sub S (nat_lit 1)) (bitsN J (nat_lit 0) (nat_lit 12))
      (bitsN J (nat_lit 12) (nat_lit 5)))

private theorem runTree_cons (RB PT : ℕ → ℕ) (rm PR fr tb C : ℕ) (Cs : List ℕ) (s : ℕ) :
    runTree RB PT rm PR fr tb (C :: Cs) s =
      runTree RB PT rm PR fr tb Cs (treeChunk RB PT rm PR fr tb (Nat.land C (nat_lit 65535))
        (Nat.shiftRight C (nat_lit 16)) s) :=
  strictN_eq' _ _

private theorem brec_zero {Q : ℕ → Prop} (h0 : Q 0) {Y : ℕ} {c : Bool}
    (h : c = true → Q Y) :
    Q (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) Y c) := by
  cases c
  · exact h0
  · exact h rfl

private theorem treeChunk_inv (RB PT : ℕ → ℕ) (rm PR fr tb : ℕ) :
    ∀ m J s, TreeInv RB PT rm PR fr tb s →
      TreeInv RB PT rm PR fr tb (treeChunk RB PT rm PR fr tb m J s)
  | 0, _, _, h => h
  | m + 1, J, s, h => by
    have e : treeChunk RB PT rm PR fr tb (m + 1) J s =
        treeChunk RB PT rm PR fr tb m (Nat.shiftRight J (nat_lit 17))
          (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (Nat.succ s)
            (andB (Nat.blt (nat_lit 0) s) (andB (Nat.blt (bitsN J 0 12) (s - 1))
              (andB (Nat.blt fr (bitsN J 12 5)) (andB (Nat.ble (bitsN J 12 5) tb)
                (Nat.beq (PT (s - 1)) (vecB rm (PT (bitsN J 0 12))
                  (RB (regAt PR (Nat.sub (bitsN J 12 5) 1)))))))))) :=
      strictN_eq' _ _
    rw [e]
    apply treeChunk_inv
    refine brec_zero (Q := TreeInv RB PT rm PR fr tb) (Or.inl rfl) fun hc => ?_
    obtain ⟨h0, hc⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 hc
    obtain ⟨h1, hc⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 hc
    obtain ⟨h2, hc⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 hc
    obtain ⟨h3, h4⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 hc
    have hs0 : 0 < s := Nat.blt_eq.mp h0
    rcases h with h | ⟨hs2, hk⟩
    · omega
    refine Or.inr ⟨by omega, fun k hk1 hks => ?_⟩
    rcases Nat.lt_or_ge (k + 1) s with hklt | hkge
    · exact hk k hk1 hklt
    · have hk' : k = s - 1 := by
        change k + 1 < s + 1 at hks
        omega
      subst hk'
      exact ⟨_, _, Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.le_of_ble_eq_true h3,
        Nat.eq_of_beq_eq_true h4⟩

private theorem runTree_inv (RB PT : ℕ → ℕ) (rm PR fr tb : ℕ) :
    ∀ (Cs : List ℕ) s, TreeInv RB PT rm PR fr tb s →
      TreeInv RB PT rm PR fr tb (runTree RB PT rm PR fr tb Cs s)
  | [], _, h => h
  | C :: Cs, s, h => by
    rw [runTree_cons]
    exact runTree_inv RB PT rm PR fr tb Cs _ (treeChunk_inv RB PT rm PR fr tb _ _ _ h)

private theorem tree_spec {RB PT : ℕ → ℕ} {rm PR fr tb N : ℕ} {Cs : List ℕ}
    (h : runTree RB PT rm PR fr tb Cs 2 = N + 1) :
    ∀ k, 1 ≤ k → k < N → TreeGood RB PT rm PR fr tb k := by
  have hi := runTree_inv RB PT rm PR fr tb Cs 2
    (Or.inr ⟨le_rfl, fun k h1 h2 => by omega⟩)
  rw [h] at hi
  rcases hi with hi | ⟨-, hi⟩
  · omega
  · intro k h1 h2
    exact hi k h1 (by omega)

private theorem baseFixed_spec {RB : ℕ → ℕ} {rm PR v tb n : ℕ}
    (h : baseFixed RB rm PR v tb n = true) :
    ∀ k < n, tb ≤ k → vecB rm v (RB (regAt PR k)) = v := by
  have hf := (CFSG.KC.Th.Spec.Dce.allB_iff (fun k => Bool.rec (motive := fun _ => Bool) true
    (Nat.beq (vecB rm v (RB (regAt PR k))) v) (Nat.ble tb k)) n).1 h
  intro k hk htk
  have hk' := hf k hk
  rw [Nat.ble_eq_true_of_le htk] at hk'
  exact Nat.eq_of_beq_eq_true hk'

private theorem runSorted_eq_sortRun (get : ℕ → ℕ) (qb m : ℕ) (Cs : List ℕ) (S : ℕ) :
    DceS.runSorted get qb m Cs S = CFSG.Certificates.DceLoop.sortRun get qb m Cs S := rfl

private theorem sorted_spec {PT : ℕ → ℕ} {m : ℕ} {SC : List ℕ} {SS : ℕ}
    (hs : DceS.runSorted PT 11 m SC 1 = SS) (hc : DceS.sortedCount SS = m) :
    ∀ q < m, ∀ q' < m, PT q = PT q' → q = q' := by
  have hs' : CFSG.Certificates.DceLoop.sortRun PT 11 m SC 1 = SS :=
    (runSorted_eq_sortRun PT 11 m SC 1).symm.trans hs
  exact (CFSG.Certificates.DceLoop.sortRun_spec hs' hc).2

private noncomputable def blkAcc (BL : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 1) (fun b acc => (fun fr tb =>
      Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (Nat.succ tb)
        (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.beq fr (Nat.sub acc (nat_lit 1)))
          (Nat.blt fr tb))))
    (bitsN BL (Nat.mul (nat_lit 10) b) (nat_lit 5))
    (bitsN BL (Nat.add (Nat.mul (nat_lit 10) b) (nat_lit 5)) (nat_lit 5)))

private theorem blkAcc_succ {BL b : ℕ} (h : 0 < blkAcc BL (b + 1)) :
    0 < blkAcc BL b ∧ blkFr BL b = blkAcc BL b - 1 ∧ blkFr BL b < blkTo BL b ∧
      blkAcc BL (b + 1) = blkTo BL b + 1 := by
  have e : blkAcc BL (b + 1) = Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
      (Nat.succ (blkTo BL b))
      (andB (Nat.blt (nat_lit 0) (blkAcc BL b))
        (andB (Nat.beq (blkFr BL b) (Nat.sub (blkAcc BL b) (nat_lit 1)))
          (Nat.blt (blkFr BL b) (blkTo BL b)))) := rfl
  rw [e] at h ⊢
  generalize hc : andB (Nat.blt (nat_lit 0) (blkAcc BL b)) (andB (Nat.beq (blkFr BL b)
    (Nat.sub (blkAcc BL b) (nat_lit 1))) (Nat.blt (blkFr BL b) (blkTo BL b))) = c at h ⊢
  cases c
  · exact absurd h (Nat.lt_irrefl 0)
  · obtain ⟨h1, h2⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 hc
    obtain ⟨h2, h3⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 h2
    exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, Nat.blt_eq.mp h3, rfl⟩

private theorem blkAcc_pos {BL m : ℕ} (h : 0 < blkAcc BL m) :
    ∀ i ≤ m, 0 < blkAcc BL i := by
  induction m with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := by omega
    exact h
  | succ m ih =>
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · exact ih (blkAcc_succ (b := m) h).1 i (by omega)
    · exact h

private theorem blkAcc_lt_succ {BL i : ℕ} (h : 0 < blkAcc BL (i + 1)) :
    blkAcc BL i < blkAcc BL (i + 1) := by
  obtain ⟨-, hfr, hlt, hacc⟩ := blkAcc_succ (b := i) h
  rw [hacc]
  omega

private theorem blkAcc_le {BL : ℕ} : ∀ {m i : ℕ}, 0 < blkAcc BL m → i ≤ m →
    blkAcc BL i ≤ blkAcc BL m
  | 0, i, h, hi => by
    obtain rfl : i = 0 := by omega
    exact le_rfl
  | m + 1, i, h, hi => by
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · have h0 : 0 < blkAcc BL m := (blkAcc_succ (b := m) h).1
      exact (blkAcc_le h0 (by omega)).trans (Nat.le_of_lt (blkAcc_lt_succ h))
    · exact le_rfl

private theorem pcSub_anti {J : Subgroup (GL (Fin 248) (ZMod 2))} {RB : ℕ → ℕ} {PR i j n : ℕ}
    (hij : i ≤ j) : pcSub J RB PR j n ≤ pcSub J RB PR i n :=
  Subgroup.closure_mono fun _ ⟨k, h1, h2, h3⟩ => ⟨k, Nat.le_trans hij h1, h2, h3⟩

private theorem card_pcSub_eq_closure {G : Type*} [Group G]
    {ψ : G →* GL (Fin 248) (ZMod 2)} (hψ : Function.Injective ψ)
    {RB : ℕ → ℕ} {PR n : ℕ} {g : ℕ → G}
    (hg : ∀ k < n, ((ψ (g k) : GL (Fin 248) (ZMod 2)) :
      Matrix (Fin 248) (Fin 248) (ZMod 2)) = pkMat (RB (regAt PR k))) :
    Nat.card (pcSub ψ.range RB PR 0 n) =
      Nat.card (Subgroup.closure (g '' Set.Ico 0 n)) := by
  have hgen : ψ.range.subtype '' {x : ψ.range | ∃ k, 0 ≤ k ∧ k < n ∧
      𝕄 x = pkMat (RB (regAt PR k))} = ψ '' (g '' Set.Ico 0 n) := by
    ext x
    constructor
    · rintro ⟨y, ⟨k, -, hklt, hx⟩, rfl⟩
      refine ⟨g k, ⟨k, Set.mem_Ico.2 ⟨Nat.zero_le k, hklt⟩, rfl⟩, ?_⟩
      have hyz : y = ⟨ψ (g k), MonoidHom.mem_range.mpr ⟨g k, rfl⟩⟩ :=
        mat_injective (hx.trans (hg k hklt).symm)
      rw [hyz]
      rfl
    · rintro ⟨y, ⟨k, hkIco, rfl⟩, rfl⟩
      refine ⟨⟨ψ (g k), MonoidHom.mem_range.mpr ⟨g k, rfl⟩⟩, ?_, rfl⟩
      exact ⟨k, Nat.zero_le k, (Set.mem_Ico.1 hkIco).2,
        hg k (Set.mem_Ico.1 hkIco).2⟩
  have hpc : (pcSub ψ.range RB PR 0 n).map ψ.range.subtype =
      (Subgroup.closure (g '' Set.Ico 0 n)).map ψ := by
    have hL : (pcSub ψ.range RB PR 0 n).map ψ.range.subtype =
        Subgroup.closure (ψ '' (g '' Set.Ico 0 n)) := by
      unfold pcSub
      rw [MonoidHom.map_closure, hgen]
    have hR : (Subgroup.closure (g '' Set.Ico 0 n)).map ψ =
        Subgroup.closure (ψ '' (g '' Set.Ico 0 n)) :=
      MonoidHom.map_closure ψ (g '' Set.Ico 0 n)
    exact hL.trans hR.symm
  rw [← Subgroup.card_subtype ψ.range (pcSub ψ.range RB PR 0 n), hpc,
    Subgroup.card_map_of_injective hψ]

end CFSG.KC.Th.Spec.SylowOrbit

end
