module

public import Certificates.Data.Kernel.O8.CPM
public import CFSG.Certificates.Kernel.O8AutSound
public import CFSG.Certificates.Kernel.O8SoundDefs
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.SiftEq
import CFSG.Certificates.Kernel.F2WordSound

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.EvenSmallLie CFSG.EvenSmallLie.OmegaEight.Stage1.Model
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (bmulVec)
open CFSG.KC.Enum (pidn permOK pg pcomp)

@[expose] def LevelsK (n w : Nat) (PS PSI LR TR TRI : Nat → Nat) (kS kO nb BP : Nat)
    (D : List (List Int)) (S : Array (Array Nat)) (B : Array Nat) : Prop :=
  Binds n w PS kS nb BP S B ∧ headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true ∧
    LevelsOK n w PS PSI LR TR TRI kS nb BP

@[expose] def memG (n : ℕ) (S : Array (Array ℕ)) (B : Array ℕ) (g : Array ℕ) : Bool :=
  siftA n (rawLevels n S B) B 0 g

@[expose] def sigCheckG (n : ℕ) (σ : Array ℕ) (ψ : ℕ → Array ℕ) (R : Array ℕ)
    (uA : ℕ → Array ℕ) (US : Array (Array ℕ)) (UB : Array ℕ) : Bool :=
  isInvA n σ (invCand n σ) && eqA n (compA n σ σ) (idA n) &&
    allLt 64 (fun y => eqA n (conjA n σ (ψ y)) (ψ (bmulVec 6 6 R y))) &&
    allLt 6 (fun k => memG n US UB (conjA n σ (uA k)))

@[expose] def wArrG (g8 g9 : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 360
  | 1 => g9
  | 2 => g8
  | 3 => compA 360 g8 g9
  | 4 => compA 360 g8 g8
  | _ => compA 360 (compA 360 g8 g8) g9

@[expose] def cosetCheckG (g8 g9 : Array ℕ) (AS : Array (Array ℕ)) (AB : Array ℕ)
    (OS : Array (Array ℕ)) (OB : Array ℕ) : Bool :=
  allLt 6 (fun i => isInvA 360 (wArrG g8 g9 i) (invCand 360 (wArrG g8 g9 i)) &&
      memG 360 AS AB (wArrG g8 g9 i)) &&
    allLt 6 (fun i => allLt 6 fun j =>
      i == j || !memG 360 OS OB (compA 360 (wArrG g8 g9 j) (invCand 360 (wArrG g8 g9 i)))) &&
    !memG 360 OS OB (compA 360 (wArrG g8 g9 2) (wArrG g8 g9 2)) &&
    !memG 360 OS OB (compA 360 (wArrG g8 g9 4) (wArrG g8 g9 4)) &&
    allLt 4 (fun j => decide (120 ≤ (wArrG g8 g9 (j + 2))[0]!)) &&
    allLt 360 (fun p => decide (g9[p]! < 120) == decide (p < 120)) &&
    eqA 360 (compA 360 g9 g9) (idA 360) &&
    eqA 360 (OmegaEight.conjArr (wArrG g8 g9 2) (wArrG g8 g9 3)) g9 &&
    eqA 360 (OmegaEight.conjArr (wArrG g8 g9 4) (wArrG g8 g9 5)) g9

@[expose] def minusCheckG (g : Array ℕ) (LS : Array (Array ℕ)) (LB : Array ℕ) : Bool :=
  !memG 136 LS LB g && eqA 136 (compA 136 g g) (idA 136)

open CFSG.Monster.B.Co2 PA

private theorem prep_unique' {n w P : ℕ} {g h : Equiv.Perm (Fin n)} (hg : Orb.PRep n w P g)
    (hh : Orb.PRep n w P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

private theorem range_of_prep {n w P : ℕ} {g : Equiv.Perm (Fin n)} (h : Orb.PRep n w P g) :
    CFSG.KC.Enum.allN n (fun i => Nat.blt (pg w (mask w) P i) n) = true :=
  Orb.allN_iff.2 fun i hi => by
    rw [Nat.blt_eq, h ⟨i, hi⟩]
    exact (g ⟨i, hi⟩).2

private theorem perm_head {n w kS kO nb BP : ℕ} {PS PSI : ℕ → ℕ} {D : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    CFSG.KC.Enum.allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true := by
  unfold headK at hh
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at hh
  exact hh.2.2.2.2.1

private theorem perm_facts {n w P : ℕ} (h : permOK n w (mask w) (n * w) P P = true) :
    ∃ s : Equiv.Perm (Fin n), Rep n (unpack n w P) s ∧ s⁻¹ = s ∧ P >>> (n * w) = 0 ∧
      Orb.PRep n w P s := by
  have hr := rep_permOfArr (Orb.isInvA_unpack h)
  exact ⟨_, hr.1, hr.2.unique hr.1, (Orb.permOK_facts h).1, Orb.prep_of_rep hr.1⟩

private theorem pg_conj {n w SG X i : ℕ} (h32 : n < 2 ^ 32)
    (hSG : ∀ i < n, pg w (mask w) SG i < n) (hi : i < n) :
    pg w (mask w) (pc n w (pc n w SG X) SG) i =
      pg w (mask w) SG (pg w (mask w) X (pg w (mask w) SG i)) := by
  unfold pc
  rw [PF.pg_pcomp h32 hi, PF.pg_pcomp h32 (hSG i hi)]

private theorem conj_unpack {n w SG X : ℕ} {s : Equiv.Perm (Fin n)} (h32 : n < 2 ^ 32)
    (hR : Rep n (unpack n w SG) s) (hs : s⁻¹ = s) (hshr : SG >>> (n * w) = 0) :
    conjA n (unpack n w SG) (unpack n w X) = unpack n w (pc n w (pc n w SG X) SG) := by
  have hSG : ∀ i < n, pg w (mask w) SG i < n := fun i hi => by
    rw [← Orb.unpack_get hi]
    exact hR.lt hi
  have hRi : Rep n (invCand n (unpack n w SG)) s := by
    have := rep_invCand hR
    rwa [hs] at this
  apply arr_ext (by simp [conjA, compA]) (unpack_size _ _ _)
  intro i hi
  have h1 : (invCand n (unpack n w SG))[i]! = pg w (mask w) SG i := by
    rw [hRi.apply hi, ← hR.apply hi, Orb.unpack_get hi]
  unfold conjA
  rw [compA_get hi, h1, compA_get (hSG i hi), Orb.unpack_get (hSG i hi), unpack_get' hshr,
    Orb.unpack_get hi, pg_conj h32 hSG hi]

private theorem range_conj {n w SG X : ℕ} (h32 : n < 2 ^ 32) (hn0 : 0 < n)
    (hSG : ∀ i < n, pg w (mask w) SG i < n) (hshr : SG >>> (n * w) = 0) :
    CFSG.KC.Enum.allN n (fun i => Nat.blt (pg w (mask w) (pc n w (pc n w SG X) SG) i) n) = true :=
  Orb.allN_iff.2 fun i hi => by
    rw [Nat.blt_eq, pg_conj h32 hSG hi]
    by_cases hm : pg w (mask w) X (pg w (mask w) SG i) < n
    · exact hSG _ hm
    · rw [pg_high hshr (by omega)]
      exact hn0

private theorem popc_mod (x : ℕ) : ∀ m,
    popc m x % 2 = (CFSG.EvenSmallLie.UnitarySix.YamadaPar.xorFold m fun j => x.testBit j).toNat
  | 0 => rfl
  | m + 1 => by
    have e : popc (m + 1) x = Nat.land (Nat.shiftRight x m) 1 + popc m x := rfl
    have hb : Nat.land (Nat.shiftRight x m) 1 = (x.testBit m).toNat := by
      change (x >>> m) &&& 1 = _
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.toNat_testBit]
    rw [e, CFSG.EvenSmallLie.UnitarySix.YamadaPar.xorFold_succ, Nat.add_mod, popc_mod x m, hb]
    cases CFSG.EvenSmallLie.UnitarySix.YamadaPar.xorFold m (fun j => x.testBit j) <;>
      cases x.testBit m <;> rfl

private theorem toNat_testBit0 (b : Bool) : b.toNat.testBit 0 = b := by
  cases b <;> rfl

private theorem bvecK_eq (RP y : ℕ) : bmulVec 6 6 (decR RP) y = bvecK RP y ∧ bvecK RP y < 64 := by
  have hf : ∀ i < 6, par6 (Nat.land (frow RP i) y) < 2 ^ 1 := fun i _ =>
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have he : bvecK RP y = orN 6 fun i => par6 (Nat.land (frow RP i) y) <<< (1 * i) := by
    unfold bvecK
    exact congrArg (orN 6) (funext fun i => by rw [Nat.one_mul]; rfl)
  have hb : ∀ p, (bvecK RP y).testBit p = (decide (p < 6) &&
      CFSG.EvenSmallLie.UnitarySix.YamadaPar.xorFold 6 fun j => (frow RP p).testBit j && y.testBit j) := by
    intro p
    rw [he, F2W.testBit_orN_fields hf, Nat.one_mul, Nat.div_one, Nat.mod_one]
    have hp6 : ∀ x, par6 x = (CFSG.EvenSmallLie.UnitarySix.YamadaPar.xorFold 6
        fun j => x.testBit j).toNat := fun x => by
      change (popc 6 x) &&& 1 = _
      rw [Nat.and_one_is_mod, popc_mod]
    rw [hp6, toNat_testBit0]
    congr
    funext j
    exact Nat.testBit_land _ _ _
  have hd : ∀ p < 6, (decR RP).getD p 0 = frow RP p := fun p hp => by
    rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine ⟨Nat.eq_of_testBit_eq fun p => ?_, ?_⟩
  · rw [hb, bmulVec, CFSG.EvenSmallLie.UnitarySix.YamadaPar.testBit_bitsOf]
    by_cases hp : p < 6
    · rw [hd p hp]
    · simp [hp]
  · have : bvecK RP y < 2 ^ 6 := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      rw [hb]
      simp [show ¬ i < 6 by omega]
    exact this

theorem sig_sound {n w : Nat} {σ R : Array ℕ} {ψ uA : ℕ → Array ℕ} {US : Array (Array ℕ)}
    {UB : Array ℕ} {SG RP BP kS nb : Nat} {PSI UA PS PSI' LR TR TRI : Nat → Nat}
    (hU : LevelsK n w PS PSI' LR TR TRI kS kS nb BP [] US UB)
    (hσ : σ = unpack n w SG) (hψ : ∀ y < 64, (ψ y).toList = (List.range n).map fun i => fget (PSI y) i w)
    (hR : R = decR RP) (huA : ∀ k < 6, uA k = unpack n w (UA k))
    (h : sigOK n w SG PSI UA RP LR TRI BP nb = true) : sigCheckG n σ ψ R uA US UB = true := by
  obtain ⟨hb, hh, hl⟩ := hU
  have hb' := hb
  obtain ⟨hn0, -, hn16, -, -, -, -⟩ := hb'
  have hperm := perm_head hh
  have h32 : n < 2 ^ 32 := by omega
  unfold sigOK at h
  simp only [ctAndB_eq, Bool.and_eq_true, ctAllN_iff] at h
  obtain ⟨hpS, -, hconj, hu⟩ := h
  subst hσ hR
  obtain ⟨s, hR, hs, hshr, -⟩ := perm_facts hpS
  have hSG : ∀ i < n, pg w (mask w) SG i < n := fun i hi => by
    rw [← Orb.unpack_get hi]
    exact hR.lt hi
  have hψ' : ∀ y < 64, ψ y = unpack n w (PSI y) := fun y hy => unpack_of_toList (hψ y hy)
  unfold sigCheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨isInvA_of_rep hR (rep_invCand hR), ?_⟩, ?_⟩, ?_⟩
  · refine (eqA_iff (rep_compA hR hR) rep_idA).2 ?_
    exact (congrArg (s * ·) hs.symm).trans (mul_inv_cancel s)
  · rw [allLt_iff]
    intro y hy
    obtain ⟨hz1, hz2⟩ := bvecK_eq RP y
    rw [hψ' y hy, conj_unpack h32 hR hs hshr, hz1, Nat.eq_of_beq_eq_true (hconj y hy),
      hψ' _ hz2]
    exact eqA_self _
  · rw [allLt_iff]
    intro k hk
    rw [huA k hk, conj_unpack h32 hR hs hshr]
    exact siftK_sound hb hperm hl rfl (range_conj h32 hn0 hSG hshr) (hu k hk)

theorem coset_sound {g8 g9 : Array ℕ} {AS OS : Array (Array ℕ)} {AB OB : Array ℕ}
    {G8 G9 I8 I9 kSA kOA BPA kSO kOO BPO : Nat} {PA PAI LA TA TAI PO POI LO TO TOI : Nat → Nat}
    {DA DO : List (List Int)}
    (hA : LevelsK 360 9 PA PAI LA TA TAI kSA kOA 7 BPA DA AS AB)
    (hO : LevelsK 360 9 PO POI LO TO TOI kSO kOO 7 BPO DO OS OB)
    (h8 : g8 = unpack 360 9 G8) (h9 : g9 = unpack 360 9 G9)
    (h : cosetOK G8 G9 I8 I9 LA TAI BPA LO TOI BPO = true) :
    cosetCheckG g8 g9 AS AB OS OB = true := by
  obtain ⟨hbA, hhA, hlA⟩ := hA
  obtain ⟨hbO, hhO, hlO⟩ := hO
  have hpA := perm_head hhA
  have hpO := perm_head hhO
  have h32 : (360 : ℕ) < 2 ^ 32 := by decide
  have hn : (360 : ℕ) < 16777216 := by decide
  have hw : (360 : ℕ) + 1 < 2 ^ 9 := by decide
  unfold cosetOK at h
  simp only [ctAndB_eq, ctOrB_eq, ctNotB_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    ctAllN_iff] at h
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9⟩ := h
  subst h8 h9
  have hr := rep_permOfArr (Orb.isInvA_unpack
    ((hw1 2 (by decide)).1 : permOK 360 9 (mask 9) (360 * 9) G8 I8 = true))
  have ht := rep_permOfArr (Orb.isInvA_unpack
    ((hw1 1 (by decide)).1 : permOK 360 9 (mask 9) (360 * 9) G9 I9 = true))
  have hP8 := Orb.prep_of_rep hr.1
  have hP9 := Orb.prep_of_rep ht.1
  have hW : ∀ j < 6, wArrG (unpack 360 9 G8) (unpack 360 9 G9) j = unpack 360 9 (wK G8 G9 j) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · have hs : (idA 360).size = 360 := Array.size_ofFn
      exact arr_eq_of_rep hs (unpack_size _ _ _) rep_idA (Orb.rep_unpack (Orb.prep_pidn hn hw))
    · rfl
    · rfl
    · have hs : (compA 360 (unpack 360 9 G8) (unpack 360 9 G9)).size = 360 := Array.size_ofFn
      have e : wK G8 G9 3 = pcomp 360 9 (mask 9) G8 G9 := rfl
      rw [e]
      exact arr_eq_of_rep hs (unpack_size _ _ _) (rep_compA hr.1 ht.1)
        (Orb.rep_unpack (Orb.prep_pcomp h32 hP8 hP9))
    · have hs : (compA 360 (unpack 360 9 G8) (unpack 360 9 G8)).size = 360 := Array.size_ofFn
      have e : wK G8 G9 4 = pcomp 360 9 (mask 9) G8 G8 := rfl
      rw [e]
      exact arr_eq_of_rep hs (unpack_size _ _ _) (rep_compA hr.1 hr.1)
        (Orb.rep_unpack (Orb.prep_pcomp h32 hP8 hP8))
    · have hs : (compA 360 (compA 360 (unpack 360 9 G8) (unpack 360 9 G8))
          (unpack 360 9 G9)).size = 360 := Array.size_ofFn
      have e : wK G8 G9 5 = pcomp 360 9 (mask 9) (pcomp 360 9 (mask 9) G8 G8) G9 := rfl
      rw [e]
      exact arr_eq_of_rep hs (unpack_size _ _ _)
        (rep_compA (rep_compA hr.1 hr.1) ht.1)
        (Orb.rep_unpack (Orb.prep_pcomp h32 (Orb.prep_pcomp h32 hP8 hP8) hP9))
  have hg : ∀ j < 6, ∃ g : Equiv.Perm (Fin 360),
      Rep 360 (wArrG (unpack 360 9 G8) (unpack 360 9 G9) j) g ∧ Orb.PRep 360 9 (wK G8 G9 j) g ∧
        Orb.PRep 360 9 (wIK I8 I9 j) g⁻¹ := by
    intro j hj
    have hrj := rep_permOfArr (Orb.isInvA_unpack
      ((hw1 j hj).1 : permOK 360 9 (mask 9) (360 * 9) (wK G8 G9 j) (wIK I8 I9 j) = true))
    rw [hW j hj]
    exact ⟨_, hrj.1, Orb.prep_of_rep hrj.1, Orb.prep_of_rep hrj.2⟩
  have nm : ∀ {A B : Array ℕ} {X Y : ℕ} {a b : Equiv.Perm (Fin 360)}, Rep 360 A a →
      Orb.PRep 360 9 X a → Rep 360 B b → Orb.PRep 360 9 Y b →
      siftC 360 9 LO TOI BPO 7 (pc 360 9 X Y) = false → memG 360 OS OB (compA 360 A B) = false := by
    intro A B X Y a b hA hX hB hY hs
    have hP := Orb.prep_pcomp h32 hX hY
    have e : compA 360 A B = unpack 360 9 (pc 360 9 X Y) :=
      arr_eq_of_rep (by simp [compA]) (unpack_size _ _ _) (rep_compA hA hB) (Orb.rep_unpack hP)
    unfold memG
    rw [e]
    exact (siftK_eq hbO hpO hlO rfl (PF.pcomp_shr _ _ h32 (by decide)) (range_of_prep hP)).trans hs
  obtain ⟨g1, hR1, hP1, -⟩ := hg 1 (by decide)
  obtain ⟨g2, hR2, hP2, hPI2⟩ := hg 2 (by decide)
  obtain ⟨g3, hR3, hP3, -⟩ := hg 3 (by decide)
  obtain ⟨g4, hR4, hP4, hPI4⟩ := hg 4 (by decide)
  obtain ⟨g5, hR5, hP5, -⟩ := hg 5 (by decide)
  have hR9 : Rep 360 (unpack 360 9 G9) g1 := hR1
  have hPG9 : Orb.PRep 360 9 G9 g1 := hP1
  unfold cosetCheckG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro i hi
    obtain ⟨g, hRg, -, -⟩ := hg i hi
    rw [Bool.and_eq_true]
    refine ⟨isInvA_of_rep hRg (rep_invCand hRg), ?_⟩
    unfold memG
    rw [hW i hi]
    exact siftK_sound hbA hpA hlA rfl (range_of_permOK (hw1 i hi).1) (hw1 i hi).2
  · rw [allLt_iff]
    intro i hi
    rw [allLt_iff]
    intro j hj
    rw [Bool.or_eq_true]
    rcases hw2 i hi j hj with he | hs
    · left
      rw [Nat.eq_of_beq_eq_true he]
      exact beq_self_eq_true _
    · right
      obtain ⟨gi, hRi, -, hPIi⟩ := hg i hi
      obtain ⟨gj, hRj, hPj, -⟩ := hg j hj
      rw [Bool.not_eq_true']
      exact nm hRj hPj (rep_invCand hRi) hPIi hs
  · rw [Bool.not_eq_true']
    exact nm hR2 hP2 hR2 hP2 hw3
  · rw [Bool.not_eq_true']
    exact nm hR4 hP4 hR4 hP4 hw4
  · rw [allLt_iff]
    intro j hj
    have h1 := hw5 j hj
    rw [Nat.ble_eq] at h1
    rw [hW (j + 2) (by omega), Orb.unpack_get (by decide)]
    exact decide_eq_true h1
  · rw [allLt_iff]
    intro p hp
    have h1 := hw6 p hp
    rw [Orb.bIf_eq, Orb.blt_dec, Orb.blt_dec] at h1
    rw [Orb.unpack_get hp]
    by_cases ha : pg 9 (mask 9) G9 p < 120 <;> by_cases hb : p < 120 <;> simp [ha, hb] at h1 ⊢
  · refine (eqA_iff (rep_compA hR9 hR9) rep_idA).2 ?_
    have hP := Orb.prep_pcomp h32 hPG9 hPG9
    have e : pcomp 360 9 (mask 9) G9 G9 = pidn 360 9 := Nat.eq_of_beq_eq_true hw7
    rw [e] at hP
    exact prep_unique' hP (Orb.prep_pidn hn hw)
  · unfold OmegaEight.conjArr
    refine (eqA_iff (rep_compA (rep_compA hR2 hR3) (rep_invCand hR2)) hR9).2 ?_
    have hP := Orb.prep_pcomp h32 (Orb.prep_pcomp h32 hP2 hP3) hPI2
    have e : pcomp 360 9 (mask 9) (pcomp 360 9 (mask 9) (wK G8 G9 2) (wK G8 G9 3))
        (wIK I8 I9 2) = G9 :=
      Nat.eq_of_beq_eq_true hw8
    rw [e] at hP
    exact prep_unique' hP hPG9
  · unfold OmegaEight.conjArr
    refine (eqA_iff (rep_compA (rep_compA hR4 hR5) (rep_invCand hR4)) hR9).2 ?_
    have hP := Orb.prep_pcomp h32 (Orb.prep_pcomp h32 hP4 hP5) hPI4
    have e : pcomp 360 9 (mask 9) (pcomp 360 9 (mask 9) (wK G8 G9 4) (wK G8 G9 5))
        (wIK I8 I9 4) = G9 := Nat.eq_of_beq_eq_true hw9
    rw [e] at hP
    exact prep_unique' hP hPG9

theorem minus_sound {g : Array ℕ} {LS : Array (Array ℕ)} {LB : Array ℕ} {G kS kO BP : Nat}
    {PS PSI LR TR TRI : Nat → Nat} {D : List (List Int)}
    (hL : LevelsK 136 8 PS PSI LR TR TRI kS kO 7 BP D LS LB) (hg : g = unpack 136 8 G)
    (hp : permOK 136 8 (mask 8) (136 * 8) G G = true) (h : minusOK G LR TRI BP = true) :
    minusCheckG g LS LB = true := by
  obtain ⟨hb, hh, hl⟩ := hL
  obtain ⟨s, hR, hs, hshr, -⟩ := perm_facts hp
  unfold minusOK at h
  simp only [ctAndB_eq, ctNotB_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  subst hg
  unfold minusCheckG memG
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨?_, ?_⟩
  · rw [siftK_eq hb (perm_head hh) hl rfl hshr (range_of_permOK hp)]
    exact h.1
  · refine (eqA_iff (rep_compA hR hR) rep_idA).2 ?_
    exact (congrArg (s * ·) hs.symm).trans (mul_inv_cancel s)

end CFSG.KC.O8

end
