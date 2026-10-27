module

public import CFSG.Certificates.Kernel.LocalQTPipeCoset

public section

namespace CFSG.KC.LQT.PPC

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.PPB
open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

theorem masks_core {N W : Nat} (hN : 0 < N) {Aa' Ab' par gen repR : Array Nat}
    {qp : List (Nat × Nat)} {tab : Nat → Array Nat} (xs : Array (List Nat))
    (TF MF : Nat → Nat) (ML REPS OML BM : List Nat) (BWL : List (List Nat))
    (PRK GNK RPK RIK QPK QGK DPK KM KR LR KB : Nat)
    (t0 : TabP N W (TF 0) Aa') (t1 : TabP N W (TF 1) Ab')
    (rP : Rep N W PRK par) (rG : Rep N W GNK gen) (rR : Rep N W RPK repR)
    (hpar : ∀ y < N, 0 < y → par.getD y 0 < y)
    (hT : ∀ p ∈ qp, TabP N W (TF p.1) (tab p.1))
    (hid : idK N W (MF 0) = true) (hM : needP W PRK ML = true)
    (hKM : lenA ML = KM) (hm : ∀ c < KM, omChk N W TF MF PRK GNK (getK ML c) = true)
    (hXM : ∀ l ∈ xs.toList, ∀ x ∈ l, x = 0 ∨ x ∈ ML)
    (hrs : repsSumK N REPS OML = true) (hKR : KR * LR = N)
    (hr : ∀ c < KR, repsChunk N W (qpK TF qp) RPK RIK QPK QGK DPK REPS OML (c * LR) LR = true)
    (hKB : xs.size = KB)
    (hb : ∀ h < KB, blockK N W (qpK TF qp) MF RPK REPS BM BWL xs.toList h = true) :
    ∀ h < xs.size,
      (∀ i < N, ((blocksOf (qp.map fun p => tab p.1) N Aa' Ab' par gen xs).getD h #[]).getD i
          false = true ↔ (getK BM h).testBit i = true) ∧
        ∀ i, N ≤ i → (getK BM h).testBit i = false := by
  have hMF := om_nodes hN t0 t1 rP rG hpar hid hM (by intro c hc; rw [hKM] at hc; exact hm c hc)
  have hROmT : List.Forall₂ (TabP N W) (qpK TF qp) (qp.map fun p => tab p.1) := by
    rw [qpK_eq]; exact f2_map qp (fun p => TF p.1) (fun p => tab p.1) hT
  have hall : ∀ i < N, repsAt N W (qpK TF qp) RPK RIK QPK QGK DPK REPS OML i = true := by
    intro i hi
    have hLR : 0 < LR := by
      rcases Nat.eq_zero_or_pos LR with h | h
      · rw [h] at hKR; omega
      · exact h
    have hc : i / LR < KR := by
      rw [Nat.div_lt_iff_lt_mul hLR]; omega
    have := allR_spec' (hr _ hc) (i % LR) (Nat.mod_lt _ hLR)
    have e : i / LR * LR + i % LR = i := by
      have := Nat.div_add_mod i LR; rw [Nat.mul_comm] at this; exact this
    rwa [e] at this
  obtain ⟨R1, R2⟩ := reps_sound hN hT rR hrs hall
  have hTS : ∀ h < xs.size, List.Forall₂ (TabP N W)
      (gensK (qpK TF qp) MF (getT xs.toList h))
      ((qp.map fun p => tab p.1) ++
        (xs.getD h []).map fun x => omegaOf N Aa' Ab' par gen x x) := by
    intro h hh
    rw [gensK_eq, getT_eq, xs_getD_toList]
    refine f2_append hROmT (f2_map _ MF _ fun x hx => (hMF x ?_).2)
    exact hXM _ (xs_getD_mem xs hh) x hx
  have hRO : ∀ (ts : List (Array Nat)), (∀ t ∈ (qp.map fun p => tab p.1), t ∈ ts) →
      ∀ i < N, Reach ts (repR.getD i 0) i := fun ts hts i hi => reach_mono hts (R2 i hi)
  have hmask : ∀ h < xs.size, MaskOf N ((qp.map fun p => tab p.1) ++
      (xs.getD h []).map fun x => omegaOf N Aa' Ab' par gen x x) (getK BM h) := by
    intro h hh
    have hbh := hb h (by omega)
    have e : blockK N W (qpK TF qp) MF RPK REPS BM BWL xs.toList h =
        orbChk N W (gensK (qpK TF qp) MF (getT xs.toList h)) RPK REPS (getK BM h)
          (getT BWL h) := rfl
    rw [e] at hbh
    obtain ⟨f1, f2, f3, f4⟩ := f2_facts (hTS h hh)
    exact orbChk_sound hN rR (hRO _ (fun t ht => List.mem_append_left _ ht)) R1 f1 f2 f3 f4 hbh
  intro h hh
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hblk : (blocksOf (qp.map fun p => tab p.1) N Aa' Ab' par gen xs).getD h #[] =
        bfsVis N ((qp.map fun p => tab p.1) ++
          (xs.getD h []).map fun x => omegaOf N Aa' Ab' par gen x x) 0 :=
      blocksOf_getD' _ N Aa' Ab' par gen xs hh
    rw [hblk, bfsVis_getD_iff N _ (f2_facts (hTS h hh)).2.2.1 hN hi]
    exact (and_iff_right hi).symm.trans ((hmask h hh) i).symm
  · by_contra hne
    have := ((hmask h hh) i).1 (by simpa using hne)
    omega

theorem masks_sound {N W : Nat} (hW : N ≤ 2 ^ W) (hN : 0 < N)
    (Aa Ab ps gs rs : Array (Array Nat)) (prog qp : List (Nat × Nat)) (xs : Array (List Nat))
    (TF MF : Nat → Nat) (SL ML REPS OML BM : List Nat) (BWL : List (List Nat))
    (PRK GNK RPK RIK QPK QGK DPK KS KM KR LR KB : Nat)
    (hA : PP.permK N (chunksK Aa) = true) (hB : PP.permK N (chunksK Ab) = true)
    (h0 : Nat.beq (codeK W (chunksK Aa)) (TF 0) = true)
    (h1 : Nat.beq (codeK W (chunksK Ab)) (TF 1) = true)
    (htree : treeK N (chunksK ps) (chunksK gs) = true)
    (hpt : tabL N (chunksK ps) = true) (hgt : tabL N (chunksK gs) = true)
    (hrt : tabL N (chunksK rs) = true)
    (hPK : Nat.beq (codeK W (chunksK ps)) PRK = true)
    (hGK : Nat.beq (codeK W (chunksK gs)) GNK = true)
    (hRK : Nat.beq (codeK W (chunksK rs)) RPK = true)
    (hso : slpOKK prog 2 = true) (hsn : slpNeedK prog SL = true)
    (hq : allA qp (fun p => anyL SL (Nat.beq p.1)) = true)
    (hKS : lenA SL = KS) (hs : ∀ c < KS, slpChk N W TF prog (getK SL c) = true)
    (hid : idK N W (MF 0) = true) (hM : needP W PRK ML = true)
    (hKM : lenA ML = KM) (hm : ∀ c < KM, omChk N W TF MF PRK GNK (getK ML c) = true)
    (hXM : allA xs.toList (fun l => allL l fun x => orB (Nat.beq x 0) (anyL ML (Nat.beq x))) =
      true)
    (hrs : repsSumK N REPS OML = true) (hKR : KR * LR = N)
    (hr : ∀ c < KR, repsChunk N W (qpK TF qp) RPK RIK QPK QGK DPK REPS OML (c * LR) LR = true)
    (hKB : xs.size = KB)
    (hb : ∀ h < KB, blockK N W (qpK TF qp) MF RPK REPS BM BWL xs.toList h = true) :
    ∀ h < xs.size,
      (∀ i < N, ((blocksOf (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab)
          prog)[p.1]!) N (Array.flatten Aa) (Array.flatten Ab) (Array.flatten ps)
          (Array.flatten gs) xs).getD h #[]).getD i false = true ↔
          (getK BM h).testBit i = true) ∧
        ∀ i, N ≤ i → (getK BM h).testBit i = false := by
  have t0 : TabP N W (TF 0) (Array.flatten Aa) := tabP_of_perm hW hA h0
  have t1 : TabP N W (TF 1) (Array.flatten Ab) := tabP_of_perm hW hB h1
  have tv := tree_sound N ps gs htree
  have hpar : ∀ y < N, 0 < y → (Array.flatten ps).getD y 0 < y :=
    fun y hy hy0 => (tv.2.2 y hy hy0).1
  have rP : Rep N W PRK (Array.flatten ps) := rep_of_tab hW hpt hPK
  have rG : Rep N W GNK (Array.flatten gs) := rep_of_tab hW hgt hGK
  have rR : Rep N W RPK (Array.flatten rs) := rep_of_tab hW hrt hRK
  have hsl := slp_nodes t0 t1 hso hsn (by intro c hc; rw [hKS] at hc; exact hs c hc)
  have hT : ∀ p ∈ qp, TabP N W (TF p.1)
      ((slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) := by
    intro p hp
    rw [allA_eq, List.all_eq_true] at hq
    exact (hsl p.1 (Or.inr ((any_beq_iff SL p.1).1 (hq p hp)))).2
  have hXM' : ∀ l ∈ xs.toList, ∀ x ∈ l, x = 0 ∨ x ∈ ML := by
    intro l hl x hx
    rw [allA_eq, List.all_eq_true] at hXM
    have := hXM l hl
    rw [allL_iff] at this
    have := this x hx
    rw [orB_iff, beq_iff, any_beq_iff] at this
    exact this
  exact masks_core (tab := fun j => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[j]!)
    hN xs TF MF ML REPS OML BM BWL PRK GNK RPK RIK QPK QGK DPK KM KR LR KB t0 t1 rP rG rR hpar hT
    hid hM hKM hm hXM' hrs hKR hr hKB hb

end CFSG.KC.LQT.PPC

end
