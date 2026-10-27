module

public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.Monster.B.Mathieu.SylowCore
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.Misc.ArrEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native CFSG.Monster.B.Co2.Native

theorem enumK_sound {n w ngen N : ℕ} {G PT : ℕ → ℕ} {gs : Array (Array ℕ)} {ps : List ℕ}
    {c : CFSG.Monster.B.Fischer.ArrCert} (hw : szOK n w = true) (hps : ∀ p ∈ ps, p < n)
    (hgs : gs.size = ngen) (hG : ∀ k < ngen, gs[k]! = unpack n w (G k))
    (hN : c.pts.size = N) (hP : ∀ i < N, c.pts[i]! = unpack n w (PT i))
    {E : ℕ → ℕ → ℕ} {PAR LAB : ℕ → ℕ}
    (hE : ∀ i < N, (c.edges[i]!).size = ngen ∧ ∀ k < ngen, (c.edges[i]!)[k]! = E i k)
    (hPL : ∀ i < N, c.par[i]! = PAR i ∧ c.lab[i]! = LAB i)
    (hh : headK n w ngen N G PT = true)
    (hp : ∀ i < N, pointK n w ngen N G PT E PAR LAB i = true)
    (hk : ∀ i < N, ∀ j < i, keyK n w ps (PT i) ≠ keyK n w ps (PT j)) :
    enumOK n gs ps c = true :=
  enumK_sound' hw hps hgs hG hN hP hE hPL hh hp hk

theorem certA_sound {n w ngen N R : ℕ} {G PT : ℕ → ℕ} {gs : Array (Array ℕ)} {ps : List ℕ}
    {valid : Array ℕ → Bool} {c : CFSG.Monster.B.Fischer.ArrCert} (hw : szOK n w = true)
    (hps : ∀ p ∈ ps, p < n) (hG : ∀ k < ngen, gs[k]! = unpack n w (G k))
    (hGp : ∀ k < ngen, permB n w (G k) = true)
    (hN : c.pts.size = N) (hP : ∀ i < N, c.pts[i]! = unpack n w (PT i))
    {E : ℕ → ℕ → ℕ} {PAR LAB : ℕ → ℕ}
    (hE : ∀ i < N, (c.edges[i]!).size = ngen ∧ ∀ k < ngen, (c.edges[i]!)[k]! = E i k)
    (hPL : ∀ i < N, c.par[i]! = PAR i ∧ c.lab[i]! = LAB i)
    (hpos : 0 < N) (hR : PT 0 = R) (hv : ∀ i < N, valid c.pts[i]! = true)
    (hp : ∀ i < N, pointA n w ngen N (conjAct n w G) PT E PAR LAB i = true)
    (hk : ∀ i < N, ∀ j < i, keyK n w ps (PT i) ≠ keyK n w ps (PT j)) :
    CFSG.Monster.B.Fischer.arrCertOK (fun k t => conjA n gs[k]! t) ngen valid (keyA n ps)
      (unpack n w R) c = true := by
  have hpt : ∀ i < N, permB n w (PT i) = true ∧
      (∀ k < ngen, E i k < N ∧ PT (E i k) = conjAct n w G k (PT i)) ∧
      (i = 0 ∨ (PAR i < i ∧ LAB i < ngen ∧ PT i = conjAct n w G (LAB i) (PT (PAR i)))) := by
    intro i hi
    have h := hp i hi
    unfold pointA at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨h1, fun k hk1 => ?_, h3.imp id fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    have := allNP_iff.1 h2 k hk1
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact this
  have hact : ∀ k < ngen, ∀ i < N, conjA n gs[k]! c.pts[i]! =
      unpack n w (conjAct n w G k (PT i)) := by
    intro k hk1 i hi
    show _ = unpack n w (pcomp n w (mask w) (G k)
      (pcomp n w (mask w) (PT i) (pinvS n w (mask w) (G k))))
    rw [hG k hk1, hP i hi, conj_unpack' hw (hGp k hk1) (hpt i hi).1]
  unfold CFSG.Monster.B.Fischer.arrCertOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨⟨⟨?_, ?_⟩, fun i hi => ?_⟩, ?_⟩
  · rw [hN]
    exact hpos
  · rw [hP 0 hpos, hR]
  · rw [hN] at hi
    obtain ⟨_, hed, hpar⟩ := hpt i hi
    unfold CFSG.Monster.B.Fischer.arrPointOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      beq_iff_eq, Bool.or_eq_true, hN]
    refine ⟨⟨⟨hv i hi, (hE i hi).1⟩, fun k hk1 => ?_⟩, ?_⟩
    · rw [(hE i hi).2 k hk1]
      refine ⟨(hed k hk1).1, ?_⟩
      rw [hP _ (hed k hk1).1, hact k hk1 i hi, (hed k hk1).2]
    · rcases hpar with h0 | ⟨hpi, hli, he⟩
      · exact Or.inl h0
      · refine Or.inr ⟨⟨?_, ?_⟩, ?_⟩
        · rw [(hPL i hi).1]
          exact hpi
        · rw [(hPL i hi).2]
          exact hli
        · rw [(hPL i hi).1, (hPL i hi).2, hact _ hli _ (by omega), hP i hi, he]
  · have hl : c.pts.toList.map (keyA n ps) = (List.range N).map fun i => keyK n w ps (PT i) := by
      apply List.ext_getElem
      · simp [hN]
      · intro i h1 h2
        have hi : i < N := by simpa [hN] using h1
        rw [List.getElem_map, Array.getElem_toList, List.getElem_map, List.getElem_range,
          ← getElem!_pos c.pts i (by simpa using h1 : i < c.pts.size), hP i hi,
          keyA_unpackK hps]
    rw [hl]
    have hnd : ((List.range N).map fun i => keyK n w ps (PT i)).Nodup := by
      refine List.Nodup.map_on (fun a ha b hb e => ?_) List.nodup_range
      rw [List.mem_range] at ha hb
      rcases Nat.lt_trichotomy a b with h' | h' | h'
      · exact absurd e.symm (hk b hb a h')
      · exact h'
      · exact absurd e (hk a ha b h')
    generalize ((List.range N).map fun i => keyK n w ps (PT i)) = l at hnd
    have hs := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
    have hnd' : (l.mergeSort fun a b => decide (a ≤ b)).Nodup :=
      (List.mergeSort_perm l _).nodup_iff.2 hnd
    refine (hs.and hnd').imp fun hab => ?_
    simp only [decide_eq_true_eq] at hab
    omega

private theorem unpack_get' {n w P i : ℕ} (hi : i < n) :
    (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem validA_unpack {n w p r : ℕ}
    (h : CFSG.KS.Prim.invEqK n w (mask w) (n * w) p r = true) :
    validA n (unpack n w p) = true := by
  obtain ⟨h1, h2⟩ := CFSG.KS.Prim.invEqK_sound h
  rw [validA, h1]
  exact h2

section Ops

variable {n w : ℕ} (hw : szOK n w = true)
include hw

theorem comp_unpack {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    compA n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) :=
  comp_unpack' hw hp hq

theorem inv_unpack {p : ℕ} (hp : permB n w p = true) :
    invCand n (unpack n w p) = unpack n w (pinvS n w (mask w) p) :=
  (CFSG.KS.Prim.invEqK_sound hp).1

theorem eqA_unpack {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    eqA n (unpack n w p) (unpack n w q) = Nat.beq p q :=
  eqA_unpack' hw hp hq

theorem pow_unpack {p : ℕ} (hp : permB n w p = true) (e : ℕ) :
    CFSG.Monster.B.Mathieu.powArr n (unpack n w p) e =
      unpack n w (ppow n w (mask w) (pidn n w) p e) :=
  pow_unpack' hw hp e

theorem conj_unpack {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    conjA n (unpack n w p) (unpack n w q) =
      unpack n w (pcomp n w (mask w) p (pcomp n w (mask w) q (pinvS n w (mask w) p))) :=
  conj_unpack' hw hp hq

theorem conjInv_unpack {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    conjInvA n (unpack n w p) (unpack n w q) =
      unpack n w (pcomp n w (mask w) (pinvS n w (mask w) p) (pcomp n w (mask w) q p)) := by
  have hP := pp_of_permB hw hp
  have hQ := pp_of_permB hw hq
  rw [conjInvA, CFSG.KC.BfsPin.invCand_PP hP, CFSG.KC.BfsPin.compA_PP hQ hP,
    CFSG.KC.BfsPin.compA_PP hP.inv (hQ.mul hP)]

theorem commutator_unpack {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    commutatorA n (unpack n w p) (unpack n w q) =
      unpack n w (pcomp n w (mask w) (pcomp n w (mask w) p q)
        (pcomp n w (mask w) (pinvS n w (mask w) p) (pinvS n w (mask w) q))) := by
  have hP := pp_of_permB hw hp
  have hQ := pp_of_permB hw hq
  rw [commutatorA, CFSG.KC.BfsPin.invCand_PP hP, CFSG.KC.BfsPin.invCand_PP hQ,
    CFSG.KC.BfsPin.compA_PP hP hQ, CFSG.KC.BfsPin.compA_PP hP.inv hQ.inv,
    CFSG.KC.BfsPin.compA_PP (hP.mul hQ) (hP.inv.mul hQ.inv)]

theorem any_eqA_unpack {N : ℕ} {PT : ℕ → ℕ} {c : CFSG.Monster.B.Fischer.ArrCert}
    (hN : c.pts.size = N) (hP : ∀ i < N, c.pts[i]! = unpack n w (PT i))
    (hPp : ∀ i < N, permB n w (PT i) = true) {p : ℕ} (hp : permB n w p = true) :
    c.pts.toList.any (eqA n (unpack n w p)) = memK N PT p :=
  any_eqA_unpack' hw hN hP hPp hp

theorem fixedCount_unpack (P : ℕ) :
    CFSG.ComponentClassification.J2Cover.fixedCount n (unpack n w P) = fixK n w P := by
  have _ := hw
  suffices h : ∀ m, m ≤ n → (List.range m).countP (fun i => (unpack n w P)[i]! == i) =
      Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun i acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
          (Nat.beq (pg w (mask w) P i) i))) m from h n le_rfl
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.countP_append, ih (by omega), List.countP_singleton,
      unpack_get' (by omega)]
    change _ = Nat.add _ _
    cases e : Nat.beq (pg w (mask w) P m) m
    · have hne := PackFld.false_of_beq e
      simp [hne]
    · have : (pg w (mask w) P m == m) = true := by simpa [Nat.beq_eq] using e
      simp [this]

end Ops

theorem all_contains_unpack {n w P : ℕ} {S T : Array ℕ} (hS : ∀ q ∈ S.toList, q < n) :
    (S.all fun q => T.contains (unpack n w P)[q]!) =
      S.all fun q => T.contains (pg w (mask w) P q) := by
  rw [← Array.all_toList, ← Array.all_toList]
  generalize S.toList = l at hS ⊢
  induction l with
  | nil => rfl
  | cons q l ih =>
    rw [List.all_cons, List.all_cons, unpack_get' (hS q List.mem_cons_self),
      ih (fun x hx => hS x (List.mem_cons_of_mem _ hx))]

end CFSG.KC.Misc.ArrEnum

end
