module

public import Certificates.Data.Kernel.Misc.ArrEnum
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Monster.B.Mathieu.SylowCore
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.Misc.ArrEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2
open CFSG.KC.BfsPin (PP eqA_PP compA_PP invCand_PP idA_eq validA_unpack)
open CFSG.KS.PinvS (permOK_pinvS)

theorem anyNP_eq (m : ℕ) (f : ℕ → Bool) : CFSG.KC.LQT.P.anyN m f = (List.range m).any f := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change CFSG.KC.Ord.orB (f m) (CFSG.KC.LQT.P.anyN m f) = _
    rw [ih, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_comm]
    cases f m <;> rfl

theorem allNP_eq (m : ℕ) (f : ℕ → Bool) : CFSG.KC.LQT.P.allN m f = (List.range m).all f := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change CFSG.KC.Ord.andB (f m) (CFSG.KC.LQT.P.allN m f) = _
    rw [ih, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_comm]
    cases f m <;> rfl

theorem allNP_iff {m : ℕ} {f : ℕ → Bool} :
    CFSG.KC.LQT.P.allN m f = true ↔ ∀ i < m, f i = true := by
  rw [allNP_eq, List.all_eq_true]
  exact ⟨fun h i hi => h i (List.mem_range.2 hi), fun h x hx => h x (List.mem_range.1 hx)⟩

@[expose] def Ag (n w : ℕ) (t : Array ℕ) (P : ℕ) : Prop :=
  ∀ x < n, t[x]! = pg w (mask w) P x

theorem ag_unpack (n w P : ℕ) : Ag n w (unpack n w P) P := fun _ hx => Orb.unpack_get hx

theorem eqA_congr {n : ℕ} {t t' u u' : Array ℕ} (ht : ∀ x < n, t[x]! = t'[x]!)
    (hu : ∀ x < n, u[x]! = u'[x]!) : eqA n t u = eqA n t' u' := by
  apply Bool.eq_iff_iff.2
  rw [eqA, eqA, allLt_iff, allLt_iff]
  constructor
  · intro h x hx
    rw [← ht x hx, ← hu x hx]
    exact h x hx
  · intro h x hx
    rw [ht x hx, hu x hx]
    exact h x hx

theorem eqA_ag {n w : ℕ} {t u : Array ℕ} {P Q : ℕ} (ht : Ag n w t P) (hu : Ag n w u Q)
    (hP : PP n w P) (hQ : PP n w Q) : eqA n t u = Nat.beq P Q := by
  rw [eqA_congr (t' := unpack n w P) (u' := unpack n w Q)
    (fun x hx => by rw [ht x hx, Orb.unpack_get hx])
    (fun x hx => by rw [hu x hx, Orb.unpack_get hx])]
  exact eqA_PP hP hQ

theorem ag_compA {n w : ℕ} {t u : Array ℕ} {P Q : ℕ} (hn : n < 2 ^ 32) (ht : Ag n w t P)
    (hu : Ag n w u Q) (hQ : ∀ x < n, pg w (mask w) Q x < n) :
    Ag n w (compA n t u) (pcomp n w (mask w) P Q) := fun x hx => by
  rw [compA_get hx, hu x hx, ht _ (hQ x hx), PF.pg_pcomp hn hx]

variable {n w : ℕ} (hw : szOK n w = true)
include hw

theorem pp_of_permOK {p q : ℕ} (h : permOK n w (mask w) (n * w) p q = true) : PP n w p := by
  obtain ⟨h1, -, h3⟩ := Orb.permOK_facts h
  have hc : CFSG.KS.Prim.canonK n w (mask w) (n * w) p = true := by
    unfold CFSG.KS.Prim.canonK
    simp only [bAnd_iff]
    exact ⟨hw, Nat.beq_eq.mpr h1, Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (h3 i hi).1⟩
  refine ⟨hc, ⟨fun i hi => (h3 i hi).1, fun a ha b hb e => ?_⟩⟩
  rw [← (h3 a ha).2, ← (h3 b hb).2, e]

theorem pp_of_permB {p : ℕ} (hp : permB n w p = true) : PP n w p :=
  pp_of_permOK hw hp

omit hw in
theorem permB_of_pp {p : ℕ} (hp : PP n w p) : permB n w p = true :=
  permOK_pinvS hp.1 hp.2

theorem pp_ppow {p : ℕ} (hp : PP n w p) (e : ℕ) : PP n w (ppow n w (mask w) (pidn n w) p e) := by
  induction e with
  | zero => exact CFSG.KC.BfsPin.PP.id hw
  | succ e ih =>
    have e1 : ppow n w (mask w) (pidn n w) p (e + 1) =
        pcomp n w (mask w) p (ppow n w (mask w) (pidn n w) p e) :=
      PF.strictN_eqP (ppow n w (mask w) (pidn n w) p e) (fun q => pcomp n w (mask w) p q)
    rw [e1]
    exact hp.mul ih

theorem comp_unpack' {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    compA n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) :=
  compA_PP (pp_of_permB hw hp) (pp_of_permB hw hq)

theorem eqA_unpack' {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    eqA n (unpack n w p) (unpack n w q) = Nat.beq p q :=
  eqA_PP (pp_of_permB hw hp) (pp_of_permB hw hq)

theorem pow_unpack' {p : ℕ} (hp : permB n w p = true) (e : ℕ) :
    CFSG.Monster.B.Mathieu.powArr n (unpack n w p) e =
      unpack n w (ppow n w (mask w) (pidn n w) p e) := by
  have hP := pp_of_permB hw hp
  induction e with
  | zero => exact idA_eq hw
  | succ e ih =>
    have e1 : ppow n w (mask w) (pidn n w) p (e + 1) =
        pcomp n w (mask w) p (ppow n w (mask w) (pidn n w) p e) :=
      PF.strictN_eqP (ppow n w (mask w) (pidn n w) p e) (fun q => pcomp n w (mask w) p q)
    change compA n (unpack n w p) (CFSG.Monster.B.Mathieu.powArr n (unpack n w p) e) = _
    rw [ih, e1, compA_PP hP (pp_ppow hw hP e)]

theorem conj_unpack' {p q : ℕ} (hp : permB n w p = true) (hq : permB n w q = true) :
    conjA n (unpack n w p) (unpack n w q) =
      unpack n w (pcomp n w (mask w) p (pcomp n w (mask w) q (pinvS n w (mask w) p))) := by
  have hP := pp_of_permB hw hp
  have hQ := pp_of_permB hw hq
  rw [conjA, invCand_PP hP, compA_PP hQ hP.inv, compA_PP hP (hQ.mul hP.inv)]

theorem any_eqA_unpack' {N : ℕ} {PT : ℕ → ℕ} {c : CFSG.Monster.B.Fischer.ArrCert}
    (hN : c.pts.size = N) (hP : ∀ i < N, c.pts[i]! = unpack n w (PT i))
    (hPp : ∀ i < N, permB n w (PT i) = true) {p : ℕ} (hp : permB n w p = true) :
    c.pts.toList.any (eqA n (unpack n w p)) = memK N PT p := by
  have hl : c.pts.toList = (List.range N).map fun i => unpack n w (PT i) := by
    apply List.ext_getElem
    · simp [hN]
    · intro i h1 h2
      rw [Array.getElem_toList, List.getElem_map, List.getElem_range,
        ← hP i (by simpa [hN] using h1), getElem!_pos c.pts i (by simpa using h1)]
  rw [hl, memK, anyNP_eq]
  apply Bool.eq_iff_iff.2
  simp only [List.any_map, List.any_eq_true, List.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, by rwa [eqA_PP (pp_of_permB hw hp) (pp_of_permB hw (hPp i hi))] at h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, by rwa [eqA_PP (pp_of_permB hw hp) (pp_of_permB hw (hPp i hi))]⟩

theorem letter_code {SC SIC : ℕ → ℕ} {z : ℤ} (hz : z ≠ 0) :
    Bool.rec (motive := fun _ => ℕ)
      (SIC (Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 1)))
      (SC (Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 1)))
      (Nat.beq (Nat.land (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 0)) =
      if 0 < z then SC (z.toNat - 1) else SIC ((-z).toNat - 1) := by
  have _ := hw
  cases z with
  | ofNat k =>
    have ec : CFSG.KS.Mathieu.icode (Int.ofNat k) = k + k := rfl
    have hk0 : k ≠ 0 := fun h => hz (by simp [h])
    have e1 : Nat.land (k + k) 1 = 0 := by
      change (k + k) &&& 1 = 0
      rw [Nat.and_one_is_mod]
      omega
    have e2 : Nat.shiftRight (k + k) 1 = k := by
      rw [Orb.shr_eq]
      omega
    have hpos : (0 : ℤ) < Int.ofNat k := by
      have : 0 < k := Nat.pos_of_ne_zero hk0
      exact Int.ofNat_lt.mpr this
    rw [ec, e1, e2]
    simp only [hpos, ↓reduceIte]
    rfl
  | negSucc k =>
    have ec : CFSG.KS.Mathieu.icode (Int.negSucc k) = (k + 1) + (k + 1) + 1 := rfl
    have e1 : Nat.land ((k + 1) + (k + 1) + 1) 1 = 1 := by
      change ((k + 1) + (k + 1) + 1) &&& 1 = 1
      rw [Nat.and_one_is_mod]
      omega
    have e2 : Nat.shiftRight ((k + 1) + (k + 1) + 1) 1 = k + 1 := by
      rw [Orb.shr_eq]
      omega
    have hneg : ¬ (0 : ℤ) < Int.negSucc k := by
      have := Int.negSucc_lt_zero k
      omega
    have et : (-(Int.negSucc k)).toNat - 1 = k := by
      rw [Int.neg_negSucc]
      rfl
    rw [ec, e1, e2, et]
    simp only [hneg, ↓reduceIte]
    rfl

theorem pp_wordK {SC SIC : ℕ → ℕ} {j : ℕ} (hSp : ∀ h < j, permB n w (SC h) = true)
    (hSIp : ∀ h < j, permB n w (SIC h) = true) :
    ∀ wd : List ℤ, CFSG.Monster.B.Co2.Native.lettersOK j wd = true →
      PP n w (CFSG.KS.Raw.wordK n w (mask w) (pidn n w) SC SIC wd)
  | [], _ => CFSG.KC.BfsPin.PP.id hw
  | z :: wd, hl => by
    simp only [CFSG.Monster.B.Co2.Native.lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hl
    obtain ⟨⟨hz, hzj⟩, hl⟩ := hl
    rw [Orb.wordK_cons, letter_code hw hz]
    refine CFSG.KC.BfsPin.PP.mul ?_ (pp_wordK hSp hSIp wd hl)
    by_cases h0 : 0 < z
    · simp only [h0, ↓reduceIte]
      exact pp_of_permB hw (hSp _ (by omega))
    · simp only [h0, ↓reduceIte]
      exact pp_of_permB hw (hSIp _ (by omega))

theorem wordA_eq {S Sinv : Array (Array ℕ)} {SC SIC : ℕ → ℕ} {j : ℕ}
    (hS : ∀ h < j, S[h]! = unpack n w (SC h)) (hSI : ∀ h < j, Sinv[h]! = unpack n w (SIC h))
    (hSp : ∀ h < j, permB n w (SC h) = true) (hSIp : ∀ h < j, permB n w (SIC h) = true) :
    ∀ wd : List ℤ, CFSG.Monster.B.Co2.Native.lettersOK j wd = true →
      CFSG.Monster.B.Co2.Native.wordA n S Sinv wd =
        unpack n w (CFSG.KS.Raw.wordK n w (mask w) (pidn n w) SC SIC wd)
  | [], _ => idA_eq hw
  | z :: wd, hl => by
    have hl' := hl
    simp only [CFSG.Monster.B.Co2.Native.lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hl'
    obtain ⟨⟨hz, hzj⟩, hl'⟩ := hl'
    have ih := wordA_eq hS hSI hSp hSIp wd hl'
    have hW := pp_wordK hw hSp hSIp wd hl'
    rw [Orb.wordK_cons, letter_code hw hz]
    change compA n (CFSG.Monster.B.Co2.Native.letterA S Sinv z)
      (CFSG.Monster.B.Co2.Native.wordA n S Sinv wd) = _
    unfold CFSG.Monster.B.Co2.Native.letterA
    rw [ih]
    by_cases h0 : 0 < z
    · simp only [h0, ↓reduceIte]
      have hk : z.toNat - 1 < j := by omega
      rw [hS _ hk, compA_PP (pp_of_permB hw (hSp _ hk)) hW]
    · simp only [h0, ↓reduceIte]
      have hk : (-z).toNat - 1 < j := by omega
      rw [hSI _ hk, compA_PP (pp_of_permB hw (hSIp _ hk)) hW]

omit hw in
theorem keyA_unpackK {ps : List ℕ} (hps : ∀ p ∈ ps, p < n) (P : ℕ) :
    keyA n ps (unpack n w P) = keyK n w ps P := by
  unfold keyA keyK
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, Nat.ofDigits_cons, ih fun q hq => hps q (List.mem_cons_of_mem p hq),
      List.foldr_cons, Orb.unpack_get (hps p List.mem_cons_self)]
    rfl

theorem enumK_sound' {ngen N : ℕ} {G PT : ℕ → ℕ} {gs : Array (Array ℕ)} {ps : List ℕ}
    {c : CFSG.Monster.B.Fischer.ArrCert} (hps : ∀ p ∈ ps, p < n)
    (hgs : gs.size = ngen) (hG : ∀ k < ngen, gs[k]! = unpack n w (G k))
    (hN : c.pts.size = N) (hP : ∀ i < N, c.pts[i]! = unpack n w (PT i))
    {E : ℕ → ℕ → ℕ} {PAR LAB : ℕ → ℕ}
    (hE : ∀ i < N, (c.edges[i]!).size = ngen ∧ ∀ k < ngen, (c.edges[i]!)[k]! = E i k)
    (hPL : ∀ i < N, c.par[i]! = PAR i ∧ c.lab[i]! = LAB i)
    (hh : headK n w ngen N G PT = true)
    (hp : ∀ i < N, pointK n w ngen N G PT E PAR LAB i = true)
    (hk : ∀ i < N, ∀ j < i, keyK n w ps (PT i) ≠ keyK n w ps (PT j)) :
    enumOK n gs ps c = true := by
  unfold headK at hh
  simp only [Bool.and_eq_true, Nat.blt_eq] at hh
  obtain ⟨⟨hGp, hN0⟩, hT0⟩ := hh
  have hGP : ∀ k < ngen, PP n w (G k) := fun k hk1 => pp_of_permB hw (allNP_iff.1 hGp k hk1)
  have hpt : ∀ i < N, PP n w (PT i) ∧
      (∀ k < ngen, E i k < N ∧ PT (E i k) = pcomp n w (mask w) (G k) (PT i)) ∧
      (i = 0 ∨ (PAR i < i ∧ LAB i < ngen ∧
        PT i = pcomp n w (mask w) (G (LAB i)) (PT (PAR i)))) := by
    intro i hi
    have h := hp i hi
    unfold pointK at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨pp_of_permB hw h1, fun k hk1 => ?_, h3.imp id fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    have := allNP_iff.1 h2 k hk1
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact this
  have hleft : ∀ k < ngen, ∀ i < N, leftA n gs k c.pts[i]! =
      unpack n w (pcomp n w (mask w) (G k) (PT i)) := by
    intro k hk1 i hi
    rw [leftA, hG k hk1, hP i hi, compA_PP (hGP k hk1) (hpt i hi).1]
  unfold enumOK CFSG.Monster.B.Fischer.arrCertOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨?_, ⟨⟨?_, ?_⟩, fun i hi => ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk1
    rw [hgs] at hk1
    rw [hG k hk1]
    exact validA_unpack (allNP_iff.1 hGp k hk1)
  · rw [hN]
    exact hN0
  · rw [hP 0 (by rw [← hN] at hN0; omega), Nat.eq_of_beq_eq_true hT0]
    exact (idA_eq hw).symm
  · rw [hN] at hi
    obtain ⟨hpp, hed, hpar⟩ := hpt i hi
    unfold CFSG.Monster.B.Fischer.arrPointOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      beq_iff_eq, Bool.or_eq_true, hgs, hN]
    refine ⟨⟨⟨?_, (hE i hi).1⟩, fun k hk1 => ?_⟩, ?_⟩
    · rw [hP i hi]
      exact validA_unpack (permB_of_pp hpp)
    · rw [(hE i hi).2 k hk1]
      refine ⟨(hed k hk1).1, ?_⟩
      rw [hP _ (hed k hk1).1, hleft k hk1 i hi, (hed k hk1).2]
    · rcases hpar with h0 | ⟨hpi, hli, he⟩
      · exact Or.inl h0
      · refine Or.inr ⟨⟨?_, ?_⟩, ?_⟩
        · rw [(hPL i hi).1]
          exact hpi
        · rw [(hPL i hi).2]
          exact hli
        · rw [(hPL i hi).1, (hPL i hi).2, hleft _ hli _ (by omega), hP i hi, he]
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

end CFSG.KC.Misc.ArrEnum

end
