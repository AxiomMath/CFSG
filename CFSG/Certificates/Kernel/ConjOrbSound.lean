module

public import Certificates.Data.Kernel.ConjOrb
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace CFSG.KC.ConjOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.KC.Bfs CFSG.KC.BfsPin
open CFSG.KLie.CT (fget)

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem headK_spec {n w ng : Nat} {G GI : Nat → Nat} (h : headK n w ng G GI = true) :
    szOK n w = true ∧ ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true ∧
      canonK n w (mask w) (n * w) (GI k) = true ∧
      permOK n w (mask w) (n * w) (G k) (GI k) = true := by
  unfold headK at h
  rw [bAnd_iff] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have h2 := allN_spec h.2 k hk
  simp only [bAnd_iff] at h2
  exact ⟨h2.1, h2.2.1, h2.2.2⟩

theorem closPt_spec {n w ng N : Nat} {G GI T E : Nat → Nat} {i : Nat}
    (h : closPt n w ng N G GI T E i = true) :
    canonK n w (mask w) (n * w) (T i) = true ∧ ∀ k < ng, fget (E i) k 20 < N ∧
      pconj n w (mask w) (G k) (GI k) (T i) = T (fget (E i) k 20) := by
  unfold closPt at h
  rw [strictB_eq, strictB_eq, bAnd_iff] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have h2 := allN_spec h.2 k hk
  rw [strictB_eq, bAnd_iff] at h2
  exact ⟨Nat.blt_eq.mp h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem treePt_spec {ng N r : Nat} {E D : Nat → Nat} {i : Nat} (h : treePt ng N r E D i = true)
    (hi : i ≠ r) :
    tPar (D i) < N ∧ tLab (D i) < ng ∧ fget (E (tPar (D i))) (tLab (D i)) 20 = i ∧
      tDep (D (tPar (D i))) + 1 = tDep (D i) := by
  unfold treePt at h
  have hb : Nat.beq i r = false := by
    cases e : Nat.beq i r
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hi
  rw [hb] at h
  change strictB (D i) _ = true at h
  rw [strictB_eq] at h
  simp only [bAnd_iff] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.blt_eq.mp h.2.1, Nat.eq_of_beq_eq_true h.2.2.1,
    Nat.eq_of_beq_eq_true h.2.2.2⟩

theorem arrBfs_of_orb {n w ng ngc N r fuel : Nat} {G GI T E D S : Nat → Nat}
    {gs : Array (Array Nat)} {ps : List Nat} {act : Nat → Array Nat → Array Nat}
    {root : Array Nat} (hng : ng ≤ ngc)
    (hg : ∀ k < ng, gs[k]! = unpack n w (G k))
    (hact : ∀ k < ng, ∀ a, act k a = conjA n gs[k]! a)
    (hh0 : headK n w ngc G GI = true) (hcl : ∀ i < N, closPt n w ngc N G GI T E i = true)
    (htr : ∀ i < N, treePt ng N r E D i = true) (hr : r < N)
    (hroot : root = unpack n w (T r)) (hv0 : validA n root = true)
    (hps : ∀ p ∈ ps, p < n) (hK : distinctK N (fun i => pkeyK n w ps (T i)) S = true)
    (hf : N ≤ fuel) :
    arrCertOK act ng (validA n) (keyA n ps) root (arrBfs act ng (keyA n ps) root fuel) = true ∧
      (∀ x, x ∈ (arrBfs act ng (keyA n ps) root fuel).pts ↔ ∃ i < N, unpack n w (T i) = x) ∧
      (arrBfs act ng (keyA n ps) root fuel).pts.size = N := by
  classical
  obtain ⟨hsz, hG0⟩ := headK_spec hh0
  have hG : ∀ k < ng, canonK n w (mask w) (n * w) (G k) = true ∧
      canonK n w (mask w) (n * w) (GI k) = true ∧
      permOK n w (mask w) (n * w) (G k) (GI k) = true := fun k hk => hG0 k (by omega)
  have hcl1 : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true ∧ ∀ k < ng,
      fget (E i) k 20 < N ∧ pconj n w (mask w) (G k) (GI k) (T i) = T (fget (E i) k 20) :=
    fun i hi => ⟨(closPt_spec (hcl i hi)).1, fun k hk => (closPt_spec (hcl i hi)).2 k (by omega)⟩
  have hinv : ∀ k < ng, invCand n (unpack n w (G k)) = unpack n w (GI k) ∧
      isInvA n (unpack n w (G k)) (unpack n w (GI k)) = true :=
    fun k hk => invEqK_sound (hG k hk).2.2
  have hvg : ∀ k < ng, validA n gs[k]! = true := by
    intro k hk
    rw [hg k hk]
    unfold validA
    rw [(hinv k hk).1]
    exact (hinv k hk).2
  have hstep : ∀ i < N, ∀ k < ng, act k (unpack n w (T i)) = unpack n w (T (fget (E i) k 20)) := by
    intro i hi k hk
    obtain ⟨hc, hcl'⟩ := hcl1 i hi
    rw [hact k hk, conjA, hg k hk, (hinv k hk).1, compA_unpack hc (hG k hk).2.1,
      compA_unpack (hG k hk).1 (canonK_pcomp hc (hG k hk).2.1), ← (hcl' k hk).2]
    rfl
  let U : Nat → Array Nat := fun i => unpack n w (T i)
  let Sf : Finset (Array Nat) := (Finset.range N).image U
  have hmemS : ∀ x, x ∈ Sf ↔ ∃ i < N, unpack n w (T i) = x := by
    intro x
    simp only [Sf, U, Finset.mem_image, Finset.mem_range]
  have hrootS : root ∈ Sf := (hmemS _).2 ⟨r, hr, hroot.symm⟩
  have hclosed : ∀ x ∈ Sf, ∀ k < ng, act k x ∈ Sf := by
    intro x hx k hk
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    rw [hstep i hi k hk]
    exact (hmemS _).2 ⟨_, ((hcl1 i hi).2 k hk).1, rfl⟩
  have hreach : ∀ d, ∀ i < N, tDep (D i) = d → Reach act ng root (unpack n w (T i)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hi hd
      by_cases hir : i = r
      · rw [hir, ← hroot]
        exact Reach.root
      · obtain ⟨hp, hl, he, hdep⟩ := treePt_spec (htr i hi) hir
        have hpr := ih _ (by omega) _ hp rfl
        have e := hstep _ hp _ hl
        rw [he] at e
        rw [← e]
        exact Reach.step _ hl hpr
  have hR : ∀ x ∈ Sf, Reach act ng root x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    exact hreach _ i hi rfl
  have hS : ∀ x, Reach act ng root x ↔ x ∈ Sf := reach_iff_of_closed hrootS hclosed hR
  have hv : ∀ x ∈ Sf, validA n x = true := by
    intro x hx
    have hrx := hR x hx
    clear hx
    induction hrx with
    | root => exact hv0
    | step k hk _ ih =>
      rw [hact k hk]
      exact CFSG.RankThree.Native.F2.validA_of_rep
        (rep_conjA (hvg k hk) (rep_of_validA ih))
  have hkeyS : ∀ x ∈ Sf, ∀ y ∈ Sf, keyA n ps x = keyA n ps y → x = y := by
    intro x hx y hy e
    obtain ⟨i, hi, rfl⟩ := (hmemS x).1 hx
    obtain ⟨j, hj, rfl⟩ := (hmemS y).1 hy
    rw [keyA_unpack hps, keyA_unpack hps] at e
    rw [distinctK_inj hK i hi j hj e]
  have hinj : ∀ i < N, ∀ j < N, unpack n w (T i) = unpack n w (T j) → i = j := by
    intro i hi j hj e
    refine distinctK_inj hK i hi j hj ?_
    have e2 := congrArg (keyA n ps) e
    rw [keyA_unpack hps, keyA_unpack hps] at e2
    exact e2
  have hcard : Sf.card = N := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    exact hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) e
  obtain ⟨hcert, hmem, hsize, -⟩ := arrBfs_spec (act := act) (ngen := ng) (valid := validA n)
    (key := keyA n ps) (root := root) (fuel := fuel) Sf hS hv hkeyS (by rw [hcard]; exact hf)
  exact ⟨hcert, fun x => (hmem x).trans (hmemS x), hsize.trans hcard⟩

end CFSG.KC.ConjOrb

end
