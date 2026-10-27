module

public import Certificates.Data.Kernel.LeftOrb
public import CFSG.Certificates.Kernel.ConjOrbSound
import CFSG.Certificates.Kernel.Spor.PackWord

public section

namespace CFSG.KC.LeftOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.KC.Bfs CFSG.KC.BfsPin CFSG.KC.ConjOrb
open CFSG.KLie.CT (fget)

theorem closPtL_spec {n w ng N : Nat} {G T E : Nat → Nat} {i : Nat}
    (h : closPtL n w ng N G T E i = true) :
    canonK n w (mask w) (n * w) (T i) = true ∧ ∀ k < ng, fget (E i) k 20 < N ∧
      pcomp n w (mask w) (G k) (T i) = T (fget (E i) k 20) := by
  unfold closPtL at h
  rw [ConjOrb.strictB_eq, ConjOrb.strictB_eq, bAnd_iff] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have h2 := allN_spec h.2 k hk
  rw [ConjOrb.strictB_eq, bAnd_iff] at h2
  exact ⟨Nat.blt_eq.mp h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem arrBfs_of_left {n w ng ngc N r fuel : Nat} {G GI T E D S : Nat → Nat}
    {gs : Array (Array Nat)} {ps : List Nat} {act : Nat → Array Nat → Array Nat}
    {root : Array Nat} (hng : ng ≤ ngc)
    (hg : ∀ k < ng, gs[k]! = unpack n w (G k))
    (hact : ∀ k < ng, ∀ a, act k a = compA n gs[k]! a)
    (hh0 : headK n w ngc G GI = true) (hcl : ∀ i < N, closPtL n w ngc N G T E i = true)
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
      fget (E i) k 20 < N ∧ pcomp n w (mask w) (G k) (T i) = T (fget (E i) k 20) :=
    fun i hi => ⟨(closPtL_spec (hcl i hi)).1, fun k hk => (closPtL_spec (hcl i hi)).2 k (by omega)⟩
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
    rw [hact k hk, hg k hk, compA_unpack (hG k hk).1 hc, (hcl' k hk).2]
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
        (rep_compA (rep_of_validA (hvg k hk)) (rep_of_validA ih))
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

theorem enumBfs_of_left {n w ng N r fuel : Nat} {G GI T E D S : Nat → Nat}
    {gs : Array (Array Nat)} {ps : List Nat} (hs : gs.size = ng)
    (hg : ∀ k < ng, gs[k]! = unpack n w (G k))
    (hh0 : headK n w ng G GI = true) (hcl : ∀ i < N, closPtL n w ng N G T E i = true)
    (htr : ∀ i < N, treePt ng N r E D i = true) (hr : r < N) (hT : T r = pidn n w)
    (hps : ∀ p ∈ ps, p < n) (hK : distinctK N (fun i => pkeyK n w ps (T i)) S = true)
    (hf : N ≤ fuel) :
    enumOK n gs ps (enumBfs n gs ps fuel) = true ∧
      (∀ x, x ∈ (enumBfs n gs ps fuel).pts ↔ ∃ i < N, unpack n w (T i) = x) ∧
      (enumBfs n gs ps fuel).pts.size = N := by
  obtain ⟨hsz, hG0⟩ := headK_spec hh0
  have hvg : ∀ k < gs.size, validA n gs[k]! = true := by
    intro k hk
    rw [hg k (hs ▸ hk)]
    have hi := invEqK_sound (hG0 k (hs ▸ hk)).2.2
    unfold validA
    rw [hi.1]
    exact hi.2
  have hid : idA n = unpack n w (T r) := by
    rw [hT, idK_sound (idK_of_szOK hsz)]
  obtain ⟨hc, hm, hz⟩ := arrBfs_of_left (act := leftA n gs) (root := idA n) (fuel := fuel)
    (le_refl ng) hg (fun k _ a => rfl) hh0 hcl htr hr hid
    (CFSG.RankThree.Native.F2.validA_of_rep rep_idA) hps hK hf
  unfold enumOK enumBfs
  rw [hs, Bool.and_eq_true]
  exact ⟨⟨allLt_iff.2 (hs ▸ hvg), hc⟩, hm, hz⟩

end CFSG.KC.LeftOrb

end
