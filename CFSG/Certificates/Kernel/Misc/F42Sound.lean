module

public import Certificates.Data.Kernel.Misc.F42
public import CFSG.Certificates.Kernel.Misc.F42Defs
import CFSG.Certificates.Kernel.Spor.PK.F42

public section

namespace CFSG.KC.Misc.F42

open CFSG.LieType.Multipliers.F42 CFSG.F3.Native CFSG.Blueprint.Chevalley

theorem lifts_eq : lifts = liftsOf payloadA payloadB slpText liftRefs := rfl

theorem pairsOK_eq (L : Array Pair) : pairsOK L = pairsOKG f4ArtifactRoots L := rfl

theorem wordOK_eq (L : Array Pair) (k : ℕ) : wordOK L k = wordOKG f4ArtifactRoots commPairs L k :=
  rfl

theorem negOK_eq (L : Array Pair) (i j : ℕ) : negOK L i j = negOKG f4ArtifactRoots L i j := rfl

theorem f42_sound {pA pB slp : String} {refs : List ℤ} {R : List (List ℤ)} {CP : List (ℕ × ℕ)}
    {cA cB cS Rc LR RC F I LF LI : List ℕ} {RL : List (List ℕ)} {nI nP : ℕ}
    (hA : pA = strOf cA) (hB : pB = strOf cB) (hS : slp = strOf cS)
    (hrefs : refs = LR.map refOfCode) (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32))
    (hfmt : fmtK cS = true) (hints : eqLN (intsK cS) Rc = true)
    (hst : startK cA cB F I = true)
    (hnI : nI = lenN Rc / 2) (hF : Nat.beq (lenN F) (nI + 2) = true)
    (hins : ∀ c < nP, insChunk F I Rc nI (16 * c) 16 = true) (hnP : nI ≤ 16 * nP)
    (hl : liftsK F I LR LF LI (nI + 2) = true) (hr : rootsK RL RC = true)
    (hlk : ∀ k < 48, liftK LF LI k = true)
    (hp : ∀ c < 48, pairsChunk LF LI RC c 1 = true)
    (hw : ∀ k < 48, wordK LF LI RC k (CP.getD k (0, 0)).1 (CP.getD k (0, 0)).2 = true)
    (hn : negK LF LI RC 0 35 = true) (hwI : ∀ k < nI + 2, wfS (nthV I k) = true) :
    (List.range 48).all (liftOK (liftsOf pA pB slp refs)) = true ∧
      pairsOKG R (liftsOf pA pB slp refs) = true ∧
      (List.range 48).all (wordOKG R CP (liftsOf pA pB slp refs)) = true ∧
      negOKG R (liftsOf pA pB slp refs) 0 35 = true :=
  CFSG.KS.PK.f42_sound_wf hA hB hS hrefs hR hfmt hints hst hnI hF hins hnP hl hr hlk hp hw hn hwI

end CFSG.KC.Misc.F42

end
