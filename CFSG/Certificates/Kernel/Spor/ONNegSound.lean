module

public import CFSG.Certificates.Kernel.Spor.ONKSound
public import Certificates.Data.Kernel.Spor.ONNegK
import CFSG.Certificates.Kernel.Spor.ONSplitSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.ON

open CFSG.KC.Enum CFSG.KS CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.ON.Native
open CFSG.ONSchreier.Native

theorem bfsK_keys {cA cB : Array W} {root : W} {n SL NS : Nat}
    {K A B SO SOI NX : Nat → Nat} {LA LB : List Nat}
    (hcA : cA.size = 154 ∧ LA.length = 154 ∧ ∀ j < 154, cA[j]! = wOfK (LA.getD j 0))
    (hcB : cB.size = 154 ∧ LB.length = 154 ∧ ∀ j < 154, cB[j]! = wOfK (LB.getD j 0))
    (hCA : ∀ j < 154, canon (LA.getD j 0) = true) (hCB : ∀ j < 154, canon (LB.getD j 0) = true)
    (hr : root = wOfK (key K 0)) (hn : 0 < n ∧ n < 2 ^ 18)
    (hmv : ∀ h < n, mvAt K LA LB A B n h = true)
    (hNS : NS * SL = n) (hX0 : NX 0 = 1) (hXN : NX NS = n)
    (hord : ∀ s < NS, Nat.beq (ordRun A B (s * SL) SL (NX s)) (NX (s + 1)) = true)
    (hsort : ∀ i < n, sortAt K SO SOI n i = true) :
    (orbitBFS cA cB root n).keys = Array.ofFn (n := n) fun i => wOfK (key K i.val) :=
  (bfsK_sim hcA hcB hCA hCB hr hn hmv hNS hX0 hXN hord hsort).1

theorem sigma_sound {O : VOrbit} {K SO SOI NEG : Nat → Nat}
    (hk : O.keys = Array.ofFn (n := nPts) fun i => wOfK (key K i.val))
    (hm : ∀ h < nPts, canon (key K h) = true)
    (hsort : ∀ i < nPts, sortAt K SO SOI nPts i = true)
    (hneg : ∀ i < nPts, negAt K NEG nPts i = true) :
    sigmaTab O (posOf (indexOf O.keys) nPts) = Array.ofFn (n := nPts) fun i => tab NEG i.val := by
  have hget : ∀ i < nPts, O.keys[i]! = wOfK (key K i) := fun i hi => by
    rw [getElem!_pos O.keys i (by rw [hk, Array.size_ofFn]; exact hi)]
    simp [hk]
  unfold sigmaTab
  congr 1
  funext i
  obtain ⟨hj, he, -⟩ : tab NEG i.val < nPts ∧ key K (tab NEG i.val) = vneg (key K i.val) ∧
      tab NEG (tab NEG i.val) = i.val := by
    have h := hneg i.val i.isLt
    unfold negAt at h
    rw [PackFld.strictB_eqP] at h
    obtain ⟨a1, h4⟩ := (bAnd_iff _ _).1 h
    obtain ⟨a2, a3⟩ := (bAnd_iff _ _).1 h4
    exact ⟨Nat.blt_eq.mp a1, Nat.eq_of_beq_eq_true a2, Nat.eq_of_beq_eq_true a3⟩
  rw [hget i.val i.isLt, wOfK_vneg (hm i.val i.isLt), ← he, ← hget _ hj]
  exact index_sound hk hm hsort _ hj nPts

end CFSG.KS.ON

end
