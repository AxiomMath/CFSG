module

public import Certificates.Data.Kernel.LocalQT.Six
public import CFSG.Certificates.Kernel.LocalQTSmallSound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsSixInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Aut6Inputs
public import CFSG.Certificates.Kernel.LocalQTSix35Sound
public import CFSG.Certificates.Kernel.LocalQTSix51Sound
public import Certificates.Data.Kernel.LocalQT.SixRank
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import Certificates.Certificate113

set_option maxRecDepth 100000

public section

namespace CFSG.KC.LQT.X6

open Equiv CFSG.KC.LQT.S CFSG.QuasithinUnique.Unc25K1.Six

theorem rankOK_true : rankOK = true := by quickRfl

theorem s4051 (G0 Ga Gb R : List P6) {n0 na nb m k0 ka kb : ℕ} {C0 Ca Cb CR : List ℕ}
    (h0 : G0.map code = C0) (ha : Ga.map code = Ca) (hb : Gb.map code = Cb)
    (hr : R.map code = CR) (hk : c4051 C0 Ca Cb CR n0 na nb m k0 ka kb = true) :
    let L0 := iterL (G0.map R6.enc) n0
    let La := iterL (Ga.map R6.enc) na
    let Lb := iterL (Gb.map R6.enc) nb
    (L0.length = k0 ∧ La.length = ka ∧ Lb.length = kb ∧ L0.Nodup ∧ La.Nodup ∧ Lb.Nodup)
    ∧ (closedB (G0.map R6.enc) L0 = true ∧ closedB (Ga.map R6.enc) La = true ∧
          closedB (Gb.map R6.enc) Lb = true)
    ∧ (∀ x : P6, Perm.sign x = 1 → R6.enc x ∈ La ∨ R6.enc x ∈ Lb ∨
          ∃ r ∈ R, ∃ d ∈ L0, ∃ e ∈ L0, R6.enc x = d * R6.enc r * e)
    ∧ (∀ x : P6, Perm.sign x = 1 →
          ∀ L ∈ R.map (fun r => iterL ((G0 ++ [r]).map R6.enc) m), R6.enc x ∈ L)
    ∧ (∀ τ : P6, (G0.map R6.enc).all (conjIn (R6.enc τ) L0) = true →
          (Ga.map R6.enc).all (conjIn (R6.enc τ) La) = true ∧
          (Gb.map R6.enc).all (conjIn (R6.enc τ) Lb) = true) := by
  exact s4051k rankOK_true G0 Ga Gb R h0 ha hb hr hk

open CFSG.QuasithinUnique.A5.Aut6 in
theorem s4035 (T : List (ℕ × List Bool)) (R : List (List Bool)) {LA LY : List ℕ}
    {LXs : List (List ℕ)} {CA CB : ℕ} (ha : code ga = CA) (hb : code gb = CB)
    (hk : c4035 T R LA LXs LY CA CB = true)
    (hp : ∀ i < LXs.length, p4035 T R LA LXs LY CA CB i = true) :
    let w := fun g : Perm (Fin 6) => (List.lookup (key g) T).getD []
    (∀ x y : A6, IsCand w x y → IsInv w x y → ¬ IsConj w x y → HasFix w x y)
    ∧ (∀ g : A6, ev ga gb (w (g : Perm (Fin 6))) = (g : Perm (Fin 6))) := by
  exact s4035k T R ha hb hk hp

end CFSG.KC.LQT.X6

end
