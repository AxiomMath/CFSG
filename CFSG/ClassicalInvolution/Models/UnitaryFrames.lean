module

public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Weyl

public section

namespace CFSG.ClassicalInvolution.Models

open CFSG.ClassicalInvolution.Generic CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem unitaryFrame (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (h5 : 5 ≤ p ^ f) (hn : 4 ≤ n) :
    ToralFrame (fixedSubfield K p f) (longRootSetU (K := K) (p := p) (f := f) (by omega : 2 ≤ n))
        (signGroupU K p f n) (coordSetU K p f n) ∧
      sigmaSet (fixedSubfield K p f) (longRootSetU (K := K) (p := p) (f := f) (by omega : 2 ≤ n))
        (signGroupU K p f n) = coordSetU K p f n ∧
      (coordSetU K p f n).ncard = n.choose 2 ∧
      A2Dichotomy (signGroupU K p f n) (coordSetU K p f n) ∧
      NonCommConnected (coordSetU K p f n) ∧
      FibreLE2 (coordSetU K p f n) ∧
      Nonempty (weylGraph n ≃g commGraph (coordSetU K p f n)) ∧
      Nonempty (swapGraph n ≃g commGraph (coordSetU K p f n)) := by
  have hF := isPairFamily_LcU (K := K) (p := p) (f := f) (n := n) hK hp (by omega)
  exact ⟨toralFrameU hK hp h5 hn, (coordSetU_eq_sigmaSet hK hp (by omega)).symm,
    ncard_coordSetU hK hp (by omega), a2Dichotomy_coordSetU hK hp h5 hn,
    nonCommConnected_coordSetU hK hp (by omega), fibreLE2_coordSetU hK hp (by omega),
    ⟨hF.iso⟩, ⟨(swapGraphIso n).trans hF.iso⟩⟩

end CFSG.ClassicalInvolution.Models
