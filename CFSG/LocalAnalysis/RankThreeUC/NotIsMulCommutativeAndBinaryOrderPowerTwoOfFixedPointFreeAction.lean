module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.AbelianCharacteristicCentrality.AbelianCharacteristicCentrality
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PrimePowerConclusion.PrimePowerConclusion

public section

namespace CFSG.LocalAnalysis.RankThreeUC

theorem not_isMulCommutative_and_binary_order_power_two_of_fixedPointFree_action {G : Type} [Group G] [Finite G] {p : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ρ : Representation (ZMod p) G V}
    (hS : FaithfulPrimeFieldKGroupModule G p V ρ) {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hqp : q ≠ p) (hrp : r ≠ p) (hqr : q ≠ r)
    (D : Subgroup G) (hD : Nat.card D = r)
    (hCV : (⨅ d ∈ D, LinearMap.ker (ρ d - LinearMap.id)) = (⊥ : Submodule (ZMod p) V))
    (Q : Subgroup G) (hQD : ⁅D, Q⁆ = Q) (hQ1 : Q ≠ ⊥) (hQq : IsPGroup q Q) :
    ¬ IsMulCommutative Q ∧ (q = 2 ∧ ∃ k : ℕ, orderOf (2 : ZMod r) = 2 ^ k) :=
  ⟨CFSG.LocalAnalysis.RankThreeUC.ProofSupport.AbelianCharacteristicCentrality.nonabelian hS hq hr hqp hrp hqr D hD
      hCV Q hQD hQ1 hQq,
    CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PrimePowerConclusion.conclusion hS hq hr hqp hrp hqr D hD hCV Q hQD
      hQ1 hQq⟩

end CFSG.LocalAnalysis.RankThreeUC
