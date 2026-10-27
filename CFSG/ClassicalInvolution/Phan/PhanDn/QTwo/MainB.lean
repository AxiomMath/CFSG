module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.Defs
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.LieType.Universal.Spin

@[expose] def GHNSMainBQTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (m : ℕ), 4 ≤ m →
    ∀ {G : Type} [Group G] (H : Subgroup G) (U : Fin m → Subgroup G)
      (W : Fin m → Fin m → Subgroup G), QTwoWeakPhanSystemD K m H U W →
      (Even m → ∃ ψ : ↥(spinGroup (quadPlus m (GaloisField 2 1))) →* G, ψ.range = H) ∧
      (Odd m → ∀ b c : GaloisField 2 1, (∀ s, s ^ 2 + b * s + c ≠ 0) →
        ∃ ψ : ↥(spinGroup (quadMinus m (GaloisField 2 1) b c)) →* G, ψ.range = H)

end CFSG.ClassicalInvolution.PhanDn.QTwo
