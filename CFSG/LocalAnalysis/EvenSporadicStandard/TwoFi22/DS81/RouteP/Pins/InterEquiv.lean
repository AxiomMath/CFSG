module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Pins.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

variable {G G₀ : Type*} [Group G] [Group G₀]

@[expose] def equivInfOfMemIff {L M : Subgroup G} (A : Subgroup ↥M)
    (hA : ∀ n : ↥M, n ∈ A ↔ (n : G) ∈ L) : ↥A ≃* ↥(L ⊓ M) where
  toFun b := ⟨((b : ↥M) : G), (hA b).1 b.2, (b : ↥M).2⟩
  invFun x := ⟨⟨(x : G), x.2.2⟩, (hA ⟨(x : G), x.2.2⟩).2 x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] def restrictSubgroupOf {L M : Subgroup G} {L₀ M₀ : Subgroup G₀} {A : Subgroup ↥M}
    {A₀ : Subgroup ↥M₀} (ψ : ↥L ≃* ↥L₀)
    (hψ : ∀ x : ↥L, (x : G) ∈ M ↔ ((ψ x : ↥L₀) : G₀) ∈ M₀)
    (hA : ∀ n : ↥M, n ∈ A ↔ (n : G) ∈ L) (hA₀ : ∀ n : ↥M₀, n ∈ A₀ ↔ (n : G₀) ∈ L₀) :
    ↥A ≃* ↥A₀ :=
  (equivInfOfMemIff A hA).trans ((infEquiv ψ hψ).trans (equivInfOfMemIff A₀ hA₀).symm)

@[expose] def interAut {L N : Subgroup G} {L₀ N₀ : Subgroup G₀} (ψL : ↥L ≃* ↥L₀)
    (ψN : ↥N ≃* ↥N₀) (hψL : ∀ x : ↥L, (x : G) ∈ N ↔ ((ψL x : ↥L₀) : G₀) ∈ N₀)
    (hψN : ∀ y : ↥N, (y : G) ∈ L ↔ ((ψN y : ↥N₀) : G₀) ∈ L₀) : ↥(L₀ ⊓ N₀) ≃* ↥(L₀ ⊓ N₀) :=
  (((MulEquiv.subgroupCongr (inf_comm L N)).trans (infEquiv ψN hψN)).trans
      (MulEquiv.subgroupCongr (inf_comm N₀ L₀))).symm.trans (infEquiv ψL hψL)

theorem interAut_apply {L N : Subgroup G} {L₀ N₀ : Subgroup G₀} (ψL : ↥L ≃* ↥L₀)
    (ψN : ↥N ≃* ↥N₀) (hψL : ∀ x : ↥L, (x : G) ∈ N ↔ ((ψL x : ↥L₀) : G₀) ∈ N₀)
    (hψN : ∀ y : ↥N, (y : G) ∈ L ↔ ((ψN y : ↥N₀) : G₀) ∈ L₀) (b : ↥(L₀ ⊓ N₀)) (n : ↥N)
    (hnL : (n : G) ∈ L) (hb : (b : G₀) = ((ψN n : ↥N₀) : G₀)) :
    ((interAut ψL ψN hψL hψN b : ↥(L₀ ⊓ N₀)) : G₀) = ((ψL ⟨(n : G), hnL⟩ : ↥L₀) : G₀) := by
  have hb' : b = (((MulEquiv.subgroupCongr (inf_comm L N)).trans (infEquiv ψN hψN)).trans
      (MulEquiv.subgroupCongr (inf_comm N₀ L₀))) ⟨(n : G), hnL, n.2⟩ := Subtype.ext hb
  rw [hb', interAut, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
