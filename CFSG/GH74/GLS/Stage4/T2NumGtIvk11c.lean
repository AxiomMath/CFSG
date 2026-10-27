module

public import CFSG.GH74.GLS.IVK.Proofs2.Stmt111c

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

@[expose] def IVK_11_1c_dim : Prop :=
  ∀ (p m : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K],
    HasSL2Model K (fun r => r = p ^ m) →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
        (ρ : Representation (ZMod p) K V), Function.Injective ρ →
          IsSimpleModule (MonoidAlgebra (ZMod p) K) ρ.asModule →
            2 * m < Module.finrank (ZMod p) V → Module.finrank (ZMod p) V < 4 * m →
              3 * Module.finrank (ZMod p) V = 8 * m

theorem ivk_11_1c_dim_of_fixed (h : IVK.Proofs2.IVK_11_1c_fixed) : IVK_11_1c_dim := by
  intro p m hp hp2 K _ _ hK V _ _ _ ρ hinj hsimple h1 h2
  obtain ⟨F, iF, fF, hF, ⟨eK⟩⟩ := hK
  have key := h p m hp hp2 K (⊤ : Subgroup K)
    (Or.inl ⟨F, iF, fF, hF, ⟨Subgroup.topEquiv.trans eK⟩⟩) V ρ hinj hsimple h1 h2
  rcases key with ⟨-, hd, -⟩ | ⟨⟨F₀, iF₀, fF₀, hF₀, ⟨eL⟩⟩, -⟩
  · exact hd
  · exfalso
    have hcardK : Nat.card (L2 F₀) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
      calc Nat.card (L2 F₀) = Nat.card ↥(⊤ : Subgroup K) := (Nat.card_congr eL.toEquiv).symm
        _ = Nat.card K := Nat.card_congr Subgroup.topEquiv.toEquiv
        _ = Nat.card (StatedSL 2 F) := Nat.card_congr eK.toEquiv
        _ = _ := (Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv).symm
    rw [CFSG.BenderSuzuki.External.huppert614_card_specialLinearGroup] at hcardK
    have hodd₀ : GorensteinWalter.IsOddPrimePower (Nat.card F₀) := by
      have hq : 1 < Nat.card F₀ := Finite.one_lt_card
      refine ⟨p, m, hp, hp.odd_of_ne_two hp2, ?_, hF₀⟩
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, pow_zero] at hF₀
        omega
      · exact h0
    have h3 : Nat.card (L2 F₀) = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) / 2 := by
      rw [Nat.card_congr (L2.equivPSL F₀).toEquiv]
      exact GorensteinWalter.psl2_card_formula F₀ hodd₀
    rw [h3, hF₀, hF] at hcardK
    have hpos : 0 < p ^ m * ((p ^ m) ^ 2 - 1) := by
      have hq : 2 ≤ p ^ m := by
        have : 1 < Nat.card F₀ := Finite.one_lt_card
        omega
      have : 1 < (p ^ m) ^ 2 := by nlinarith
      apply Nat.mul_pos (by omega) (by omega)
    omega

end CFSG.GH74.GLS.Stage4.Rest
