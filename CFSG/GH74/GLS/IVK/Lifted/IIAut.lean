module

public import CFSG.GH74.GLS.IVK.Lifted.Dict

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip

@[expose] def II4_Aut_a : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSL2Or2A7 Q →
    ∀ c : Q, c ∉ center Q → c * c ∈ center Q → ¬ IsFAutomorphism Q (MulAut.conj c)

@[expose] def II4_Aut_b : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSL2Or2A7 Q →
    ∀ a b : Q, orderOf a = 4 → orderOf b = 4 → IsConj a b

@[expose] def II4_Aut_c : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSL2Or2A7 Q →
    ∀ φ : MulAut Q, φ * φ = 1 → φ ≠ 1 → ∀ P : Subgroup Q, CFSG.GH74.GLS.Stage1.Thm6.IsSylow2In P ⊤ →
      (∀ p ∈ P, φ p ∈ P) → ∃ w ∈ P, orderOf w = 4 ∧ φ w = w⁻¹

@[expose] def II4_Aut_d : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSL2Or2A7 Q →
    ∀ φ : MulAut Q, φ * φ = 1 → φ ∉ innOf Q → ¬ IsFAutomorphism Q φ → ∀ ψ : MulAut Q, ψ * ψ ≠ φ

theorem ii4_aut_of_parts (ha : II4_Aut_a) (hb : II4_Aut_b) (hc : II4_Aut_c) (hd : II4_Aut_d) :
    II4_Aut :=
  fun Q _ _ hQ => ⟨ha Q hQ, hb Q hQ, fun φ hφ =>
    ⟨fun h1 P hP hPφ => hc Q hQ φ hφ h1 P hP hPφ, fun hin hnf => hd Q hQ φ hφ hin hnf⟩⟩

theorem ii4_aut_a (h2A7 : II4_2A7) : II4_Aut_a :=
  fun _ _ _ hQ c hcz _ hf => hcz (dict_inner h2A7 hQ c hf)

end CFSG.GH74.GLS.IVK.Lifted
