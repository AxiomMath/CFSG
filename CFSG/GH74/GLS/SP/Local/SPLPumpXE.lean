module

public import CFSG.GH74.GLS.SP.Local.SPLPumpXD

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

theorem three_lt_of_not_fm9 {q : ℕ} (hodd : Odd q) (hq2 : 2 ≤ q) (hn : ¬ IsFM9 q) : 3 < q := by
  by_contra h
  have h3 : q = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  exact hn (by rw [h3]; exact Or.inr ⟨Nat.prime_three, Or.inl ⟨0, by norm_num⟩⟩)

namespace XCtx

variable {X : Type} [Group X] [Finite X] {z t : X} {A T₁ : Subgroup X}

theorem stable_T2 (hUI : StableUniqueInvolution) (hAlt : StableDoubleCoverAlt)
    (hL34 : StableL34Cover) (hX : XCtx X z t A T₁) {L : Subgroup X} (hL : StableL z A L)
    (hT : InT2 ↥L) : False := by
  obtain ⟨hq, hcases⟩ := hT
  rcases hcases with ⟨p, f, hp, hf, ⟨hodd, hnfm⟩, hlie⟩ | hSL | hA7 | ⟨n, hn7, hn11, hn⟩ | ⟨hlq, hexp⟩
  · obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hlie
    have hp2 : 2 ≤ p ^ f := (hp.one_lt).trans_le (Nat.le_self_pow (by omega) p)
    have hL2F : IVK.L2Field F := ⟨hF ▸ hodd, hF ▸ three_lt_of_not_fm9 hodd hp2 hnfm⟩
    exact hX.stable_L2 hL hL2F e
  · exact hUI X z t A T₁ L hX hL hq (Or.inl hSL)
  · obtain ⟨e⟩ := hA7
    exact hX.stable_A7 hL e
  · by_cases h7 : n = 7
    · subst h7
      exact hUI X z t A T₁ L hX hL hq (Or.inr hn)
    · exact hAlt X z t A T₁ L hX hL ⟨n, by omega, hn11, hn⟩
  · exact hL34 X z t A T₁ L hX hL hq hlq hexp

theorem stable_central
    (hG : CFSG.GH74.Generic.GenericKnownFacts) (hF : CFSG.GH74.E2.E2ComponentFacts)
    (hUI : StableUniqueInvolution) (hAlt : StableDoubleCoverAlt) (hL34 : StableL34Cover)
    (hX : XCtx X z t A T₁) {L : Subgroup X} (hshape : InC2 ↥L ∨ InT2 ↥L)
    (hst : ∀ x ∈ L, z * x * z⁻¹ ∈ L) (hAL : A ≤ L) : ∀ x ∈ L, z * x = x * z := by
  by_contra hcon
  push Not at hcon
  have hL : StableL z A L := ⟨hst, hAL, hcon⟩
  rcases hshape with hC | hT
  · exact hX.stable_C2 hG hF hL hC
  · exact hX.stable_T2 hUI hAlt hL34 hL hT

end XCtx

end CFSG.GH74.GLS.SP.Local
