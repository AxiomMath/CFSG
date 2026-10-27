module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL22C
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma23
public import CFSG.GH74.GLS.Bg.TwoGroups.L26S

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open CFSG.GH74.GLS.Bg.TwoGroups.L23 CFSG.GH74.GLS.Bg.TwoGroups.L26

private theorem fzl_center_exp_sylSU3c :
    ∀ z : ↥sylSU3c, (∀ x : ↥sylSU3c, x * z = z * x) → z * z = 1 := by
  decide +kernel

private theorem fzl_aniso_sylSU3c :
    ∀ g : ↥sylSU3c, g * g = 1 → ∀ x : ↥sylSU3c, x * g = g * x := by
  decide +kernel

private theorem fzl_suz_sylSU3c : FzSuz ↥sylSU3c := by
  obtain ⟨hcard, _hexp, hcomm, hsq, _hsurj, hcen⟩ := sfacts_sylSU3c
  refine ⟨hcard, ?_, ?_, ?_, ?_, ?_⟩
  · intro g h
    rw [Subgroup.mem_center_iff]
    intro x
    simpa only [commutatorElement_def] using hcomm g h x
  · intro g
    rw [Subgroup.mem_center_iff]
    intro x
    exact hsq g x
  · rw [← hcen]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun _ => Subgroup.mem_center_iff))
  · intro z hz
    exact fzl_center_exp_sylSU3c z ((Subgroup.mem_center_iff).mp hz)
  · intro g hg
    rw [Subgroup.mem_center_iff]
    exact fzl_aniso_sylSU3c g hg

theorem fzl_suz_SU : FzSuz SylSU3_4 :=
  FzSuz.of_equiv sylCongr fzl_suz_sylSU3c

theorem fzl_sl_of_sigma3 (T : Type) [Group T] [Finite T] (hT : Nat.card T = 64) (f u : MulAut T)
    (hf3 : orderOf f = 3) (hfix : ∀ g : T, f g = g → g = 1) (hu2 : u * u = 1)
    (huf : u * f * u⁻¹ = f⁻¹) (A : Subgroup T) [A.Normal] (hA : ∀ a ∈ A, f a ∈ A)
    (hAZ : Nonempty (↥A ≃* Z4Z4)) (hCA : centralizer (A : Set T) = A) :
    Nonempty (T ≃* SylSL3_4) := by
  obtain ⟨hSU, hSL⟩ := iv2_2_3 T hT f hf3 hfix A (inferInstance : A.Normal) hA hAZ hCA
  by_cases h : Om1 A = Om1 (⊤ : Subgroup T)
  · exfalso
    obtain ⟨e⟩ := hSU h
    have hsuz : FzSuz T := FzSuz.of_equiv e fzl_suz_SU
    have hfpow : f ^ 3 = 1 := by
      have := pow_orderOf_eq_one f
      rwa [hf3] at this
    exact fzl_no_sigma3 hsuz f u hfpow hfix hu2 huf
  · exact hSL h

end CFSG.OddStandard.SmallF3.FritzII
