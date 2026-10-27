module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87InvMax
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Proofs2
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.LieType.Ree (ReeTag)

theorem fg2_iso {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : FG2 Y) : FG2 Y' := by
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := h
  exact ⟨p, f, hp, hf, hp2, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩

theorem five_le_pow_of_ne_three_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h3 : ¬ (p = 3 ∧ f = 1)) : 5 ≤ p ^ f := by
  by_cases hp5 : 5 ≤ p
  · exact hp5.trans (Nat.le_self_pow (by omega) p)
  · have hp3 : p = 3 := by
      have h2 := hp.two_le
      have h4 : p ≤ 4 := by omega
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · exact absurd hp (by norm_num)
    subst hp3
    have hf2 : 2 ≤ f := by
      by_contra hf2
      exact h3 ⟨rfl, by omega⟩
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf2

section Certs

theorem fg2_outAbel {Y : Type} [Group Y] [Finite Y] (h : FG2 Y) : OutAbelian Y := by
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hm
  refine outAbelian_of_mulEquiv e.symm ?_
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP F ReeTag.G2.prime := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hcard
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := CFSG.LieType.Chevalley.G2_three_exact_automorphism_normal_form hf F hcard
    exact outAbelian_of_hom Θ (fun a b => mul_comm a b) hker
  · obtain ⟨-, Θ, -, -, hker, -⟩ :=
      CFSG.LieType.Chevalley.odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf F hcard
        .G2 (Or.inr ⟨rfl, hp3⟩)
    exact outAbelian_of_hom Θ (comm_of_isCyclic_group (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F hcard).2) hker

theorem fg2_mult (hMult3 : G2ThreeMult) {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L)
    (hZ2 : IsPGroup 2 ↥(center L)) (hF : FG2 (L ⧸ center L)) : center L = ⊥ := by
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := hF
  by_cases h3 : p = 3 ∧ f = 1
  · obtain ⟨rfl, rfl⟩ := h3
    exact hMult3 L hL hZ2 hm
  · exact g2_center_eq_bot hL hm (five_le_pow_of_ne_three_one hp hp2 hf h3)

end Certs

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
