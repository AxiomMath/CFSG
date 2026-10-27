module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineFi22
public import CFSG.Sporadic.SuzOddCore.SmallAut

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.SuzOddCore
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Sporadic.Schreier (fixSub)

section Suz


@[expose] def fixSubSuzConjTEquiv (t : suzT) :
    fixSub (suzConjT t) ≃* ↥(centM (t : Equiv.Perm (Fin 1782))) where
  toFun g := ⟨((g : suzM) : Equiv.Perm (Fin 1782)), by
    refine Subgroup.mem_inf.2 ⟨?_, (g : suzM).2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : ((suzConjT t (g : suzM) : suzM) : Equiv.Perm (Fin 1782)) = g :=
      congrArg Subtype.val g.2
    rw [suzConjT_apply] at h2
    calc ((g : suzM) : Equiv.Perm (Fin 1782)) * t =
        (t : Equiv.Perm (Fin 1782)) * g * (t : Equiv.Perm (Fin 1782))⁻¹ * t := by rw [h2]
      _ = t * g := by group⟩
  invFun x := ⟨⟨x, (Subgroup.mem_inf.1 x.2).2⟩, by
    show suzConjT t ⟨x, (Subgroup.mem_inf.1 x.2).2⟩ = ⟨x, (Subgroup.mem_inf.1 x.2).2⟩
    apply Subtype.ext
    rw [suzConjT_apply]
    have hx := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).1
    show (t : Equiv.Perm (Fin 1782)) * x * (t : Equiv.Perm (Fin 1782))⁻¹ = x
    rw [← hx]
    group⟩
  left_inv g := rfl
  right_inv x := rfl
  map_mul' x y := rfl

theorem card_centM_conj {c : Equiv.Perm (Fin 1782)} (hc : c ∈ suzT) (t : Equiv.Perm (Fin 1782)) :
    Nat.card ↥(centM (c * t * c⁻¹)) = Nat.card ↥(centM t) := by
  have hn : c ∈ Subgroup.normalizer (suzM : Set (Equiv.Perm (Fin 1782))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨fun hm => suzT_conj_mem_suzM hc hm, fun hm => ?_⟩
    have := suzT_conj_mem_suzM (suzT.inv_mem hc) hm
    rwa [show c⁻¹ * (c * m * c⁻¹) * c⁻¹⁻¹ = m by group] at this
  rw [centM, centM, inf_comm, inf_comm (centralizer {t})]
  exact (Nat.card_congr (Sporadic.FischerOddCore.fi22CP_conj_equiv hn t).toEquiv).symm

theorem suz_outer_card_fixedSubgroup {S : Type} [Group S] (e : S ≃* NativeSporadic.Suz)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    Nat.card (fixedSubgroup σ) = 190080 ∨ Nat.card (fixedSubgroup σ) = 1209600 := by
  set θ : S ≃* suzM := e.trans suzEquivM
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hβ2 := Sporadic.FischerOddCore.congr_mul_self θ σ hσ2
  have hβout : MulAut.congr θ σ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner suzM :=
    fun h => hout ((Sporadic.FischerOddCore.congr_mem_inner_iff θ σ).1 h)
  obtain ⟨t, ht⟩ := suzConjT_bijective.2 (MulAut.congr θ σ)
  have ht2 : t * t = 1 := suzConjT_bijective.1 (by rw [map_mul, ht, hβ2, map_one])
  have htM : (t : Equiv.Perm (Fin 1782)) ∉ suzM := by
    intro h
    apply hβout
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, ← suzConjT_map_suzM, ← ht]
    exact ⟨t, Subgroup.mem_subgroupOf.2 h, rfl⟩
  have ht1 : (t : Equiv.Perm (Fin 1782)) ≠ 1 := fun h => htM (h ▸ suzM.one_mem)
  have hto : orderOf (t : Equiv.Perm (Fin 1782)) = 2 :=
    orderOf_eq_prime (by rw [sq, ← Subgroup.coe_mul, ht2, Subgroup.coe_one]) ht1
  obtain ⟨i, ⟨hi, c, hc, hct⟩, -⟩ := suzT_involution_class t.2 hto
  obtain ⟨-, -, -, -, -, h0, h1, -, -, -, hE, -, -, -, -, -, -, hE2, hE3, -⟩ :=
    CTUC_Suz_four_exact_involution_centralizers
  have hcard : Nat.card (fixedSubgroup σ) = Nat.card ↥(centM (suzInv i)) := by
    rw [Nat.card_congr (MulEquiv.subgroupCongr (fixedSubgroup_eq_fixSub σ)).toEquiv,
      Nat.card_congr (Sporadic.FischerOddCore.fixSubCongr θ σ).toEquiv, ← ht,
      Nat.card_congr (fixSubSuzConjTEquiv t).toEquiv, ← hct]
    exact card_centM_conj hc _
  rw [hcard, ← (hE i hi).2]
  interval_cases i
  · exact absurd (hct ▸ suzT_conj_mem_suzM hc h0) htM
  · exact absurd (hct ▸ suzT_conj_mem_suzM hc h1) htM
  · exact .inl hE2
  · exact .inr hE3

theorem suz_outer_not_dvd_card_fixedSubgroup {S : Type} [Group S] (e : S ≃* NativeSporadic.Suz)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    ¬ 1451520 ∣ Nat.card (fixedSubgroup σ) := by
  rcases suz_outer_card_fixedSubgroup e hσ hout with h | h <;> rw [h] <;> norm_num

end Suz

end CFSG.SeitzReduction.SporadicRefine
