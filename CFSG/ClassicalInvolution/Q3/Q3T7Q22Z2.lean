module

import CFSG.ClassicalInvolution.AschTight.S19MFund
import CFSG.ClassicalInvolution.AschTight.S19MCenter
import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainLModel
public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha
public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainUModel
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.ExceptionalSL3

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def Z2NoD8 : Prop :=
  ∀ (t : StatedLieTag) (k e : ℕ), StatedLieAdmissible t k 3 e →
    ((t = .PSL ∧ k = 3 ∧ 3 ^ e % 4 = 3) ∨ (t = .PSU ∧ k = 3 ∧ 3 ^ e % 4 = 1)) →
    ∀ {H : Type} [Group H] [Finite H] (ψ : (modelUniv t k 3 e Fact.out).K →* H),
      ψ.ker ≤ Subgroup.center (modelUniv t k 3 e Fact.out).K →
      ∀ (R : Subgroup (modelUniv t k 3 e Fact.out).K) (x : (modelUniv t k 3 e Fact.out).K),
        R ∈ fundamentalSubgroups t (modelUniv t k 3 e Fact.out).D →
        x ∈ R → x * x = 1 → x ≠ 1 →
        ∀ (a v : ↥(inducedAutOn ψ.range)),
          (∀ r ∈ R, a * innerHom ψ r = innerHom ψ r * a) →
          (∀ r ∈ R, v * innerHom ψ r = innerHom ψ r * v) →
          a * a = innerHom ψ x → v * v = 1 → v * a * v⁻¹ = a⁻¹ → False

theorem z2NoD8 : Z2NoD8 := by
  intro t k e hadm hZ2 H _ _ ψ hker R x hR hxR hx2 hx1 a v ha hv ha2 hv2 hva
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨ht, rfl⟩ : (t = .PSL ∨ t = .PSU) ∧ k = 3 := by
    rcases hZ2 with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, h2⟩
  have hT6 : AschTight.S1911.IsT6Tag t 3 := by
    rcases ht with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  have hperf : Group.IsPerfect (modelUniv t 3 3 e Fact.out).K := by
    rcases ht with rfl | rfl
    · exact Group.isPerfect_def.2
        (ModelFacts.modelClauseZero .PSL 3 3 e Fact.out trivial hadm).1.1
    · exact Group.isPerfect_def.2
        (ModelFacts.modelClauseZero .PSU 3 3 e Fact.out trivial hadm).1.1
  obtain ⟨hk1, hnormal, hcent⟩ := innerHom_spec ψ hker
  obtain ⟨c, hc⟩ := AschTight.S19M.exists_isUniqueInvolution_of_mem_fund hp2 hT6 hadm hR
  have hxc : ∀ r ∈ R, x * r = r * x := by
    have hxcc : x = c := (hc.unique x hxR hx2).resolve_left hx1
    intro r hr
    have := hc.conj_eq (conjSub_eq_self_of_mem hr)
    rw [hxcc]
    calc c * r = (r * c * r⁻¹) * r := by rw [this]
      _ = r * c := by group
  have hvn : v ∈ Subgroup.normalizer (((innerHom ψ).range : Subgroup _) : Set _) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hnormal]
    exact Subgroup.mem_top v
  have hker' : (innerHom ψ).ker ≤ Subgroup.center (modelUniv t 3 3 e Fact.out).K :=
    fun g hg => hk1 g (MonoidHom.mem_ker.mp hg)
  have hcase : (∀ y ∈ (innerHom ψ).range, v * y = y * v) ∨
      (∀ y ∈ (innerHom ψ).range, (v * innerHom ψ x) * y = y * (v * innerHom ψ x)) := by
    rcases ht with rfl | rfl
    · exact ModelFacts.Orth15.psl3_model_involution_fund hp2 hadm (innerHom ψ) hker' hR hxR hxc
        hx1 hvn hv2 hv
    · have h4 : 3 ^ e % 4 = 1 := by
        rcases hZ2 with ⟨h1, -⟩ | ⟨-, -, h3⟩
        · exact absurd h1 (by decide)
        · exact h3
      have hq : 5 ≤ 3 ^ e := by
        rcases Nat.lt_or_ge e 2 with h | h
        · obtain rfl : e = 1 := by
            have := hadm.2.1
            omega
          norm_num at h4
        · calc 5 ≤ 3 ^ 2 := by norm_num
            _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) h
      exact ModelFacts.Orth15.psu3_model_involution_fund hp2 hq hadm (innerHom ψ) hker' hR hxR
        hxc hx1 hvn hv2 hv
  have hainv : a = a⁻¹ := by
    rcases hcase with hA | hB
    · have hv1 : v = 1 := hcent v hA
      rw [hv1] at hva
      simpa using hva
    · have hv1 : v * innerHom ψ x = 1 := hcent _ hB
      have hvm : v = (innerHom ψ x)⁻¹ := eq_inv_of_mul_eq_one_left hv1
      have hax : a * innerHom ψ x = innerHom ψ x * a := ha x hxR
      rw [hvm] at hva
      have hconj : (innerHom ψ x)⁻¹ * a * (innerHom ψ x)⁻¹⁻¹ = a := by
        rw [inv_inv, mul_assoc, hax, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hconj] at hva
      exact hva
  have hm : innerHom ψ x = 1 := by
    rw [← ha2]
    exact mul_eq_one_iff_eq_inv.mpr hainv
  have hxcen := hk1 x hm
  have hodd : Odd (Nat.card (Subgroup.center (modelUniv t 3 3 e Fact.out).K)) :=
    AschTight.S19M.factM3 3 e Fact.out hp2 t 3 hT6 hadm
  apply hx1
  by_contra hne
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hne
  have h1 : orderOf x ∣ Nat.card (Subgroup.center (modelUniv t 3 3 e Fact.out).K) :=
    Subgroup.orderOf_dvd_natCard _ hxcen
  rw [hord] at h1
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16
