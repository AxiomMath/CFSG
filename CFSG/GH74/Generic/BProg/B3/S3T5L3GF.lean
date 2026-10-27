module

public import CFSG.GH74.Generic.BProg.B3.S3T5L3Tr
public import CFSG.GH74.Generic.BProg.B3.S3T5L3SU
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU4Kill

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T5L3

open Matrix Subgroup CFSG CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F]

theorem oddCore_bot_linGField {K : Type} [Group K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) (e₀ : K ≃* projectiveSL 3 F)
    (hZ : ∀ z : K, (∀ x, z * x = x * z) → z = 1) {H : Subgroup (MulAut K)}
    (hH : (MulAut.conj : K →* MulAut K).range ≤ H) (u : H) (hu : u * u = 1)
    (A : GL (Fin 3) F) (σ : F ≃+* F) (hσ : σ ≠ 1)
    (hα : MulAut.congr e₀ (u : MulAut K) = conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) :
    involutionOddCore u = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hu' : (u : MulAut K) * u = 1 := congrArg Subtype.val hu
  have hsq : (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) ^ 2 = 1 := by
    rw [← hα, sq, ← map_mul, hu', map_one]
  obtain ⟨hfe, hσpow, H₀, hH₀⟩ :=
    odd_linear_graph_field_involution_conjugacy hp hf hcard le_rfl A σ hσ hsq
  obtain ⟨e, he⟩ : ∃ e, f = 2 * e := ⟨f / 2, by obtain ⟨k, hk⟩ := hfe; omega⟩
  have he1 : 1 ≤ e := by omega
  have hF : Nat.card F = (p ^ e) ^ 2 := by rw [hcard, he, ← pow_mul, mul_comm]
  have hσe : ∀ x, σ x = x ^ p ^ e := fun x => by rw [hσpow x, show f / 2 = e by omega]
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    rw [hσe, hσe, ← pow_mul, ← sq, ← hF, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := fun h => by
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).1 (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
  set c := conjAut 3 F H₀ with hc
  let e₁ : K ≃* projectiveSL 3 F := e₀.trans c⁻¹
  have hγ : MulAut.congr e₁ (u : MulAut K) = fieldAut 3 F σ * dualAut 3 F := by
    have h1 : MulAut.congr e₁ (u : MulAut K) = c⁻¹ * MulAut.congr e₀ (u : MulAut K) * c := by
      ext y; rfl
    rw [h1, hα, hH₀]
    group
  have hΩ : ∀ g, g ∈ (Odd87.suSL (F := F) (p ^ e)).range ↔ psiU σ g = g := fun g => by
    rw [psiU_fix_iff σ hσσ, mem_suRange_iff hF hσe]
  have hperf : Group.IsPerfect (Odd87.suSL (F := F) (p ^ e)).range := by
    have := Odd87.isPerfect_statedSU_three_odd hF hp2 (K := F)
    exact Group.IsPerfect.range _
  have hsimp : IsSimpleGroup ((Odd87.suSL (F := F) (p ^ e)).range.map (LinearFlag.proj 3 F)) := by
    have hr : (Odd87.suSL (F := F) (p ^ e)).range.map (LinearFlag.proj 3 F) =
        (Odd87.suToProj (F := F) (p ^ e)).range := by
      rw [Odd87.suToProj, MonoidHom.range_comp]
    rw [hr]
    have := Odd87.isSimpleGroup_statedProj_three_odd hF (fun h => by
      rw [h] at hodd; exact (Nat.not_odd_iff_even.2 even_two) hodd)
    exact ((QuotientGroup.quotientKerEquivRange _).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (Odd87.ker_suToProj (p ^ e)))).isSimpleGroup
  refine involutionOddCore_eq_bot_of_proj e₁ hZ hH u hγ (psiU σ) (proj_psiU σ) _ hΩ hperf
    (R := sgnSet) (fun g hg => (mem_suRange_iff hF hσe g).2 (sgn_unitary σ g hg))
    sgn_map (sgn_comm h2) fun τ _ _ _ hτΩ => ?_
  refine ringEquiv_eq_one_of_fix_normOne hp he1 hF τ fun x hx => ?_
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hmem := (mem_suRange_iff hF hσe ⟨diagU x, diagU_det hx0⟩).2 (diagU_unitary σ hσe hx)
  have h := congrFun (congrFun (hτΩ _ hmem) 0) 0
  simpa [diagU] using h

end CFSG.GH74.Generic.BProg.B3.S3T5L3
