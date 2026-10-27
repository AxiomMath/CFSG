module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.L44AtlasBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.L44AtlasInner
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ElimFacts

public noncomputable section

namespace CFSG.EvenSporadicStandard.M24Std

namespace L44Atlas

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.KS21.L44 (F4 M PL card_F4 center_PL conjAut_mem_range)

theorem card_ringAut_F4 : Nat.card (F4 ≃+* F4) = 2 := by
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality
    (F := F4) Nat.prime_two (n := 2) (by norm_num) (by rw [card_F4]; norm_num)
  exact hcard

theorem conj_injective_PL : Function.Injective (MulAut.conj : PL →* MulAut PL) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  have hZ : g ∈ Subgroup.center PL := by
    rw [Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun φ : MulAut PL => φ h) (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [center_PL] at hZ
  exact hZ

theorem card_mulAut_PL : Nat.card (MulAut PL) = 4 * Nat.card PL := by
  let Φ : PL × ((F4 ≃+* F4) × Bool) → MulAut PL := fun t =>
    MulAut.conj t.1 * (fieldAut 4 F4 t.2.1 * dpow t.2.2)
  have surj : Function.Surjective Φ := by
    intro α
    obtain ⟨-, hgen⟩ := automorphism_generation (K := F4) (n := 4) (by norm_num)
    obtain ⟨A, σ, ε, hε, hα⟩ := hgen α
    obtain ⟨x, hx⟩ := conjAut_mem_range A
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · refine ⟨(x, σ, false), ?_⟩
      simp only [Φ, dpow_false, mul_one, hx, hα, pow_zero]
    · refine ⟨(x, σ, true), ?_⟩
      simp only [Φ, dpow, ite_true, hx, hα, pow_one, mul_assoc]
  have inj : Function.Injective Φ := by
    rintro ⟨x, σ, b⟩ ⟨y, τ, c⟩ h
    simp only [Φ] at h
    have h1 : MulAut.conj (y⁻¹ * x) = fieldAut 4 F4 (τ * σ⁻¹) * dpow (xor c b) := by
      have hb : (dpow b)⁻¹ = dpow b := by
        rw [inv_eq_iff_mul_eq_one, dpow_mul, Bool.xor_self, dpow_false]
      calc MulAut.conj (y⁻¹ * x) = (MulAut.conj y)⁻¹ * MulAut.conj x := by rw [map_mul, map_inv]
        _ = (fieldAut 4 F4 τ * dpow c) * (fieldAut 4 F4 σ * dpow b)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, inv_mul_cancel_left]
        _ = fieldAut 4 F4 τ * (dpow c * dpow b) * (fieldAut 4 F4 σ)⁻¹ := by
          rw [_root_.mul_inv_rev, hb]
          simp only [mul_assoc]
        _ = fieldAut 4 F4 τ * (dpow (xor c b) * fieldAut 4 F4 σ⁻¹) := by
          rw [dpow_mul, map_inv, mul_assoc]
        _ = fieldAut 4 F4 (τ * σ⁻¹) * dpow (xor c b) := by
          rw [dpow_comm, map_mul, mul_assoc]
    obtain ⟨hρ, hcb⟩ := eq_of_mem_range (τ * σ⁻¹) (xor c b) ⟨y⁻¹ * x, h1⟩
    have h2 : MulAut.conj (y⁻¹ * x) = 1 := by
      rw [h1, hρ, hcb, map_one, dpow_false, mul_one]
    have hτσ : τ = σ := mul_inv_eq_one.mp hρ
    have hcb' : c = b := by simpa using hcb
    have hxy : x = y := by
      have : y⁻¹ * x = 1 := conj_injective_PL (by rw [h2, map_one])
      rwa [inv_mul_eq_one, eq_comm] at this
    rw [hxy, hτσ, hcb']
  rw [← Nat.card_congr (Equiv.ofBijective Φ ⟨inj, surj⟩), Nat.card_prod, Nat.card_prod,
    card_ringAut_F4, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  ring

end L44Atlas

theorem atlasL44Aut : AtlasL44Aut := by
  intro E _ ⟨e⟩
  let e' : E ≃* CFSG.RankThree.PartTwo.KFacts.KS21.L44.PL :=
    e.trans (L44Atlas.pslEquivProjectiveSL 4 (GaloisField 2 2))
  rw [Nat.card_congr (MulAut.congr e').toEquiv, Nat.card_congr e'.toEquiv]
  exact L44Atlas.card_mulAut_PL

end CFSG.EvenSporadicStandard.M24Std
