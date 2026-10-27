module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Defs
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.L34Exp3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem l34EquivProjectiveSL {K : Type} [Group K] (hL : IsRankThreeL34 K) :
    ∃ (F : Type) (_ : Field F), Nat.card F = 4 ∧ Nonempty (K ≃* projectiveSL 3 F) := by
  obtain ⟨q, hq2, hqe, hv, ⟨e⟩⟩ := hL
  exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.exists_equiv_projectiveSL_of_l34Index
    (d := ⟨.A 2 q, hv⟩) ⟨q, hq2, hqe, rfl⟩ e

theorem l34SylowCard {K : Type} [Group K] [Finite K] (hL : IsRankThreeL34 K) (S : Sylow 3 K) :
    Nat.card (S : Subgroup K) = 9 := by
  obtain ⟨F, _, hF, ⟨ψ⟩⟩ := l34EquivProjectiveSL hL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfK : (Nat.card K).factorization 3 = 2 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact factorization_card hF
  rw [Sylow.card_eq_multiplicity, hfK]
  norm_num

theorem l34SylowElemAbelian {K : Type} [Group K] [Finite K] (hL : IsRankThreeL34 K)
    (S : Sylow 3 K) : IsElemAbelian 3 (S : Subgroup K) := by
  obtain ⟨F, _, hF, ⟨ψ⟩⟩ := l34EquivProjectiveSL hL
  have hE9 : Nat.card ((S : Subgroup K).map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact l34SylowCard hL S
  have hEA : CFSG.IsElementaryAbelian 3 ((S : Subgroup K).map ψ.toMonoidHom) :=
    isElementaryAbelian_of_card_eq_nine hF hE9
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have := hEA.toIsMulCommutative.is_comm.comm
      ⟨ψ a, Subgroup.mem_map_of_mem ψ.toMonoidHom a.2⟩
      ⟨ψ b, Subgroup.mem_map_of_mem ψ.toMonoidHom b.2⟩
    apply ψ.injective
    show ψ ((a : K) * b) = ψ ((b : K) * a)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val this
  · have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3)
      (A := (S : Subgroup K).map ψ.toMonoidHom) (ψ x) (Subgroup.mem_map_of_mem ψ.toMonoidHom hx)
    apply ψ.injective
    simpa [map_pow] using this

private theorem klein_model {k : Type*} [Field k] (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) :
    ∃ x y : projectiveSL 3 k, x * x = 1 ∧ y * y = 1 ∧ x * y = y * x ∧
      aP u * x * (aP u)⁻¹ = y ∧ aP u * y * (aP u)⁻¹ = x * y ∧ x ≠ 1 := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hω2 := LinearFieldFour.omega_mul_omega hk u.ne_zero (val_ne_one hu)
  have h2 : ∀ c : k, c + c = 0 := fun c => CharTwo.add_self_eq_zero c
  have h0 : (LinearFieldFour.xP 0 : projectiveSL 3 k) = 1 := (LinearFieldFour.xP_eq_one_iff 0).2 rfl
  refine ⟨LinearFieldFour.xP 1, LinearFieldFour.xP (u : k), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← LinearFieldFour.xP_add, h2, h0]
  · rw [← LinearFieldFour.xP_add, h2, h0]
  · rw [← LinearFieldFour.xP_add, ← LinearFieldFour.xP_add, add_comm]
  · rw [aP_eq_hP hk, LinearFieldFour.hP_conj_xP, mul_one]
  · rw [aP_eq_hP hk, LinearFieldFour.hP_conj_xP, ← LinearFieldFour.xP_add, hω2, add_comm]
  · rw [Ne, LinearFieldFour.xP_eq_one_iff]
    exact one_ne_zero

theorem l34KleinOfSylow {K : Type} [Group K] [Finite K] (hL : IsRankThreeL34 K) (S : Sylow 3 K) :
    ∃ b ∈ (S : Subgroup K), b ≠ 1 ∧ ∃ x y : K, x * x = 1 ∧ y * y = 1 ∧ x * y = y * x ∧
      b * x * b⁻¹ = y ∧ b * y * b⁻¹ = x * y ∧ x ∉ normalizer ((S : Subgroup K) : Set K) := by
  obtain ⟨F, _, hF, ⟨ψ⟩⟩ := l34EquivProjectiveSL hL
  have hE9 : Nat.card ((S : Subgroup K).map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact l34SylowCard hL S
  obtain ⟨g, hg⟩ := exists_eq_map_conj_eZero hF hE9
  obtain ⟨u, hu⟩ := exists_units_ne_one hF
  obtain ⟨x₀, y₀, hx₀, hy₀, hxy₀, hax, hay, hx₀1⟩ := klein_model hF hu
  have hmem : g * aP u * g⁻¹ ∈ (S : Subgroup K).map ψ.toMonoidHom := by
    rw [hg]
    exact ⟨aP u, aP_mem_eZero, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  obtain ⟨b, hbS, hb⟩ := hmem
  have hb' : ψ b = g * aP u * g⁻¹ := hb
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [map_one] at hb'
    apply aP_ne_one hF hu
    calc aP u = g⁻¹ * (g * aP u * g⁻¹) * g := by group
      _ = 1 := by rw [← hb']; group
  have hx : (ψ.symm (g * x₀ * g⁻¹)) * ψ.symm (g * x₀ * g⁻¹) = 1 := by
    apply ψ.injective
    rw [map_mul ψ, ψ.apply_symm_apply, map_one]
    calc g * x₀ * g⁻¹ * (g * x₀ * g⁻¹) = g * (x₀ * x₀) * g⁻¹ := by group
      _ = 1 := by rw [hx₀]; group
  have hy : (ψ.symm (g * y₀ * g⁻¹)) * ψ.symm (g * y₀ * g⁻¹) = 1 := by
    apply ψ.injective
    rw [map_mul ψ, ψ.apply_symm_apply, map_one]
    calc g * y₀ * g⁻¹ * (g * y₀ * g⁻¹) = g * (y₀ * y₀) * g⁻¹ := by group
      _ = 1 := by rw [hy₀]; group
  have hxy : ψ.symm (g * x₀ * g⁻¹) * ψ.symm (g * y₀ * g⁻¹) =
      ψ.symm (g * y₀ * g⁻¹) * ψ.symm (g * x₀ * g⁻¹) := by
    apply ψ.injective
    rw [map_mul ψ, map_mul ψ, ψ.apply_symm_apply, ψ.apply_symm_apply]
    calc g * x₀ * g⁻¹ * (g * y₀ * g⁻¹) = g * (x₀ * y₀) * g⁻¹ := by group
      _ = g * (y₀ * x₀) * g⁻¹ := by rw [hxy₀]
      _ = g * y₀ * g⁻¹ * (g * x₀ * g⁻¹) := by group
  have hbx : b * ψ.symm (g * x₀ * g⁻¹) * b⁻¹ = ψ.symm (g * y₀ * g⁻¹) := by
    apply ψ.injective
    rw [map_mul ψ, map_mul ψ, map_inv ψ, hb', ψ.apply_symm_apply, ψ.apply_symm_apply]
    calc g * aP u * g⁻¹ * (g * x₀ * g⁻¹) * (g * aP u * g⁻¹)⁻¹ =
        g * (aP u * x₀ * (aP u)⁻¹) * g⁻¹ := by group
      _ = g * y₀ * g⁻¹ := by rw [hax]
  have hby : b * ψ.symm (g * y₀ * g⁻¹) * b⁻¹ =
      ψ.symm (g * x₀ * g⁻¹) * ψ.symm (g * y₀ * g⁻¹) := by
    apply ψ.injective
    rw [map_mul ψ, map_mul ψ, map_mul ψ, map_inv ψ, hb', ψ.apply_symm_apply, ψ.apply_symm_apply]
    calc g * aP u * g⁻¹ * (g * y₀ * g⁻¹) * (g * aP u * g⁻¹)⁻¹ =
        g * (aP u * y₀ * (aP u)⁻¹) * g⁻¹ := by group
      _ = g * (x₀ * y₀) * g⁻¹ := by rw [hay]
      _ = g * x₀ * g⁻¹ * (g * y₀ * g⁻¹) := by group
  refine ⟨b, hbS, hb1, ψ.symm (g * x₀ * g⁻¹), ψ.symm (g * y₀ * g⁻¹), hx, hy, hxy, hbx, hby, ?_⟩
  intro hxN
  set x := ψ.symm (g * x₀ * g⁻¹) with hxdef
  set y := ψ.symm (g * y₀ * g⁻¹) with hydef
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hcomm : x * y ∈ (S : Subgroup K) := by
    have h1 : x * b * x⁻¹ * b⁻¹ ∈ (S : Subgroup K) :=
      mul_mem ((mem_normalizer_iff.1 hxN b).1 hbS) (inv_mem hbS)
    have h2 : x * b * x⁻¹ * b⁻¹ = x * y := by
      calc x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
        _ = x * (b * x * b⁻¹) := by rw [hxinv]
        _ = x * y := by rw [hbx]
    rwa [h2] at h1
  have hsq : (x * y) * (x * y) = 1 := by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx, hy, one_mul]
  have hxy1 : x * y = 1 := by
    have h1 : orderOf (x * y) ∣ 9 := l34SylowCard hL S ▸ Subgroup.orderOf_dvd_natCard _ hcomm
    have h2 : orderOf (x * y) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    have h3 : orderOf (x * y) ∣ Nat.gcd 9 2 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 9 2 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  have hyx : y = x := by
    have h := hxy1
    rw [mul_eq_one_iff_eq_inv, inv_eq_of_mul_eq_one_right hy] at h
    exact h.symm
  have hy1 : y = 1 := by
    have h1 : b * y * b⁻¹ = 1 := by rw [hby]; exact hxy1
    calc y = b⁻¹ * (b * y * b⁻¹) * b := by group
      _ = 1 := by rw [h1]; group
  have hx1 : x = 1 := hyx.symm.trans hy1
  apply hx₀1
  have h1 : g * x₀ * g⁻¹ = 1 := by
    have := congrArg ψ hx1
    rwa [hxdef, ψ.apply_symm_apply, map_one] at this
  calc x₀ = g⁻¹ * (g * x₀ * g⁻¹) * g := by group
    _ = 1 := by rw [h1]; group

end CFSG.LocalAnalysis.RankThreeTheoremC
