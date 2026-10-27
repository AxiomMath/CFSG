module

public import CFSG.GF2Type.Smith1979.IdxFourIdentECtx
public import CFSG.GF2Type.Smith1979.IdxFourIdentEFL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.Case25.U43Weights
open CFSG.LieType.Multipliers.U43 (X₀)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six

theorem conjSub_one (H : Subgroup G12) : conjSub H 1 = H := by
  ext x
  rw [mem_conjSub]
  simp

theorem exists_conj_eq_E0 {E : Subgroup G12} (hEg : E ≤ gammaU) (hEcard : Nat.card E = 9797760)
    (π : E →* X₀) (hπs : Function.Surjective π) (hπk : π.ker = Subgroup.center E)
    (hZ : (Subgroup.center E).map E.subtype = Subgroup.zpowers theta0e)
    (hE0card : Nat.card E0 = 9797760) :
    ∃ t ∈ gammaU, conjSub E t = E0 := by
  let C : ECtx := ⟨E, hEg, hEcard, π, hπs, hπk, hZ⟩
  obtain ⟨g, c, p, ψ', hgg, hgu, hD5, hD5s, hbconj, hp3, hψ'a, hψ's, hψ'k, hψ'eq⟩ :=
    C.frame_of_ectx
  have hD5E₁ : D5 ≤ conjSub E g⁻¹ := by
    intro d hd
    obtain ⟨a, ha⟩ := hD5s d hd
    rw [mem_conjSub_inv, ← ha]
    have h1 : g * (g⁻¹ * C.rhoA a * g) * g⁻¹ = C.rhoA a := by group
    rw [h1]
    exact a.1.2
  have hA6 : ∀ γ ∈ alternatingGroup (Fin 6), permE γ ∈ conjSub E g⁻¹ := by
    have hp := perm_closure_eq_alternating p hp3 ψ' hψ's hψ'k hψ'eq
    intro γ hγ
    refine permE_mem_of_closure hD5E₁ c p (fun k => ?_) hp hγ
    rw [← hbconj k, mem_conjSub_inv]
    have : g * (g⁻¹ * ((C.levLift k : C.E) : G12) * g) * g⁻¹ = ((C.levLift k : C.E) : G12) := by
      group
    rw [this]
    exact (C.levLift k).2
  have hR0 : R0 ≤ conjSub E g⁻¹ := by
    rintro _ ⟨c', γ, hc', hγ, rfl⟩
    exact mul_mem (hD5E₁ ⟨c', hc', rfl⟩) (hA6 γ hγ)
  have hE₁card : Nat.card (conjSub E g⁻¹) = 9797760 := by
    rw [card_conjSub]; exact hEcard
  obtain ⟨y, a₀, a₀', a₁, hya, hψa₀, hψa₀', hnot⟩ := C.exists_adjacent
  have hyaG : (y : G12) * C.rhoA a₀ * (y : G12)⁻¹ = C.rhoA a₀' := by
    have := congrArg Subtype.val hya
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this
  have hd₀ : ψ' ⟨g⁻¹ * C.rhoA a₀' * g, hD5 a₀'⟩ = Multiplicative.ofAdd ((1, 0, 0, 0) : T4) := by
    rw [hψ'a a₀' (hD5 a₀'), hψa₀']
  obtain ⟨S, j, e, c₂, hS, he, hdc, hc₂⟩ := root_type p ψ' hψ's hψ'k hψ'eq _ hd₀
  have hdc' : g⁻¹ * C.rhoA a₀' * g = diagE c₂ := hdc
  have hyE : g⁻¹ * (y : G12) * g ∈ conjSub E g⁻¹ := by
    rw [mem_conjSub_inv]
    have : g * (g⁻¹ * (y : G12) * g) * g⁻¹ = y := by group
    rw [this]
    exact y.2
  have hyg : g⁻¹ * (y : G12) * g ∈ gammaU :=
    mul_mem (mul_mem (inv_mem hgg) (hEg y.2)) hgg
  have hyu : (g⁻¹ * (y : G12) * g) * theta0e = theta0e * (g⁻¹ * (y : G12) * g) := by
    have := commute_conj_of_commute (inv_mem hgg) (C.theta0e_comm y)
    simpa only [inv_inv] using this
  have hnot₂ : g⁻¹ * (y : G12) * g ∉ monLin := by
    intro hmon
    have hnorm := mul_mem_D5_of_mem_monGamma (monLin_le_monGamma hmon) (hD5 a₁)
    obtain ⟨a, ha⟩ := hD5s _ (by
      have h1 : g⁻¹ * (y : G12) * g * (g⁻¹ * C.rhoA a₁ * g) * (g⁻¹ * (y : G12) * g)⁻¹ =
          g⁻¹ * ((y : G12) * C.rhoA a₁ * (y : G12)⁻¹) * g := by group
      rwa [h1] at hnorm)
    have h2 : (y : G12) * C.rhoA a₁ * (y : G12)⁻¹ = C.rhoA a :=
      (mul_left_cancel (mul_right_cancel ha)).symm
    apply hnot a.1 a.2
    exact Subtype.ext h2
  have hd : (g⁻¹ * (y : G12) * g)⁻¹ * diagE c₂ * (g⁻¹ * (y : G12) * g) ∈ D5 := by
    have h1 : (g⁻¹ * (y : G12) * g)⁻¹ * diagE c₂ * (g⁻¹ * (y : G12) * g) =
        g⁻¹ * C.rhoA a₀ * g := by
      rw [← hdc']
      have h2 : C.rhoA a₀ = (y : G12)⁻¹ * C.rhoA a₀' * y := by rw [← hyaG]; group
      rw [h2]
      group
    rw [h1]
    exact hD5 a₀
  obtain ⟨m, hm, hle⟩ := fl_of_type_E hE₁card hR0 hyE hyg hyu hnot₂ hS he hc₂ hd
  have hmg : m ∈ gammaU := monGamma_le_gammaU hm
  haveI : Finite (conjSub E g⁻¹) := Nat.finite_of_card_ne_zero (by rw [hE₁card]; norm_num)
  have heq : conjSub E0 m = conjSub E g⁻¹ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hE₁card, card_conjSub, hE0card])
  refine ⟨m⁻¹ * g⁻¹, mul_mem (inv_mem hmg) (inv_mem hgg), ?_⟩
  rw [← conjSub_conjSub, ← heq, conjSub_conjSub, inv_mul_cancel, conjSub_one]

end CFSG.GF2Type.Smith1979.IdxFour
