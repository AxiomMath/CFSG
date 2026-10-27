module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7N7
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmBase
import CFSG.ClassicalInvolution.Q3.TL4AE286None

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7W

variable {Y : Type} [Group Y]

variable [Finite Y]

theorem centMod_of_sylow {J R₁ : Subgroup Y} {j c : Y} (hj : IsUniqueInvolution J j)
    (hR : IsSylow2In R₁ J) (hc2 : c * c = 1) (hcN : c ∈ Subgroup.normalizer (J : Set Y))
    (hcR : ∀ r ∈ R₁, r * c = c * r) : CentMod J c := by
  by_cases hc1 : c = 1
  · subst hc1
    intro b _
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hord : ∀ {x : Y}, x * x = 1 → x ≠ 1 → orderOf x = 2 := fun {x} hx hx1 =>
    orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  have hU : ∀ x ∈ J, orderOf x = 2 → x = j := by
    intro x hx hx2
    have hxx : x * x = 1 := by rw [← pow_two, ← hx2, pow_orderOf_eq_one]
    have hx1 : x ≠ 1 := by
      rintro rfl
      simp at hx2
    exact (hj.unique x hx hxx).resolve_left hx1
  intro b hb
  have h := commutator_mem_oddCore_of_centralizes_sylow (hord hj.sq hj.ne_one) hj.mem hU
    (hord hc2 hc1) hcN ⟨hR.1, hR.2.1, hR.2.2⟩ hcR hb
  have e : c * b * c⁻¹ * b⁻¹ = (b * c * b⁻¹ * c⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.inv_mem _ h

end F7W

section Steps

variable {n : ℕ}

section Facts

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem P23Cfg.mem_normalizer_of_sylow (hc : P23Cfg n Y R S t K' W u e g) {R₁ : Subgroup Y}
    (hR₁ : IsSylow2In R₁ (conjSub g (tightCore R))) {x : Y} (hxue : x * (u * e) = (u * e) * x)
    (hxR : x ∈ Subgroup.normalizer (R₁ : Set Y)) :
    x ∈ Subgroup.normalizer ((conjSub g (tightCore R) : Subgroup Y) : Set Y) := by
  have hd := hc.data
  have hdt : g⁻¹ * x * g ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : x * (g * t * g⁻¹) = (g * t * g⁻¹) * x := by rw [hd.hgt]; exact hxue
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [h1]
      _ = t * (g⁻¹ * x * g) := by group
  rw [mem_normalizer_iff_conjSub_eq]
  rcases p23_conj_twins hc hdt with ⟨h1, -⟩ | ⟨h1, -⟩
  · calc conjSub x (conjSub g (tightCore R)) = conjSub g (conjSub (g⁻¹ * x * g) (tightCore R)) := by
          rw [← conjSub_mul, ← conjSub_mul]
          congr 1
          group
      _ = conjSub g (tightCore R) := by rw [h1]
  · exfalso
    have hC := CoreData.of_S hc.std.perp.core
    have hΩ : HypOmegaGen (Om R) := hC.hyp
    have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
    have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
    have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
    have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
    have heW : e ∈ W := (T7K.e_mem_inf hd).1
    set C := Subgroup.centralizer ({t} : Set Y) with hCdef
    have hWt : W ≤ C := fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
    have htC : t ∈ C := hWt hd.hzW
    have heC : e ∈ C := hWt heW
    have hKC : tightCore R ≤ C := le_centralizer_of_unique hz
    have hK'C : K' ≤ C := le_centralizer_of_unique hz'
    have hR₂ : IsSylow2In (conjSub g⁻¹ R₁) (tightCore R) := by
      have := hR₁.conj g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have hR₂x : conjSub (g⁻¹ * x * g) (conjSub g⁻¹ R₁) = conjSub g⁻¹ R₁ := by
      have hx1 : conjSub x R₁ = R₁ := mem_normalizer_iff_conjSub_eq.mp hxR
      calc conjSub (g⁻¹ * x * g) (conjSub g⁻¹ R₁) = conjSub g⁻¹ (conjSub x R₁) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = conjSub g⁻¹ R₁ := by rw [hx1]
    have hR₂K' : conjSub g⁻¹ R₁ ≤ K' := by
      rw [← hR₂x, ← h1]
      exact conjSub_mono hR₂.1
    have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
      TwinADescent3.isPGroup_two_quotient_conjClass
        (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
    have hK0 : tightCore R ≤ oddCoreOf C ⊔ conjSub g⁻¹ R₁ := by
      have h1 := TL4.le_sup_oddCoreOf_of_isSylow2In (h2 _ hK) hR₂
      have h3 : oddCoreOf (tightCore R) ≤ oddCoreOf C := Small.oddCoreOf_core_le hc.std.perp
      rw [sup_comm]
      exact h1.trans (sup_le_sup_left h3 _)
    have hAB' := F7I.map_le_of_le_sup hK'C (hK0.trans (sup_le_sup_left hR₂K' _))
    obtain ⟨-, -, -, -, ⟨a, ha, b, hb, hab⟩, -, hABc, -⟩ := p23_twin_q8 hc hCdef htC heC
    exact hab (hABc a ha b (hAB' hb))

end Facts

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
