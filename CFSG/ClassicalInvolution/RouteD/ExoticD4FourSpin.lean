module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourRot
public import CFSG.ClassicalInvolution.RouteD.ExoticD4TwinModel
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutPlus
public import CFSG.ClassicalInvolution.Models.Transfer.Orthogonal.Standard
public import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.ClassicalInvolution.SmallCases.ConnectedA2FactsFibre
import CFSG.ClassicalInvolution.Balance.PassTwoConj
import CFSG.ClassicalInvolution.Generic.InductionMain
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
import CFSG.ClassicalInvolution.RouteD.TypeAChain
import CFSG.ClassicalInvolution.SmallCases.ConnectedA2
import CFSG.ClassicalInvolution.SmallCases.ConnectedA2Exact

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.RouteD.NonClassical (IsFundSpin)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Squares

theorem exists_two_sq_eq_neg_one (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ a b : F, a ^ 2 + b ^ 2 = -1 :=
  CFSG.ClassicalInvolution.ConnectedA2.exists_sq_add_sq_eq_neg_one F hodd

theorem pow_four_eq_one_of_sq {G : Type*} [Group G] {t : G} (h : t * t * (t * t) = 1) :
    t ^ 4 = 1 := by
  calc t ^ 4 = t * t * (t * t) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h

end Squares

section UB

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {F₁ F₃ : OFrame Q} {a b : F}

theorem uB_ne_one (h2 : (2 : F) ≠ 0) (hab : a ^ 2 + b ^ 2 = -1)
    (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0) : uB (F := F) F₃ ≠ 1 := by
  intro h
  have h0 : uB (F := F) F₃ (bV F₁ F₃ a b (Sum.inr 0)) = bV F₁ F₃ a b (Sum.inr 0) := by
    rw [h]
    rfl
  rw [uB_bV horth] at h0
  simp only [epsU, sgnB, Sum.elim_inr] at h0
  simp at h0
  exact bV_ne_zero hab (Sum.inr 0) (eq_zero_of_neg_eq_self h2 h0)

theorem uB_ne_neg (h2 : (2 : F) ≠ 0) (hab : a ^ 2 + b ^ 2 = -1)
    (horth : ∀ X Y, polar Q (F₁.incl X) (F₃.incl Y) = 0) :
    uB (F := F) F₃ ≠ LinearEquiv.neg F := by
  intro h
  have h0 := congrArg (fun T : V ≃ₗ[F] V => T (bV F₁ F₃ a b (Sum.inl 0))) h
  simp only [LinearEquiv.neg_apply] at h0
  rw [uB_bV horth] at h0
  simp only [epsU, Sum.elim_inl, one_smul] at h0
  exact bV_ne_zero hab (Sum.inl 0) (eq_zero_of_neg_eq_self h2 h0.symm)

end UB

section Partner

variable {F : Type} [Field F] [Finite F]

theorem exists_partner_spin (hodd : Odd (Nat.card F))
    (hperf : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)),
      ⁅R, R⁆ = R)
    {R₁ R₃ R₄ : Subgroup (spinGroup (quadPlus 4 F))}
    (h₁ : R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)))
    (F₁ F₃ : OFrame (quadPlus 4 F))
    (hθ₁ : R₁.map (spinAction (quadPlus 4 F)) = F₁.La.range)
    (hθ₃ : R₃.map (spinAction (quadPlus 4 F)) = F₃.La.range)
    (hθ₄ : R₄.map (spinAction (quadPlus 4 F)) = F₃.swap.La.range)
    (horth : ∀ X Y, polar (quadPlus 4 F) (F₁.incl X) (F₃.incl Y) = 0)
    {c : spinGroup (quadPlus 4 F)} (hc : spinAction (quadPlus 4 F) c = F₁.La (-1)) :
    ∃ u₃ ∈ R₃, ∃ u₄ ∈ R₄,
      ∃ P ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)), ∃ x ∈ P,
        spinAction (quadPlus 4 F) u₃ = F₃.La (slB F) ∧
        spinAction (quadPlus 4 F) u₄ = F₃.swap.La (slB F) ∧
        spinAction (quadPlus 4 F) (u₃ * u₄) ≠ 1 ∧
        spinAction (quadPlus 4 F) (u₃ * u₄) ≠ LinearEquiv.neg F ∧
        (∀ r ∈ P, r * (u₃ * u₄) = (u₃ * u₄) * r) ∧
        spinAction (quadPlus 4 F) ((x * c * x⁻¹ * c⁻¹) * (x * c * x⁻¹ * c⁻¹)) = 1 ∧
        (x * c * x⁻¹ * c⁻¹) ^ 4 = 1 ∧
        x * c * x⁻¹ * c⁻¹ ∉ Subgroup.center (spinGroup (quadPlus 4 F)) := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hdim : Module.finrank F (Fin 4 ⊕ Fin 4 → F) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  obtain ⟨a, b, hab⟩ := exists_two_sq_eq_neg_one F hodd
  have hQnd : (polarBilin (quadPlus 4 F)).Nondegenerate := nondegenerate_polarBilin_quadPlus 4 F
  have hgO := gRot_mem h2 hab horth
  have hperp : 2 ≤ Module.finrank F F₁.perp := by
    have h1 := Submodule.finrank_add_eq_of_isCompl F₁.isCompl_span_perp
    rw [Frame.finrank_span, hdim] at h1
    omega
  obtain ⟨x₀, hx₀⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_spin_conj hodd hQnd F₁
    (F₁.map hgO) hperp
  have hker := ker_spinAction_le_center (quadPlus 4 F)
  have hPθ : (conjSub x₀ R₁).map (spinAction (quadPlus 4 F)) = (F₁.map hgO).La.range := by
    show (R₁.map (MulAut.conj x₀).toMonoidHom).map _ = _
    rw [CFSG.ClassicalInvolution.ModelFacts.map_conj_map, hθ₁]
    exact (CFSG.ClassicalInvolution.ModelFacts.La_range_eq_map_conj hx₀).symm
  have hP : conjSub x₀ R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus
      (plusDatum 4 F (by norm_num)) := conjSub_mem_fundamentalSubgroups h₁ x₀
  have hxmem : gRot h2 hab horth * F₁.La (slW hab) * (gRot h2 hab horth)⁻¹ ∈
      (conjSub x₀ R₁).map (spinAction (quadPlus 4 F)) := by
    rw [hPθ]
    exact ⟨slW hab, Frame.map_La F₁ hgO _⟩
  obtain ⟨x, hxP, hxθ⟩ := hxmem
  obtain ⟨u₃, hu₃, hu₃θ⟩ : F₃.La (slB F) ∈ R₃.map (spinAction (quadPlus 4 F)) := by
    rw [hθ₃]
    exact ⟨slB F, rfl⟩
  obtain ⟨u₄, hu₄, hu₄θ⟩ : F₃.swap.La (slB F) ∈ R₄.map (spinAction (quadPlus 4 F)) := by
    rw [hθ₄]
    exact ⟨slB F, rfl⟩
  have hswap : ∀ X Y, polar (quadPlus 4 F) (F₁.incl X) (F₃.swap.incl Y) = 0 := fun X Y => by
    rw [Frame.incl_swap]
    exact horth X _
  have hcomm_u : ∀ A : SL(2, F), Commute (F₁.La A) (uB F₃) := fun A => by
    have e1 := Frame.La_comm_of_orth horth A (slB F)
    have e2 := Frame.La_comm_of_orth hswap A (slB F)
    show F₁.La A * uB F₃ = uB F₃ * F₁.La A
    rw [uB, ← mul_assoc, e1, mul_assoc, e2, ← mul_assoc]
  have hgu : Commute (gRot h2 hab horth) (uB F₃) := gRot_comm_uB h2 hab horth hdim
  have hcentθ : ∀ y ∈ (conjSub x₀ R₁).map (spinAction (quadPlus 4 F)),
      y * (F₃.La (slB F) * F₃.swap.La (slB F)) = (F₃.La (slB F) * F₃.swap.La (slB F)) * y := by
    intro y hy
    rw [hPθ] at hy
    obtain ⟨A, rfl⟩ := hy
    rw [Frame.map_La]
    exact ((hgu.mul_left (hcomm_u A)).mul_left hgu.inv_left).eq
  have hi₁ : F₁.La (-1) * F₁.La (-1) = 1 := Frame.La_neg_one_mul_self F₁
  have hθt : spinAction (quadPlus 4 F) (x * c * x⁻¹ * c⁻¹) = iX h2 hab horth * F₁.La (-1) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxθ, hc, inv_eq_of_mul_eq_one_right hi₁]
    rfl
  have hiXiX : iX h2 hab horth * iX h2 hab horth = 1 := by
    show xRot h2 hab horth * F₁.La (-1) * (xRot h2 hab horth)⁻¹ *
      (xRot h2 hab horth * F₁.La (-1) * (xRot h2 hab horth)⁻¹) = 1
    calc _ = xRot h2 hab horth * (F₁.La (-1) * F₁.La (-1)) * (xRot h2 hab horth)⁻¹ := by group
      _ = 1 := by rw [hi₁]; group
  have hsq : (iX h2 hab horth * F₁.La (-1)) * (iX h2 hab horth * F₁.La (-1)) = 1 := by
    have hc' := iX_comm_i₁ h2 hab horth hdim
    calc (iX h2 hab horth * F₁.La (-1)) * (iX h2 hab horth * F₁.La (-1))
        = iX h2 hab horth * (F₁.La (-1) * iX h2 hab horth) * F₁.La (-1) := by group
      _ = iX h2 hab horth * (iX h2 hab horth * F₁.La (-1)) * F₁.La (-1) := by rw [hc']
      _ = (iX h2 hab horth * iX h2 hab horth) * (F₁.La (-1) * F₁.La (-1)) := by group
      _ = 1 := by rw [hiXiX, hi₁, one_mul]
  have hsqθ : spinAction (quadPlus 4 F)
      ((x * c * x⁻¹ * c⁻¹) * (x * c * x⁻¹ * c⁻¹)) = 1 := by
    rw [map_mul, hθt]
    exact hsq
  refine ⟨u₃, hu₃, u₄, hu₄, conjSub x₀ R₁, hP, x, hxP, hu₃θ, hu₄θ, ?_, ?_, ?_, hsqθ, ?_, ?_⟩
  · rw [map_mul, hu₃θ, hu₄θ]
    exact uB_ne_one h2 hab horth
  · rw [map_mul, hu₃θ, hu₄θ]
    exact uB_ne_neg h2 hab horth
  · intro r hr
    have hmem : u₃ * u₄ ∈ Subgroup.centralizer ((conjSub x₀ R₁ : Subgroup _) : Set _) := by
      refine Models.Transfer.mem_centralizer_of_map hker (hperf _ hP) (g := u₃ * u₄) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [map_mul, hu₃θ, hu₄θ]
      exact hcentθ y hy
    exact Subgroup.mem_centralizer_iff.mp hmem r hr
  · have h4 := CFSG.ClassicalInvolution.ModelFacts.OrthAut.plus_hker2 (F := F) 4 _
      (MonoidHom.mem_ker.mpr hsqθ)
    exact pow_four_eq_one_of_sq h4
  · intro hz
    have hmem : spinAction (quadPlus 4 F) (x * c * x⁻¹ * c⁻¹) ∈ elementaryGroup (quadPlus 4 F) := by
      rw [← range_spinAction_quadPlus (by norm_num)]
      exact ⟨_, rfl⟩
    let zz : ↥(elementaryGroup (quadPlus 4 F)) := ⟨_, hmem⟩
    have hzc : zz ∈ Subgroup.center ↥(elementaryGroup (quadPlus 4 F)) := by
      rw [Subgroup.mem_center_iff]
      intro u
      have hu : (u : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) ∈
          (spinAction (quadPlus 4 F)).range := by
        rw [range_spinAction_quadPlus (by norm_num)]
        exact u.2
      obtain ⟨y, hy⟩ := hu
      apply Subtype.ext
      show (u : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) *
        spinAction (quadPlus 4 F) (x * c * x⁻¹ * c⁻¹) =
          spinAction (quadPlus 4 F) (x * c * x⁻¹ * c⁻¹) *
            (u : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F))
      rw [← hy, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz y)]
    have hz2 : zz * zz = 1 := Subtype.ext (by
      show spinAction (quadPlus 4 F) (x * c * x⁻¹ * c⁻¹) *
        spinAction (quadPlus 4 F) (x * c * x⁻¹ * c⁻¹) = 1
      rw [hθt]
      exact hsq)
    have hZ := CFSG.ClassicalInvolution.Models.Transfer.centerScalar_quadPlus (K := F)
      (n := 4) (by norm_num)
    rcases CFSG.ClassicalInvolution.Models.Transfer.eq_one_or_eq_neg_of_mem_center hZ hzc hz2 with
      h | h
    · exact iX_mul_i₁_ne_one h2 hab horth hdim (hθt ▸ congrArg Subtype.val h)
    · exact iX_mul_i₁_ne_neg h2 hab horth hdim (hθt ▸ h)

end Partner

end CFSG.ClassicalInvolution.RouteD.Exotic
