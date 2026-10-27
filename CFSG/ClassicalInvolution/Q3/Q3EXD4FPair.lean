module

public import CFSG.ClassicalInvolution.Q3.Q3EXD4FModel
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourNodes

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.ModelFacts.TG3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.RouteD.NonClassical (IsFundSpin eq_of_map_eq_fund
  exists_inv_of_commutes)
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1


section Partner

theorem exists_partner_spin3 (hF : D4Facts3)
    {R₁ R₃ R₄ : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    (h₁ : R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (F₁ F₃ : OFrame (quadPlus 4 𝔽₃))
    (hθ₁ : R₁.map (spinAction (quadPlus 4 𝔽₃)) = F₁.La.range)
    (hθ₃ : R₃.map (spinAction (quadPlus 4 𝔽₃)) = F₃.La.range)
    (hθ₄ : R₄.map (spinAction (quadPlus 4 𝔽₃)) = F₃.swap.La.range)
    (horth : ∀ X Y, polar (quadPlus 4 𝔽₃) (F₁.incl X) (F₃.incl Y) = 0)
    {c : spinGroup (quadPlus 4 𝔽₃)} (hc : spinAction (quadPlus 4 𝔽₃) c = F₁.La (-1)) :
    ∃ u₃ ∈ R₃, ∃ u₄ ∈ R₄,
      ∃ P ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)), ∃ x ∈ P,
        spinAction (quadPlus 4 𝔽₃) u₃ = F₃.La (slB 𝔽₃) ∧
        spinAction (quadPlus 4 𝔽₃) u₄ = F₃.swap.La (slB 𝔽₃) ∧
        spinAction (quadPlus 4 𝔽₃) (u₃ * u₄) ≠ 1 ∧
        spinAction (quadPlus 4 𝔽₃) (u₃ * u₄) ≠ LinearEquiv.neg 𝔽₃ ∧
        (∀ r ∈ P, r * (u₃ * u₄) = (u₃ * u₄) * r) ∧
        spinAction (quadPlus 4 𝔽₃) ((x * c * x⁻¹ * c⁻¹) * (x * c * x⁻¹ * c⁻¹)) = 1 ∧
        (x * c * x⁻¹ * c⁻¹) ^ 4 = 1 ∧
        x * c * x⁻¹ * c⁻¹ ∉ Subgroup.center (spinGroup (quadPlus 4 𝔽₃)) := by
  have hodd : Odd (Nat.card 𝔽₃) := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have hdim : Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  obtain ⟨a, b, hab⟩ := exists_two_sq_eq_neg_one 𝔽₃ hodd
  have hQnd : (polarBilin (quadPlus 4 𝔽₃)).Nondegenerate := nondegenerate_polarBilin_quadPlus 4 𝔽₃
  have hgO := gRot_mem h2 hab horth
  have hperp : 2 ≤ Module.finrank 𝔽₃ F₁.perp := by
    have h1 := Submodule.finrank_add_eq_of_isCompl F₁.isCompl_span_perp
    rw [Frame.finrank_span, hdim] at h1
    omega
  obtain ⟨x₀, hx₀⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_spin_conj hodd hQnd F₁
    (F₁.map hgO) hperp
  have hker := ker_spinAction_le_center (quadPlus 4 𝔽₃)
  have hPθ : (conjSub x₀ R₁).map (spinAction (quadPlus 4 𝔽₃)) = (F₁.map hgO).La.range := by
    show (R₁.map (MulAut.conj x₀).toMonoidHom).map _ = _
    rw [CFSG.ClassicalInvolution.ModelFacts.map_conj_map, hθ₁]
    exact (CFSG.ClassicalInvolution.ModelFacts.La_range_eq_map_conj hx₀).symm
  have hP : conjSub x₀ R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus
      (plusDatum 4 𝔽₃ (by norm_num)) := conjSub_mem_fundamentalSubgroups h₁ x₀
  have hxmem : gRot h2 hab horth * F₁.La (slW hab) * (gRot h2 hab horth)⁻¹ ∈
      (conjSub x₀ R₁).map (spinAction (quadPlus 4 𝔽₃)) := by
    rw [hPθ]
    exact ⟨slW hab, Frame.map_La F₁ hgO _⟩
  obtain ⟨x, hxP, hxθ⟩ := hxmem
  obtain ⟨u₃, hu₃, hu₃θ⟩ : F₃.La (slB 𝔽₃) ∈ R₃.map (spinAction (quadPlus 4 𝔽₃)) := by
    rw [hθ₃]
    exact ⟨slB 𝔽₃, rfl⟩
  obtain ⟨u₄, hu₄, hu₄θ⟩ : F₃.swap.La (slB 𝔽₃) ∈ R₄.map (spinAction (quadPlus 4 𝔽₃)) := by
    rw [hθ₄]
    exact ⟨slB 𝔽₃, rfl⟩
  have hswap : ∀ X Y, polar (quadPlus 4 𝔽₃) (F₁.incl X) (F₃.swap.incl Y) = 0 := fun X Y => by
    rw [Frame.incl_swap]
    exact horth X _
  have hcomm_u : ∀ A : SL(2, 𝔽₃), Commute (F₁.La A) (Exotic.uB F₃) := fun A => by
    have e1 := Frame.La_comm_of_orth horth A (slB 𝔽₃)
    have e2 := Frame.La_comm_of_orth hswap A (slB 𝔽₃)
    show F₁.La A * Exotic.uB F₃ = Exotic.uB F₃ * F₁.La A
    rw [Exotic.uB, ← mul_assoc, e1, mul_assoc, e2, ← mul_assoc]
  have hgu : Commute (gRot h2 hab horth) (Exotic.uB F₃) := gRot_comm_uB h2 hab horth hdim
  have hcentθ : ∀ y ∈ (conjSub x₀ R₁).map (spinAction (quadPlus 4 𝔽₃)),
      y * (F₃.La (slB 𝔽₃) * F₃.swap.La (slB 𝔽₃)) = (F₃.La (slB 𝔽₃) * F₃.swap.La (slB 𝔽₃)) * y := by
    intro y hy
    rw [hPθ] at hy
    obtain ⟨A, rfl⟩ := hy
    rw [Frame.map_La]
    exact ((hgu.mul_left (hcomm_u A)).mul_left hgu.inv_left).eq
  have hi₁ : F₁.La (-1) * F₁.La (-1) = 1 := Frame.La_neg_one_mul_self F₁
  have hθt : spinAction (quadPlus 4 𝔽₃) (x * c * x⁻¹ * c⁻¹) = iX h2 hab horth * F₁.La (-1) := by
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
  have hsqθ : spinAction (quadPlus 4 𝔽₃)
      ((x * c * x⁻¹ * c⁻¹) * (x * c * x⁻¹ * c⁻¹)) = 1 := by
    rw [map_mul, hθt]
    exact hsq
  refine ⟨u₃, hu₃, u₄, hu₄, conjSub x₀ R₁, hP, x, hxP, hu₃θ, hu₄θ, ?_, ?_, ?_, hsqθ, ?_, ?_⟩
  · rw [map_mul, hu₃θ, hu₄θ]
    exact uB_ne_one h2 hab horth
  · rw [map_mul, hu₃θ, hu₄θ]
    exact uB_ne_neg h2 hab horth
  · intro r hr
    exact ModelFacts.commute_of_map_commute_of_gen3 (spinAction (quadPlus 4 𝔽₃)) hker
      hF.central.k3 (hF.central.gen _ hP) (b := u₃ * u₄) (by
        intro y hy
        rw [map_mul, hu₃θ, hu₄θ]
        exact hcentθ _ ⟨y, hy, rfl⟩) r hr
  · have h4 := CFSG.ClassicalInvolution.ModelFacts.OrthAut.plus_hker2 (F := 𝔽₃) 4 _
      (MonoidHom.mem_ker.mpr hsqθ)
    exact pow_four_eq_one_of_sq h4
  · intro hz
    have hmem : spinAction (quadPlus 4 𝔽₃) (x * c * x⁻¹ * c⁻¹) ∈
        elementaryGroup (quadPlus 4 𝔽₃) := by
      rw [← range_spinAction_quadPlus (by norm_num)]
      exact ⟨_, rfl⟩
    let zz : ↥(elementaryGroup (quadPlus 4 𝔽₃)) := ⟨_, hmem⟩
    have hzc : zz ∈ Subgroup.center ↥(elementaryGroup (quadPlus 4 𝔽₃)) := by
      rw [Subgroup.mem_center_iff]
      intro u
      have hu : (u : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) ∈
          (spinAction (quadPlus 4 𝔽₃)).range := by
        rw [range_spinAction_quadPlus (by norm_num)]
        exact u.2
      obtain ⟨y, hy⟩ := hu
      apply Subtype.ext
      show (u : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) *
        spinAction (quadPlus 4 𝔽₃) (x * c * x⁻¹ * c⁻¹) =
          spinAction (quadPlus 4 𝔽₃) (x * c * x⁻¹ * c⁻¹) *
            (u : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃))
      rw [← hy, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz y)]
    have hz2 : zz * zz = 1 := Subtype.ext (by
      show spinAction (quadPlus 4 𝔽₃) (x * c * x⁻¹ * c⁻¹) *
        spinAction (quadPlus 4 𝔽₃) (x * c * x⁻¹ * c⁻¹) = 1
      rw [hθt]
      exact hsq)
    have hZ := CFSG.ClassicalInvolution.Models.Transfer.centerScalar_quadPlus (K := 𝔽₃)
      (n := 4) (by norm_num)
    rcases CFSG.ClassicalInvolution.Models.Transfer.eq_one_or_eq_neg_of_mem_center hZ hzc hz2 with
      h | h
    · exact iX_mul_i₁_ne_one h2 hab horth hdim (hθt ▸ congrArg Subtype.val h)
    · exact iX_mul_i₁_ne_neg h2 hab horth hdim (hθt ▸ h)


theorem partner_of_opposite3 (hF : D4Facts3) {R₁ Ra Rb : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    (h₁ : R₁ ∈ fundD4 𝔽₃) (ha : Ra ∈ fundD4 𝔽₃) (hb : Rb ∈ fundD4 𝔽₃) (hab : Ra ≠ Rb)
    {F₁ : OFrame (quadPlus 4 𝔽₃)} (hF₁ : R₁.map (spinAction (quadPlus 4 𝔽₃)) = F₁.La.range)
    (ca1 : Commutes R₁ Ra) {ia ib : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)}
    (hia : IsFundSpin Ra ia) (hib : IsFundSpin Rb ib)
    (hoa : F₁.La (-1) * ia = LinearEquiv.neg 𝔽₃) (hob : F₁.La (-1) * ib = LinearEquiv.neg 𝔽₃)
    {c : spinGroup (quadPlus 4 𝔽₃)} (hc : c ∈ R₁) (hcz : ∀ r ∈ R₁, c * r = r * c) (hc1 : c ≠ 1) :
    ∃ ua ∈ Ra, ∃ ub ∈ Rb, ∃ P ∈ fundD4 𝔽₃, ∃ x ∈ P,
      (∀ r ∈ P, r * (ua * ub) = (ua * ub) * r) ∧
      (∀ ca ∈ Ra, (∀ r ∈ Ra, ca * r = r * ca) → ca ≠ 1 → ua * ua = ca) ∧
      (∀ cb ∈ Rb, (∀ r ∈ Rb, cb * r = r * cb) → cb ≠ 1 → ub * ub = cb) ∧
      (¬ ∀ r ∈ Ra, ua * r = r * ua) ∧ (¬ ∀ r ∈ Rb, ub * r = r * ub) ∧
      ua * ub ∉ Subgroup.center (spinGroup (quadPlus 4 𝔽₃)) ∧
      (x * c * x⁻¹ * c⁻¹) ^ 4 = 1 ∧
      x * c * x⁻¹ * c⁻¹ ∉ Subgroup.center (spinGroup (quadPlus 4 𝔽₃)) := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  unfold IsFundSpin at hia hib
  obtain ⟨F₃, hF₃⟩ := hF.exists_frame ha
  obtain ⟨Fb, hFb⟩ := hF.exists_frame hb
  have hia' : F₃.La (-1) = ia :=
    IsFundamental.involution_unique odd_natCard_galoisField_three
      (⟨F₃, hF₃, rfl⟩ : IsFundamental (quadPlus 4 𝔽₃) _ _) hia
  have hib' : Fb.La (-1) = ib :=
    IsFundamental.involution_unique odd_natCard_galoisField_three
      (⟨Fb, hFb, rfl⟩ : IsFundamental (quadPlus 4 𝔽₃) _ _) hib
  rw [← hia'] at hoa
  rw [← hib'] at hob
  have hbeq : Fb.La (-1) = F₃.La (-1) := mul_left_cancel (hob.trans hoa.symm)
  have hFb' : Rb.map (spinAction (quadPlus 4 𝔽₃)) = F₃.swap.La.range := by
    rcases Frame.La_range_eq_or_eq_swap h2 hbeq with h | h
    · exact absurd (hF.eq_of_map_eq hb ha (hFb.trans (h.trans hF₃.symm))) hab.symm
    · exact hFb.trans h
  have hcent : ∀ A : SL(2, 𝔽₃), F₃.La (-1) * F₁.La A = F₁.La A * F₃.La (-1) := by
    intro A
    obtain ⟨r, hr, hrA⟩ : F₁.La A ∈ R₁.map (spinAction (quadPlus 4 𝔽₃)) := hF₁ ▸ ⟨A, rfl⟩
    obtain ⟨s, hs, hsθ⟩ : F₃.La (-1) ∈ Ra.map (spinAction (quadPlus 4 𝔽₃)) := hF₃ ▸ ⟨-1, rfl⟩
    rw [← hsθ, ← hrA, ← map_mul, ← map_mul, (ca1 r hr s hs).symm]
  have hne : F₃.La (-1) ≠ F₁.La (-1) := by
    intro h
    rw [h] at hoa
    exact one_ne_neg_of_frame h2 F₁ (by rw [← hoa, Frame.La_neg_one_mul_self])
  have horth := (Frame.orth_or_eq h2 (hcent (-1)) hcent).resolve_right hne
  have hθc := hF.theta_central h₁ hF₁ hc hcz hc1
  obtain ⟨u₃, hu₃, u₄, hu₄, P, hP, x, hxP, hθ3, hθ4, hn1, hneg, hcom, -, ht4, hnc⟩ :=
    exists_partner_spin3 hF h₁ F₁ F₃ hF₁ hF₃ hFb' horth hθc
  refine ⟨u₃, hu₃, u₄, hu₄, P, hP, x, hxP, hcom, ?_, ?_, ?_, ?_, ?_, ht4, hnc⟩
  · intro ca hca hz hc1'
    exact hF.sq_eq_of_central ha hF₃ hu₃ hθ3 slB_mul_slB hca hz hc1'
  · intro cb hcb hz hc1'
    obtain ⟨hFb3⟩ : Nonempty (OFrame (quadPlus 4 𝔽₃)) := ⟨F₃.swap⟩
    exact hF.sq_eq_of_central hb hFb' hu₄ hθ4 slB_mul_slB hcb hz hc1'
  · intro hz
    obtain ⟨ca, hca, hz', hc1', -⟩ := hF.exists_central ha hF₃
    exact hF.not_central_of_sq ha hu₃ hca hz' hc1' (hF.sq_eq_of_central ha hF₃ hu₃ hθ3
      slB_mul_slB hca hz' hc1') hz
  · intro hz
    obtain ⟨cb, hcb, hz', hc1', -⟩ := hF.exists_central hb hFb'
    exact hF.not_central_of_sq hb hu₄ hcb hz' hc1' (hF.sq_eq_of_central hb hFb' hu₄ hθ4
      slB_mul_slB hcb hz' hc1') hz
  · intro hz
    have hmem : spinAction (quadPlus 4 𝔽₃) (u₃ * u₄) ∈ elementaryGroup (quadPlus 4 𝔽₃) := by
      rw [← range_spinAction_quadPlus (by norm_num)]
      exact ⟨_, rfl⟩
    let zz : ↥(elementaryGroup (quadPlus 4 𝔽₃)) := ⟨_, hmem⟩
    have hzc : zz ∈ Subgroup.center ↥(elementaryGroup (quadPlus 4 𝔽₃)) := by
      rw [Subgroup.mem_center_iff]
      intro u
      have hu : (u : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) ∈
          (spinAction (quadPlus 4 𝔽₃)).range := by
        rw [range_spinAction_quadPlus (by norm_num)]
        exact u.2
      obtain ⟨y, hy⟩ := hu
      apply Subtype.ext
      show (u : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) *
        spinAction (quadPlus 4 𝔽₃) (u₃ * u₄) =
          spinAction (quadPlus 4 𝔽₃) (u₃ * u₄) *
            (u : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃))
      rw [← hy, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz y)]
    have hz2 : zz * zz = 1 := Subtype.ext (by
      show spinAction (quadPlus 4 𝔽₃) (u₃ * u₄) * spinAction (quadPlus 4 𝔽₃) (u₃ * u₄) = 1
      rw [map_mul, hθ3, hθ4]
      exact uB_mul_self' F₃)
    have hZ := CFSG.ClassicalInvolution.Models.Transfer.centerScalar_quadPlus (K := 𝔽₃)
      (n := 4) (by norm_num)
    rcases CFSG.ClassicalInvolution.Models.Transfer.eq_one_or_eq_neg_of_mem_center hZ hzc hz2 with
      h | h
    · exact hn1 (congrArg Subtype.val h)
    · exact hneg h


theorem exists_clique_partner3 (hF : D4Facts3)
    {R₁ R₂ R₃ R₄ : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    (h₁ : R₁ ∈ fundD4 𝔽₃) (h₂ : R₂ ∈ fundD4 𝔽₃) (h₃ : R₃ ∈ fundD4 𝔽₃) (h₄ : R₄ ∈ fundD4 𝔽₃)
    (h12 : R₁ ≠ R₂) (h13 : R₁ ≠ R₃) (h14 : R₁ ≠ R₄) (h23 : R₂ ≠ R₃) (h24 : R₂ ≠ R₄)
    (h34 : R₃ ≠ R₄) (c12 : Commutes R₁ R₂) (c13 : Commutes R₁ R₃) (c14 : Commutes R₁ R₄)
    {c : spinGroup (quadPlus 4 𝔽₃)} (hc : c ∈ R₁) (hcz : ∀ r ∈ R₁, c * r = r * c) (hc1 : c ≠ 1) :
    CliquePartner .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)) R₂ R₃ R₄ c := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  obtain ⟨F₁, hF₁⟩ := hF.exists_frame h₁
  have hdich : ∀ {R : Subgroup (spinGroup (quadPlus 4 𝔽₃))}, R ∈ fundD4 𝔽₃ → Commutes R₁ R →
      IsFundSpin R (F₁.La (-1)) ∨
        ∃ i, IsFundSpin R i ∧ F₁.La (-1) * i = LinearEquiv.neg 𝔽₃ := by
    intro R hR hcomm
    obtain ⟨i, i', hi, hi', hdi⟩ := exists_inv_of_commutes odd_natCard_galoisField_three
      hF.single hF.long h₁ hR hcomm
    unfold IsFundSpin at hi
    have hi1 : F₁.La (-1) = i := IsFundamental.involution_unique odd_natCard_galoisField_three
      (⟨F₁, hF₁, rfl⟩ : IsFundamental (quadPlus 4 𝔽₃) _ _) hi
    rcases hdi with h | h
    · left
      rw [hi1]
      exact h ▸ hi'
    · right
      exact ⟨i', hi', by rw [hi1]; exact h⟩
  have hsame : ∀ {R R' : Subgroup (spinGroup (quadPlus 4 𝔽₃))}, R ∈ fundD4 𝔽₃ → R' ∈ fundD4 𝔽₃ →
      R ≠ R₁ → R' ≠ R₁ → R ≠ R' → IsFundSpin R (F₁.La (-1)) → IsFundSpin R' (F₁.La (-1)) →
      False := by
    intro R R' hR hR' hR1 hR'1 hRR' hi hi'
    obtain ⟨fr, hfr, hfi⟩ := hi
    obtain ⟨fr', hfr', hfi'⟩ := hi'
    have hne : ∀ {S : Subgroup (spinGroup (quadPlus 4 𝔽₃))}, S ∈ fundD4 𝔽₃ → S ≠ R₁ →
        S.map (spinAction (quadPlus 4 𝔽₃)) = F₁.La.range → False := fun hS hSR h =>
      hSR (hF.eq_of_map_eq hS h₁ (h.trans hF₁.symm))
    rcases Frame.La_range_eq_or_eq_swap h2 hfi.symm with e1 | e1
    · exact hne hR hR1 (hfr.trans e1)
    rcases Frame.La_range_eq_or_eq_swap h2 hfi'.symm with e2 | e2
    · exact hne hR' hR'1 (hfr'.trans e2)
    exact hRR' (hF.eq_of_map_eq hR hR' ((hfr.trans e1).trans (hfr'.trans e2).symm))
  have core : ∀ {Ra Rb : Subgroup (spinGroup (quadPlus 4 𝔽₃))}, Ra ∈ fundD4 𝔽₃ → Rb ∈ fundD4 𝔽₃ →
      Ra ≠ Rb → Commutes R₁ Ra →
      (∃ i, IsFundSpin Ra i ∧ F₁.La (-1) * i = LinearEquiv.neg 𝔽₃) →
      (∃ i, IsFundSpin Rb i ∧ F₁.La (-1) * i = LinearEquiv.neg 𝔽₃) →
      ∃ ua ∈ Ra, ∃ ub ∈ Rb, ∃ P ∈ fundD4 𝔽₃, ∃ x ∈ P,
        (∀ r ∈ P, r * (ua * ub) = (ua * ub) * r) ∧
        (∀ ca ∈ Ra, (∀ r ∈ Ra, ca * r = r * ca) → ca ≠ 1 → ua * ua = ca) ∧
        (∀ cb ∈ Rb, (∀ r ∈ Rb, cb * r = r * cb) → cb ≠ 1 → ub * ub = cb) ∧
        (¬ ∀ r ∈ Ra, ua * r = r * ua) ∧ (¬ ∀ r ∈ Rb, ub * r = r * ub) ∧
        ua * ub ∉ Subgroup.center (spinGroup (quadPlus 4 𝔽₃)) ∧
        (x * c * x⁻¹ * c⁻¹) ^ 4 = 1 ∧
        x * c * x⁻¹ * c⁻¹ ∉ Subgroup.center (spinGroup (quadPlus 4 𝔽₃)) := by
    rintro Ra Rb ha hb hab ca1 ⟨ia, hia, hoa⟩ ⟨ib, hib, hob⟩
    exact partner_of_opposite3 hF h₁ ha hb hab hF₁ ca1 hia hib hoa hob hc hcz hc1
  rcases hdich h₂ c12 with s2 | o2 <;> rcases hdich h₃ c13 with s3 | o3 <;>
    rcases hdich h₄ c14 with s4 | o4
  · exact (hsame h₂ h₃ h12.symm h13.symm h23 s2 s3).elim
  · exact (hsame h₂ h₃ h12.symm h13.symm h23 s2 s3).elim
  · exact (hsame h₂ h₄ h12.symm h14.symm h24 s2 s4).elim
  · exact ⟨R₃, R₄, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), h34, core h₃ h₄ h34 c13 o3 o4⟩
  · exact (hsame h₃ h₄ h13.symm h14.symm h34 s3 s4).elim
  · exact ⟨R₂, R₄, Or.inl rfl, Or.inr (Or.inr rfl), h24, core h₂ h₄ h24 c12 o2 o4⟩
  · exact ⟨R₂, R₃, Or.inl rfl, Or.inr (Or.inl rfl), h23, core h₂ h₃ h23 c12 o2 o3⟩
  · exact ⟨R₂, R₃, Or.inl rfl, Or.inr (Or.inl rfl), h23, core h₂ h₃ h23 c12 o2 o3⟩


end Partner

section Nodes

open CFSG.ClassicalInvolution.RouteD.NonClassical (d4Node d4Frame d4Node_mem)

theorem D4Facts3.eq_cNode_of_central (hF : D4Facts3) (k : Fin 4)
    {c' : spinGroup (quadPlus 4 𝔽₃)} (hc' : c' ∈ d4Node 𝔽₃ k)
    (hz : ∀ r ∈ d4Node 𝔽₃ k, c' * r = r * c') (h1 : c' ≠ 1) : c' = cNode 𝔽₃ k := by
  have hθ := hF.theta_central (d4Node_mem k) (NonClassical.map_rankOne_d4 𝔽₃ k) hc' hz h1
  have hmem : c' * (cNode 𝔽₃ k)⁻¹ ∈ d4Node 𝔽₃ k :=
    (d4Node 𝔽₃ k).mul_mem hc' ((d4Node 𝔽₃ k).inv_mem (cNode_mem k))
  have h0 : spinAction (quadPlus 4 𝔽₃) (c' * (cNode 𝔽₃ k)⁻¹) = 1 := by
    rw [map_mul, map_inv, hθ, spinAction_cNode, mul_inv_cancel]
  exact mul_inv_eq_one.mp (hF.inj (d4Node_mem k) hmem h0)

theorem D4Facts3.exists_nodes (hF : D4Facts3) :
    ∃ (R : Fin 4 → Subgroup (spinGroup (quadPlus 4 𝔽₃)))
      (c : Fin 4 → spinGroup (quadPlus 4 𝔽₃)),
      (∀ k, R k ∈ fundD4 𝔽₃) ∧ (∀ k, c k ∈ R k) ∧ (∀ k, ∀ r ∈ R k, c k * r = r * c k) ∧
      (∀ k, c k ≠ 1) ∧
      (∀ k, ∀ c' ∈ R k, (∀ r ∈ R k, c' * r = r * c') → c' ≠ 1 → c' = c k) ∧
      (∀ j k, c j * c k = c k * c j) ∧ (⨆ k, R k) = ⊤ := by
  refine ⟨fun k => d4Node 𝔽₃ k, fun k => cNode 𝔽₃ k, fun k => d4Node_mem k,
    fun k => cNode_mem k, fun k => cNode_central k,
    fun k => cNode_ne_one odd_natCard_galoisField_three k,
    fun k c' hc' hz h1 => hF.eq_cNode_of_central k hc' hz h1, fun j k => commute_cNode j k, ?_⟩
  have := hF.gen 1
  simp only [rankOneRoot_one_eq] at this
  exact this

end Nodes

end CFSG.ClassicalInvolution.Q3.Q3W.EX
