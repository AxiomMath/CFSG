module

public import CFSG.ClassicalInvolution.RouteD.TWU2Conj
public import CFSG.ClassicalInvolution.RouteD.TWT9Spin
public import CFSG.ClassicalInvolution.RouteD.TWT9Cls
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWU

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.RouteD.TWE.B6
open CliffordAlgebra
open CFSG.ClassicalInvolution.RouteD.TWE.B4 (mem_negSpace_iff' mem_posSpace_iff')
open CFSG.ClassicalInvolution.RouteD.TWT8 (isCompl_pos_neg)
open CFSG.ClassicalInvolution.Generic (Commutes fundamentalSubgroups)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

set_option linter.unusedSectionVars false

section Generic

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}


theorem eq_of_scalar_involutions (hodd : Odd (Nat.card K)) {L L' : Subgroup (V ≃ₗ[K] V)}
    {i i' : V ≃ₗ[K] V} (hL : IsFundamental Q L i) (hL' : IsFundamental Q L' i')
    (hdim : Module.finrank K V ≠ 8) (hsc : i⁻¹ * i' ∈ scalars K V) : i' = i := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  rw [mem_scalars] at hsc
  obtain ⟨c, hc⟩ := hsc
  have hi2 : i * i = 1 := hL.mul_self
  have hi'2 : i' * i' = 1 := hL'.mul_self
  have hv : ∀ v, i' v = c • i v := by
    intro v
    calc i' v = (i * (i⁻¹ * i')) v := by rw [mul_inv_cancel_left]
      _ = i ((i⁻¹ * i') v) := rfl
      _ = c • i v := by rw [hc v, map_smul]
  have hne : ∃ v : V, v ≠ 0 := by
    obtain ⟨F, -, -⟩ := hL
    exact ⟨F.P.e, F.P.e_ne_zero⟩
  have hc2 : c * c = 1 := by
    obtain ⟨v, hv0⟩ := hne
    have e1 : i' (i' v) = v := LinearEquiv.congr_fun hi'2 v
    have e2 : i (i v) = v := LinearEquiv.congr_fun hi2 v
    have h1 : (c * c) • v = v := by
      calc (c * c) • v = c • c • i (i v) := by rw [e2, smul_smul]
        _ = c • i' (i v) := by rw [hv (i v)]
        _ = i' (c • i v) := (map_smul i' c (i v)).symm
        _ = i' (i' v) := by rw [hv v]
        _ = v := e1
    have h3 : (c * c - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hv0)
  rcases mul_self_eq_one_iff.mp hc2 with rfl | rfl
  · exact LinearEquiv.ext fun v => by rw [hv, one_smul]
  · exfalso
    have hneg : negSpace i' = posSpace i := by
      ext v
      rw [mem_negSpace_iff', mem_posSpace_iff', hv, neg_one_smul, neg_inj]
    have h4 : Module.finrank K (negSpace i') = 4 := finrank_negSpace hodd hL'
    have h4' : Module.finrank K (negSpace i) = 4 := finrank_negSpace hodd hL
    have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_pos_neg h2 hi2)
    rw [← hneg, h4, h4'] at hsum
    exact hdim hsum.symm

theorem polar_span_mkFrame_eq_zero {c₀ c₁ c₂ c₃ : HypPair Q} (o01 : c₀.Orth (swapPair c₁))
    (o23 : c₂.Orth (swapPair c₃)) (h02 : c₀.Orth c₂) (h03 : c₀.Orth c₃) (h12 : c₁.Orth c₂)
    (h13 : c₁.Orth c₃) :
    ∀ x ∈ (mkFrame c₀ (swapPair c₁) o01).span, ∀ y ∈ (mkFrame c₂ (swapPair c₃) o23).span,
      polar Q x y = 0 := by
  rw [frame_span_eq (mkFrame c₀ (swapPair c₁) o01), frame_span_eq (mkFrame c₂ (swapPair c₃) o23)]
  refine polar_eq_zero_of_sup (fun x hx y hy => ?_) (fun x hx y hy => ?_)
    (fun x hx y hy => ?_) (fun x hx y hy => ?_)
  · exact polar_hypPlane_of_orth h02 x hx y hy
  · rw [show (mkFrame c₂ (swapPair c₃) o23).P' = swapPair c₃ from rfl, hypPlane_swapPair] at hy
    exact polar_hypPlane_of_orth h03 x hx y hy
  · rw [show (mkFrame c₀ (swapPair c₁) o01).P' = swapPair c₁ from rfl, hypPlane_swapPair] at hx
    exact polar_hypPlane_of_orth h12 x hx y hy
  · rw [show (mkFrame c₀ (swapPair c₁) o01).P' = swapPair c₁ from rfl, hypPlane_swapPair] at hx
    rw [show (mkFrame c₂ (swapPair c₃) o23).P' = swapPair c₃ from rfl, hypPlane_swapPair] at hy
    exact polar_hypPlane_of_orth h13 x hx y hy

theorem eq_twin_of_involution (hodd : Odd (Nat.card K)) (hdim : Module.finrank K V ≠ 8) {m : ℕ}
    (F₀ : HypFrame Q m) (x : spinGroup Q) {i j : Fin m} (hij : i ≠ j)
    {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) (scalars K V))
    {R₀ R₀' RT : Subgroup (spinGroup Q)}
    (hR₀ : R₀ = (F₀.longSL2 hij true false).range.map (MulAut.conj x).toMonoidHom)
    (hR₀' : R₀' = (F₀.longSL2 hij true true).range.map (MulAut.conj x).toMonoidHom)
    (h₀ : R₀ ∈ 𝓕) (h₀' : R₀' ∈ 𝓕) (hT : RT ∈ 𝓕) (hTne : RT ≠ R₀)
    (hTinv : ∃ r r', InvOf R₀ r ∧ InvOf RT r' ∧
      r⁻¹ * r' ∈ Subgroup.center (spinGroup Q)) :
    RT = R₀' := by
  classical
  have hg := mem_orthogonalGroup_spinAction x
  set fr₀ := (F₀.toFrame hij true false).map hg with hfr₀
  have hL₀ : R₀.map (spinAction Q) = fr₀.La.range := by
    rw [hR₀]
    exact map_conj_longSL2_range F₀ hij true false x
  have hL₀' : R₀'.map (spinAction Q) = fr₀.swap.La.range := by
    rw [hR₀', map_conj_longSL2_range F₀ hij true true x, toFrame_map_true_true]
  obtain ⟨r, r', hr, hr', hrr'⟩ := hTinv
  have hf₀ : IsFundamental Q (R₀.map (spinAction Q)) (fr₀.La (-1)) := by
    rw [hL₀]
    exact IsFundamental.of_frame fr₀
  obtain ⟨iT, hiT⟩ := cq.map_mem _ hT
  have hrfix : spinAction Q r = fr₀.La (-1) := invOf_eq hodd hf₀ (cq.invOf h₀ hr)
  have hr'fix : spinAction Q r' = iT := invOf_eq hodd hiT (cq.invOf hT hr')
  have hsc : (fr₀.La (-1))⁻¹ * iT ∈ scalars K V := by
    rw [← hrfix, ← hr'fix, ← map_inv, ← map_mul]
    exact cq.center_le _ hrr'
  have hiTeq : iT = fr₀.La (-1) := eq_of_scalar_involutions hodd hf₀ hiT hdim hsc
  rw [hiTeq] at hiT
  obtain ⟨L', -, -, -, huniq⟩ := IsFundamental.exists_twin hodd hf₀
  have hswap : fr₀.swap.La.range = L' := by
    rcases huniq _ (IsFundamental.of_frame_swap fr₀) with h | h
    · exact absurd (hL₀.symm.trans h.symm) (Frame.La_range_ne_swap_La_range fr₀)
    · exact h
  rcases huniq _ hiT with h | h
  · exact absurd (cq.map_inj hT h₀ h) hTne
  · exact cq.map_inj hT h₀' (h.trans (hswap.symm.trans hL₀'.symm))

theorem eq_or_eq_negOne_mul [Invertible (2 : K)] [Nontrivial V] (hQ : Q.Nondegenerate)
    {P r : spinGroup Q} (h : spinAction Q P = spinAction Q r) :
    P = r ∨ P = spinGroup.negOne Q hQ.ne_zero * r := by
  have hk : P * r⁻¹ ∈ (spinAction Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  rcases (mem_ker_spinAction_iff Q hQ _).mp hk with h1 | h1
  · exact Or.inl (mul_inv_eq_one.mp h1)
  · exact Or.inr (mul_inv_eq_iff_eq_mul.mp h1)

end Generic

end CFSG.ClassicalInvolution.RouteD.TWU
