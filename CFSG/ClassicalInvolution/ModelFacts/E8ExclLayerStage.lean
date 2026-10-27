module

public import CFSG.ClassicalInvolution.ModelFacts.E8ExclD6Words
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
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld

section Stage

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

theorem exists_levi_conj_of_commutes_theta (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Subgroup M₇}
    (hX : X ∈ fundamentalSubgroups .E7 D₇) (hcomm : Commutes (stdRankOne D₇ thetaE7) X) :
    ∃ x : M₇, εm (GaloisField p f) x ∈ parabolicLevi .E7 (GaloisField p f) JE7 ∧
      ∃ γ : V7, IsRoot .E7 γ ∧ conjSub x X = stdRankOne D₇ γ := by
  obtain ⟨hodd, -⟩ := odd_and_five_le_card_galoisField hp2 hq
  obtain ⟨hsingle, hRθF, hperf⟩ := e7_fund_class hp2 hq
  obtain ⟨c, hc⟩ := exists_galoisField_unit_pow_ne_one (p := p) (f := f) hq
  obtain ⟨r₁, hr₁, hr₁2⟩ := exists_involution_fund hp2 hq hX
  obtain ⟨h, hh⟩ := hsingle _ hRθF X hX
  have hεr₁ := εm_involution_of_mem_fund hp2 hq (h := h) (by rw [← hh]; exact hr₁) hr₁2
  set y := εm (GaloisField p f) r₁ with hy
  have hr1sq : r₁ * r₁ = 1 := by rw [← sq]; exact hr₁2 ▸ pow_orderOf_eq_one r₁
  have hy2 : y * y = 1 := by rw [hy, ← map_mul, hr1sq, map_one]
  have hyT : y * rootDiagUnit .E7 (thetaDiag thetaE7 c) =
      rootDiagUnit .E7 (thetaDiag thetaE7 c) * y := by
    have hdc : rootDiagUnit .E7 (thetaDiag thetaE7 c) =
        rootSL2 .E7 (GaloisField p f) thetaE7 (HSL c) := (rootTorusSL2_thetaE7 c).symm
    have hmem : rootDiagUnit .E7 (thetaDiag thetaE7 c) ∈
        (stdRankOne D₇ thetaE7).map (εm (GaloisField p f)) := by
      rw [map_stdRankOne_εm isRoot_thetaE7]
      exact ⟨HSL c, hdc.symm⟩
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hmem
    rw [← hxe, hy, ← map_mul, ← map_mul, (hcomm x hx r₁ hr₁).symm]
  have hyLevi : y ∈ parabolicLevi .E7 (GaloisField p f) JE7 :=
    toralCentralizer_thetaE7_le_levi hc (mem_toralCentralizer.2 ⟨εm_mem r₁, by
      rw [mul_inv_eq_iff_eq_mul]
      exact hyT.symm⟩)
  obtain ⟨δ, hδ, u, huG, hu, hucomm⟩ := exists_rational_levi_conj hodd
    (fun j hj => iform_thetaE7_single_of_mem hj) (fun σ hσ => abs_iform_thetaE7_le σ hσ)
    (fun σ hσ h0 => mem_parabolicRoots_E7 (mem_rootFinset.1 hσ) h0)
    (εm_mem r₁) (εm_mem h) hy2 (baseChangeGL_mem_parabolicLevi _ hyLevi) hεr₁.symm
  obtain ⟨x, hx⟩ := εm_surjective huG
  have huLevi : u ∈ parabolicLevi .E7 (GaloisField p f) JE7 :=
    toralCentralizer_thetaE7_le_levi hc (mem_toralCentralizer.2 ⟨huG, by
      rw [mul_inv_eq_iff_eq_mul]
      exact (hucomm _ (fun j hj => by simp [thetaDiag, iform_thetaE7_single_of_mem hj])).symm⟩)
  refine ⟨x, hx ▸ huLevi, ?_⟩
  have hconj : (u * εm (GaloisField p f) h) * rootTorusSL2 .E7 (GaloisField p f) thetaE7 (-1) *
      (u * εm (GaloisField p f) h)⁻¹ =
      rootDiagUnit .E7 (thetaDiag δ (-1 : (GaloisField p f)ˣ)) := by
    rw [rootTorusSL2_thetaE7]
    calc (u * εm (GaloisField p f) h) *
          rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) *
          (u * εm (GaloisField p f) h)⁻¹ =
        u * (εm (GaloisField p f) h *
          rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) *
          (εm (GaloisField p f) h)⁻¹) * u⁻¹ := by group
      _ = u * y * u⁻¹ := by rw [← hεr₁]
      _ = _ := hu
  obtain ⟨γ, hγ, hLγ, -, -⟩ := exists_rootRankOneGroup_of_conj_toral hp2 hq
    (isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inl rfl)) isRoot_thetaE7)
    (mul_mem huG (εm_mem h)) (fun i => thetaDiag_neg_one_sign_E7 δ i) hconj
  have hγr : IsRoot .E7 γ := hγ.1
  refine ⟨γ, hγr, ?_⟩
  have hγF := std_mem_fund hq hγr
  rw [hh, ← conjSub_mul]
  apply eq_of_map_εm_eq (by rw [conjSub_commutator, hperf _ hRθF]) (hperf _ hγF)
  rw [map_conjSub, map_mul, hx, map_stdRankOne_εm isRoot_thetaE7, map_stdRankOne_εm hγr]
  exact hLγ

theorem exists_mem_HJ_conj_of_commutes_theta (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Subgroup M₇}
    (hX : X ∈ fundamentalSubgroups .E7 D₇) (hcomm : Commutes (stdRankOne D₇ thetaE7) X) :
    ∃ h ∈ HJ p f, X = conjSub h (rankOne (e7Datum (GaloisField p f)).rootGroup (e7Idx 6)) := by
  obtain ⟨x, hxL, γ, hγ, hxX⟩ := exists_levi_conj_of_commutes_theta hp2 hq hX hcomm
  obtain ⟨h₀, hh₀, hh₀γ⟩ := exists_mem_HJ_conj hp2 hq hxL
  have hxθ : conjSub x (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 := by
    rw [hh₀γ _ isRoot_thetaE7]
    exact conjSub_eq_of_mem_of_commutes hh₀ (commutes_HJ_theta hp2 hq)
  have hcγ : Commutes (stdRankOne D₇ thetaE7) (stdRankOne D₇ γ) := by
    have := hcomm.conjSub x
    rwa [hxθ, hxX] at this
  have h0 : iform thetaE7 γ = 0 := iform_eq_zero_of_commutes hp2 hq isRoot_thetaE7 hγ hcγ
  have hxinv : εm (GaloisField p f) x⁻¹ ∈ parabolicLevi .E7 (GaloisField p f) JE7 := by
    rw [map_inv]
    exact inv_mem hxL
  obtain ⟨h₁, hh₁, hh₁γ⟩ := exists_mem_HJ_conj hp2 hq hxinv
  obtain ⟨k, hk, hkγ⟩ := exists_mem_HJ_conj_rankOne (p := p) (f := f) hγ h0
  refine ⟨h₁ * k⁻¹, mul_mem hh₁ (inv_mem hk), ?_⟩
  have hX' : X = conjSub x⁻¹ (stdRankOne D₇ γ) := by
    rw [← hxX, conjSub_inv_conjSub]
  have hRγ : stdRankOne D₇ γ =
      conjSub k⁻¹ (rankOne (e7Datum (GaloisField p f)).rootGroup (e7Idx 6)) := by
    rw [← hkγ, conjSub_inv_conjSub]
  rw [hX', hh₁γ γ hγ, hRγ, ← conjSub_mul]

end Stage

end CFSG.ClassicalInvolution.ModelFacts.E7Model
