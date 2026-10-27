module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelFrameStep
public import CFSG.ClassicalInvolution.RouteD.TypeE8Excl
public import CFSG.ClassicalInvolution.RouteD.TypeE8Witness
public import CFSG.ClassicalInvolution.RouteD.GapsFrIso
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclOdd
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
public import CFSG.ClassicalInvolution.RouteD.GapsFrPair

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement MatrixGroups

section Adjacent

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

theorem modelAdj_std (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {δ δ' : V7} (hδ : IsRoot .E7 δ)
    (hδ' : IsRoot .E7 δ') (h : iform δ δ' = -1) :
    Gaps.ModelAdj (Subgroup.center M₇) (stdRankOne D₇ δ) (stdRankOne D₇ δ') ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (stdRankOne D₇ δ) (stdRankOne D₇ δ') := by
  obtain ⟨W, hW⟩ := linearPair_of_roots (GaloisField p f) hδ hδ' (Or.inr h)
  have h2 : (2 : GaloisField p f) ≠ 0 := two_ne_zero_galoisField f hp2
  obtain ⟨r₁, hr₁, hr₁2⟩ := exists_involution_std hp2 hq hδ
  obtain ⟨r₂, hr₂, hr₂2⟩ := exists_involution_std hp2 hq hδ'
  have hc : r₁ * r₂ = r₂ * r₁ := Gaps.standardPair_involutions_commute h2 hW hr₁ hr₂ hr₁2 hr₂2
  refine ⟨⟨ne_of_linearBlockStandardPair hW, not_commutes_of_linearBlockStandardPair hW, r₁, r₂,
    ⟨hr₁, hr₁2⟩, ⟨hr₂, hr₂2⟩, ?_, ?_⟩, W, hW⟩
  · have : ⁅r₁, r₂⁆ = 1 := by
      rw [commutatorElement_def, hc]
      group
    rw [this]
    exact Subgroup.one_mem _
  · intro x hx
    have := Gaps.conjSub_eq_of_standardPair h2 hW hr₂ hr₂2
    rw [← this]
    exact conj_mem_conjSub hx

end Adjacent

section Relations

variable {p f : ℕ} [Fact p.Prime]

theorem e7FrameRelations (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : TypeE8.E7FrameRelations p f := by
  intro g δ δ' hδ hδ'
  have hδr : IsRoot .E7 δ := mem_rootFinset.1 ((TypeE8.mem_roots_D7_iff p f δ).1 hδ)
  have hδ'r : IsRoot .E7 δ' := mem_rootFinset.1 ((TypeE8.mem_roots_D7_iff p f δ').1 hδ')
  refine ⟨conjSub_mem_fundamentalSubgroups (std_mem_fund hq hδr) g, fun h => ?_, fun h => ?_⟩
  · exact (commutes_std_of_iform_eq_zero hp2 hq hδr hδ'r h).conjSub g
  · obtain ⟨hadj, W, hW⟩ := modelAdj_std hp2 hq hδr hδ'r h
    exact ⟨Gaps.ModelAdj.map_equiv (MulAut.conj g) hadj, _,
      Gaps.linearBlockStandardPair_map_equiv (MulAut.conj g) hW⟩

end Relations

section Involutions

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

theorem rootChar_signProd (δ₁ δ₂ σ : V7) :
    rootChar (thetaDiag δ₁ (-1 : (GaloisField p f)ˣ) * thetaDiag δ₂ (-1)) σ =
      (-1 : (GaloisField p f)ˣ) ^ (iform δ₁ σ + iform δ₂ σ) := by
  rw [rootChar_mul, rootChar_thetaDiag, rootChar_thetaDiag, zpow_add]

theorem εm_mul_involutions (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {δ₁ δ₂ : V7} (h₁ : IsRoot .E7 δ₁)
    (h₂ : IsRoot .E7 δ₂) {r₁ r₂ : M₇} (hr₁ : r₁ ∈ stdRankOne D₇ δ₁) (hr₂ : r₂ ∈ stdRankOne D₇ δ₂)
    (h₁2 : orderOf r₁ = 2) (h₂2 : orderOf r₂ = 2) :
    εm (GaloisField p f) (r₁ * r₂) = rootDiagUnit .E7
      (thetaDiag δ₁ (-1 : (GaloisField p f)ˣ) * thetaDiag δ₂ (-1)) := by
  rw [map_mul, εm_involution_std hp2 hq h₁ hr₁ h₁2, εm_involution_std hp2 hq h₂ hr₂ h₂2,
    ← rootDiagUnit_mul]

theorem frameInvolutions_std (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {δ₁ δ₂ : V7} (h₁ : IsRoot .E7 δ₁)
    (h₂ : IsRoot .E7 δ₂) (horth : iform δ₁ δ₂ = 0) {r₁ r₂ : M₇} (hr₁ : r₁ ∈ stdRankOne D₇ δ₁)
    (hr₂ : r₂ ∈ stdRankOne D₇ δ₂) (h₁2 : orderOf r₁ = 2) (h₂2 : orderOf r₂ = 2) :
    r₁ ∉ Subgroup.center M₇ ∧ r₂ ∉ Subgroup.center M₇ ∧ r₁ * r₂ ∉ Subgroup.center M₇ ∧
      ∀ δ : V7, IsRoot .E7 δ → (iform δ δ₁ + iform δ δ₂) % 2 = 0 →
        stdRankOne D₇ δ ≤ Subgroup.centralizer ({r₁ * r₂} : Set M₇) := by
  have hF : ringChar (GaloisField p f) ≠ 2 := ringChar_galoisField_ne_two hp2
  obtain ⟨-, -, hperf⟩ := e7_fund_class hp2 hq
  have hεz := εm_mul_involutions hp2 hq h₁ h₂ hr₁ hr₂ h₁2 h₂2
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_, fun δ hδ hev => ?_⟩
  · have := no_central_fund hp2 hq (std_mem_fund hq h₁) hr₁ hc
    rw [this, orderOf_one] at h₁2
    omega
  · have := no_central_fund hp2 hq (std_mem_fund hq h₂) hr₂ hc
    rw [this, orderOf_one] at h₂2
    omega
  · obtain ⟨j, hodd⟩ := exists_odd_total h₁ h₂ horth
    have hσr : IsRoot .E7 (Pi.single j 1 : V7) := isRoot_single .E7 j
    have hmem : rootSL2 .E7 (GaloisField p f) (Pi.single j 1) (uSL 1) ∈
        (stdRankOne D₇ (Pi.single j 1)).map (εm (GaloisField p f)) := by
      rw [map_stdRankOne_εm hσr]
      exact ⟨uSL 1, rfl⟩
    obtain ⟨y, hy, hyε⟩ := Subgroup.mem_map.1 hmem
    have hcomm : y * (r₁ * r₂) = (r₁ * r₂) * y := Subgroup.mem_center_iff.1 hc y
    have h1 : εm (GaloisField p f) y * εm (GaloisField p f) (r₁ * r₂) =
        εm (GaloisField p f) (r₁ * r₂) * εm (GaloisField p f) y := by
      rw [← map_mul, ← map_mul, hcomm]
    rw [hεz, hyε] at h1
    have h2 := rootDiagUnit_conj_rootSL2_gen
      (thetaDiag δ₁ (-1 : (GaloisField p f)ˣ) * thetaDiag δ₂ (-1)) hσr (uSL 1)
    rw [mul_inv_eq_iff_eq_mul.2 h1.symm, rootChar_signProd, hodd.neg_one_zpow,
      diagConj2_uSL_gen] at h2
    have hinj := ((exceptional_Lang_root_rank_one_data .E7 (GaloisField p f)
      (Pi.single j 1)).2.2.2.2.2.2.2.1 hF).1
    have h3 := uSL_injective_of_field (hinj h2.symm)
    simp only [Units.val_neg, Units.val_one, mul_one] at h3
    exact Ring.neg_one_ne_one_of_char_ne_two hF h3
  · have hδF := std_mem_fund hq hδ
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    set b := thetaDiag δ₁ (-1 : (GaloisField p f)ˣ) * thetaDiag δ₂ (-1) with hb
    have hbδ : rootChar b δ = 1 := by
      rw [hb, rootChar_signProd, iform_comm δ₁, iform_comm δ₂]
      exact (Int.even_iff.2 hev).neg_one_zpow
    have hu : ∀ r ∈ stdRankOne D₇ δ, (r₁ * r₂) * r * (r₁ * r₂)⁻¹ * r⁻¹ ∈ Subgroup.center M₇ := by
      intro r hr
      apply εm_ker_le_center
      rw [MonoidHom.mem_ker]
      have hr' : εm (GaloisField p f) r ∈ rootRankOneGroup .E7 (GaloisField p f) δ := by
        rw [← map_stdRankOne_εm hδ]
        exact Subgroup.mem_map_of_mem _ hr
      obtain ⟨A, hA⟩ := hr'
      have h4 := rootDiagUnit_conj_rootSL2_gen b hδ A
      rw [hbδ] at h4
      have h5 : diagConj2 (1 : (GaloisField p f)ˣ) 1 A = A := by
        refine SL2_ext ?_ ?_ ?_ ?_ <;>
          simp [coe_diagConj2, Matrix.mul_apply, Matrix.diagonal_apply]
      rw [h5] at h4
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hεz, ← hA]
      calc rootDiagUnit .E7 b * rootSL2 .E7 (GaloisField p f) δ A * (rootDiagUnit .E7 b)⁻¹ *
            (rootSL2 .E7 (GaloisField p f) δ A)⁻¹ =
          rootSL2 .E7 (GaloisField p f) δ A * (rootSL2 .E7 (GaloisField p f) δ A)⁻¹ := by
            rw [h4]
        _ = 1 := by group
    exact (commute_of_commutator_central (stdRankOne D₇ δ) (hperf _ hδF).ge (r₁ * r₂) hu w hw).symm

end Involutions

section Involutions2

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

theorem e7FrameInvolutions_sc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ∀ (g : M₇) (δ₁ δ₂ : V7), IsRoot .E7 δ₁ → IsRoot .E7 δ₂ → iform δ₁ δ₂ = 0 →
      ∀ r₁ ∈ conjSub g (stdRankOne D₇ δ₁), ∀ r₂ ∈ conjSub g (stdRankOne D₇ δ₂), orderOf r₁ = 2 →
        orderOf r₂ = 2 → r₁ ∉ Subgroup.center M₇ ∧ r₂ ∉ Subgroup.center M₇ ∧
          r₁ * r₂ ∉ Subgroup.center M₇ ∧
          ∀ δ : V7, IsRoot .E7 δ → (iform δ δ₁ + iform δ δ₂) % 2 = 0 →
            conjSub g (stdRankOne D₇ δ) ≤ Subgroup.centralizer ({r₁ * r₂} : Set M₇) := by
  intro g δ₁ δ₂ hδ₁r hδ₂r horth r₁ hr₁ r₂ hr₂ h₁2 h₂2
  obtain ⟨a₁, ha₁, rfl⟩ := Subgroup.mem_map.1 hr₁
  obtain ⟨a₂, ha₂, rfl⟩ := Subgroup.mem_map.1 hr₂
  have ha₁2 : orderOf a₁ = 2 := by
    rw [← h₁2]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a₁).symm
  have ha₂2 : orderOf a₂ = 2 := by
    rw [← h₂2]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a₂).symm
  obtain ⟨c₁, c₂, c₃, c₄⟩ := frameInvolutions_std hp2 hq hδ₁r hδ₂r horth ha₁ ha₂ ha₁2 ha₂2
  refine ⟨?_, ?_, ?_, fun δ hδr hev => ?_⟩
  · exact fun h => c₁ ((MulEquivClass.apply_mem_center_iff (MulAut.conj g)).1 h)
  · exact fun h => c₂ ((MulEquivClass.apply_mem_center_iff (MulAut.conj g)).1 h)
  · intro h
    apply c₃
    refine (MulEquivClass.apply_mem_center_iff (MulAut.conj g)).1 ?_
    have e : (MulAut.conj g) (a₁ * a₂) = g * a₁ * g⁻¹ * (g * a₂ * g⁻¹) := by
      simp only [MulAut.conj_apply]
      group
    rw [e]
    exact h
  · intro w hw
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.1 hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 (c₄ δ hδr hev hw')
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * w' * g⁻¹ * (g * a₁ * g⁻¹ * (g * a₂ * g⁻¹)) = g * (w' * (a₁ * a₂)) * g⁻¹ := by group
      _ = g * (a₁ * a₂ * w') * g⁻¹ := by rw [this]
      _ = g * a₁ * g⁻¹ * (g * a₂ * g⁻¹) * (g * w' * g⁻¹) := by group

theorem e7FrameInvolutions (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : TypeE8.E7FrameInvolutions p f := by
  intro g δ₁ δ₂ hδ₁ hδ₂ horth r₁ hr₁ r₂ hr₂ h₁2 h₂2
  have hδ₁r : IsRoot .E7 δ₁ := mem_rootFinset.1 ((TypeE8.mem_roots_D7_iff p f δ₁).1 hδ₁)
  have hδ₂r : IsRoot .E7 δ₂ := mem_rootFinset.1 ((TypeE8.mem_roots_D7_iff p f δ₂).1 hδ₂)
  obtain ⟨c₁, c₂, c₃, c₄⟩ := e7FrameInvolutions_sc hp2 hq g δ₁ δ₂ hδ₁r hδ₂r horth r₁ hr₁ r₂ hr₂
    h₁2 h₂2
  exact ⟨c₁, c₂, c₃, fun δ hδ hev =>
    c₄ δ (mem_rootFinset.1 ((TypeE8.mem_roots_D7_iff p f δ).1 hδ)) hev⟩

end Involutions2

end CFSG.ClassicalInvolution.ModelFacts.E7Model
