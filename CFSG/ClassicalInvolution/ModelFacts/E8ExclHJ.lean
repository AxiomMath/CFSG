module

public import CFSG.ClassicalInvolution.ModelFacts.E8ExclLevi
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelFrameStep
public import CFSG.ClassicalInvolution.RouteD.TypeEModel
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

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld

section HJ

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

@[expose] noncomputable def HJ (p f : ℕ) [Fact p.Prime] : Subgroup (E7sc p f) :=
  ⨆ i : Fin 6, rankOne (e7Datum (GaloisField p f)).rootGroup (iota7 i)

theorem exists_iota7_eq : ∀ j : Fin 7, j.val ≠ 0 → ∃ m : Fin 6, iota7 m = j := by
  decide

theorem iota7_mem_JE7 (m : Fin 6) : iota7 m ∈ JE7 := by
  have : ∀ m : Fin 6, (iota7 m).val ≠ 0 := by decide
  exact this m

theorem rankOne_le_HJ (m : Fin 6) :
    rankOne (e7Datum (GaloisField p f)).rootGroup (iota7 m) ≤ HJ p f :=
  le_iSup (fun i : Fin 6 => rankOne (e7Datum (GaloisField p f)).rootGroup (iota7 i)) m

theorem rankOne_le_HJ_of_ne_zero {j : Fin 7} (hj : j.val ≠ 0) :
    rankOne (e7Datum (GaloisField p f)).rootGroup j ≤ HJ p f := by
  obtain ⟨m, rfl⟩ := exists_iota7_eq j hj
  exact rankOne_le_HJ m

theorem xUnit_mem_rootRankOne {F : Type} [Field F] (j : Fin (Tag.rank .E7)) (c : F) :
    xUnit .E7 F j c ∈ rootRankOneGroup .E7 F (Pi.single j 1) ∧
      yUnit .E7 F j c ∈ rootRankOneGroup .E7 F (Pi.single j 1) := by
  have hβ := isRoot_single .E7 j
  constructor
  · rw [← pinnedX_single _ F j c, rootRankOneGroup_eq_sup hβ]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨c, rfl⟩)
  · rw [← pinnedX_neg_single _ F j c, rootRankOneGroup_eq_sup hβ]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨c, rfl⟩)

theorem NJ_le_map_HJ : NJ (GaloisField p f) JE7 ≤ (HJ p f).map (εm (GaloisField p f)) := by
  rw [NJ, Subgroup.closure_le]
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  all_goals
    have hj0 : j.val ≠ 0 := hj
    have hstd : rootRankOneGroup .E7 (GaloisField p f) (Pi.single j 1) ≤
        (HJ p f).map (εm (GaloisField p f)) := by
      rw [← map_stdRankOne_εm (isRoot_single .E7 j)]
      exact Subgroup.map_mono (rankOne_le_HJ_of_ne_zero hj0)
  · exact hstd (xUnit_mem_rootRankOne j c).1
  · exact hstd (xUnit_mem_rootRankOne j c).2

theorem conjSub_std_of_torus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {y : M₇}
    (hy : εm (GaloisField p f) y ∈ torusGroup .E7 (GaloisField p f)) {γ : V7}
    (hγ : IsRoot .E7 γ) : conjSub y (stdRankOne D₇ γ) = stdRankOne D₇ γ := by
  have hF : ringChar (GaloisField p f) ≠ 2 := ringChar_galoisField_ne_two hp2
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  obtain ⟨-, -, hperf⟩ := e7_fund_class hp2 hq
  have hγF := std_mem_fund hq hγ
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  have hwd : εm (GaloisField p f) y * rootTorusSL2 .E7 (GaloisField p f) γ (-1) =
      rootTorusSL2 .E7 (GaloisField p f) γ (-1) * εm (GaloisField p f) y := by
    rw [hb, rootTorusSL2_eq_thetaDiag hγ, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  apply eq_of_map_εm_eq (by rw [conjSub_commutator, hperf _ hγF]) (hperf _ hγF)
  rw [map_conjSub, map_stdRankOne_εm hγ,
    map_conj_rootRankOneGroup_of_commute_gen hF hodd hγ (εm_mem y) hwd]

theorem exists_mem_HJ_conj (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {x : M₇}
    (hx : εm (GaloisField p f) x ∈ parabolicLevi .E7 (GaloisField p f) JE7) :
    ∃ h ∈ HJ p f, ∀ γ : V7, IsRoot .E7 γ →
      conjSub x (stdRankOne D₇ γ) = conjSub h (stdRankOne D₇ γ) := by
  obtain ⟨t, ht, η, hη, hxe⟩ := exists_mul_of_mem_levi (inv_mem hx)
  obtain ⟨h₀, hh₀, hεh₀⟩ := Subgroup.mem_map.1 (NJ_le_map_HJ (inv_mem hη))
  refine ⟨h₀, hh₀, fun γ hγ => ?_⟩
  have hεy : εm (GaloisField p f) (h₀⁻¹ * x) = t⁻¹ := by
    have h1 : εm (GaloisField p f) x = η⁻¹ * t⁻¹ := by
      rw [← inv_inv (εm (GaloisField p f) x), hxe, mul_inv_rev]
    rw [map_mul, map_inv, hεh₀, h1]
    group
  have hx' : x = h₀ * (h₀⁻¹ * x) := by group
  rw [hx', conjSub_mul, conjSub_std_of_torus hp2 hq (hεy ▸ inv_mem ht) hγ]

theorem commutes_HJ_theta (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    Commutes (HJ p f) (stdRankOne D₇ thetaE7) := by
  refine commutes_iSup_left.mpr fun i => ?_
  exact commutes_std_of_iform_eq_zero hp2 hq (isRoot_single .E7 (iota7 i)) isRoot_thetaE7
    (iform_single_eq_zero_of_mem_E7 (iota7_mem_JE7 i))

end HJ

end CFSG.ClassicalInvolution.ModelFacts.E7Model
