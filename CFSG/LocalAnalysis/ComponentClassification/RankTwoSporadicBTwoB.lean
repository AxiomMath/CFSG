module

public import CFSG.LocalAnalysis.ComponentClassification.BMCaseJbar
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseCo2Local
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMovedPerfect
public import CFSG.Monster.B.CTIB.CoreCensus
public import CFSG.Monster.B.CTIB.FourClasses
public import Certificates.Certificate2049
public import Certificates.Certificate2051
public import Certificates.Certificate2053
public import Certificates.Certificate2054
public import Certificates.Certificate2055
public import Certificates.Certificate2056
public import Certificates.Certificate2057
public import Certificates.Certificate2058
public import Certificates.Certificate2059
public import Certificates.Certificate2060
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.B

open Subgroup CFSG.Monster.B CFSG.Monster.B.CTIB MulOpposite

@[expose] noncomputable def cbarEquiv
    : Blueprint.NativeSporadic.B ≃* Cbar :=
  iotaEquiv.trans (MulEquiv.inv' Cbar).symm

@[expose] noncomputable def xTwoB
    : Blueprint.NativeSporadic.B :=
  iotaEquiv.symm (rs 0)

theorem cbarEquiv_xTwoB
    : cbarEquiv xTwoB = xbar⁻¹ := by
  rw [cbarEquiv, xTwoB, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, rs0_eq]
  rfl

theorem twoB_perfect_centralizer
    : ∃ P : Subgroup Blueprint.NativeSporadic.B, ⁅P, P⁆ = P ∧ P ≤ centralizer {xTwoB} ∧
      centralizer (P : Set Blueprint.NativeSporadic.B) ≤ zpowers xTwoB := by
  obtain ⟨hJ, -⟩ := CFSG.ComponentClassification.BMCase.jbar_perfect_and_inner
  have hJJ : ⁅Jbar, Jbar⁆ = Jbar :=
    commutator_self_of_commutator_eq_top ((Group.isPerfect_def).1 hJ)
  have hx : xTwoB = cbarEquiv.symm xbar⁻¹ := by
    rw [← cbarEquiv_xTwoB, MulEquiv.symm_apply_apply]
  refine ⟨Jbar.map (cbarEquiv.symm : Cbar →* Blueprint.NativeSporadic.B), ?_, ?_, ?_⟩
  · rw [← map_commutator, hJJ]
  · rintro _ ⟨j, hj, rfl⟩
    have hjx : j ∈ centralizer {xbar} := by rw [centralizer_xbar]; exact hj
    have h := mem_centralizer_singleton_iff.mp hjx
    have h' : j * xbar⁻¹ = xbar⁻¹ * j := (Commute.inv_right (show Commute j xbar from h)).eq
    rw [mem_centralizer_singleton_iff, hx]
    simp only [MonoidHom.coe_ofClass]
    rw [← map_mul, ← map_mul, h']
  · intro y hy
    have hy' : cbarEquiv y ∈ centralizer (Ebar : Set Cbar) := by
      rw [mem_centralizer_iff]
      intro e he
      have h := (mem_centralizer_iff.mp hy) (cbarEquiv.symm e)
        ⟨e, Ebar_le_Jbar he, rfl⟩
      have h2 := congrArg cbarEquiv h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    rw [CFSG.ComponentClassification.BMCase.centralizer_Ebar_eq] at hy'
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy'
    refine mem_zpowers_iff.mpr ⟨-k, ?_⟩
    apply cbarEquiv.injective
    rw [map_zpow, ← hk, cbarEquiv_xTwoB, inv_zpow', neg_neg]

end CFSG.ComponentClassification.RankTwoSporadic.B
