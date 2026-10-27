module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
import CFSG.LocalAnalysis.GLTheoremB.Prop95Ii
import CFSG.LocalAnalysis.GLTheoremB.Prop95Setup
import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar
import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Lift

variable {G : Type*} [Group G] [Finite G]

theorem barX_pCoreOf_centralizer_normal {p : ℕ} (hp : p.Prime) {M : Subgroup G} {d : G}
    (hdM : d ∈ M) (hdp : d ^ p = 1) (hHM : pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) ≤ M) :
    ∀ c ∈ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M)),
      ∀ y ∈ barX p M (pCoreOf 2 (Subgroup.centralizer ({d} : Set G))),
        c * y * c⁻¹ ∈ barX p M (pCoreOf 2 (Subgroup.centralizer ({d} : Set G))) := by
  intro c hc y hy
  have hdT : IsPGroup p (Subgroup.zpowers d) := isPGroup_zpowers_of_pow_eq_one' hdp
  have hcb : c ∈ barX p M (M ⊓ Subgroup.centralizer ({d} : Set G)) := by
    rw [barX_inf_centralizer hp hdM le_rfl (Subgroup.le_normalizer hdM) hdT, barX_self]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, hc⟩
  obtain ⟨x, hx, rfl⟩ := hcb
  have hxC : (x : G) ∈ Subgroup.centralizer ({d} : Set G) :=
    (Subgroup.mem_inf.1 ((Subgroup.mem_subgroupOf).1 hx)).2
  obtain ⟨w, hw, rfl⟩ := hy
  have hwH : (w : G) ∈ pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) :=
    (Subgroup.mem_subgroupOf).1 hw
  refine ⟨x * w * x⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  refine (Subgroup.mem_subgroupOf).2 ?_
  have hnorm := Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hxC) (w : G)
  exact hnorm.1 hwH

end Lift

section Main

theorem isKGroup_catalog_of_open {X : Type} [Group X] [Finite X]
    (h : CFSG.Open.IsKGroup X) : CFSG.IsKGroup X :=
  KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
    CFSG.Assembly.inCatalog_containsAbelianSimple h

theorem prop95iii_of_two : Prop95iii := by
  have h := input18Two_holds
  intro G _ _ m p hS M D hD L hL
  have hp : p.Prime := prime_of_standing hS
  have hp2 : p ≠ 2 := ne_two_of_standing hS
  have hpF : Fact p.Prime := ⟨hp⟩
  have hMtop : M ≠ ⊤ := isTwoLocal_ne_top hS hD.twoLocal
  have hXK : CFSG.IsKGroup (↥M ⧸ GLAPPrimeCore p ↥M) :=
    isKGroup_catalog_of_open (isKGroup_quotient' (isKGroup_of_isKProper hS.kProper hMtop) _)
  have hcore : GLAPPrimeCore p (↥M ⧸ GLAPPrimeCore p ↥M) = ⊥ :=
    glaPPrimeCore_quotient_eq_bot hp
  have hLbar : GLAPComponent p ⊤ (barX p M L) :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_glaPComponent_of_isComponentOf hcore
      hL.2.2.1
  have key : ∀ d ∈ D, d ≠ 1 → barX p M (pCoreOf 2 (Subgroup.centralizer ({d} : Set G))) ≤
      Subgroup.normalizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    intro d hd hd1
    have hdM : d ∈ M := hD.le hd
    have hdp : d ^ p = 1 := hD.plane.1.2 d hd
    have hHM := hD.clause_a d hd hd1
    have hdbp : (QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨d, hdM⟩ : ↥M)) ^ p = 1 := by
      rw [← map_pow]
      have h1 : (⟨d, hdM⟩ : ↥M) ^ p = 1 := Subtype.ext (by simpa using hdp)
      rw [h1, map_one]
    have hHc : barX p M (pCoreOf 2 (Subgroup.centralizer ({d} : Set G))) ≤
        Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
      rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hwc : (w : G) ∈ Subgroup.centralizer ({d} : Set G) :=
        CFSG.LieType.BorelTits.pCoreOf_le 2 _ ((Subgroup.mem_subgroupOf).1 hw)
      have h1 : (w : G) * d = d * w := Subgroup.mem_centralizer_singleton_iff.1 hwc
      have h2 : w * (⟨d, hdM⟩ : ↥M) = ⟨d, hdM⟩ * w := Subtype.ext h1
      rw [← map_mul, ← map_mul, h2]
    have hHP : IsPGroup 2 (barX p M (pCoreOf 2 (Subgroup.centralizer ({d} : Set G)))) :=
      isPGroup_barX (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hHM
    exact h (↥M ⧸ GLAPPrimeCore p ↥M) hXK p hp hp2 hcore _ hdbp _ hHc
      (barX_pCoreOf_centralizer_normal hp hdM hdp hHM) hHP _ hLbar
  refine (barX_mono p (gammaD_le_sigmaStar D)).trans ?_
  refine (barX_le_iff (sigmaStar_le hD)).2 ?_
  refine iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => ?_
  exact (barX_le_iff (hD.clause_a d hd hd1)).1 (key d hd hd1)

end Main

theorem prop95iii_holds : Prop95iii := prop95iii_of_two

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
