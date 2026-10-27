module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf
public import CFSG.Sporadic.Recognition.LyonsLocalPerfect
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SporRec

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Yardstones.Md0ec50421ce4 CFSG.Sporadic.Recognition.LyonsSims
open Subgroup Equiv

section ThreeA

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)} {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem tabLy_isPGroup_cent (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    IsPGroup 3 ↥(centralizer ({(x₁ : G)} : Set G) ⊓
      centralizer ((centralizer ({(x₁ : G)} : Set G) : Subgroup G) : Set G)) := by
  have hle : centralizer ({(x₁ : G)} : Set G) ⊓
      centralizer ((centralizer ({(x₁ : G)} : Set G) : Subgroup G) : Set G) ≤
        zpowers (x₁ : G) := by
    rintro c ⟨hcC, hcZ⟩
    have hz : (⟨c, hcC⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) ∈
        Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G)) :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 hcZ g g.2)
    rw [D.center_centralizer S] at hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    have := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_zpow] at this
    exact Subgroup.mem_zpowers_iff.2 ⟨k, this⟩
  have hp : IsPGroup 3 ↥(zpowers (x₁ : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, LyData.orderOf_x₁ S, pow_one])
  exact hp.to_le hle

theorem tabLy_three_dvd (S : LyStd ρ x₁ x₂ x₃) :
    3 ∣ Nat.card ↥(centralizer ({(x₁ : G)} : Set G)) := by
  have h := orderOf_dvd_natCard (⟨(x₁ : G), self_mem_centralizer_singleton _⟩ :
    ↥(centralizer ({(x₁ : G)} : Set G)))
  rwa [Subgroup.orderOf_mk, LyData.orderOf_x₁ S] at h


theorem tabLy_centerQuot (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nonempty (↥(centralizer ({(x₁ : G)} : Set G)) ⧸
      Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G)) ≃* NativeSporadic.McL) := by
  obtain ⟨eM⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (D.center_centralizer S)).trans eM⟩


theorem tabLy_quasisimple (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    CFSG.Open.IsQuasisimple ↥(centralizer ({(x₁ : G)} : Set G)) := by
  obtain ⟨e⟩ := tabLy_centerQuot D S
  have hperf := D.isPerfect_centralizer S
  exact ⟨hperf.commutator_eq_top,
    @MulEquiv.isSimpleGroup _ _ NativeSporadic.McL _ CFSG.Sporadic.McL.isSimpleGroup_McL e⟩

theorem tabLy_core (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    GLAPPrimeCore 3 ↥(centralizer ({(x₁ : G)} : Set G)) = ⊥ :=
  glaPPrimeCore_eq_bot_of_normal_quasisimple Nat.prime_three le_rfl
    (fun g hg l hl => Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hl) (Subgroup.inv_mem _ hg))
    (tabLy_quasisimple D S) (tabLy_three_dvd S) (tabLy_isPGroup_cent D S)

theorem tabLy_pSimple (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nonempty (PSimple 3 (centralizer ({(x₁ : G)} : Set G)) ≃* NativeSporadic.McL) := by
  obtain ⟨e⟩ := tabLy_centerQuot D S
  exact ⟨(pSimpleEquivCenterQuot _ (tabLy_core D S)).trans e⟩

theorem tabLy_threeA (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hBr : Nonempty (NativeSporadic.McL ≃* (TauCeti.CFSGIndex.sporadic .McL).Group))
    (hRk : RkAut 3 ↥(centralizer ({(x₁ : G)} : Set G))) :
    ShapeRkAt 3 (GoodSpor 3 [.McL]) (RkSpor 3 [.McL]) (x₁ : G) := by
  obtain ⟨eP⟩ := tabLy_pSimple D S
  obtain ⟨eB⟩ := hBr
  refine shapeRkAt_of_normal_quasisimple Nat.prime_three le_rfl
    (fun g hg l hl => Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hl) (Subgroup.inv_mem _ hg))
    (tabLy_quasisimple D S) (tabLy_three_dvd S) (tabLy_isPGroup_cent D S)
    (Or.inr (Or.inr ⟨.McL, List.mem_singleton_self _, ⟨eP.trans eB⟩⟩)) ?_
  intro _
  exact rkAut_of_equiv (pQuotEquivSelf _ (tabLy_core D S)).symm hRk

end ThreeA

end CFSG.HardMathSupport.Dickson.I271
