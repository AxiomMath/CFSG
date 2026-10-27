module

public import CFSG.ClassicalInvolution.SmallCases.NDBE2S
public import CFSG.ClassicalInvolution.SmallCases.NDBE3SFrame
public import CFSG.ClassicalInvolution.SmallCases.NDBE2Lift
import CFSG.ClassicalInvolution.SmallCases.NDB5Sec
import CFSG.ClassicalInvolution.SmallCases.NDBC7
import CFSG.ClassicalInvolution.Asc77.WP3FrameLieB
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
import CFSG.ClassicalInvolution.AschTight.S1911C8c
import CFSG.ClassicalInvolution.AschTight.S1911Case2a
import CFSG.ClassicalInvolution.AschTight.S1911E2c
import CFSG.ClassicalInvolution.AschTight.S1911FusA
import CFSG.ClassicalInvolution.AschTight.Sec19Targets3
import CFSG.ClassicalInvolution.AschTight.Thm6Tight3
import CFSG.ClassicalInvolution.SmallCases.NDB5Layer
import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer
import CFSG.Timmesfeld.ARS.CaseEFrame
import CFSG.Timmesfeld.ARS.CaseMLevi
import CFSG.Timmesfeld.ARS.Sec12Center
import CFSG.Timmesfeld.ARS.Sec13Closed
import CFSG.Timmesfeld.ARS.Sec13Maximal
import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

section Lift

structure ExoticLiftS {K : Subgroup G} {z : G} (C : ExoticCtxS p f K z) where
  R₁ : Subgroup (compModel C.D C.i₁).K
  hR₁ : R₁ ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D
  τ₁ : (compModel C.D C.i₁).K
  k : (compModel C.D C.i₁).K
  uR₁ : IsUniqueInvolution R₁ τ₁
  rel : ExoticModel.FrameRel τ₁ k
  nc₁ : ∃ r ∈ conjSub k R₁, τ₁ * r ≠ r * τ₁
  nc₂ : ∃ r ∈ R₁, k * τ₁ * k⁻¹ * r ≠ r * (k * τ₁ * k⁻¹)
  nc₃ : ∃ r ∈ R₁, τ₁ * (k * τ₁ * k⁻¹) * r ≠ r * (τ₁ * (k * τ₁ * k⁻¹))
  alpha : ∀ (H : Type) [Group H] [Finite H] (ψ : (compModel C.D C.i₁).K →* H),
    ψ.ker ≤ Subgroup.center (compModel C.D C.i₁).K →
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ τ₁, Subgroup.le_normalizer ⟨τ₁, rfl⟩⟩,
      toInducedAutOn ψ.range ⟨ψ (k * τ₁ * k⁻¹), Subgroup.le_normalizer ⟨_, rfl⟩⟩} :
        Set ↥(inducedAutOn ψ.range))) = ⊥
  gen : Subgroup.centralizer ({τ₁} : Set (compModel C.D C.i₁).K) ⊔
      Subgroup.centralizer ({k * τ₁ * k⁻¹} : Set (compModel C.D C.i₁).K) ⊔
        Subgroup.centralizer ({τ₁ * (k * τ₁ * k⁻¹)} : Set (compModel C.D C.i₁).K) = ⊤
  J : Subgroup G
  K' : Subgroup G
  K'' : Subgroup G
  t : G
  z' : G
  hJ : J ∈ tqMembers (𝒞 K) z
  hK' : K' ∈ tqMembers (𝒞 K) z
  hK'' : K'' ∈ tqMembers (𝒞 K) z
  hJt : IsClassicalMember p f J t
  hK'z' : IsClassicalMember p f K' z'
  hK''tz' : IsClassicalMember p f K'' (t * z')
  ht : t ∈ Subgroup.centralizer ({z} : Set G)
  hz' : z' ∈ Subgroup.centralizer ({z} : Set G)
  hJimg : modOdd z (exactCore z J) = R₁.map (C.psi C.i₁)
  hK'img : modOdd z (exactCore z K') = (conjSub k R₁).map (C.psi C.i₁)
  htbar : oddQuotMk z ⟨t, ht⟩ = C.psi C.i₁ τ₁
  hz'bar : oddQuotMk z ⟨z', hz'⟩ = C.psi C.i₁ (k * τ₁ * k⁻¹)
  htz' : t * z' = z' * t

end Lift

theorem ExoticCtxS.exists_lift {K : Subgroup G} {z : G} (C : ExoticCtxS p f K z) :
    Nonempty (ExoticLiftS C) := by
  have hp2 : p ≠ 2 := C.hS.odd
  have hΩ := C.X.hΩ
  have hinj := C.psi_injective
  obtain ⟨R₀, hR₀, N₀, hN₀, hN₀img⟩ : ∃ R ∈ fundamentalSubgroups (C.D.tag C.i₁)
      (compModel C.D C.i₁).D, ∃ N ∈ tqMembers (𝒞 K) z,
        modOdd z (exactCore z N) = R.map (C.psi C.i₁) := Cover.exists_member_of_meets C.X C.i₁
  obtain ⟨w₀, hw₀⟩ := hΩ.classical N₀ hN₀.1
  have hw₀C := C.X.involution_mem_centralizer hN₀ hw₀
  have hU₀ := C.X.isUniqueInvolution_modOdd hN₀ hw₀
  have hw₀m : oddQuotMk z ⟨w₀, hw₀C⟩ ∈ R₀.map (C.psi C.i₁) := hN₀img ▸ hU₀.mem
  obtain ⟨x₀, hx₀R, hx₀⟩ := hw₀m
  have hx₀U : IsUniqueInvolution R₀ x₀ := by
    refine ⟨hx₀R, fun h => hU₀.ne_one (by rw [← hx₀, h, map_one]),
      hinj (by rw [map_mul, hx₀, hU₀.sq, map_one]), fun y hy hy2 => ?_⟩
    have hmem : C.psi C.i₁ y ∈ modOdd z (exactCore z N₀) := by
      rw [hN₀img]
      exact ⟨y, hy, rfl⟩
    rcases hU₀.unique _ hmem (by rw [← map_mul, hy2, map_one]) with h | h
    · exact Or.inl (hinj (h.trans (map_one _).symm))
    · exact Or.inr (hinj (h.trans hx₀.symm))
  obtain ⟨k, hk, hnc₁, hnc₂, hnc₃, hα, hgen⟩ :=
    ExoticModel.exists_frame_spin_full hp2 C.five C.tag₁ (C.D.admissible C.i₁) hR₀ hx₀U
  obtain ⟨y₂, hy₂, hy₂k⟩ : ∃ (y : G) (hy : y ∈ exactLayer (𝒞 K) z),
      oddQuotMk z ⟨y, exactLayer_le_centralizer (𝒞 K) z hy⟩ = C.psi C.i₁ k :=
    C.X.exists_lift_psi C.i₁ k
  obtain ⟨y₃, hy₃, hy₃k⟩ : ∃ (y : G) (hy : y ∈ exactLayer (𝒞 K) z),
      oddQuotMk z ⟨y, exactLayer_le_centralizer (𝒞 K) z hy⟩ = C.psi C.i₁ (k * k) :=
    C.X.exists_lift_psi C.i₁ (k * k)
  have hy₂C := exactLayer_le_centralizer (𝒞 K) z hy₂
  have hy₃C := exactLayer_le_centralizer (𝒞 K) z hy₃
  have hw₂C : y₂ * w₀ * y₂⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    mul_mem (mul_mem hy₂C hw₀C) (inv_mem hy₂C)
  have hw₃C : y₃ * w₀ * y₃⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    mul_mem (mul_mem hy₃C hw₀C) (inv_mem hy₃C)
  have hN₂ := conjSub_mem_tqMembers hΩ.conjInvariant hy₂C hN₀
  have hN₃ := conjSub_mem_tqMembers hΩ.conjInvariant hy₃C hN₀
  have hw₂ : IsClassicalMember p f (conjSub y₂ N₀) (y₂ * w₀ * y₂⁻¹) := hw₀.conj y₂
  have hw₃ : IsClassicalMember p f (conjSub y₃ N₀) (y₃ * w₀ * y₃⁻¹) := hw₀.conj y₃
  have hw₂bar : oddQuotMk z ⟨y₂ * w₀ * y₂⁻¹, hw₂C⟩ = C.psi C.i₁ (k * x₀ * k⁻¹) := by
    rw [Exotic.oddQuotMk_conj' hy₂C hw₀C, hy₂k, ← hx₀, ← map_inv, ← map_mul, ← map_mul]
  have hw₃bar : oddQuotMk z ⟨y₃ * w₀ * y₃⁻¹, hw₃C⟩ = C.psi C.i₁ (x₀ * (k * x₀ * k⁻¹)) := by
    rw [Exotic.oddQuotMk_conj' hy₃C hw₀C, hy₃k, ← hx₀, ← map_inv, ← map_mul, ← map_mul,
      hk.sq_conj]
  have hw₀sq : w₀ * w₀ = 1 := (isCentralInvolution_of_isClassicalMember hw₀).sq
  have hw₂sq : y₂ * w₀ * y₂⁻¹ * (y₂ * w₀ * y₂⁻¹) = 1 :=
    (isCentralInvolution_of_isClassicalMember hw₂).sq
  have hw₃sq : y₃ * w₀ * y₃⁻¹ * (y₃ * w₀ * y₃⁻¹) = 1 :=
    (isCentralInvolution_of_isClassicalMember hw₃).sq
  have hcomm : oddQuotMk z ⟨w₀, hw₀C⟩ * oddQuotMk z ⟨y₂ * w₀ * y₂⁻¹, hw₂C⟩ =
      oddQuotMk z ⟨y₂ * w₀ * y₂⁻¹, hw₂C⟩ * oddQuotMk z ⟨w₀, hw₀C⟩ := by
    rw [← hx₀, hw₂bar, ← map_mul, ← map_mul, hk.comm]
  obtain ⟨o₁, ho₁, o₂, ho₂, hc⟩ := exists_conj_commuting z hw₀C hw₂C hw₀sq hw₂sq hcomm
  have ho₁C : o₁ ∈ Subgroup.centralizer ({z} : Set G) := oddCoreIn_le _ ho₁
  have ho₂C : o₂ ∈ Subgroup.centralizer ({z} : Set G) := oddCoreIn_le _ ho₂
  have htC : o₁ * w₀ * o₁⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    mul_mem (mul_mem ho₁C hw₀C) (inv_mem ho₁C)
  have hz'C : o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    mul_mem (mul_mem ho₂C hw₂C) (inv_mem ho₂C)
  have hJ := conjSub_mem_tqMembers hΩ.conjInvariant ho₁C hN₀
  have hK' := conjSub_mem_tqMembers hΩ.conjInvariant ho₂C hN₂
  have hJt : IsClassicalMember p f (conjSub o₁ N₀) (o₁ * w₀ * o₁⁻¹) := hw₀.conj o₁
  have hK'z' : IsClassicalMember p f (conjSub o₂ (conjSub y₂ N₀))
      (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹) := hw₂.conj o₂
  have htbar : oddQuotMk z ⟨o₁ * w₀ * o₁⁻¹, htC⟩ = C.psi C.i₁ x₀ :=
    (Exotic.oddQuotMk_conj ho₁ ho₁C hw₀C htC).trans hx₀.symm
  have hz'bar : oddQuotMk z ⟨o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹, hz'C⟩ = C.psi C.i₁ (k * x₀ * k⁻¹) :=
    (Exotic.oddQuotMk_conj ho₂ ho₂C hw₂C hz'C).trans hw₂bar
  have hK'img : modOdd z (exactCore z (conjSub o₂ (conjSub y₂ N₀))) =
      (conjSub k R₀).map (C.psi C.i₁) := by
    rw [Exotic.modOdd_exactCore_conj (conjSub y₂ N₀) ho₂ ho₂C,
      show exactCore z (conjSub y₂ N₀) = conjSub y₂ (exactCore z N₀) from
        triangleResidual_conjSub N₀ hy₂C, S.modOdd_conjSub hy₂C, hy₂k, hN₀img, S.map_conjSub]
  have htY : o₁ * w₀ * o₁⁻¹ ∈ exactLayer (𝒞 K) z :=
    exactCore_le_exactLayer hJ (C.X.involution_mem_exactCore hJ hJt)
  have hz'Y : o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹ ∈ exactLayer (𝒞 K) z :=
    exactCore_le_exactLayer hK' (C.X.involution_mem_exactCore hK' hK'z')
  have hw₃Y : y₃ * w₀ * y₃⁻¹ ∈ exactLayer (𝒞 K) z :=
    exactCore_le_exactLayer hN₃ (C.X.involution_mem_exactCore hN₃ hw₃)
  have htz'Y := mul_mem htY hz'Y
  have htsq : o₁ * w₀ * o₁⁻¹ * (o₁ * w₀ * o₁⁻¹) = 1 :=
    (isCentralInvolution_of_isClassicalMember hJt).sq
  have hz'sq : o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹ * (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹) = 1 :=
    (isCentralInvolution_of_isClassicalMember hK'z').sq
  have htz'sq : o₁ * w₀ * o₁⁻¹ * (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹) *
      (o₁ * w₀ * o₁⁻¹ * (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹)) = 1 := by
    rw [show o₁ * w₀ * o₁⁻¹ * (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹) *
        (o₁ * w₀ * o₁⁻¹ * (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹)) =
        o₁ * w₀ * o₁⁻¹ * ((o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹) * (o₁ * w₀ * o₁⁻¹)) *
          (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹) by group, ← hc]
    rw [show o₁ * w₀ * o₁⁻¹ * (o₁ * w₀ * o₁⁻¹ * (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹)) *
        (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹) =
        (o₁ * w₀ * o₁⁻¹ * (o₁ * w₀ * o₁⁻¹)) *
          ((o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹) * (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹)) by group,
      htsq, hz'sq, one_mul]
  have hsame : oddQuotMk z ⟨y₃ * w₀ * y₃⁻¹, exactLayer_le_centralizer (𝒞 K) z hw₃Y⟩ =
      oddQuotMk z ⟨o₁ * w₀ * o₁⁻¹ * (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹),
        exactLayer_le_centralizer (𝒞 K) z htz'Y⟩ := by
    have e : (⟨o₁ * w₀ * o₁⁻¹ * (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹),
        exactLayer_le_centralizer (𝒞 K) z htz'Y⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨o₁ * w₀ * o₁⁻¹, htC⟩ * ⟨o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹, hz'C⟩ := rfl
    rw [e, map_mul, htbar, hz'bar, ← map_mul]
    exact hw₃bar
  obtain ⟨o, ho, hwo⟩ := C.X.exists_conj_of_oddQuotMk_eq hw₃Y htz'Y hw₃sq htz'sq hsame
  have hoC : o ∈ Subgroup.centralizer ({z} : Set G) :=
    exactLayer_le_centralizer (𝒞 K) z (oddCoreIn_le _ ho)
  have hK'' := conjSub_mem_tqMembers hΩ.conjInvariant (inv_mem hoC) hN₃
  have hK''c : IsClassicalMember p f (conjSub o⁻¹ (conjSub y₃ N₀))
      (o₁ * w₀ * o₁⁻¹ * (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹)) := by
    have h := hw₃.conj o⁻¹
    rwa [hwo, show o⁻¹ * (o * (o₁ * w₀ * o₁⁻¹ * (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹)) * o⁻¹) * o⁻¹⁻¹ =
      o₁ * w₀ * o₁⁻¹ * (o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹) by group] at h
  exact ⟨⟨R₀, hR₀, x₀, k, hx₀U, hk, hnc₁, hnc₂, hnc₃, hα, hgen, conjSub o₁ N₀,
    conjSub o₂ (conjSub y₂ N₀), conjSub o⁻¹ (conjSub y₃ N₀), o₁ * w₀ * o₁⁻¹,
    o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹, hJ, hK', hK'', hJt, hK'z', hK''c, htC, hz'C,
    (Exotic.modOdd_exactCore_conj N₀ ho₁ ho₁C).trans hN₀img, hK'img, htbar, hz'bar, hc⟩⟩

end CFSG.ClassicalInvolution.NDB
