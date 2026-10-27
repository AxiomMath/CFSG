module

public import CFSG.ClassicalInvolution.SmallCases.NDBE0Stmt
public import CFSG.ClassicalInvolution.SmallCases.NDBE1
import CFSG.ClassicalInvolution.SmallCases.NDBC7
import CFSG.ClassicalInvolution.Asc77.WP3FrameLieB
import CFSG.ClassicalInvolution.RouteD.NoG2D4Model
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
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

namespace Exotic

theorem exists_exoticCtx {K : Subgroup G} {z : G} (hS : ExoticBase p f K z)
    (hnoT : ¬ HasTwin p f K z) (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z)
    {i : Fin D.card} (hi : D.tag i = .G2 ∨ D.tag i = .trialityD4) :
    Nonempty (ExoticCtx p f K z) := by
  set C₀ := Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D with hC₀
  have hQ : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := by
    rintro ⟨h, -⟩
    rcases hi with h' | h' <;> rw [h'] at h <;> exact nomatch h
  obtain ⟨i₀, hi₀, hK₀⟩ := C₀.exists_A1_of_K
  have hi₀i : i₀ ≠ i := fun h => hQ (h ▸ hi₀)
  have hcases : ∀ j, j = i₀ ∨ j = i := by
    intro j
    by_cases hji : j = i
    · exact Or.inr hji
    by_cases hj₀ : j = i₀
    · exact Or.inl hj₀
    have hjA : D.tag j = .PSL ∧ D.rank j = 2 := by
      by_contra h
      exact Cover.false_of_two_nonA1 C₀ hnoF hji h hQ
    obtain ⟨T, hT, hTK, hTz, -⟩ := Cover.A1_member_twin C₀ hnoF hQ hi₀ hK₀ hjA hj₀
    exact (hnoT ⟨T, hT, hTK, hTz⟩).elim
  exact ⟨⟨hS, hnoT, hnoF, D, Cover.card_eq_two_of hi₀i hcases, i₀, i, hi₀i, hi₀.1, hi₀.2, hi,
    hK₀⟩⟩

end Exotic

section Lift

structure ExoticLift {K : Subgroup G} {z : G} (C : ExoticCtx p f K z) where
  R₁ : Subgroup (compModel C.D C.i₁).K
  hR₁ : R₁ ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D
  τ₁ : (compModel C.D C.i₁).K
  τ₂ : (compModel C.D C.i₁).K
  mem₁ : τ₁ ∈ R₁
  cen₁ : ∀ r ∈ R₁, τ₁ * r = r * τ₁
  sq₁ : τ₁ * τ₁ = 1
  sq₂ : τ₂ * τ₂ = 1
  ne₁ : τ₁ ≠ 1
  ne₂ : τ₂ ≠ 1
  ne₁₂ : τ₁ ≠ τ₂
  comm : τ₁ * τ₂ = τ₂ * τ₁
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
  htbar : oddQuotMk z ⟨t, ht⟩ = C.psi C.i₁ τ₁
  hz'bar : oddQuotMk z ⟨z', hz'⟩ = C.psi C.i₁ τ₂
  htz' : t * z' = z' * t

end Lift

section Construct

omit [Finite G] [IsSimpleGroup G] in
theorem Exotic.oddQuotMk_conj {z o w : G}
    (ho : o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)))
    (hoC : o ∈ Subgroup.centralizer ({z} : Set G)) (hwC : w ∈ Subgroup.centralizer ({z} : Set G))
    (hC : o * w * o⁻¹ ∈ Subgroup.centralizer ({z} : Set G)) :
    oddQuotMk z ⟨o * w * o⁻¹, hC⟩ = oddQuotMk z ⟨w, hwC⟩ := by
  have h1 : oddQuotMk z ⟨o, hoC⟩ = 1 := oddQuotMk_eq_one_of_mem_oddCoreIn ho hoC
  have e : (⟨o * w * o⁻¹, hC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
      ⟨o, hoC⟩ * ⟨w, hwC⟩ * ⟨o, hoC⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, h1]
  simp

omit [Finite G] [IsSimpleGroup G] in
theorem Exotic.oddQuotMk_conj' {z y w : G} (hyC : y ∈ Subgroup.centralizer ({z} : Set G))
    (hwC : w ∈ Subgroup.centralizer ({z} : Set G))
    (hC : y * w * y⁻¹ ∈ Subgroup.centralizer ({z} : Set G)) :
    oddQuotMk z ⟨y * w * y⁻¹, hC⟩ =
      oddQuotMk z ⟨y, hyC⟩ * oddQuotMk z ⟨w, hwC⟩ * (oddQuotMk z ⟨y, hyC⟩)⁻¹ := by
  have e : (⟨y * w * y⁻¹, hC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
      ⟨y, hyC⟩ * ⟨w, hwC⟩ * ⟨y, hyC⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]

omit [IsSimpleGroup G] in
theorem Exotic.modOdd_exactCore_conj {z o : G} (N : Subgroup G)
    (ho : o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)))
    (hoC : o ∈ Subgroup.centralizer ({z} : Set G)) :
    modOdd z (exactCore z (conjSub o N)) = modOdd z (exactCore z N) := by
  have e : exactCore z (conjSub o N) = conjSub o (exactCore z N) := triangleResidual_conjSub N hoC
  rw [e]
  exact modOdd_conjSub_of_mem_oddCoreIn ho

theorem ExoticCtx.exists_lift {K : Subgroup G} {z : G} (C : ExoticCtx p f K z) :
    Nonempty (ExoticLift C) := by
  have hp2 : p ≠ 2 := C.hS.odd
  have hΩ := C.X.hΩ
  have hinj : Function.Injective (C.psi C.i₁) :=
    RouteD.G2D4.injective_of_ker_le_center hp2 C.tag₁ (C.D.rank C.i₁)
      (C.D.admissible C.i₁).2.1 (C.psi C.i₁) (C.X.psi_ker C.i₁)
  obtain ⟨R₀, hR₀, N₀, hN₀, hN₀img⟩ : ∃ R ∈ fundamentalSubgroups (C.D.tag C.i₁)
      (compModel C.D C.i₁).D, ∃ N ∈ tqMembers (𝒞 K) z,
        modOdd z (exactCore z N) = R.map (C.psi C.i₁) := Cover.exists_member_of_meets C.X C.i₁
  obtain ⟨w₀, hw₀⟩ := hΩ.classical N₀ hN₀.1
  have hw₀C := C.X.involution_mem_centralizer hN₀ hw₀
  have hU₀ := C.X.isUniqueInvolution_modOdd hN₀ hw₀
  have hw₀m : oddQuotMk z ⟨w₀, hw₀C⟩ ∈ R₀.map (C.psi C.i₁) := hN₀img ▸ hU₀.mem
  obtain ⟨x₀, hx₀R, hx₀⟩ := hw₀m
  have hx₀2 : x₀ * x₀ = 1 := hinj (by rw [map_mul, hx₀, hU₀.sq, map_one])
  have hx₀1 : x₀ ≠ 1 := fun h => hU₀.ne_one (by rw [← hx₀, h, map_one])
  have hx₀c : ∀ r ∈ R₀, x₀ * r = r * x₀ := by
    intro r hr
    have hmem : C.psi C.i₁ (r * x₀ * r⁻¹) ∈ modOdd z (exactCore z N₀) := by
      rw [hN₀img]
      exact ⟨_, R₀.mul_mem (R₀.mul_mem hr hx₀R) (R₀.inv_mem hr), rfl⟩
    have hsq : C.psi C.i₁ (r * x₀ * r⁻¹) * C.psi C.i₁ (r * x₀ * r⁻¹) = 1 := by
      rw [← map_mul, show r * x₀ * r⁻¹ * (r * x₀ * r⁻¹) = r * (x₀ * x₀) * r⁻¹ by group, hx₀2]
      simp
    rcases hU₀.unique _ hmem hsq with h | h
    · exfalso
      apply hx₀1
      have h1 : r * x₀ * r⁻¹ = 1 := hinj (h.trans (map_one _).symm)
      calc x₀ = r⁻¹ * (r * x₀ * r⁻¹) * r := by group
        _ = 1 := by rw [h1]; group
    · have h' : r * x₀ * r⁻¹ = x₀ := hinj (h.trans hx₀.symm)
      calc x₀ * r = (r * x₀ * r⁻¹) * r := by rw [h']
        _ = r * x₀ := by group
  obtain ⟨k, hk⟩ := ExoticModel.exists_frameRel hp2 C.tag₁ (C.D.admissible C.i₁) hR₀ hx₀R hx₀c
    hx₀2 hx₀1
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
  have hτ₂sq : k * x₀ * k⁻¹ * (k * x₀ * k⁻¹) = 1 := by
    rw [show k * x₀ * k⁻¹ * (k * x₀ * k⁻¹) = k * (x₀ * x₀) * k⁻¹ by group, hx₀2]
    group
  have hτ₂1 : k * x₀ * k⁻¹ ≠ 1 := by
    intro h
    apply hx₀1
    calc x₀ = k⁻¹ * (k * x₀ * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  exact ⟨⟨R₀, hR₀, x₀, k * x₀ * k⁻¹, hx₀R, hx₀c, hx₀2, hτ₂sq, hx₀1, hτ₂1,
    fun h => hk.ne h.symm, hk.comm, conjSub o₁ N₀, conjSub o₂ (conjSub y₂ N₀),
    conjSub o⁻¹ (conjSub y₃ N₀), o₁ * w₀ * o₁⁻¹, o₂ * (y₂ * w₀ * y₂⁻¹) * o₂⁻¹, hJ, hK', hK'',
    hJt, hK'z', hK''c, htC, hz'C, (Exotic.modOdd_exactCore_conj N₀ ho₁ ho₁C).trans hN₀img,
    htbar, hz'bar, hc⟩⟩

end Construct

end CFSG.ClassicalInvolution.NDB
