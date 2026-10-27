module

public import CFSG.ClassicalInvolution.SmallCases.NDBE2Lift
import CFSG.ClassicalInvolution.SmallCases.DSplitEdge
import CFSG.ClassicalInvolution.Balance.Q27FuzzyBalance
import CFSG.ClassicalInvolution.Asc77.WP3LayerPair
import CFSG.ClassicalInvolution.Asc77.WP3FrameData
import CFSG.ClassicalInvolution.RouteD.NoG2D4Shared
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
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

namespace Exotic

section Group

variable {X : Type*} [Group X]

theorem comm_of_isUniqueInvolution {B : Subgroup X} {w : X}
    (h : IsUniqueInvolution B w) : ∀ y ∈ B, w * y = y * w := by
  intro y hy
  have hmem : y * w * y⁻¹ ∈ B := B.mul_mem (B.mul_mem hy h.mem) (B.inv_mem hy)
  have hsq : y * w * y⁻¹ * (y * w * y⁻¹) = 1 := by
    rw [show y * w * y⁻¹ * (y * w * y⁻¹) = y * (w * w) * y⁻¹ by group, h.sq]
    group
  rcases h.unique _ hmem hsq with h1 | h1
  · exfalso
    apply h.ne_one
    calc w = y⁻¹ * (y * w * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  · calc w * y = (y * w * y⁻¹) * y := by rw [h1]
      _ = y * w := by group

theorem commutator_eq_self {B : Subgroup X} (h : CFSG.Open.IsQuasisimple ↥B) : ⁅B, B⁆ = B := by
  have h1 := congrArg (Subgroup.map B.subtype) h.1
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h1
  exact h1

end Group

end Exotic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G}

namespace ExoticCtx

variable (C : ExoticCtx p f K z)

theorem eq_or_eq (j : Fin C.D.card) : j = C.i₀ ∨ j = C.i₁ := by
  have h0 := C.i₀.2
  have h1 := C.i₁.2
  have hj := j.2
  have hne : C.i₀.val ≠ C.i₁.val := fun e => C.ne (Fin.ext e)
  have hc := C.card_eq
  by_contra h
  push Not at h
  have a0 : j.val ≠ C.i₀.val := fun e => h.1 (Fin.ext e)
  have a1 : j.val ≠ C.i₁.val := fun e => h.2 (Fin.ext e)
  omega

theorem center_eq_bot : Subgroup.center (compModel C.D C.i₁).K = ⊥ :=
  RouteD.G2D4.center_modelUniv_g2d4_eq_bot C.hS.odd C.tag₁ _ (C.D.admissible C.i₁).2.1

theorem psi_injective : Function.Injective (C.psi C.i₁) :=
  RouteD.G2D4.injective_of_ker_le_center C.hS.odd C.tag₁ (C.D.rank C.i₁)
    (C.D.admissible C.i₁).2.1 (C.psi C.i₁) (C.X.psi_ker C.i₁)

theorem eq_one_of_comm {x : (compModel C.D C.i₁).K}
    (h : ∀ y : (compModel C.D C.i₁).K, C.psi C.i₁ x * C.psi C.i₁ y = C.psi C.i₁ y * C.psi C.i₁ x) :
    x = 1 := by
  have hx : x ∈ Subgroup.center (compModel C.D C.i₁).K := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply C.psi_injective
    rw [map_mul, map_mul]
    exact (h y).symm
  rw [C.center_eq_bot] at hx
  exact Subgroup.mem_bot.mp hx

theorem ne_z_of_bar {a : G} (haC : a ∈ Subgroup.centralizer ({z} : Set G))
    {x : (compModel C.D C.i₁).K} (hx : oddQuotMk z ⟨a, haC⟩ = C.psi C.i₁ x) (hx1 : x ≠ 1) :
    a ≠ z := by
  rintro rfl
  apply hx1
  apply C.eq_one_of_comm
  intro y
  rw [← hx]
  exact oddQuotMk_central haC _

theorem le_Q_of_bar {N : Subgroup G} (hN : N ∈ tqMembers (𝒞 K) z) {w : G}
    (hw : IsClassicalMember p f N w) {x : (compModel C.D C.i₁).K}
    (hx : oddQuotMk z ⟨w, C.X.involution_mem_centralizer hN hw⟩ = C.psi C.i₁ x) (hx1 : x ≠ 1) :
    modOdd z (exactCore z N) ≤ (C.psi C.i₁).range := by
  obtain ⟨j, R, -, hRN⟩ := C.X.exists_fund_of_mem hN
  rcases C.eq_or_eq j with rfl | rfl
  · exfalso
    have hwN : oddQuotMk z ⟨w, C.X.involution_mem_centralizer hN hw⟩ ∈
        modOdd z (exactCore z N) :=
      oddQuotMk_mem_modOdd (C.X.involution_mem_exactCore hN hw) _
    rw [← hRN] at hwN
    obtain ⟨r, -, hr⟩ := hwN
    apply hx1
    apply C.eq_one_of_comm
    intro y
    rw [← hx, ← hr]
    exact C.X.psi_commute C.ne r y
  · rw [← hRN]
    exact Subgroup.map_le_range _ _

end ExoticCtx

namespace Exotic

theorem not_mem_trivialOnQuot (C : ExoticCtx p f K z) {N : Subgroup G}
    (hN : N ∈ tqMembers (𝒞 K) z) {w : G} (hw : IsClassicalMember p f N w)
    (hNQ : modOdd z (exactCore z N) ≤ (C.psi C.i₁).range) {a : G}
    (haC : a ∈ Subgroup.centralizer ({z} : Set G))
    (haQ : oddQuotMk z ⟨a, haC⟩ ∈ (C.psi C.i₁).range)
    (ha2 : oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a, haC⟩ = 1) (ha1 : oddQuotMk z ⟨a, haC⟩ ≠ 1)
    (hne : oddQuotMk z ⟨a, haC⟩ ≠ oddQuotMk z ⟨w, C.X.involution_mem_centralizer hN hw⟩) :
    a ∉ trivialOnQuot N := by
  intro htq
  have hq : CFSG.Open.IsQuasisimple ↥(modOdd z (exactCore z N)) :=
    Q27.isQuasisimple_modOdd_free C.X.hs C.D C.hS.odd C.hS.five (exactCore_mem_exactFamily hN)
  have hcen := oddQuotMk_centralizes_modOdd_exactCore hw C.X.hc2 hN.2 htq haC hq
  have hU := C.X.isUniqueInvolution_modOdd hN hw
  have e := RouteD.G2D4.eq_of_central_involutions (RouteD.G2D4.g2d4SharedInvolution p) C.hS.odd
    C.tag₁ (C.D.admissible C.i₁) (C.psi C.i₁) C.psi_injective hNQ (commutator_eq_self hq) haQ
    ha2 ha1 hcen hU.mem hU.ne_one (comm_of_isUniqueInvolution hU)
  exact hne e.symm

end Exotic

namespace ExoticLift

variable {C : ExoticCtx p f K z} (L : ExoticLift C)

theorem htz'C : L.t * L.z' ∈ Subgroup.centralizer ({z} : Set G) := mul_mem L.ht L.hz'

theorem htz'bar : oddQuotMk z ⟨L.t * L.z', L.htz'C⟩ = C.psi C.i₁ (L.τ₁ * L.τ₂) := by
  have e : (⟨L.t * L.z', L.htz'C⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
      ⟨L.t, L.ht⟩ * ⟨L.z', L.hz'⟩ := rfl
  rw [e, map_mul, L.htbar, L.hz'bar, map_mul]

theorem ne₃ : L.τ₁ * L.τ₂ ≠ 1 := by
  intro h
  apply L.ne₁₂
  calc L.τ₁ = L.τ₁ * L.τ₂ * L.τ₂ := by rw [mul_assoc, L.sq₂, mul_one]
    _ = L.τ₂ := by rw [h, one_mul]

theorem sq₃ : L.τ₁ * L.τ₂ * (L.τ₁ * L.τ₂) = 1 := by
  calc L.τ₁ * L.τ₂ * (L.τ₁ * L.τ₂) = L.τ₁ * (L.τ₂ * L.τ₁) * L.τ₂ := by group
    _ = L.τ₁ * (L.τ₁ * L.τ₂) * L.τ₂ := by rw [L.comm]
    _ = 1 := by rw [← mul_assoc, L.sq₁, one_mul, L.sq₂]

theorem t_ne_z : L.t ≠ z := C.ne_z_of_bar L.ht L.htbar L.ne₁

theorem z'_ne_z : L.z' ≠ z := C.ne_z_of_bar L.hz' L.hz'bar L.ne₂

theorem tz'_ne_z : L.t * L.z' ≠ z := C.ne_z_of_bar L.htz'C L.htz'bar L.ne₃

theorem J_le_Q : modOdd z (exactCore z L.J) ≤ (C.psi C.i₁).range :=
  C.le_Q_of_bar L.hJ L.hJt L.htbar L.ne₁

theorem K'_le_Q : modOdd z (exactCore z L.K') ≤ (C.psi C.i₁).range :=
  C.le_Q_of_bar L.hK' L.hK'z' L.hz'bar L.ne₂

theorem uJ : IsUniqueInvolution L.J L.t :=
  ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hS.odd C.hS.five L.hJt

theorem uK' : IsUniqueInvolution L.K' L.z' :=
  ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hS.odd C.hS.five L.hK'z'

theorem uK'' : IsUniqueInvolution L.K'' (L.t * L.z') :=
  ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hS.odd C.hS.five L.hK''tz'

theorem J_ne_K : L.J ≠ K := fun h => L.t_ne_z (L.uJ.eq (by rw [h]; exact C.X.hKz))

theorem K'_ne_K : L.K' ≠ K := fun h => L.z'_ne_z (L.uK'.eq (by rw [h]; exact C.X.hKz))

theorem K''_ne_K : L.K'' ≠ K := fun h => L.tz'_ne_z (L.uK''.eq (by rw [h]; exact C.X.hKz))

theorem t_ne_z' : L.t ≠ L.z' := by
  intro h
  apply L.ne₁₂
  apply C.psi_injective
  rw [← L.htbar, ← L.hz'bar]
  congr 1
  exact Subtype.ext h

theorem hperp₁ : L.K' ∉ KPerp (𝒞 K) L.J := by
  rintro (h | h)
  · exact L.t_ne_z' (L.uJ.eq (h ▸ L.uK'))
  · obtain ⟨a, ha, hKa⟩ := Disconnected.tq_of_mem_omegaNbr C.hS.odd C.hS.five C.X.hΩ.classical
      L.hJ.1 h
    have hat : a = L.t :=
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hS.odd C.hS.five ha).eq L.uJ
    have htq : L.t ∈ trivialOnQuot L.K' :=
      (mem_trivialOnQuot_iff_actsTrivOnQuot (J := L.K')).mpr (hat ▸ hKa)
    refine Exotic.not_mem_trivialOnQuot C L.hK' L.hK'z' L.K'_le_Q L.ht ⟨_, L.htbar.symm⟩ ?_ ?_
      ?_ htq
    · rw [L.htbar, ← map_mul, L.sq₁, map_one]
    · rw [L.htbar]
      exact fun h1 => L.ne₁ (C.psi_injective (h1.trans (map_one _).symm))
    · show oddQuotMk z ⟨L.t, L.ht⟩ ≠ oddQuotMk z ⟨L.z', L.hz'⟩
      rw [L.htbar, L.hz'bar]
      exact fun h1 => L.ne₁₂ (C.psi_injective h1)

theorem hperp₂ : L.J ∉ KPerp (𝒞 K) L.K' := by
  rintro (h | h)
  · exact L.t_ne_z' (L.uJ.eq (h ▸ L.uK'))
  · obtain ⟨a, ha, hJa⟩ := Disconnected.tq_of_mem_omegaNbr C.hS.odd C.hS.five C.X.hΩ.classical
      L.hK'.1 h
    have haz : a = L.z' :=
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hS.odd C.hS.five ha).eq L.uK'
    have htq : L.z' ∈ trivialOnQuot L.J :=
      (mem_trivialOnQuot_iff_actsTrivOnQuot (J := L.J)).mpr (haz ▸ hJa)
    refine Exotic.not_mem_trivialOnQuot C L.hJ L.hJt L.J_le_Q L.hz' ⟨_, L.hz'bar.symm⟩ ?_ ?_
      ?_ htq
    · rw [L.hz'bar, ← map_mul, L.sq₂, map_one]
    · rw [L.hz'bar]
      exact fun h1 => L.ne₂ (C.psi_injective (h1.trans (map_one _).symm))
    · show oddQuotMk z ⟨L.z', L.hz'⟩ ≠ oddQuotMk z ⟨L.t, L.ht⟩
      rw [L.htbar, L.hz'bar]
      exact fun h1 => L.ne₁₂ (C.psi_injective h1).symm

theorem hperp₃ : L.J ∉ KPerp (𝒞 K) L.K'' := by
  rintro (h | h)
  · have e : L.t = L.t * L.z' := (h ▸ L.uJ).eq L.uK''
    apply L.uK'.ne_one
    calc L.z' = L.t⁻¹ * (L.t * L.z') := by group
      _ = 1 := by rw [← e]; group
  · obtain ⟨a, ha, hJa⟩ := Disconnected.tq_of_mem_omegaNbr C.hS.odd C.hS.five C.X.hΩ.classical
      L.hK''.1 h
    have haz : a = L.t * L.z' :=
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hS.odd C.hS.five ha).eq L.uK''
    have htq : L.t * L.z' ∈ trivialOnQuot L.J :=
      (mem_trivialOnQuot_iff_actsTrivOnQuot (J := L.J)).mpr (haz ▸ hJa)
    refine Exotic.not_mem_trivialOnQuot C L.hJ L.hJt L.J_le_Q L.htz'C ⟨_, L.htz'bar.symm⟩ ?_ ?_
      ?_ htq
    · rw [L.htz'bar, ← map_mul, L.sq₃, map_one]
    · rw [L.htz'bar]
      exact fun h1 => L.ne₃ (C.psi_injective (h1.trans (map_one _).symm))
    · show oddQuotMk z ⟨L.t * L.z', L.htz'C⟩ ≠ oddQuotMk z ⟨L.t, L.ht⟩
      rw [L.htz'bar, L.htbar]
      intro h1
      apply L.ne₂
      have h2 := C.psi_injective h1
      calc L.τ₂ = L.τ₁⁻¹ * (L.τ₁ * L.τ₂) := by group
        _ = 1 := by rw [h2]; group

theorem frameData₁ : ChainFrameData (𝒞 K) K L.J L.K' z L.t L.z' where
  mem := C.X.hK
  hz := C.X.hKz
  hJ := mem_omegaNbr_of_trivialOnQuot C.hS.odd C.hS.five C.X.hΩ C.X.hK C.X.hKz L.hJ.1 L.J_ne_K
    L.hJ.2
  ht := L.uJ
  hK' := mem_omegaNbr_of_trivialOnQuot C.hS.odd C.hS.five C.X.hΩ C.X.hK C.X.hKz L.hK'.1
    L.K'_ne_K L.hK'.2
  hz' := L.uK'
  htz' := L.htz'
  hperp := L.hperp₁

theorem frameData₂ : ChainFrameData (𝒞 K) K L.K' L.J z L.z' L.t where
  mem := C.X.hK
  hz := C.X.hKz
  hJ := mem_omegaNbr_of_trivialOnQuot C.hS.odd C.hS.five C.X.hΩ C.X.hK C.X.hKz L.hK'.1
    L.K'_ne_K L.hK'.2
  ht := L.uK'
  hK' := mem_omegaNbr_of_trivialOnQuot C.hS.odd C.hS.five C.X.hΩ C.X.hK C.X.hKz L.hJ.1 L.J_ne_K
    L.hJ.2
  hz' := L.uJ
  htz' := L.htz'.symm
  hperp := L.hperp₂

theorem frameData₃ : ChainFrameData (𝒞 K) K L.K'' L.J z (L.t * L.z') L.t where
  mem := C.X.hK
  hz := C.X.hKz
  hJ := mem_omegaNbr_of_trivialOnQuot C.hS.odd C.hS.five C.X.hΩ C.X.hK C.X.hKz L.hK''.1
    L.K''_ne_K L.hK''.2
  ht := L.uK''
  hK' := mem_omegaNbr_of_trivialOnQuot C.hS.odd C.hS.five C.X.hΩ C.X.hK C.X.hKz L.hJ.1 L.J_ne_K
    L.hJ.2
  hz' := L.uJ
  htz' := by rw [mul_assoc, ← L.htz']
  hperp := L.hperp₃

end ExoticLift

end CFSG.ClassicalInvolution.NDB
