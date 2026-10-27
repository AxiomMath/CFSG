module

public import CFSG.ClassicalInvolution.SmallCases.NDBE2SLift
public import CFSG.ClassicalInvolution.SmallCases.NDBE2Frame
import CFSG.ClassicalInvolution.SmallCases.DSplitEdge
import CFSG.ClassicalInvolution.Balance.Q27FuzzyBalance
import CFSG.ClassicalInvolution.Asc77.WP3LayerPair
import CFSG.ClassicalInvolution.Asc77.WP3FrameData
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

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G}

omit [Finite G] [IsSimpleGroup G] in
theorem Exotic.not_mem_center_conj {X : Type*} [Group X] {x : X} (hx : x ∉ Subgroup.center X)
    (g : X) : g * x * g⁻¹ ∉ Subgroup.center X := by
  intro h
  apply hx
  have := (Subgroup.normal_of_characteristic (Subgroup.center X)).conj_mem _ h g⁻¹
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

namespace ExoticCtxS

variable (C : ExoticCtxS p f K z)

include C in
theorem centralizes_of_tq {N : Subgroup G} (hN : N ∈ tqMembers (𝒞 K) z) {w : G}
    (hw : IsClassicalMember p f N w) {a : G} (haC : a ∈ Subgroup.centralizer ({z} : Set G))
    (htq : a ∈ trivialOnQuot N) :
    ∀ y ∈ modOdd z (exactCore z N), oddQuotMk z ⟨a, haC⟩ * y = y * oddQuotMk z ⟨a, haC⟩ := by
  have hq : CFSG.Open.IsQuasisimple ↥(modOdd z (exactCore z N)) :=
    Q27.isQuasisimple_modOdd_free C.X.hs C.D C.hS.odd C.hS.five (exactCore_mem_exactFamily hN)
  exact oddQuotMk_centralizes_modOdd_exactCore hw C.X.hc2 hN.2 htq haC hq

theorem not_mem_trivialOnQuot {N : Subgroup G} (hN : N ∈ tqMembers (𝒞 K) z) {w : G}
    (hw : IsClassicalMember p f N w) {R : Subgroup (compModel C.D C.i₁).K}
    (hNR : modOdd z (exactCore z N) = R.map (C.psi C.i₁)) {a : G}
    (haC : a ∈ Subgroup.centralizer ({z} : Set G)) {x : (compModel C.D C.i₁).K}
    (hax : oddQuotMk z ⟨a, haC⟩ = C.psi C.i₁ x) (hnc : ∃ r ∈ R, x * r ≠ r * x) :
    a ∉ trivialOnQuot N := by
  intro htq
  obtain ⟨r, hr, hne⟩ := hnc
  have h := C.centralizes_of_tq hN hw haC htq (C.psi C.i₁ r) (hNR ▸ ⟨r, hr, rfl⟩)
  rw [hax, ← map_mul, ← map_mul] at h
  exact hne (C.psi_injective h)

end ExoticCtxS

namespace ExoticLiftS

variable {C : ExoticCtxS p f K z} (L : ExoticLiftS C)

theorem htz'C : L.t * L.z' ∈ Subgroup.centralizer ({z} : Set G) := mul_mem L.ht L.hz'

theorem htz'bar : oddQuotMk z ⟨L.t * L.z', L.htz'C⟩ =
    C.psi C.i₁ (L.τ₁ * (L.k * L.τ₁ * L.k⁻¹)) := by
  have e : (⟨L.t * L.z', L.htz'C⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
      ⟨L.t, L.ht⟩ * ⟨L.z', L.hz'⟩ := rfl
  rw [e, map_mul, L.htbar, L.hz'bar, ← map_mul]

theorem ne₁₂ : L.τ₁ ≠ L.k * L.τ₁ * L.k⁻¹ := fun h => L.rel.ne h.symm

theorem ne₁ : L.τ₁ ≠ 1 := L.uR₁.ne_one

theorem nz₁ : L.τ₁ ∉ Subgroup.center (compModel C.D C.i₁).K := fun h =>
  L.uR₁.ne_one (ExoticModel.spin_fund_noncentral C.tag₁ (C.D.admissible C.i₁) L.R₁ L.hR₁ L.τ₁
    L.uR₁.mem h)

theorem nz₂ : L.k * L.τ₁ * L.k⁻¹ ∉ Subgroup.center (compModel C.D C.i₁).K :=
  Exotic.not_mem_center_conj L.nz₁ L.k

theorem nz₃ : L.τ₁ * (L.k * L.τ₁ * L.k⁻¹) ∉ Subgroup.center (compModel C.D C.i₁).K := by
  rw [← L.rel.sq_conj]
  exact Exotic.not_mem_center_conj L.nz₁ _

theorem t_ne_z : L.t ≠ z := C.ne_z_of_bar L.ht L.htbar L.nz₁

theorem z'_ne_z : L.z' ≠ z := C.ne_z_of_bar L.hz' L.hz'bar L.nz₂

theorem tz'_ne_z : L.t * L.z' ≠ z := C.ne_z_of_bar L.htz'C L.htz'bar L.nz₃

theorem J_le_Q : modOdd z (exactCore z L.J) ≤ (C.psi C.i₁).range :=
  C.le_Q_of_bar L.hJ L.hJt L.htbar L.nz₁

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
    exact C.not_mem_trivialOnQuot L.hK' L.hK'z' L.hK'img L.ht L.htbar L.nc₁ htq

theorem hperp₂ : L.J ∉ KPerp (𝒞 K) L.K' := by
  rintro (h | h)
  · exact L.t_ne_z' (L.uJ.eq (h ▸ L.uK'))
  · obtain ⟨a, ha, hJa⟩ := Disconnected.tq_of_mem_omegaNbr C.hS.odd C.hS.five C.X.hΩ.classical
      L.hK'.1 h
    have haz : a = L.z' :=
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hS.odd C.hS.five ha).eq L.uK'
    have htq : L.z' ∈ trivialOnQuot L.J :=
      (mem_trivialOnQuot_iff_actsTrivOnQuot (J := L.J)).mpr (haz ▸ hJa)
    exact C.not_mem_trivialOnQuot L.hJ L.hJt L.hJimg L.hz' L.hz'bar L.nc₂ htq

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
    exact C.not_mem_trivialOnQuot L.hJ L.hJt L.hJimg L.htz'C L.htz'bar L.nc₃ htq

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

end ExoticLiftS

end CFSG.ClassicalInvolution.NDB
