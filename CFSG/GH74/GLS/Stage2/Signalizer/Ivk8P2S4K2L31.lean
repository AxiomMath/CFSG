module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Local.P34Embed
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87AltPerm
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Burnside

theorem perfect_sylow_two_not_cyclic {J : Type} [Group J] [Finite J] (hperf : Group.IsPerfect J)
    (heven : 2 ∣ Nat.card J) (T : Sylow 2 J) : ¬ IsCyclic ↥T := by
  intro hcyclic
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmin : (Nat.card J).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr heven
  let transfer := MonoidHom.transferSylow T (hcyclic.normalizer_le_centralizer hmin)
  have hcomplement : transfer.ker.IsComplement' (T : Subgroup J) :=
    hcyclic.isComplement' hmin
  have hker : transfer.ker = ⊤ := by
    rw [eq_top_iff]
    have hle : commutator J ≤ transfer.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 (IsMulCommutative.is_comm.comm _ _)
    rw [Group.isPerfect_def.mp hperf] at hle
    exact hle
  rw [hker] at hcomplement
  exact T.ne_bot_of_dvd_card heven (Subgroup.isComplement'_top_left.mp hcomplement)

end Burnside

section Main

variable {G : Type} [Group G] [Finite G]

theorem comps_commute {H J J' : Subgroup G} (hJ : IsCompIn H J) (hJ' : IsCompIn H J')
    (hne : J ≠ J') : ∀ a ∈ J, ∀ b ∈ J', a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute hJ.2 hJ'.2 with h | h
  · exfalso
    apply hne
    have h1 := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hJ.1, inf_eq_left.mpr hJ'.1] at h1
  · intro a ha b hb
    have h1 : ⁅(⟨a, hJ.1 ha⟩ : ↥H), (⟨b, hJ'.1 hb⟩ : ↥H)⁆ ∈
        ⁅J.subgroupOf H, J'.subgroupOf H⁆ :=
      Subgroup.commutator_mem_commutator ha hb
    rw [h, Subgroup.mem_bot] at h1
    have h2 : ⁅a, b⁆ = 1 := congrArg Subtype.val h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h2

omit [Finite G] in
theorem mem_normalizer_of_fix {J : Subgroup G} {b : G} (hc : ∀ a ∈ J, b * a * b⁻¹ = a) :
    b ∈ normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hc h hh]
    exact hh
  · intro hh
    have e : b * (b * h * b⁻¹) * b⁻¹ = b * h * b⁻¹ := hc _ hh
    have e2 : b * h * b⁻¹ = h := by
      have := congrArg (fun x => b⁻¹ * x * b) e
      group at this ⊢
      exact this
    rw [← e2]
    exact hh

omit [Finite G] in
theorem le_centralizerSection {J J' M : Subgroup G} (hMJ : M ≤ J)
    (hcomm : ∀ a ∈ J, ∀ b ∈ J', a * b = b * a) : J' ≤ centralizerSection J M := by
  intro b hb
  have hc : ∀ a ∈ J, b * a * b⁻¹ = a := fun a ha => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (hcomm a ha b hb).symm
  refine ⟨mem_normalizer_of_fix hc, mem_normalizer_of_fix fun a ha => hc a (hMJ ha), ?_⟩
  intro k hk
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcomm k hk b hb)]
  exact M.one_mem

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2
