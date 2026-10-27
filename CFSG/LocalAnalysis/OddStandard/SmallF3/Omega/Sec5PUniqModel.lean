module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CentDPull
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXPkMap
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTGen
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCMap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem sec5pu_pocket_map {φ : ↥L →* omegaGroup hQ} (hoc : OddCentralCover φ) {z : G}
    (hzL : z ∈ L) (hzz : z * z = 1) {K : Subgroup G} (hK : Sl23PocketIn L z K) :
    Sl23PocketIn (omegaGroup hQ) (sec5cdPhi φ ⟨z, hzL⟩) ((K.subgroupOf L).map (sec5cdPhi φ)) := by
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI : Finite (OGroup Q) := inferInstance
  have h1 := l34g_x_sl23PocketIn_subgroupOf (H := L) (V := L) le_rfl hzL hK
  rw [Subgroup.subgroupOf_self] at h1
  have hzz' : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 := Subtype.ext hzz
  have h2 := l34g_x_sl23PocketIn_map hoc hzz' h1
  rw [Subgroup.map_top_of_surjective φ hoc.surjective] at h2
  have h3 := (sec63PC_sl23PocketIn_map_iff (omegaGroup hQ).subtype
    Subtype.val_injective).mpr h2
  have e1 : (⊤ : Subgroup ↥(omegaGroup hQ)).map (omegaGroup hQ).subtype = omegaGroup hQ := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  rw [e1, Subgroup.map_map] at h3
  exact h3

theorem sec5pu_map_le_twoRes {φ : ↥L →* omegaGroup hQ} {z : G} (hzL : z ∈ L) {K : Subgroup G}
    (hK : Sl23PocketIn L z K) :
    (K.subgroupOf L).map (sec5cdPhi φ) ≤
      twoRes (omegaGroup hQ ⊓ centralizer ({sec5cdPhi φ ⟨z, hzL⟩} : Set (OGroup Q))) := by
  have hKL : K ≤ L := hK.2.1.trans inf_le_left
  have hmod : IsSL23Mod ↥(K.subgroupOf L) :=
    isSL23Mod_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL).symm hK.2.2.2
  refine Subgroup.map_le_iff_le_comap.mpr ((l34g_le_closure_odd hmod).trans ?_)
  rw [Subgroup.closure_le]
  rintro c ⟨hcK, hcodd⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  have hcz : (c : G) ∈ centralizer ({z} : Set G) := (hK.2.1 hcK).2
  have hcomm : c * ⟨z, hzL⟩ = ⟨z, hzL⟩ * c :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hcz)
  refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨(φ c).2, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (map_mul (sec5cdPhi φ) _ _).symm.trans
      ((congrArg (sec5cdPhi φ) hcomm).trans (map_mul (sec5cdPhi φ) _ _))
  · exact Odd.of_dvd_nat hcodd (orderOf_map_dvd _ c)

theorem sec5pu_img_cases {φ : ↥L →* omegaGroup hQ} (hoc : OddCentralCover φ) {z : G}
    (hzL : z ∈ L) (hzz : z * z = 1) (D : Om6Par Q (sec5cdPhi φ ⟨z, hzL⟩)) {K : Subgroup G}
    (hK : Sl23PocketIn L z K) :
    (K.subgroupOf L).map (sec5cdPhi φ) = D.L ∨ (K.subgroupOf L).map (sec5cdPhi φ) = D.R :=
  D.pocket_cases (sec5pu_pocket_map hoc hzL hzz hK) (sec5pu_map_le_twoRes hzL hK)

theorem sec5pu_card_img {φ : ↥L →* omegaGroup hQ} {z : G} (hzL : z ∈ L)
    (D : Om6Par Q (sec5cdPhi φ ⟨z, hzL⟩)) {K : Subgroup G}
    (h : (K.subgroupOf L).map (sec5cdPhi φ) = D.L ∨ (K.subgroupOf L).map (sec5cdPhi φ) = D.R) :
    Nat.card ↥((K.subgroupOf L).map φ) = 24 := by
  have hc : Nat.card ↥((K.subgroupOf L).map (sec5cdPhi φ)) =
      Nat.card ↥((K.subgroupOf L).map φ) := by
    rw [sec5cdPhi, ← Subgroup.map_map]
    exact Subgroup.card_map_of_injective (omegaGroup hQ).subtype_injective
  rw [← hc]
  have hSL : ∀ e : Nonempty (↥D.L ≃* SL23), Nat.card ↥D.L = 24 := by
    rintro ⟨e⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hSR : ∀ e : Nonempty (↥D.R ≃* SL23), Nat.card ↥D.R = 24 := by
    rintro ⟨e⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  rcases h with h | h
  · rw [h]
    exact hSL D.sec5Pair.iso₁
  · rw [h]
    exact hSR D.sec5Pair.iso₂

end CFSG.OddStandard.SmallF3.Omega
