module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameSyl
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

variable {G : Type} [Group G]

theorem mem_twoCoreIn_iff_pCore {X : Subgroup G} {x : G} (hx : x ∈ X) :
    x ∈ twoCoreIn X ↔ (⟨x, hx⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := by
  unfold twoCoreIn CFSG.inSubgroup
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem twoCoreIn_le_self (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

theorem isPGroup_twoCoreIn (X : Subgroup G) : IsPGroup 2 (twoCoreIn X) := by
  unfold twoCoreIn CFSG.inSubgroup
  exact (CFSG.pCore_isPGroup (G := ↥X) (p := 2)).map X.subtype

theorem normal_subgroupOf_twoCoreIn (X : Subgroup G) : ((twoCoreIn X).subgroupOf X).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (twoCoreIn_le_self X)]
  intro h k hh hk
  unfold twoCoreIn CFSG.inSubgroup at hh ⊢
  obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hh
  refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩ * h' * ⟨k, hk⟩⁻¹, ?_, ?_⟩
  · exact (CFSG.pCore_normal (p := 2) (G := ↥X)).conj_mem h' hh' ⟨k, hk⟩
  · simp

theorem le_twoCoreIn_of_normal {X P : Subgroup G} (hPX : P ≤ X) (hP2 : IsPGroup 2 P)
    (hn : (P.subgroupOf X).Normal) : P ≤ twoCoreIn X := by
  have hP2' : IsPGroup 2 (P.subgroupOf X) := hP2.comap_subtype
  have hle : P.subgroupOf X ≤ CFSG.pCore 2 ↥X := le_sSup ⟨hn, hP2'⟩
  calc P = (P.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hPX).symm
    _ ≤ (CFSG.pCore 2 ↥X).map X.subtype := Subgroup.map_mono hle
    _ = twoCoreIn X := rfl

theorem twoCoreIn_eq_of_normal_sylow [Finite G] {X P : Subgroup G} (hPX : P ≤ X)
    (hP2 : IsPGroup 2 P) (hn : (P.subgroupOf X).Normal) (hidx : ¬ 2 ∣ (P.subgroupOf X).index) :
    twoCoreIn X = P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_twoCoreIn_of_normal hPX hP2 hn)
  have hP2' : IsPGroup 2 (P.subgroupOf X) := hP2.comap_subtype
  have hR2 : IsPGroup 2 ((twoCoreIn X).subgroupOf X) := (isPGroup_twoCoreIn X).comap_subtype
  haveI := normal_subgroupOf_twoCoreIn X
  let S : Sylow 2 ↥X := hP2'.toSylow hidx
  have hScoe : (S : Subgroup ↥X) = P.subgroupOf X := IsPGroup.toSylow_coe hP2' hidx
  have hle : (twoCoreIn X).subgroupOf X ≤ (S : Subgroup ↥X) := hR2.le_sylow_of_normal S
  intro x hx
  have hxS : (⟨x, twoCoreIn_le_self X hx⟩ : ↥X) ∈ (S : Subgroup ↥X) := hle hx
  rw [hScoe] at hxS
  exact hxS

namespace PspFrame

variable {L : Subgroup G} (F : PspFrame L) {X : Subgroup G}

theorem img_twoCoreIn (hX : X ≤ L) : F.img (twoCoreIn X) = twoCoreIn (F.img X) := by
  have h2 := CFSG.pCore_map_iso 2 (F.imgEquiv hX)
  ext p
  constructor
  · intro hp
    obtain ⟨l, hl, rfl⟩ := mem_img.1 hp
    have hlX : (l : G) ∈ X := twoCoreIn_le_self X hl
    have hψ : F.ψ l ∈ F.img X := mem_img.2 ⟨l, hlX, rfl⟩
    rw [mem_twoCoreIn_iff_pCore hψ]
    have h1 : (⟨(l : G), hlX⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := (mem_twoCoreIn_iff_pCore hlX).1 hl
    rw [← h2]
    exact Subgroup.mem_map.2 ⟨⟨(l : G), hlX⟩, h1, Subtype.ext rfl⟩
  · intro hp
    have hpX : p ∈ F.img X := twoCoreIn_le_self _ hp
    have h1 := (mem_twoCoreIn_iff_pCore hpX).1 hp
    rw [← h2] at h1
    obtain ⟨x, hx, hxp⟩ := Subgroup.mem_map.1 h1
    refine mem_img.2 ⟨⟨(x : G), hX x.2⟩, (mem_twoCoreIn_iff_pCore x.2).2 hx, ?_⟩
    exact congrArg Subtype.val hxp

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
