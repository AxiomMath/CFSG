module

import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec64Cfg (T H : Subgroup G) (x y : G) : Prop where
  isPGroup : IsPGroup 2 ↥T
  hx : orderOf x = 2
  hy : orderOf y = 2
  hxy : x * y = y * x
  hxT : x ∈ T
  hyT : y ∈ T
  hxH : x ∉ H
  hyH : y ∈ H
  hRH : ∀ r ∈ T ⊓ centralizer ({y} : Set G), ∀ h ∈ H, r * h * r⁻¹ ∈ H
  hU : IsCyclic ↥(T ⊓ centralizer ({y} : Set G) ⊓ H)

@[expose] def Sec64E8 (T H : Subgroup G) (y : G) : Prop :=
  CFSG.Open.IsElemAbelian 2 (T ⊓ centralizer ({y} : Set G)) →
    Nat.card ↥(T ⊓ centralizer ({y} : Set G)) = 8 →
    Nat.card ↥(T ⊓ centralizer ({y} : Set G) ⊓ H) = 2 →
      T ⊓ centralizer ({y} : Set G) ≠ T → CFSG.GH74.sectionalTwoRank T ≤ 3

@[expose] def Sec64Tri (T H : Subgroup G) (y : G) : Prop :=
  H.relIndex (T ⊓ centralizer ({y} : Set G)) ≤ 2 ∨
    (Sec64E8 T H y ∧
      QuotEquivTo (T ⊓ centralizer ({y} : Set G)) (T ⊓ centralizer ({y} : Set G) ⊓ H)
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∨
    QuotEquivTo (T ⊓ centralizer ({y} : Set G)) (T ⊓ centralizer ({y} : Set G) ⊓ H)
      (Multiplicative (ZMod 4))

@[expose] def Sec64Out [Finite G] (T H : Subgroup G) (y : G) : Prop :=
  CFSG.Open.pRank 2 T = 2 ∨
    (¬ H.relIndex (T ⊓ centralizer ({y} : Set G)) ≤ 2 ∧ CFSG.GH74.sectionalTwoRank T ≤ 3)

theorem Sec64Cfg.mem_R {T H : Subgroup G} {x y : G} (c : Sec64Cfg T H x y) :
    x ∈ T ⊓ centralizer ({y} : Set G) :=
  Subgroup.mem_inf.mpr ⟨c.hxT, Subgroup.mem_centralizer_singleton_iff.mpr c.hxy⟩

theorem Sec64Cfg.mem_U {T H : Subgroup G} {x y : G} (c : Sec64Cfg T H x y) :
    y ∈ T ⊓ centralizer ({y} : Set G) ⊓ H :=
  Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_inf.mpr
      ⟨c.hyT, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, c.hyH⟩

theorem Sec64Cfg.norm_U {T H : Subgroup G} {x y : G} (c : Sec64Cfg T H x y)
    {r u : G} (hr : r ∈ T ⊓ centralizer ({y} : Set G))
    (hu : u ∈ T ⊓ centralizer ({y} : Set G) ⊓ H) :
    r * u * r⁻¹ ∈ T ⊓ centralizer ({y} : Set G) ⊓ H := by
  obtain ⟨huR, huH⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨huT, hucen⟩ := Subgroup.mem_inf.mp huR
  obtain ⟨hrT, hrcen⟩ := Subgroup.mem_inf.mp hr
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, c.hRH r hr u huH⟩
  · exact T.mul_mem (T.mul_mem hrT huT) (T.inv_mem hrT)
  · exact (centralizer ({y} : Set G)).mul_mem
      ((centralizer ({y} : Set G)).mul_mem hrcen hucen)
      ((centralizer ({y} : Set G)).inv_mem hrcen)

theorem sec64_unique_inv [Finite G] {U : Subgroup G} (hU : IsCyclic ↥U) {a b : G} (ha : a ∈ U)
    (hb : b ∈ U) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : a = b := by
  classical
  haveI : IsCyclic ↥U := hU
  haveI : Finite ↥U := Subtype.finite
  haveI : Fintype ↥U := Fintype.ofFinite ↥U
  have ha2' : (⟨a, ha⟩ : ↥U) ^ 2 = 1 := by
    apply Subtype.ext
    have h : a ^ 2 = 1 := by simpa [ha2] using pow_orderOf_eq_one a
    simpa using h
  have hb2' : (⟨b, hb⟩ : ↥U) ^ 2 = 1 := by
    apply Subtype.ext
    have h : b ^ 2 = 1 := by simpa [hb2] using pow_orderOf_eq_one b
    simpa using h
  have hane : (⟨a, ha⟩ : ↥U) ≠ 1 := by
    intro h
    have h1 : orderOf (⟨a, ha⟩ : ↥U) = 1 := by rw [h]; exact orderOf_one
    rw [Subgroup.orderOf_mk a ha] at h1
    omega
  have hbne : (⟨b, hb⟩ : ↥U) ≠ 1 := by
    intro h
    have h1 : orderOf (⟨b, hb⟩ : ↥U) = 1 := by rw [h]; exact orderOf_one
    rw [Subgroup.orderOf_mk b hb] at h1
    omega
  have hS : (Finset.univ.filter (fun z : ↥U => z ^ 2 = 1)).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (α := ↥U) (n := 2) (by norm_num)
  have hone : (1 : ↥U) ∈ Finset.univ.filter (fun z : ↥U => z ^ 2 = 1) := by simp
  have hamem : (⟨a, ha⟩ : ↥U) ∈ Finset.univ.filter (fun z : ↥U => z ^ 2 = 1) := by
    simp [ha2']
  have hbmem : (⟨b, hb⟩ : ↥U) ∈ Finset.univ.filter (fun z : ↥U => z ^ 2 = 1) := by
    simp [hb2']
  have herase : ((Finset.univ.filter (fun z : ↥U => z ^ 2 = 1)).erase 1).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hone]
    omega
  have hab : (⟨a, ha⟩ : ↥U) = ⟨b, hb⟩ :=
    Finset.card_le_one.mp herase _ (Finset.mem_erase.mpr ⟨hane, hamem⟩)
      _ (Finset.mem_erase.mpr ⟨hbne, hbmem⟩)
  exact congrArg Subtype.val hab

theorem sec64_two_le_pRank [Finite G] {T : Subgroup G} {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hxy : x * y = y * x) (hne : x ≠ y) (hxT : x ∈ T) (hyT : y ∈ T) :
    2 ≤ CFSG.Open.pRank 2 T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy_not : y ∉ Subgroup.zpowers x := by
    intro hyz
    exact hne (sec64_unique_inv (U := Subgroup.zpowers x) (Subgroup.isCyclic_zpowers x)
      (Subgroup.mem_zpowers x) hyz hx hy)
  have hcomm : ∀ a ∈ Subgroup.zpowers x, a * y = y * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((show Commute x y from hxy).zpow_left n).eq
  obtain ⟨hE, hcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (r := 2) (X := Subgroup.zpowers x) (v := y)
    (by rw [Nat.card_zpowers, hx]) hy hy_not hcomm
  have hET : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ T :=
    sup_le (Subgroup.zpowers_le.mpr hxT) (Subgroup.zpowers_le.mpr hyT)
  exact CFSG.SectionRank.le_pRank (p := 2) (by norm_num) hET hE (k := 2) hcard

theorem sec64_not_relIndex_le_two [Finite G] {R H : Subgroup G} {F : Type} [Group F] [Finite F]
    (hQ : QuotEquivTo R (R ⊓ H) F) (hF : Nat.card F = 4) : ¬ H.relIndex R ≤ 2 := by
  intro hle
  obtain ⟨φ, hφ, hker⟩ := hQ
  have hker' : φ.ker = H.subgroupOf R := by
    rw [hker]
    exact Subgroup.inf_subgroupOf_left H R
  have hidx : H.relIndex R = Nat.card F := by
    rw [Subgroup.relIndex, ← hker', Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ,
      Subgroup.card_top]
  rw [hidx, hF] at hle
  omega

theorem sec64_card_eq [Finite G] (R H : Subgroup G) :
    Nat.card ↥R = Nat.card ↥(R ⊓ H) * H.relIndex R := by
  have h1 : Nat.card ↥(H.subgroupOf R) = Nat.card ↥(R ⊓ H) := by
    have h := Subgroup.card_map_of_injective (K := H.subgroupOf R) R.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype] at h
    rw [inf_comm] at h
    exact h.symm
  rw [← Subgroup.card_mul_index (H := H.subgroupOf R), h1, Subgroup.relIndex]

end CFSG.OddStandard.SmallF3.Omega
