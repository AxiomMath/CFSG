module

public import CFSG.LocalAnalysis.OddStandard.Seitz77WBridgeAct
public import CFSG.LocalAnalysis.OddStandard.Seitz77WBridgeSylow

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

@[expose] def preimageX {G : Type} [Group G] (X O : Subgroup G) [(O.subgroupOf X).Normal]
    (Wb : Subgroup (Q25 X O)) : Subgroup G :=
  (Wb.comap (QuotientGroup.mk' (O.subgroupOf X))).map X.subtype

theorem mem_preimageX {G : Type} [Group G] {X O : Subgroup G} [(O.subgroupOf X).Normal]
    {Wb : Subgroup (Q25 X O)} {x : G} :
    x ∈ preimageX X O Wb ↔ ∃ hx : x ∈ X, (QuotientGroup.mk ⟨x, hx⟩ : Q25 X O) ∈ Wb := by
  unfold preimageX
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem mk_eq_one_iff_mem {G : Type} [Group G] {X O : Subgroup G} [(O.subgroupOf X).Normal]
    {x : G} (hx : x ∈ X) : (QuotientGroup.mk ⟨x, hx⟩ : Q25 X O) = 1 ↔ x ∈ O :=
  QuotientGroup.eq_one_iff (N := O.subgroupOf X) _

theorem mk_eq_mk_iff {G : Type} [Group G] {X O : Subgroup G} [(O.subgroupOf X).Normal]
    {x y : G} (hx : x ∈ X) (hy : y ∈ X) :
    (QuotientGroup.mk ⟨x, hx⟩ : Q25 X O) = QuotientGroup.mk ⟨y, hy⟩ ↔ x⁻¹ * y ∈ O := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem mk_commutator {G : Type} [Group G] {X O : Subgroup G} [(O.subgroupOf X).Normal]
    {x y : G} (hx : x ∈ X) (hy : y ∈ X) (hxy : x * y * x⁻¹ * y⁻¹ ∈ X) :
    (QuotientGroup.mk ⟨x * y * x⁻¹ * y⁻¹, hxy⟩ : Q25 X O) =
      ⁅(QuotientGroup.mk ⟨x, hx⟩ : Q25 X O), QuotientGroup.mk ⟨y, hy⟩⁆ :=
  map_commutatorElement (QuotientGroup.mk' (O.subgroupOf X)) (⟨x, hx⟩ : ↥X) ⟨y, hy⟩

namespace IsSetting25

variable {G : Type} [Group G] [Finite G] {A W X O : Subgroup G} {t : G}
  (S : IsSetting25 A W t X O) [(O.subgroupOf X).Normal]

theorem mem_range_sup_zpowers_tbar {q : Q25 X O} (hq : q ∈ S.phiW.range ⊔ zpowers S.tbar) :
    q ∈ S.phiW.range ∨ ∃ r ∈ S.phiW.range, q = r * S.tbar := by
  have : S.phiW.range.Normal := Subgroup.normal_of_le_center S.phiW_range_le_center
  have h2 : S.tbar ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact S.tbar_mul_self
  have hk : ∀ k : ℤ, S.tbar ^ k = 1 ∨ S.tbar ^ k = S.tbar := by
    intro k
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, h2, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
  obtain ⟨r, hr, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hq
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rcases hk k with h | h
  · left
    rw [h, mul_one]
    exact hr
  · right
    exact ⟨r, hr, by rw [h]⟩

include S

theorem wtSpec_of_wbar (Wb : Subgroup (Q25 X O))
    (hchar : ∀ φ : MulAut (Q25 X O), Wb.map φ.toMonoidHom = Wb) (helem : IsElemAbelian 2 Wb)
    (hidx : Wb.index = 2) (hV : S.phiW.range ≤ Wb) (ht : S.tbar ∉ Wb)
    (hdel : ∀ v ∈ S.phiW.range, ∃ w ∈ Wb, ⁅S.tbar, w⁆ = v) :
    WtSpec W t X O (preimageX X O Wb) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro o ho
    have hoX : o ∈ X := S.O_le_X ho
    refine mem_preimageX.mpr ⟨hoX, ?_⟩
    rw [(mk_eq_one_iff_mem hoX).mpr ho]
    exact Wb.one_mem
  ·
    intro x hx
    obtain ⟨hxX, -⟩ := mem_preimageX.mp hx
    exact hxX
  ·
    intro n hn x hx
    obtain ⟨hxX, hxW⟩ := mem_preimageX.mp hx
    have hnX : n * x * n⁻¹ ∈ X := (mem_normalizer_iff.mp (S.normalizer_le hn) x).mp hxX
    refine mem_preimageX.mpr ⟨hnX, ?_⟩
    rw [← conjQ_mk X O ⟨n, S.mem_Mx hn⟩ ⟨x, hxX⟩ hnX]
    have h2 : conjQ X O ⟨n, S.mem_Mx hn⟩ (QuotientGroup.mk ⟨x, hxX⟩) ∈
        Wb.map (conjQ X O ⟨n, S.mem_Mx hn⟩).toMonoidHom := ⟨_, hxW, rfl⟩
    rwa [hchar] at h2
  ·
    intro w hw
    exact mem_preimageX.mpr ⟨S.W_le_X hw, hV ⟨⟨w, hw⟩, rfl⟩⟩
  ·
    intro hmem
    obtain ⟨_, htb⟩ := mem_preimageX.mp hmem
    exact ht htb
  ·
    have h1 : Nat.card ↥(preimageX X O Wb) =
        Nat.card ↥(Wb.comap (QuotientGroup.mk' (O.subgroupOf X))) :=
      Subgroup.card_subtype X _
    have h2 : (Wb.comap (QuotientGroup.mk' (O.subgroupOf X))).index = 2 := by
      rw [Subgroup.index_comap_of_surjective Wb (QuotientGroup.mk'_surjective _), hidx]
    have h3 := Subgroup.card_mul_index (Wb.comap (QuotientGroup.mk' (O.subgroupOf X)))
    rw [h2, S.card_X] at h3
    rw [h1]
    omega
  ·
    intro x hx y hy
    obtain ⟨hxX, hxW⟩ := mem_preimageX.mp hx
    obtain ⟨hyX, hyW⟩ := mem_preimageX.mp hy
    have hxy : x * y * x⁻¹ * y⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem hxX hyX) (X.inv_mem hxX)) (X.inv_mem hyX)
    refine (mk_eq_one_iff_mem hxy).mp ?_
    rw [mk_commutator hxX hyX hxy, commutatorElement_eq_one_iff_mul_comm]
    exact L34.comm_of_isElemAbelian helem hxW hyW
  ·
    intro x hx
    obtain ⟨hxX, hxW⟩ := mem_preimageX.mp hx
    have hxx : x * x ∈ X := X.mul_mem hxX hxX
    refine (mk_eq_one_iff_mem hxx).mp ?_
    have e : (⟨x * x, hxx⟩ : ↥X) = ⟨x, hxX⟩ ^ 2 := by
      apply Subtype.ext
      exact (sq x).symm
    rw [e, QuotientGroup.mk_pow]
    exact helem.2 _ hxW
  ·
    intro w hw hwt
    obtain ⟨hwX, hwW⟩ := mem_preimageX.mp hw
    have hcent : (QuotientGroup.mk ⟨w, hwX⟩ : Q25 X O) ∈
        centralizer ({S.tbar} : Set (Q25 X O)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      show (QuotientGroup.mk ⟨w, hwX⟩ : Q25 X O) * QuotientGroup.mk ⟨t, S.t_mem_X⟩ =
        QuotientGroup.mk ⟨t, S.t_mem_X⟩ * QuotientGroup.mk ⟨w, hwX⟩
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hwt
    rw [S.centralizer_tbar] at hcent
    rcases S.mem_range_sup_zpowers_tbar hcent with ⟨⟨v, hv⟩, hvw⟩ | ⟨r, hr, hrw⟩
    · have h1 : (QuotientGroup.mk ⟨v, S.W_le_X hv⟩ : Q25 X O) = QuotientGroup.mk ⟨w, hwX⟩ := hvw
      have h2 : v⁻¹ * w ∈ O := (mk_eq_mk_iff (S.W_le_X hv) hwX).mp h1
      have h3 : w = v * (v⁻¹ * w) := by group
      rw [h3]
      exact Subgroup.mul_mem_sup hv h2
    · exfalso
      refine ht ?_
      have h1 : S.tbar = r⁻¹ * QuotientGroup.mk ⟨w, hwX⟩ := by
        rw [hrw]
        group
      rw [h1]
      exact Wb.mul_mem (Wb.inv_mem (hV hr)) hwW
  ·
    intro v hv
    obtain ⟨wb, hwb, hcomm⟩ := hdel (S.phiW ⟨v, hv⟩) ⟨_, rfl⟩
    obtain ⟨⟨w, hwX⟩, rfl⟩ := QuotientGroup.mk_surjective wb
    refine ⟨w, mem_preimageX.mpr ⟨hwX, hwb⟩, ?_⟩
    have hdX : t * w * t⁻¹ * w⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem S.t_mem_X hwX) (X.inv_mem S.t_mem_X)) (X.inv_mem hwX)
    have h1 : (QuotientGroup.mk ⟨t * w * t⁻¹ * w⁻¹, hdX⟩ : Q25 X O) =
        QuotientGroup.mk ⟨v, S.W_le_X hv⟩ :=
      (mk_commutator S.t_mem_X hwX hdX).trans hcomm
    exact (mk_eq_mk_iff (S.W_le_X hv) hdX).mp h1.symm

end IsSetting25

end CFSG.OddStandard.Seitz77
