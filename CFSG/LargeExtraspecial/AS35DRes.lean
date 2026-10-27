module

public import CFSG.LargeExtraspecial.AS35DStmt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

section Restrict

variable (H : Subgroup G) (hQH : S.QG ≤ H)

@[expose] def zH : H := ⟨S.z, hQH S.z_mem_QG⟩

abbrev MH : Subgroup H := centralizer ({S.zH H hQH} : Set H)

@[expose] def ιH : S.MH H hQH →* G := H.subtype.comp (S.MH H hQH).subtype

omit [Finite G] in
theorem ιH_injective : Function.Injective (S.ιH H hQH) :=
  H.subtype_injective.comp (S.MH H hQH).subtype_injective

omit [Finite G] in
theorem mem_MH_iff {x : H} : x ∈ S.MH H hQH ↔ (x : G) ∈ S.M := by
  rw [mem_centralizer_singleton_iff, S.mem_M_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

omit [Finite G] in
theorem ιH_mem_M (c : S.MH H hQH) : S.ιH H hQH c ∈ S.M := (S.mem_MH_iff H hQH).mp c.2

@[expose] def QH : Subgroup (S.MH H hQH) := S.QG.comap (S.ιH H hQH)

omit [Finite G] in
theorem map_QH : (S.QH H hQH).map (S.ιH H hQH) = S.QG := by
  refine le_antisymm (map_le_iff_le_comap.mpr le_rfl) fun x hx => ?_
  refine ⟨⟨⟨x, hQH hx⟩, (S.mem_MH_iff H hQH).mpr (S.QG_le_M hx)⟩, hx, rfl⟩

@[expose] noncomputable def QHEquiv : S.QH H hQH ≃* S.Q :=
  ((S.QH H hQH).equivMapOfInjective (S.ιH H hQH) (S.ιH_injective H hQH)).trans
    ((MulEquiv.subgroupCongr (S.map_QH H hQH)).trans
      (S.Q.equivMapOfInjective S.M.subtype S.M.subtype_injective).symm)

variable (hMH : ∀ m ∈ S.M, ∀ h ∈ H, m * h * m⁻¹ ∈ H)

@[expose] noncomputable def conjMH (m : G) (hm : m ∈ S.M) : S.MH H hQH ≃* S.MH H hQH where
  toFun c := ⟨⟨m * c * m⁻¹, hMH m hm _ (c : H).2⟩, (S.mem_MH_iff H hQH).mpr
    (S.M.mul_mem (S.M.mul_mem hm (S.ιH_mem_M H hQH c)) (S.M.inv_mem hm))⟩
  invFun c := ⟨⟨m⁻¹ * c * m, by
      have := hMH m⁻¹ (S.M.inv_mem hm) _ (c : H).2
      rwa [inv_inv] at this⟩, (S.mem_MH_iff H hQH).mpr
    (S.M.mul_mem (S.M.mul_mem (S.M.inv_mem hm) (S.ιH_mem_M H hQH c)) hm)⟩
  left_inv c := Subtype.ext (Subtype.ext (by
    change m⁻¹ * (m * ((c : H) : G) * m⁻¹) * m = ((c : H) : G)
    group))
  right_inv c := Subtype.ext (Subtype.ext (by
    change m * (m⁻¹ * ((c : H) : G) * m) * m⁻¹ = ((c : H) : G)
    group))
  map_mul' a b := Subtype.ext (Subtype.ext (by
    change m * (((a : H) : G) * ((b : H) : G)) * m⁻¹ =
      m * ((a : H) : G) * m⁻¹ * (m * ((b : H) : G) * m⁻¹)
    group))

omit [Finite G] in
theorem ιH_conjMH (m : G) (hm : m ∈ S.M) (c : S.MH H hQH) :
    S.ιH H hQH (S.conjMH H hQH hMH m hm c) = m * S.ιH H hQH c * m⁻¹ := rfl

@[expose] noncomputable def restrict : Setting H where
  z := S.zH H hQH
  orderOf_z := by
    rw [zH, Subgroup.orderOf_mk]
    exact S.orderOf_z
  Q := S.QH H hQH
  normal := ⟨fun x hx c => by
    change S.ιH H hQH (c * x * c⁻¹) ∈ S.QG
    rw [map_mul, map_mul, map_inv]
    exact S.conj_mem_QG (S.ιH_mem_M H hQH c) hx⟩
  extraspecial := isExtraspecialPGroup_of_mulEquiv (S.QHEquiv H hQH).symm S.extraspecial
  centralizer_le := by
    intro c hc
    change S.ιH H hQH c ∈ S.QG
    refine S.mem_QG_of_commute (S.ιH_mem_M H hQH c) fun x hx => ?_
    obtain ⟨x', hx', rfl⟩ : x ∈ (S.QH H hQH).map (S.ιH H hQH) := by
      rw [S.map_QH H hQH]
      exact hx
    have := mem_centralizer_iff.mp hc x' hx'
    rw [← map_mul, ← map_mul, this]
  le_of_normal := by
    intro P hP hP2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set R := CFSG.pCore 2 (S.MH H hQH) with hR
    have hPR : P ≤ R := le_sSup ⟨hP, hP2⟩
    have hRM : R.map (S.ιH H hQH) ≤ S.M := by
      rintro _ ⟨c, -, rfl⟩
      exact S.ιH_mem_M H hQH c
    have hRn : ((R.map (S.ιH H hQH)).subgroupOf S.M).Normal := ⟨fun x hx m => by
      rw [mem_subgroupOf] at hx ⊢
      obtain ⟨c, hc, hcx⟩ := hx
      have hmap := CFSG.pCore_map_iso 2 (S.conjMH H hQH hMH m m.2)
      refine ⟨S.conjMH H hQH hMH m m.2 c, ?_, ?_⟩
      · rw [← hR] at hmap
        rw [← hmap]
        exact ⟨c, hc, rfl⟩
      · rw [ιH_conjMH, hcx]
        rfl⟩
    have hR2 : IsPGroup 2 ((R.map (S.ιH H hQH)).subgroupOf S.M) :=
      (CFSG.pCore_isPGroup.map _).comap_of_injective S.M.subtype S.M.subtype_injective
    have hle := S.le_of_normal _ hRn hR2
    intro c hc
    change S.ιH H hQH c ∈ S.QG
    have hcR : S.ιH H hQH c ∈ R.map (S.ιH H hQH) := ⟨c, hPR hc, rfl⟩
    exact S.mem_QG_iff.mpr ⟨hRM hcR, hle (by rw [mem_subgroupOf]; exact hcR)⟩

omit [Finite G] in
theorem coe_restrict_z : ((S.restrict H hQH hMH).z : G) = S.z := rfl

omit [Finite G] in
theorem mem_restrict_QG {x : H} : x ∈ (S.restrict H hQH hMH).QG ↔ (x : G) ∈ S.QG := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hc
  · intro hx
    exact ⟨⟨x, (S.mem_MH_iff H hQH).mpr (S.QG_le_M hx)⟩, hx, rfl⟩

theorem restrict_width : (S.restrict H hQH hMH).width = S.width := by
  refine (S.restrict H hQH hMH).width_eq ?_
  rw [← S.card_Q_eq]
  exact Nat.card_congr (S.QHEquiv H hQH).toEquiv

omit [Finite G] in
theorem zInOTwo_restrict {x : H} (hx : S.ZInOTwo (x : G)) :
    (S.restrict H hQH hMH).ZInOTwo x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup H := (oTwoCent (x : G)).comap H.subtype ⊓ centralizer ({x} : Set H)
  refine (S.restrict H hQH hMH).zInOTwo_of_le (P := P) inf_le_right ?_ ?_ ?_
  · intro c hc p hp
    refine mem_inf.mpr ⟨?_, mul_mem (mul_mem hc (mem_inf.mp hp).2) (inv_mem hc)⟩
    have hc' : (c : G) ∈ centralizer ({(x : G)} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      exact congrArg Subtype.val hc
    exact conj_mem_oTwoCent hc' (mem_inf.mp hp).1
  · exact ((isPGroup_oTwoCent (x : G)).comap_of_injective H.subtype
      H.subtype_injective).to_le inf_le_left
  · refine mem_inf.mpr ⟨hx, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (oTwoCent_le_centralizer _ hx))

omit [Finite G] in
theorem map_zGen_restrict_le : (S.restrict H hQH hMH).zGen.map H.subtype ≤ S.zGen := by
  rw [map_le_iff_le_comap, zGen, closure_le]
  intro y hy
  obtain ⟨c, rfl⟩ := isConj_iff.mp hy
  exact S.conj_mem_zGen (c : G)

end Restrict

end Setting

end CFSG.LargeExtraspecial
