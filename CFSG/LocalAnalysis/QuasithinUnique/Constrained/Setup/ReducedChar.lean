module

public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.QuasithinUnique.Setup

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

section Subtype

variable {S : Subgroup G}

theorem isElemAbelian_map_subtype {p : ℕ} {E : Subgroup S} :
    IsElemAbelian p (E.map S.subtype) ↔ IsElemAbelian p E := by
  unfold IsElemAbelian
  rw [isMulCommutative_subgroup_iff, isMulCommutative_subgroup_iff]
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨fun x hx y hy => Subtype.ext ?_, fun x hx => Subtype.ext ?_⟩
    · simpa using hc x ⟨x, hx, rfl⟩ y ⟨y, hy, rfl⟩
    · simpa using hp x ⟨x, hx, rfl⟩
  · rintro ⟨hc, hp⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa using congrArg Subtype.val (hc x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      simpa using congrArg Subtype.val (hp x hx)

theorem card_map_subtype (E : Subgroup S) : Nat.card (E.map S.subtype) = Nat.card E :=
  Nat.card_congr (E.equivMapOfInjective S.subtype S.subtype_injective).toEquiv.symm

theorem isMaxElemAbelian_top_iff {A : Subgroup S} :
    IsMaxElemAbelian (⊤ : Subgroup S) A ↔ IsMaxElemAbelian S (A.map S.subtype) := by
  unfold IsMaxElemAbelian
  constructor
  · rintro ⟨-, hA, hmax⟩
    refine ⟨Subgroup.map_subtype_le A, isElemAbelian_map_subtype.mpr hA, fun B hBS hB => ?_⟩
    have hB' : IsElemAbelian 2 (B.subgroupOf S) := by
      rw [← isElemAbelian_map_subtype, Subgroup.map_subgroupOf_eq_of_le hBS]
      exact hB
    have h := hmax (B.subgroupOf S) le_top hB'
    have hBcard : Nat.card B = Nat.card (B.subgroupOf S) := by
      rw [← card_map_subtype (B.subgroupOf S), Subgroup.map_subgroupOf_eq_of_le hBS]
    rw [hBcard, card_map_subtype]
    exact h
  · rintro ⟨-, hA, hmax⟩
    refine ⟨le_top, isElemAbelian_map_subtype.mp hA, fun B _ hB => ?_⟩
    have h := hmax (B.map S.subtype) (Subgroup.map_subtype_le B)
      (isElemAbelian_map_subtype.mpr hB)
    rwa [card_map_subtype, card_map_subtype] at h

theorem thompsonJ_eq_map_top (S : Subgroup G) :
    thompsonJ S = (thompsonJ (⊤ : Subgroup S)).map S.subtype := by
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    have hA' : IsMaxElemAbelian (⊤ : Subgroup S) (A.subgroupOf S) := by
      rw [isMaxElemAbelian_top_iff, Subgroup.map_subgroupOf_eq_of_le hA.1]
      exact hA
    have h1 : A.subgroupOf S ≤ thompsonJ (⊤ : Subgroup S) :=
      le_iSup₂_of_le (f := fun (B : Subgroup S) (_ : IsMaxElemAbelian (⊤ : Subgroup S) B) => B)
        (A.subgroupOf S) hA' le_rfl
    have h2 := Subgroup.map_mono (f := S.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hA.1] at h2
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A' hA' => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (f := fun (B : Subgroup G) (_ : IsMaxElemAbelian S B) => B)
      (A'.map S.subtype) (isMaxElemAbelian_top_iff.mp hA') le_rfl

theorem omegaOneCenterOf_eq_map_top (S : Subgroup G) :
    omegaOneCenterOf S = (omegaOneCenterOf (⊤ : Subgroup S)).map S.subtype := by
  unfold omegaOneCenterOf omegaOneOf
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨hxS, hxC⟩, hx2⟩
    refine ⟨⟨x, hxS⟩, ⟨⟨trivial, ?_⟩, ?_⟩, rfl⟩
    · refine Subgroup.mem_centralizer_iff.mpr fun w _ => ?_
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC w w.2)
    · exact Subtype.ext (by simpa using hx2)
  · rintro ⟨z, ⟨⟨-, hz⟩, hz2⟩, rfl⟩
    refine ⟨⟨z.2, ?_⟩, by simpa using congrArg Subtype.val hz2⟩
    refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hz) ⟨g, hg⟩ trivial)

end Subtype

theorem map_top_mulEquiv {H : Type*} [Group H] (φ : H ≃* H) :
    (⊤ : Subgroup H).map φ.toMonoidHom = ⊤ := by
  rw [← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr φ.surjective

theorem characteristic_thompsonJ (S : Subgroup G) :
    ((thompsonJ S).subgroupOf S).Characteristic := by
  have h : (thompsonJ S).subgroupOf S = thompsonJ (⊤ : Subgroup S) := by
    rw [thompsonJ_eq_map_top S, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective]
  rw [h]
  refine Subgroup.characteristic_iff_map_le.mpr fun φ => ?_
  rw [thompsonJ_map_mulEquiv φ, map_top_mulEquiv]

theorem characteristic_omegaOneCenterOf (S : Subgroup G) :
    ((omegaOneCenterOf S).subgroupOf S).Characteristic := by
  have h : (omegaOneCenterOf S).subgroupOf S = omegaOneCenterOf (⊤ : Subgroup S) := by
    rw [omegaOneCenterOf_eq_map_top S, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective]
  rw [h]
  refine Subgroup.characteristic_iff_map_le.mpr fun φ => ?_
  rw [omegaOneCenterOf_map_mulEquiv φ, map_top_mulEquiv]

theorem omegaOneCenterOf_le (S : Subgroup G) : omegaOneCenterOf S ≤ S :=
  (Subgroup.closure_le S).mpr fun _ hx => hx.1.1

section Nontrivial

variable [Finite G] {S : Subgroup G}

theorem exists_involution_centerOf (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) :
    ∃ x : G, x ∈ centerOf S ∧ x ^ 2 = 1 ∧ x ≠ 1 := by
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS1
  have : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center S) := hS.to_subgroup _
  obtain ⟨j, hj⟩ := hZ2.exists_card_eq
  have hj0 : j ≠ 0 := by
    rintro rfl
    have h1 : Nat.card (Subgroup.center S) = 1 := by simpa using hj
    exact not_subsingleton _ (Nat.card_eq_one_iff_unique.mp h1).1
  have h2 : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hj]
    exact dvd_pow_self 2 hj0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  refine ⟨((x : S) : G), ⟨(x : S).2, ?_⟩, ?_, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp x.2) ⟨g, hg⟩)
  · simpa using congrArg (fun y : ↥(Subgroup.center S) => ((y : S) : G)) hx2
  · intro h
    exact hx1 (Subtype.ext (Subtype.ext h))

theorem omegaOneCenterOf_ne_bot (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) : omegaOneCenterOf S ≠ ⊥ := by
  obtain ⟨x, hxZ, hx2, hx1⟩ := exists_involution_centerOf hS hS1
  intro hbot
  have : x ∈ omegaOneCenterOf S := Subgroup.subset_closure ⟨hxZ, hx2⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hx1 this

theorem exists_isMaxElemAbelian_ne_bot (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) :
    ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ A ≠ ⊥ := by
  obtain ⟨x, hxZ, hx2, hx1⟩ := exists_involution_centerOf hS hS1
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian S
  refine ⟨A, hA, fun hbot => ?_⟩
  have hB : IsElemAbelian 2 (Subgroup.zpowers x) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  have hBS : Subgroup.zpowers x ≤ S := Subgroup.zpowers_le.mpr hxZ.1
  have hcard := hA.2.2 _ hBS hB
  have h2 : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx2 hx1
  rw [hbot, Subgroup.card_bot, h2] at hcard
  omega

theorem thompsonJ_ne_bot (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) : thompsonJ S ≠ ⊥ := by
  obtain ⟨A, hA, hA1⟩ := exists_isMaxElemAbelian_ne_bot hS hS1
  intro hbot
  exact hA1 (le_bot_iff.mp (hbot ▸ B6.le_thompsonJ hA))

theorem pRank_pos (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) : 0 < pRank 2 S := by
  obtain ⟨A, hA, hA1⟩ := exists_isMaxElemAbelian_ne_bot hS hS1
  have hc := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
  rw [pow_zero, mul_one] at hc
  by_contra hr
  rw [Nat.not_lt, Nat.le_zero] at hr
  rw [hr, pow_zero] at hc
  exact hA1 (Subgroup.card_eq_one.mp hc)

end Nontrivial

end CFSG.QuasithinUnique.Setup
