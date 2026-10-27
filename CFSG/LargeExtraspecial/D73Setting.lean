module

public import CFSG.LargeExtraspecial.D73ModelQ
public import CFSG.LargeExtraspecial.DWTrans
public import CFSG.LargeExtraspecial.AS35Core

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.D73

open Subgroup
open scoped MatrixGroups

noncomputable def comapEquiv {M C : Type*} [Group M] [Group C] (φ : M ≃* C) (K : Subgroup C) :
    K.comap φ.toMonoidHom ≃* K :=
  (MulEquiv.subgroupCongr (by rw [comap_equiv_eq_map_symm']; rfl)).trans
    (φ.symm.subgroupMap K).symm

theorem card_comap_mulEquiv {M C : Type*} [Group M] [Group C] (φ : M ≃* C) (K : Subgroup C) :
    Nat.card (K.comap φ.toMonoidHom) = Nat.card K :=
  Nat.card_congr (comapEquiv φ K).toEquiv

@[expose] noncomputable def settingOfCorner {G : Type*} [Group G] [Finite G] {N : ℕ} (hN : 6 ≤ N)
    (z : G) (hz : orderOf z = 2) (φ : centralizer ({z} : Set G) ≃* Ct N (by omega)) :
    Setting G where
  z := z
  orderOf_z := hz
  Q := (Qm (N := N) (by omega)).comap φ.toMonoidHom
  normal := (MonoidHom.normal_ker _).comap _
  extraspecial := isExtraspecialPGroup_of_mulEquiv (comapEquiv φ _).symm
    (isExtraspecialPGroup_Qm (N := N) (by omega))
  centralizer_le := by
    intro x hx
    rw [mem_comap]
    refine centralizer_Qm_le (N := N) (by omega) (mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨y', rfl⟩ := φ.surjective y
    have h := (mem_centralizer_iff.mp hx) y' (by rw [SetLike.mem_coe, mem_comap]; exact hy)
    simpa using congrArg φ h
  le_of_normal := by
    intro P hP h2
    have h := le_Qm_of_normal (N := N) (by omega) (P.map φ.toMonoidHom) (hP.map _ φ.surjective)
      (h2.map _)
    intro x hx
    exact h ⟨x, hx, rfl⟩

@[expose] noncomputable def cornerA {G : Type*} [Group G] {N : ℕ} (hN : 6 ≤ N) (z : G)
    (φ : centralizer ({z} : Set G) ≃* Ct N (by omega)) : Subgroup G :=
  ((Am (N := N) (by omega)).comap φ.toMonoidHom).map (centralizer ({z} : Set G)).subtype

@[expose] noncomputable def cornerB {G : Type*} [Group G] {N : ℕ} (hN : 6 ≤ N) (z : G)
    (φ : centralizer ({z} : Set G) ≃* Ct N (by omega)) : Subgroup G :=
  ((Bm (N := N) (by omega)).comap φ.toMonoidHom).map (centralizer ({z} : Set G)).subtype

section

variable {G : Type*} [Group G] [Finite G] {N : ℕ} (hN : 6 ≤ N) (z : G) (hz : orderOf z = 2)
  (φ : centralizer ({z} : Set G) ≃* Ct N (by omega))

omit [Finite G] in
include hz in
theorem φ_z : φ ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ = tZero (N := N) (by omega) := by
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  set z' : centralizer ({z} : Set G) := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  have hc : z' ∈ center (centralizer ({z} : Set G)) :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have hc' : φ z' ∈ center (Ct N _) := by
    rw [← map_center_of_mulEquiv φ]
    exact ⟨z', hc, rfl⟩
  rw [center_Ct (N := N) (by omega), mem_zpowers_tZero_iff] at hc'
  refine hc'.resolve_left fun h => hz1 ?_
  have : z' = 1 := φ.injective (by rw [h, map_one])
  exact congrArg Subtype.val this

theorem settingOfCorner_z : (settingOfCorner hN z hz φ).z = z := rfl

theorem card_Q_settingOfCorner : Nat.card (settingOfCorner hN z hz φ).Q = 2 ^ (2 * N - 3) := by
  change Nat.card ((Qm (N := N) (by omega)).comap φ.toMonoidHom) = _
  rw [card_comap_mulEquiv, card_Qm]

theorem width_settingOfCorner : (settingOfCorner hN z hz φ).width = N - 2 :=
  Setting.width_eq _ (by rw [card_Q_settingOfCorner]; congr 1; omega)

theorem mem_QG_iff {x : G} : x ∈ (settingOfCorner hN z hz φ).QG ↔
    ∃ h : x ∈ centralizer ({z} : Set G), midBlock (N := N) (by omega) (φ ⟨x, h⟩) = 1 :=
  Setting.mem_QG_iff _

omit [Finite G] in
theorem cornerA_eq_map : cornerA hN z φ =
    (Am (N := N) (by omega)).map ((centralizer ({z} : Set G)).subtype.comp φ.symm.toMonoidHom) := by
  rw [cornerA, comap_equiv_eq_map_symm', map_map]

omit [Finite G] in
theorem cornerB_eq_map : cornerB hN z φ =
    (Bm (N := N) (by omega)).map ((centralizer ({z} : Set G)).subtype.comp φ.symm.toMonoidHom) := by
  rw [cornerB, comap_equiv_eq_map_symm', map_map]

omit [Finite G] in
instance isElementaryAbelian_cornerA : IsElementaryAbelian 2 (cornerA hN z φ) := by
  rw [cornerA_eq_map]
  exact IsElementaryAbelian.map _

omit [Finite G] in
instance isElementaryAbelian_cornerB : IsElementaryAbelian 2 (cornerB hN z φ) := by
  rw [cornerB_eq_map]
  exact IsElementaryAbelian.map _

omit [Finite G] in
theorem card_cornerA : Nat.card (cornerA hN z φ) = 2 ^ (N - 1) := by
  rw [cornerA, card_map_of_injective (subtype_injective _), card_comap_mulEquiv, card_Am]

omit [Finite G] in
theorem card_cornerB : Nat.card (cornerB hN z φ) = 2 ^ (N - 1) := by
  rw [cornerB, card_map_of_injective (subtype_injective _), card_comap_mulEquiv, card_Bm]

theorem maxEA_cornerA : MaxEA (settingOfCorner hN z hz φ) (cornerA hN z φ) :=
  ⟨map_mono (comap_mono (Am_le_Qm _)), by
    rw [card_cornerA, width_settingOfCorner]
    congr 1
    omega⟩

theorem maxEA_cornerB : MaxEA (settingOfCorner hN z hz φ) (cornerB hN z φ) :=
  ⟨map_mono (comap_mono (Bm_le_Qm _)), by
    rw [card_cornerB, width_settingOfCorner]
    congr 1
    omega⟩

theorem M_le_normalizer_cornerA :
    (settingOfCorner hN z hz φ).M ≤ normalizer (cornerA hN z φ : Set G) := by
  have hn : ((Am (N := N) (by omega)).comap φ.toMonoidHom).Normal := (Am_normal _).comap _
  have h := le_normalizer_map (H := (Am (N := N) (by omega)).comap φ.toMonoidHom)
    (centralizer ({z} : Set G)).subtype
  rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

theorem M_le_normalizer_cornerB :
    (settingOfCorner hN z hz φ).M ≤ normalizer (cornerB hN z φ : Set G) := by
  have hn : ((Bm (N := N) (by omega)).comap φ.toMonoidHom).Normal := (Bm_normal _).comap _
  have h := le_normalizer_map (H := (Bm (N := N) (by omega)).comap φ.toMonoidHom)
    (centralizer ({z} : Set G)).subtype
  rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

omit [Finite G] in
include hz in
theorem cornerA_inf_cornerB : cornerA hN z φ ⊓ cornerB hN z φ = Subgroup.zpowers z := by
  rw [cornerA, cornerB, ← map_inf_eq _ _ _ (subtype_injective _), ← comap_inf, Am_inf_Bm,
    comap_equiv_eq_map_symm', MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  congr 1
  rw [← φ_z hN z hz φ]
  simp

omit [Finite G] in
include φ in
theorem two_pow_dvd_card : 2 ^ (N * (N - 1) / 2) ∣ Nat.card G :=
  ((two_pow_dvd_card_Ct (N := N) (by omega)).trans
    (Nat.card_congr φ.toEquiv).symm.dvd).trans (card_subgroup_dvd_card _)

omit [Finite G] in
include φ in
theorem exists_ne_mul_comm : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨x, -, y, -, hxy⟩ := exists_not_mul_comm_Qm (N := N) (by omega) (by omega)
  refine ⟨φ.symm x, φ.symm y, fun h => hxy ?_⟩
  have h' : φ.symm x * φ.symm y = φ.symm y * φ.symm x := Subtype.ext h
  simpa using congrArg φ h'

end

theorem card_Mbar_settingOfCorner {G : Type} [Group G] [Finite G] {N : ℕ} (hN : 6 ≤ N) (z : G)
    (hz : orderOf z = 2) (φ : centralizer ({z} : Set G) ≃* Ct N (by omega)) :
    Nat.card (settingOfCorner hN z hz φ).Mbar = Nat.card (GL (Fin (N - 2)) (ZMod 2)) := by
  set S := settingOfCorner hN z hz φ
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup S.Q
  rw [card_Q_settingOfCorner, Nat.card_congr S.quotientEquivMbar.toEquiv] at h1
  have h2 : Nat.card S.M = 2 ^ (2 * N - 3) * Nat.card (GL (Fin (N - 2)) (ZMod 2)) := by
    change Nat.card (centralizer ({z} : Set G)) = _
    rw [Nat.card_congr φ.toEquiv, card_Ct]
  exact Nat.eq_of_mul_eq_mul_right (pow_pos two_pos _) ((h1.symm.trans h2).trans (mul_comm _ _))

theorem mbarTwoBound {G : Type} [Group G] [Finite G] {N : ℕ} (hN : 6 ≤ N) (z : G)
    (hz : orderOf z = 2) (φ : centralizer ({z} : Set G) ≃* Ct N (by omega)) :
    (settingOfCorner hN z hz φ).MbarTwoBound ((N - 2) * (N - 3) / 2) := by
  refine Setting.MbarTwoBound.of _ fun P hP => ?_
  have hcard := card_Mbar_settingOfCorner hN z hz φ
  have : Finite (settingOfCorner hN z hz φ).Mbar :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk]
  refine Nat.pow_le_pow_right two_pos ?_
  have hdvd : 2 ^ k ∣ Nat.card (GL (Fin (N - 2)) (ZMod 2)) := by
    rw [← hk, ← hcard]
    exact card_subgroup_dvd_card P
  have h := le_of_two_pow_dvd_card_GL (K := ZMod 2) (s := 1) (by simp) hdvd
  rwa [one_mul, show N - 2 - 1 = N - 3 by omega] at h

end CFSG.LargeExtraspecial.DW.D73
