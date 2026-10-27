module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem mem_zpowers_of_orderOf_eq [Finite G] {Z : Subgroup G} (hZcyc : IsCyclic ↥Z)
    {x w : G} (hx : x ∈ Z) (hw : w ∈ Z) (hx4 : orderOf x = 4) (hw4 : orderOf w = 4) :
    w ∈ zpowers x := by
  classical
  let α := ↥Z
  haveI : IsCyclic α := hZcyc
  haveI : Fintype α := Fintype.ofFinite α
  let s : Set α := {a : α | a ^ 4 = 1}
  have hsle : s.toFinset.card ≤ 4 := by
    simpa [s] using IsCyclic.card_pow_eq_one_le (α := α) (n := 4) (by norm_num)
  have hsub : (Subgroup.zpowers (⟨x, hx⟩ : α) : Set α) ⊆ s := by
    intro a ha
    change a ^ 4 = 1
    rw [← orderOf_dvd_iff_pow_eq_one]
    calc orderOf a ∣ orderOf (⟨x, hx⟩ : α) := orderOf_dvd_of_mem_zpowers ha
      _ = 4 := by rw [Subgroup.orderOf_mk, hx4]
  have hcard : (Subgroup.zpowers (⟨x, hx⟩ : α) : Set α).toFinset.card = 4 := by
    rw [← Set.ncard_eq_toFinset_card', ← Nat.card_coe_set_eq]
    change Nat.card (Subgroup.zpowers (⟨x, hx⟩ : α)) = 4
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx4]
  have heq : (Subgroup.zpowers (⟨x, hx⟩ : α) : Set α).toFinset = s.toFinset := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro a ha
      rw [Set.mem_toFinset] at ha
      exact Set.mem_toFinset.mpr (hsub ha)
    · rw [hcard]
      exact hsle
  have hwmem : (⟨w, hw⟩ : α) ∈ Subgroup.zpowers (⟨x, hx⟩ : α) := by
    have hws : (⟨w, hw⟩ : α) ∈ s := by
      change (⟨w, hw⟩ : α) ^ 4 = 1
      rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_mk, hw4]
      try exact dvd_rfl
    have hmem : (⟨w, hw⟩ : α) ∈ s.toFinset := Set.mem_toFinset.mpr hws
    rw [← heq] at hmem
    rwa [Set.mem_toFinset] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwmem
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem sec76_isCyclic_inf [Finite G] (h72 : Asc82Lemma72) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec7Ctx G t L S z) : IsCyclic ↥(S ⊓ centralizer (L : Set G)) := by
  classical
  let C : Subgroup G := centralizer (L : Set G)
  let Z : Subgroup G := S ⊓ C
  have hZC : Z ≤ C := inf_le_right
  have hZ2 : IsPGroup 2 Z := hctx.sylow.2.1.to_le inf_le_left
  have hZsub2 : IsPGroup 2 (Z.subgroupOf C) :=
    hZ2.of_equiv (Subgroup.subgroupOfEquivOfLe hZC).symm
  obtain ⟨Q, hQ⟩ := hZsub2.exists_le_sylow
  have hQcyc : IsCyclic ↥(Q : Subgroup ↥C) := by
    haveI : IsCyclic ↥((Q : Subgroup ↥C).map C.subtype) :=
      h72 G t L hctx.toSec3SettingLB hctx.omega6 _ (isSylow2Of_map_sylow Q)
    exact isCyclic_of_injective
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥C) C.subtype C.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥C) C.subtype C.subtype_injective).injective
  haveI : IsCyclic ↥(Q : Subgroup ↥C) := hQcyc
  have hZsubcyc : IsCyclic ↥(Z.subgroupOf C) := Subgroup.isCyclic_of_le hQ
  haveI : IsCyclic ↥(Z.subgroupOf C) := hZsubcyc
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hZC).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hZC).surjective

theorem sec76_comm_inf [Finite G] (h72 : Asc82Lemma72) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec7Ctx G t L S z) {a b : G} (ha : a ∈ S ⊓ centralizer (L : Set G))
    (hb : b ∈ S ⊓ centralizer (L : Set G)) : a * b = b * a := by
  haveI : IsCyclic ↥(S ⊓ centralizer (L : Set G)) := sec76_isCyclic_inf h72 hctx
  haveI : IsMulCommutative ↥(S ⊓ centralizer (L : Set G)) := inferInstance
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(S ⊓ centralizer (L : Set G))) ⟨b, hb⟩)

theorem sec76_sq_eq_t [Finite G] (h72 : Asc82Lemma72) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec7Ctx G t L S z) {x : G} (hx : x ∈ S ⊓ centralizer (L : Set G))
    (hx4 : orderOf x = 4) : x * x = t := by
  have hxx : x * x ∈ S ⊓ centralizer (L : Set G) :=
    (S ⊓ centralizer (L : Set G)).mul_mem hx hx
  have ht : t ∈ S ⊓ centralizer (L : Set G) := ⟨hctx.t_mem_S, hctx.t_mem_centralizer⟩
  have hx4' : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hxx2 : (x * x) * (x * x) = 1 := by
    rw [← pow_two (x * x), ← pow_two x, ← pow_mul]
    simpa using hx4'
  have hcomm : (x * x) * t = t * (x * x) := sec76_comm_inf h72 hctx hxx ht
  rcases eq_one_or_eq_of_commute
    (hcyc := fun P hP => h72 G t L hctx.toSec3SettingLB hctx.omega6 P hP)
    hxx.2 ht.2 hxx2 hctx.involution hcomm with h1 | h1
  · exfalso
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
    rw [hx4] at hdvd
    exact absurd hdvd (by norm_num)
  · exact h1

theorem sec76_conj_mem_zpowers [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) {t : G}
    {L S : Subgroup G} {z : G} (hctx : Sec7Ctx G t L S z) {x : G}
    (hx : x ∈ S ⊓ centralizer (L : Set G)) (hx4 : orderOf x = 4) {y : G} (hy : y ∈ S) :
    y⁻¹ * x * y ∈ zpowers x := by
  let Z : Subgroup G := S ⊓ centralizer (L : Set G)
  have hxZ : x ∈ Z := hx
  have hyC : y ∈ centralizer ({t} : Set G) := hctx.sylow.1 hy
  have hyN : y ∈ normalizer (L : Set G) := hctx.cent_le_normalizer h36 y hyC
  have hwC : y⁻¹ * x * y ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hyl : y * l * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN l).mp hl
    have hxcomm : (y * l * y⁻¹) * x = x * (y * l * y⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hx.2 (y * l * y⁻¹) hyl
    calc l * (y⁻¹ * x * y) = y⁻¹ * ((y * l * y⁻¹) * x) * y := by group
      _ = y⁻¹ * (x * (y * l * y⁻¹)) * y := by rw [hxcomm]
      _ = (y⁻¹ * x * y) * l := by group
  have hwZ : y⁻¹ * x * y ∈ Z :=
    ⟨S.mul_mem (S.mul_mem (S.inv_mem hy) hx.1) hy, hwC⟩
  have hw4 : orderOf (y⁻¹ * x * y) = 4 := by
    have h1 : y⁻¹ * x * y = (MulAut.conj y⁻¹) x := by simp [MulAut.conj_apply]
    rw [h1, MulEquiv.orderOf_eq, hx4]
  exact mem_zpowers_of_orderOf_eq (sec76_isCyclic_inf h72 hctx) hxZ hwZ hx4 hw4

theorem sec76_le_zpowers_t [Finite G] (h72 : Asc82Lemma72) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec7Ctx G t L S z) (h4 : ∀ x ∈ S ⊓ centralizer (L : Set G), orderOf x ≠ 4) :
    S ⊓ centralizer (L : Set G) ≤ zpowers t := by
  intro y hy
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup G := S ⊓ centralizer (L : Set G)
  have hyZ : y ∈ Z := hy
  have hZ2 : IsPGroup 2 Z := hctx.sylow.2.1.to_le inf_le_left
  obtain ⟨k, hk⟩ := hZ2.exists_orderOf_eq_pow ⟨y, hyZ⟩
  have hordy : orderOf y = 2 ^ k := by rw [← Subgroup.orderOf_mk y hyZ, hk]
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · have hy1 : y = 1 := by
        rw [← orderOf_eq_one_iff, hordy]
        norm_num
      rw [hy1]
      exact Subgroup.one_mem _
    · have hy2 : orderOf y = 2 := by rw [hordy]; norm_num
      have hyy : y * y = 1 := by
        rw [← pow_two, ← hy2]
        exact pow_orderOf_eq_one y
      have htZ : t ∈ Z := ⟨hctx.t_mem_S, hctx.t_mem_centralizer⟩
      have hcomm : y * t = t * y := sec76_comm_inf h72 hctx hyZ htZ
      rcases eq_one_or_eq_of_commute
        (hcyc := fun P hP => h72 G t L hctx.toSec3SettingLB hctx.omega6 P hP)
        hyZ.2 htZ.2 hyy hctx.involution hcomm with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.mem_zpowers t
  · have h4dvd : 4 ∣ orderOf y := by
      rw [hordy]
      exact pow_dvd_pow 2 hk2
    have hx4 : orderOf (y ^ (orderOf y / 4)) = 4 :=
      orderOf_pow_orderOf_div (isOfFinOrder_of_finite y).orderOf_pos.ne' h4dvd
    exact absurd hx4 (h4 _ (Subgroup.pow_mem Z hyZ _))

theorem sec76_sylow_cent_tz [Finite G] {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec7Ctx G t L S z) {g : G} (hg : g⁻¹ * t * g = t * z) :
    IsSylow2Of S (centralizer ({t * z} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : S ≤ centralizer ({t * z} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hst : s * t = t * s :=
      Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hs)
    have hsz : s * z = z * s := hctx.central s hs
    calc s * (t * z) = (s * t) * z := by group
      _ = (t * s) * z := by rw [hst]
      _ = t * (s * z) := by group
      _ = t * (z * s) := by rw [hsz]
      _ = (t * z) * s := by group
  have hconj : centralizer ({t * z} : Set G) =
      CFSG.conjugate (centralizer ({t} : Set G)) g := by
    rw [← hg, conjugate_centralizer_singleton]
  have hcard : Nat.card (centralizer ({t * z} : Set G)) =
      Nat.card (centralizer ({t} : Set G)) := by
    rw [hconj]
    unfold CFSG.conjugate
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({t} : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr hctx.sylow
  have hcardS : Nat.card S =
      2 ^ (Nat.card (centralizer ({t * z} : Set G))).factorization 2 := by
    rw [hcard]
    exact hS.card_eq
  exact CFSG.ABGLocalTools.isSylowOf_iff.mp
    (CFSG.ABGLocalTools.isSylowOf_of_card hle hcardS)

theorem sq_mem_of_relIndex_le_two [Finite G] {C R : Subgroup G} (h : C.relIndex R ≤ 2) {y : G}
    (hy : y ∈ R) : y * y ∈ C := by
  let K : Subgroup ↥R := C.subgroupOf R
  have hrel : C.relIndex R = K.index := rfl
  have hindex : K.index ≤ 2 := hrel ▸ h
  have hcases : K.index = 1 ∨ K.index = 2 := by
    have h0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  rcases hcases with h1 | h2
  · have htop : K = ⊤ := Subgroup.index_eq_one.mp h1
    have hyK : (⟨y, hy⟩ : ↥R) ∈ K := by rw [htop]; exact Subgroup.mem_top _
    have hyC : y ∈ C := Subgroup.mem_subgroupOf.mp hyK
    exact C.mul_mem hyC hyC
  · haveI : K.Normal := Subgroup.normal_of_index_eq_two h2
    have hpow : (⟨y, hy⟩ : ↥R) ^ 2 ∈ K := by
      have hpi := K.pow_index_mem (⟨y, hy⟩ : ↥R)
      rwa [h2] at hpi
    have hyC : y * y ∈ C := by
      have hmem := Subgroup.mem_subgroupOf.mp hpow
      simpa [pow_two] using hmem
    exact hyC

end CFSG.OddStandard.SmallF3.Omega
