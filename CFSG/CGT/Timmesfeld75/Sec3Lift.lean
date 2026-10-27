module

public import CFSG.CGT.Timmesfeld75.Sec3Fpf
public import CFSG.CGT.Timmesfeld75.L2Three
public import CFSG.CGT.Timmesfeld75.Sec5Basic
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.SimpleCase

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

section Lift

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem Sec3.conjSubgroup_eq_of_le_mul_cfgM (hS : Sec3 T T₁) {x : G} (hx : x ∈ T ⊔ T₁)
    (hle : ∀ y ∈ conjSubgroup x T, ∃ t ∈ T, ∃ m ∈ cfgM T T₁, y = t * m) :
    conjSubgroup x T = T := by
  by_contra hne
  have hnorm : ∀ y ∈ conjSubgroup x T, y ∈ Subgroup.normalizer (T : Set G) := by
    intro y hy
    obtain ⟨t, ht, m, hm, rfl⟩ := hle y hy
    exact (Subgroup.normalizer (T : Set G)).mul_mem (Subgroup.le_normalizer ht)
      (cfgM_le_normalizer T T₁ hm)
  exact hS.not_conj_le_cfgM hx fun y hy => hS.trans x hx hne (mem_normIn.2 ⟨hy, hnorm y hy⟩)

theorem Sec3.conjSubgroup_eq_right_of_le_mul_cfgM (hS : Sec3 T T₁) {x : G} (hx : x ∈ T ⊔ T₁)
    (hle : ∀ y ∈ conjSubgroup x T, ∃ t ∈ T₁, ∃ m ∈ cfgM T T₁, y = t * m) :
    conjSubgroup x T = T₁ := by
  obtain ⟨s, hsX, hss, hsT, hsT₁⟩ := hS.exists_swap
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have h1 : conjSubgroup (s * x) T = T := by
    refine hS.conjSubgroup_eq_of_le_mul_cfgM ((T ⊔ T₁).mul_mem hsX hx) fun y hy => ?_
    rw [← conjSubgroup_conjSubgroup, mem_conjSubgroup] at hy
    obtain ⟨t, ht, m, hm, hytm⟩ := hle _ hy
    refine ⟨s * t * s⁻¹, ?_, s * m * s⁻¹, hS.cfg.conj_mem_cfgM hsX hm, ?_⟩
    · rw [← hsT₁, mem_conjSubgroup]
      simpa [mul_assoc] using ht
    · calc y = s * (s⁻¹ * y * s) * s⁻¹ := by group
        _ = s * (t * m) * s⁻¹ := by rw [hytm]
        _ = s * t * s⁻¹ * (s * m * s⁻¹) := by group
  calc conjSubgroup x T = conjSubgroup s⁻¹ (conjSubgroup (s * x) T) := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel_left]
    _ = conjSubgroup s⁻¹ T := by rw [h1]
    _ = T₁ := by rw [hsi, hsT]

end Lift

section Quotient

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

set_option quotPrecheck false in
local notation "TQ" =>
  (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

set_option quotPrecheck false in
local notation "T₁Q" =>
  (T₁.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

omit [Finite G] in
theorem exists_eq_mul_cfgM_of_map_mem {y : G} (hy : y ∈ T ⊔ T₁)
    (h : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨y, hy⟩ ∈ T₁Q) :
    ∃ t ∈ T₁, ∃ m ∈ cfgM T T₁, y = t * m := by
  obtain ⟨z, hz, hzy⟩ := h
  have h1 : (z : G)⁻¹ * y ∈ cfgM T T₁ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hzy)
  exact ⟨z, Subgroup.mem_subgroupOf.1 hz, _, h1, by group⟩

omit [Finite G] in
theorem map_mem_conjSubgroup_map {t y : G} (ht : t ∈ T ⊔ T₁) (hy : y ∈ T ⊔ T₁)
    (hyt : y ∈ conjSubgroup t T) :
    QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨y, hy⟩ ∈
      conjSubgroup (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨t, ht⟩) TQ := by
  rw [← map_conjSubgroup, conjSubgroup_subgroupOf]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hyt)

omit [Finite G] in
theorem Sec3.orderOf_eq_three_of_map (hS : Sec3 T T₁) {w : G} (hw : w ∈ T ⊔ T₁)
    (hodd : Odd (orderOf w))
    (h3 : orderOf (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨w, hw⟩) = 3) :
    orderOf w = 3 := by
  have h3' : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ((⟨w, hw⟩ : ↥(T ⊔ T₁)) ^ 3) =
      1 := by
    rw [map_pow]
    exact h3 ▸ pow_orderOf_eq_one _
  have hM3 : w ^ 3 ∈ cfgM T T₁ := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h3')
  have h6 : w ^ 6 = 1 := by
    rw [show 6 = 3 * 2 from rfl, pow_mul]
    exact hS.cfg.isElemAbelian_cfgM.2 _ hM3
  have hdvd : orderOf w ∣ 3 :=
    Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.2 hodd)
      (show orderOf w ∣ 3 * 2 from orderOf_dvd_of_pow_eq_one h6)
  have hw1 : w ≠ 1 := by
    intro hw1
    have h1 : (⟨w, hw⟩ : ↥(T ⊔ T₁)) = 1 := Subtype.ext hw1
    rw [h1, map_one, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  exact orderOf_eq_prime (orderOf_dvd_iff_pow_eq_one.1 hdvd) hw1

theorem Sec3.exists_swap_orderOf_three_of_mem (hS : Sec3 T T₁) {f : ℕ} (hf : f ≠ 0)
    (h : Nonempty (XQ ≃* PSL(2, GaloisField 2 f))) {a : G} (haT : a ∈ T)
    (haM : a ∉ cfgM T T₁) :
    ∃ t ∈ T ⊔ T₁, t * t = 1 ∧ conjSubgroup t T = T₁ ∧ orderOf (a * t) = 3 := by
  have hX := hS.isL2Pair_quotient hf h
  obtain ⟨s, hsX, -, hsT, -⟩ := hS.exists_swap
  have haX : a ∈ T ⊔ T₁ := Subgroup.mem_sup_left haT
  have hsb : conjSubgroup (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨s, hsX⟩) TQ =
      T₁Q := by
    rw [← map_conjSubgroup, conjSubgroup_subgroupOf, hsT]
  have hsbne : conjSubgroup (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨s, hsX⟩) TQ ≠
      TQ := by
    rw [hsb]
    exact hS.map_ne_map
  have hab : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨a, haX⟩ ∈ TQ :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 haT)
  have hab1 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨a, haX⟩ ≠ 1 := fun h1 =>
    haM (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1))
  obtain ⟨tb, htb, hconj, hord⟩ := hX.exists_swap_orderOf_three hab hab1 hsbne
  have htb1 : tb ≠ 1 := by
    rintro rfl
    apply hsbne
    rw [← hconj, conjSubgroup_one]
  obtain ⟨x, hx, t, htX, htx, htM, htt, hπt⟩ := hS.exists_lift_involution hX htb htb1
  have hconjt : conjSubgroup t T = T₁ := by
    refine hS.conjSubgroup_eq_right_of_le_mul_cfgM htX fun y hy => ?_
    have hyX : y ∈ T ⊔ T₁ := conjSubgroup_le_of_le_of_mem le_sup_left htX hy
    refine exists_eq_mul_cfgM_of_map_mem hyX ?_
    have := map_mem_conjSubgroup_map htX hyX hy
    rwa [hπt, hconj, hsb] at this
  refine ⟨t, htX, htt, hconjt, ?_⟩
  have htT : t ∉ T := fun htT => hS.cfg.left_ne_right
    ((mem_normalizer_iff_conjSubgroup_eq.1 (Subgroup.le_normalizer htT)).symm.trans hconjt)
  have hne : conjSubgroup 1 T ≠ conjSubgroup x T := by
    rw [conjSubgroup_one]
    exact fun heq => htT (heq ▸ htx)
  have hodd : Odd (orderOf (a * t)) :=
    hS.odd_orderOf_mul (one_mem _) hx hne (by rwa [conjSubgroup_one]) haM htx htM
  have hatX : a * t ∈ T ⊔ T₁ := (T ⊔ T₁).mul_mem haX htX
  refine hS.orderOf_eq_three_of_map hatX hodd ?_
  have hmul : (⟨a * t, hatX⟩ : ↥(T ⊔ T₁)) = ⟨a, haX⟩ * ⟨t, htX⟩ := rfl
  rw [hmul, map_mul, hπt, hord]

end Quotient

end CFSG.CGT.Timmesfeld75
