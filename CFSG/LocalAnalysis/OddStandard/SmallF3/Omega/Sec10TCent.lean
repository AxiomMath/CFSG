module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem tc_inv_eq_of_orderOf_eq_two {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {x y : A} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  haveI : Fintype A := Fintype.ofFinite A
  have hd : 2 ∣ Fintype.card A := hx ▸ orderOf_dvd_card
  have h := IsCyclic.card_orderOf_eq_totient (α := A) (d := 2) hd
  rw [Nat.totient_two] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hxa : x ∈ ({a} : Finset A) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hya : y ∈ ({a} : Finset A) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  rw [Finset.mem_singleton] at hxa hya
  rw [hxa, hya]

private theorem tc_isCyclic_of_isPGroup_le_centralizer [Finite G] (h102 : Asc82Lemma102)
    {t : G} {L : Subgroup G} (hset : Sec10Setting G t L) {X : Subgroup G}
    (hX : X ≤ centralizer (L : Set G)) (hX2 : IsPGroup 2 X) : IsCyclic ↥X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX'2 : IsPGroup 2 (X.subgroupOf (centralizer (L : Set G))) :=
    hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hX).symm
  obtain ⟨Q, hQle⟩ := hX'2.exists_le_sylow
  have hQcyc : IsCyclic ↥(Q : Subgroup (centralizer (L : Set G))) := h102 G t L hset Q
  haveI : IsCyclic ↥(Q : Subgroup (centralizer (L : Set G))) := hQcyc
  have hX'cyc : IsCyclic ↥(X.subgroupOf (centralizer (L : Set G))) :=
    Subgroup.isCyclic_of_le hQle
  haveI : IsCyclic ↥(X.subgroupOf (centralizer (L : Set G))) := hX'cyc
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hX)
    (Subgroup.subgroupOfEquivOfLe hX).surjective

private theorem tc_zpowers_eq_one_or_self {H : Type} [Group H] {t : H} (ht : orderOf t = 2)
    {p : H} (hp : p ∈ Subgroup.zpowers t) : p = 1 ∨ p = t := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  have ht2 : t ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    rw [← hk, hm, zpow_mul, ht2, one_zpow]
  · right
    rw [← hk, hm, zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

theorem sec10T_invol_cent_eq [Finite G] (h102 : Asc82Lemma102) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {c : G}
    (hcS : c ∈ S) (hcC : c ∈ centralizer (L : Set G)) (hc2 : orderOf c = 2) : c = t := by
  obtain ⟨hpsp, htC, htnotL, htS, hN, hsyl⟩ := hb G t L S z hctx.toSec10Z
  let X : Subgroup G := zpowers c ⊔ zpowers t
  have hXcent : X ≤ centralizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hcC) (Subgroup.zpowers_le.mpr htC)
  have hXS : X ≤ S := sup_le (Subgroup.zpowers_le.mpr hcS) (Subgroup.zpowers_le.mpr htS)
  have hX2 : IsPGroup 2 X := hctx.sylow.2.1.to_le hXS
  haveI : IsCyclic ↥X :=
    tc_isCyclic_of_isPGroup_le_centralizer h102 hctx.toSec10Z.toSec10Setting hXcent hX2
  have hcX : c ∈ X := Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have htX : t ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hx2 : orderOf (⟨c, hcX⟩ : ↥X) = 2 := by rw [Subgroup.orderOf_mk, hc2]
  have hy2 : orderOf (⟨t, htX⟩ : ↥X) = 2 := by rw [Subgroup.orderOf_mk, hctx.involution]
  have hxy := tc_inv_eq_of_orderOf_eq_two (A := ↥X) (x := ⟨c, hcX⟩) (y := ⟨t, htX⟩) hx2 hy2
  exact congrArg Subtype.val hxy

private theorem tc_cent_sq_eq_one_or_eq_t [Finite G] (h102 : Asc82Lemma102) (hb : Asc82Basic10)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2)
    {c : G} (hcS : c ∈ S) (hcC : c ∈ centralizer (L : Set G)) (hc2 : c * c = 1) :
    c = 1 ∨ c = t := by
  have hdvd : orderOf c ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hc2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact Or.inl (orderOf_eq_one_iff.mp h1)
  · exact Or.inr (sec10T_invol_cent_eq h102 hb hctx hcS hcC h2)

theorem sec10T_cent_case [Finite G] (h102 : Asc82Lemma102) (hb : Asc82Basic10)
    (hCK : Asc82FactCentK5) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) {s : G} (hs : s ∈ S) (hs2 : s * s = 1)
    (h1 : ∀ k ∈ K1, s * k = k * s) (h2 : ∀ k ∈ K2, s * k = k * s) :
    s = 1 ∨ s = z ∨ s = t ∨ s = t * z := by
  obtain ⟨hpsp, htC, htnotL, htS, hN, hsyl⟩ := hb G t L S z hctx.toSec10Z
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hsN : s ∈ normalizer (L : Set G) := hN hs
  have hcomm : ∀ k ∈ K1 ⊔ K2, s * k = k * s := by
    have hle : K1 ⊔ K2 ≤ Subgroup.centralizer ({s} : Set G) :=
      sup_le (fun k hk => by
              rw [Subgroup.mem_centralizer_singleton_iff]; exact (h1 k hk).symm)
             (fun k hk => by
              rw [Subgroup.mem_centralizer_singleton_iff]; exact (h2 k hk).symm)
    intro k hk
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hk)).symm
  have hsup : s ∈ centralizer (L : Set G) ⊔ zpowers z :=
    hCK G L hpsp z hz2 K1 K2 hctx.pocket1 hctx.pocket2 hctx.ne s hsN hcomm
  have hcommL : ∀ b ∈ centralizer (L : Set G), b * z = z * b := by
    intro b hb'
    exact (Subgroup.mem_centralizer_iff.mp hb' z hzL).symm
  rw [mem_sup_zpowers_iff_of_commute (B := centralizer (L : Set G)) (t := z) hcommL] at hsup
  obtain ⟨b, hbC, i, hbeq⟩ := hsup
  have hzpow : z ^ i = 1 ∨ z ^ i = z :=
    tc_zpowers_eq_one_or_self hz2 (Subgroup.zpow_mem_zpowers z i)
  rcases hzpow with hzpow | hzpow
  · have hbs : s = b := by rw [hbeq, hzpow, mul_one]
    have hbS : b ∈ S := hbs ▸ hs
    have hb2 : b * b = 1 := hbs ▸ hs2
    rcases tc_cent_sq_eq_one_or_eq_t h102 hb hctx hbS hbC hb2 with hb1 | hbt
    · exact Or.inl (by rw [hbs, hb1])
    · exact Or.inr (Or.inr (Or.inl (by rw [hbs, hbt])))
  · have hbeqz : s = b * z := by rw [hbeq, hzpow]
    have hbS : b ∈ S := by
      have hb_eq : b = s * z⁻¹ := by rw [hbeqz]; group
      rw [hb_eq]
      exact S.mul_mem hs (S.inv_mem hctx.mem_S)
    have hzb : z * b = b * z := Subgroup.mem_centralizer_iff.mp hbC z hzL
    have hzsq : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
    have hb2 : b * b = 1 := by
      have h : (b * z) * (b * z) = 1 := by rw [← hbeqz]; exact hs2
      have h2 : (b * z) * (b * z) = b * b * (z * z) := by
        calc (b * z) * (b * z) = b * (z * b) * z := by group
          _ = b * (b * z) * z := by rw [hzb]
          _ = b * b * (z * z) := by group
      rw [hzsq, mul_one] at h2
      exact h2 ▸ h
    rcases tc_cent_sq_eq_one_or_eq_t h102 hb hctx hbS hbC hb2 with hb1 | hbt
    · exact Or.inr (Or.inl (by rw [hbeqz, hb1, one_mul]))
    · exact Or.inr (Or.inr (Or.inr (by rw [hbeqz, hbt])))

end CFSG.OddStandard.SmallF3.Omega
