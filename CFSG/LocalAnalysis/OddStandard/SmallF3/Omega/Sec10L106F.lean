module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L106E

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem inv_eq_of_orderOf_eq_two {A : Type*} [Group A] [Finite A] [IsCyclic A]
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

private theorem exists_sq_eq_of_isCyclic_two [Finite G] {K : Subgroup G} (hK : IsCyclic K)
    (hK2 : IsPGroup 2 K) {t : G} (htK : t ∈ K) (ht : orderOf t = 2)
    (hne : K ≠ zpowers t) : ∃ u ∈ K, u * u = t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic K := hK
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK2
  have hle : zpowers t ≤ K := zpowers_le.2 htK
  have hn2 : 2 ≤ n := by
    by_contra hc
    push Not at hc
    have h2 : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
    have hd : Nat.card (zpowers t) ∣ Nat.card K := Subgroup.card_dvd_of_le hle
    rw [h2, hn] at hd
    interval_cases n
    · exact absurd hd (by norm_num)
    · exact hne (eq_of_le_of_card_ge hle (by rw [hn, h2]; norm_num)).symm
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  rw [hn] at hg₀
  refine ⟨((g₀ ^ 2 ^ (n - 2) : K) : G), (g₀ ^ 2 ^ (n - 2)).2, ?_⟩
  rw [← pow_two]
  have hval : (((g₀ ^ 2 ^ (n - 2) : K)) : G) ^ 2 = (((g₀ ^ 2 ^ (n - 1) : K)) : G) := by
    rw [← SubgroupClass.coe_pow, show (g₀ ^ 2 ^ (n - 2)) ^ 2 = g₀ ^ 2 ^ (n - 1) by
      rw [← pow_mul, ← pow_succ, show n - 2 + 1 = n - 1 by omega]]
  rw [hval]
  have hord : orderOf (g₀ ^ 2 ^ (n - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hg₀]; exact Nat.pow_dvd_pow 2 (by omega)),
      hg₀, Nat.pow_div (by omega) (by norm_num), show n - (n - 1) = 1 by omega, pow_one]
  have huniq := inv_eq_of_orderOf_eq_two (A := K) (x := g₀ ^ 2 ^ (n - 1))
    (y := ⟨t, htK⟩) hord (by rw [Subgroup.orderOf_mk, ht])
  exact congrArg Subtype.val huniq

private theorem isCyclic_of_isPGroup_le_centralizer [Finite G] (h102 : Asc82Lemma102)
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

theorem asc82Lemma106_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h102 : Asc82Lemma102)
    (h103 : Asc82Lemma103) (h105 : Asc82Lemma105) (hK0 : Asc82Lemma10K0) (hb : Asc82Basic10)
    (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) (hCK : Asc82FactCentK5) :
    Asc82Lemma106 := by
  intro G _ _ t L S z K1 K2 hctx
  obtain ⟨_, htC, _, htS, _, _⟩ := hb G t L S z hctx.toSec10Z
  let C : Subgroup G := centralizer (L : Set G) ⊓ S
  have hCS : C ≤ S := inf_le_right
  have hCC : C ≤ centralizer (L : Set G) := inf_le_left
  have hC2 : IsPGroup 2 C := hctx.sylow.2.1.to_le hCS
  have hCcyc : IsCyclic ↥C :=
    isCyclic_of_isPGroup_le_centralizer h102 hctx.toSec10Z.toSec10Setting hCC hC2
  have htC' : t ∈ C := ⟨htC, htS⟩
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr htC')
  intro y hy
  by_contra hyz
  have hne : C ≠ zpowers t := fun h => hyz (h ▸ hy)
  obtain ⟨x, hxC, hx2⟩ :=
    exists_sq_eq_of_isCyclic_two hCcyc hC2 htC' hctx.involution hne
  exact sec10L106_no_sq_t h36 h37 h103 h105 hK0 hP5 hC5 hCK hb hctx hxC.1 hxC.2 hx2

end CFSG.OddStandard.SmallF3.Omega
