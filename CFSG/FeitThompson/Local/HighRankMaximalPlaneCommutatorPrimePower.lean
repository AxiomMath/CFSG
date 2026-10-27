module

public import CFSG.FeitThompson.Local.PrimeFactorChainAutomorphismDerived
public import CFSG.FeitThompson.Local.FixedLineCharacteristicChainPrimeFactors
public import CFSG.FeitThompson.Local.RankTwoAutomorphismLinearQuotient
public import CFSG.FeitThompson.Local.CentralProductPlaneCentralizer
public import CFSG.FeitThompson.Representations.PrimeCentralTorsionCharacteristic
import CFSG.FeitThompson.Local.OddCriticalExponentSubgroup
import CFSG.FeitThompson.Local.CriticalSubgroupNarrowCentralizerLine
import CFSG.FeitThompson.Local.MaximalPlaneCommonCyclicFactor
import CFSG.FeitThompson.Foundations.FiniteHomImageOrder

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {p : ℕ} {R : Type*} [Group R] {E : Subgroup R}

theorem mem_iff_of_characteristic (K : Subgroup R) [K.Characteristic] (c : MulAut R) (x : R) :
    c x ∈ K ↔ x ∈ K := by
  have h := K.characteristic_iff_comap_eq.1 ‹K.Characteristic› c
  simpa using (Subgroup.ext_iff.1 h x)

theorem pointwise_smul_eq_of_forall_mem_iff (c : MulAut R) (K : Subgroup R)
    (h : ∀ x : R, c x ∈ K ↔ x ∈ K) : c • K = K := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have hx : (c⁻¹ : MulAut R) • x = c.symm x := rfl
  rw [hx, ← h (c.symm x), MulEquiv.apply_symm_apply]

theorem range_autRestrict_le_chainStabilizer (B : Subgroup (MulAut R)) (H : Subgroup R)
    [H.Characteristic] (K : ℕ → Subgroup R) [∀ i, (K i).Characteristic] (m : ℕ) :
    (autRestrict B H).range ≤ chainStabilizer (fun i => (K i).subgroupOf H) m := by
  rintro c ⟨a, rfl⟩
  refine mem_chainStabilizer.2 fun i _ => ?_
  refine pointwise_smul_eq_of_forall_mem_iff _ _ fun x => ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, coe_autRestrict_apply_apply]
  exact mem_iff_of_characteristic (K i) (a : MulAut R) (x : R)

theorem isPGroup_commutator_of_isPGroup_ker {G K : Type*} [Group G] [Group K] (f : G →* K)
    (hker : IsPGroup p f.ker) (h : IsPGroup p ↥(⁅f.range, f.range⁆ : Subgroup K)) :
    IsPGroup p ↥(commutator G) := by
  have hmap : Subgroup.map f (commutator G) = ⁅f.range, f.range⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
  exact (h.comap_of_ker_isPGroup f hker).to_le (hmap ▸ Subgroup.le_comap_map f (commutator G))

theorem orderOf_map_eq_of_coprime (hp : p.Prime) {G K : Type*} [Group G] [Group K] (f : G →* K)
    (hker : IsPGroup p f.ker) {x : G} (hcop : Nat.Coprime (orderOf x) p) :
    orderOf (f x) = orderOf x := by
  have := Fact.mk hp
  refine Nat.dvd_antisymm (orderOf_map_dvd f x) ?_
  set d := orderOf (f x) with hd
  have hmem : x ^ d ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow, hd, pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hker) ⟨x ^ d, hmem⟩
  have hk' : orderOf (x ^ d) = p ^ k := by
    rw [← hk, Subgroup.orderOf_coe (⟨x ^ d, hmem⟩ : f.ker)]
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact h0
    · exact absurd (Nat.Coprime.eq_one_of_dvd hcop.symm
        (dvd_trans (by rw [hk']; exact dvd_pow_self p (by omega)) (orderOf_pow_dvd d)))
        hp.one_lt.ne'
  rw [hk0, pow_zero] at hk'
  exact orderOf_dvd_of_pow_eq_one (orderOf_eq_one_iff.1 hk')

theorem isPrimeFactorChain_commutatorChain_subgroupOf [Finite R] (hp : p.Prime) (hR : IsPGroup p R)
    (H S : Subgroup R) [H.Characteristic] (hS : Nat.card S = p)
    (hCH : Nat.card (H ⊓ centralizer (S : Set R) : Subgroup R) = p)
    {m : ℕ} (hm : commutatorChain H m = ⊥) (hmin : ∀ i < m, commutatorChain H i ≠ ⊥) :
    IsPrimeFactorChain p (fun i => (commutatorChain H i).subgroupOf H) m where
  eq_top := by simp [Subgroup.subgroupOf_self]
  eq_bot := by simp [hm, Subgroup.bot_subgroupOf]
  le_succ i _ := Subgroup.comap_mono (commutatorChain_succ_le H i)
  normal_succ i _ := inferInstance
  relIndex_succ i hi := by
    rw [Subgroup.relIndex_subgroupOf (commutatorChain_le H i)]
    exact relIndex_commutatorChain_succ_eq_prime hp hR H S hS hCH (hmin i hi)

section Chain

variable {H : Subgroup R} {K : ℕ → Subgroup R} {m : ℕ} {B : Subgroup (MulAut R)}

theorem isPGroup_commutator_of_characteristic_chain (hp : p.Prime) [H.Characteristic]
    [∀ i, (K i).Characteristic]
    (hc : IsPrimeFactorChain p (fun i => (K i).subgroupOf H) m)
    (hfix : IsPGroup p ↥(fixingSubgroup (MulAut R) (H : Set R))) (B : Subgroup (MulAut R)) :
    IsPGroup p ↥(⁅B, B⁆ : Subgroup (MulAut R)) := by
  have hcomm : IsPGroup p ↥(commutator ↥B) :=
    isPGroup_commutator_of_isPGroup_ker (autRestrict B H) (isPGroup_ker_autRestrict hfix)
      (isPGroup_commutator_of_isPrimeFactorChain hp hc
        (range_autRestrict_le_chainStabilizer B H K m))
  have h := hcomm.of_equiv ((commutator ↥B).equivMapOfInjective B.subtype B.subtype_injective)
  rwa [Subgroup.map_subtype_commutator] at h

theorem prime_dvd_sub_one_of_dvd_natCard_of_characteristic_chain [Finite R] (hp : p.Prime) {q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) [H.Characteristic] [∀ i, (K i).Characteristic]
    (hc : IsPrimeFactorChain p (fun i => (K i).subgroupOf H) m)
    (hfix : IsPGroup p ↥(fixingSubgroup (MulAut R) (H : Set R)))
    (hdvd : q ∣ Nat.card ↥B) : q ∣ p - 1 := by
  have := Fact.mk hp
  set f := autRestrict B H
  have hker : IsPGroup p f.ker := isPGroup_ker_autRestrict hfix
  have hcard : Nat.card f.range * Nat.card f.ker = Nat.card ↥B := natCard_range_mul_natCard_ker f
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hker
  have hqker : ¬ q ∣ Nat.card f.ker := by
    rw [hk]
    exact fun hqd => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqd))
  have hqrange : q ∣ Nat.card f.range := by
    rcases (Nat.Prime.dvd_mul hq).1 (hcard ▸ hdvd) with h | h
    · exact h
    · exact absurd h hqker
  exact prime_dvd_sub_one_of_dvd_card hp hq hqp hc
    (range_autRestrict_le_chainStabilizer B H K m) hqrange

theorem orderOf_dvd_sub_one_of_coprime_of_characteristic_chain (hp : p.Prime) [H.Characteristic]
    [∀ i, (K i).Characteristic]
    (hc : IsPrimeFactorChain p (fun i => (K i).subgroupOf H) m)
    (hfix : IsPGroup p ↥(fixingSubgroup (MulAut R) (H : Set R)))
    {b : MulAut R} (hbB : b ∈ B) (hcop : Nat.Coprime (orderOf b) p) : orderOf b ∣ p - 1 := by
  set f := autRestrict B H
  have hker : IsPGroup p f.ker := isPGroup_ker_autRestrict hfix
  have hb : orderOf (⟨b, hbB⟩ : ↥B) = orderOf b := (Subgroup.orderOf_coe _).symm
  have h1 : orderOf (f ⟨b, hbB⟩) = orderOf b := by
    rw [orderOf_map_eq_of_coprime hp f hker (by rw [hb]; exact hcop), hb]
  have h2 : orderOf (f ⟨b, hbB⟩) ∣ p - 1 :=
    orderOf_dvd_sub_one_of_coprime hp hc (range_autRestrict_le_chainStabilizer B H K m)
      (MonoidHom.mem_range.2 ⟨⟨b, hbB⟩, rfl⟩) (by rw [h1]; exact hcop)
  rwa [h1] at h2

end Chain

theorem exists_line_le_ne_centerTorsionBy [Finite R] (hp : p.Prime) (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    ∃ S : Subgroup R, S ≤ E ∧ Nat.card S = p ∧ S ≠ centerTorsionBy R p := by
  have hZcard : Nat.card (centerTorsionBy R p) = p :=
    natCard_centerTorsionBy_of_maximal hp hRp hE hplane hrank
  have hnotle : ¬ E ≤ centerTorsionBy R p := by
    intro hle
    have h := Subgroup.card_le_of_le hle
    rw [hplane, hZcard, pow_two] at h
    nlinarith [hp.one_lt]
  obtain ⟨x, hxE, hxZ⟩ := SetLike.not_le_iff_exists.1 hnotle
  have hx1 : x ≠ 1 := fun h => hxZ (h ▸ one_mem _)
  have hord : orderOf x = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hE.prop.2 x hxE)) with h1 | h
    · exact absurd (orderOf_eq_one_iff.1 h1) hx1
    · exact h
  exact ⟨zpowers x, (zpowers_le).2 hxE, by rw [Nat.card_zpowers, hord],
    fun h => hxZ (h ▸ mem_zpowers x)⟩

theorem centralizer_sup_eq_of_le_center {S Z : Subgroup R} (hZ : Z ≤ center R) :
    centralizer ((S ⊔ Z : Subgroup R) : Set R) = centralizer (S : Set R) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  refine le_antisymm (centralizer_le Set.subset_union_left) fun x hx => ?_
  rw [mem_centralizer_iff]
  rintro y (hy | hy)
  · exact mem_centralizer_iff.1 hx y hy
  · exact (mem_center_iff.1 (hZ hy) x).symm

theorem exists_line_isCyclic_isInternalDirectProduct_centralizer [Finite R] (hp : p.Prime)
    (hodd : Odd p) (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    ∃ S Y : Subgroup R, Nat.card S = p ∧ IsCyclic ↥Y ∧
      IsInternalDirectProduct (centralizer (S : Set R)) S Y := by
  obtain ⟨S, hSE, hScard, hSZ⟩ := exists_line_le_ne_centerTorsionBy hp hRp hE hplane hrank
  have hsup : S ⊔ centerTorsionBy R p = E :=
    sup_centerTorsionBy_eq_of_natCard_eq_prime hp hRp hE hplane hrank hSE hScard hSZ
  have hcent : centralizer (E : Set R) = centralizer (S : Set R) := by
    rw [← hsup]; exact centralizer_sup_eq_of_le_center (centerTorsionBy_le_center p)
  refine ⟨S, planeCyclicFactor p E, hScard,
    isCyclic_planeCyclicFactor hp hodd hRp hE hplane hrank, ?_⟩
  have h := isInternalDirectProduct_centralizer_planeCyclicFactor hp hodd hRp hE hplane hrank
    hSE hScard hSZ
  rwa [hcent] at h

theorem exists_characteristic_isPrimeFactorChain [Finite R] (hp : p.Prime) (hodd : Odd p)
    (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    ∃ (H : Subgroup R) (_ : H.Characteristic) (m : ℕ),
      IsPrimeFactorChain p (fun i => (commutatorChain H i).subgroupOf H) m ∧
        IsPGroup p ↥(fixingSubgroup (MulAut R) (H : Set R)) := by
  classical
  have hnt : Nontrivial R := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    rw [elementaryAbelianPRank_eq_zero_of_subsingleton hp.one_lt] at hrank
    omega
  have := Fact.mk hp
  obtain ⟨a, ha⟩ := hRp.exists_card_eq
  obtain ⟨H, hH⟩ := exists_isOddCriticalExponentSubgroup hp hodd hRp
  have hchar := hH.characteristic
  obtain ⟨S, Y, hScard, hY, hC⟩ :=
    exists_line_isCyclic_isInternalDirectProduct_centralizer hp hodd hRp hE hplane hrank
  have hHcomm : ⁅(⊤ : Subgroup R), H⁆ ≤ H ⊓ centralizer (H : Set R) := by
    rw [Subgroup.commutator_comm]
    exact hH.commutator_top_le_inf_centralizer
  have hCH : Nat.card (H ⊓ centralizer (S : Set R) : Subgroup R) = p :=
    natCard_inf_centralizer_eq hp hodd ha hrank hScard hY hC hH.ne_bot hH.pow_eq_one hHcomm
  obtain ⟨n₀, -, hn₀, -, -⟩ :=
    exists_commutatorChain_eq_bot_and_relIndex_eq_prime hp hRp H S hH.ne_bot hScard hCH
  have hex : ∃ k, commutatorChain H k = ⊥ := ⟨n₀, hn₀⟩
  exact ⟨H, hchar, Nat.find hex,
    isPrimeFactorChain_commutatorChain_subgroupOf hp hRp H S hScard hCH (Nat.find_spec hex)
      (fun i hi => Nat.find_min hex hi),
    hH.isPGroup_fixingSubgroup⟩

theorem isPGroup_commutator_of_maximal_plane [Finite R] (hp : p.Prime) (hodd : Odd p)
    (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R)
    (B : Subgroup (MulAut R)) : IsPGroup p ↥(⁅B, B⁆ : Subgroup (MulAut R)) := by
  obtain ⟨H, hchar, m, hc, hfix⟩ :=
    exists_characteristic_isPrimeFactorChain hp hodd hRp hE hplane hrank
  have := hchar
  exact isPGroup_commutator_of_characteristic_chain (K := fun i => commutatorChain H i) hp hc
    hfix B

theorem exists_natCard_commutator_eq_pow_of_maximal_plane [Finite R] (hp : p.Prime) (hodd : Odd p)
    (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R)
    (B : Subgroup (MulAut R)) :
    ∃ a : ℕ, Nat.card ↥(⁅B, B⁆ : Subgroup (MulAut R)) = p ^ a := by
  have := Fact.mk hp
  exact IsPGroup.iff_card.1
    (isPGroup_commutator_of_maximal_plane hp hodd hRp hE hplane hrank B)

theorem prime_dvd_sub_one_of_dvd_natCard_of_maximal_plane [Finite R] (hp : p.Prime) (hodd : Odd p)
    (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R)
    {B : Subgroup (MulAut R)} {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hdvd : q ∣ Nat.card ↥B) :
    q ∣ p - 1 := by
  obtain ⟨H, hchar, m, hc, hfix⟩ :=
    exists_characteristic_isPrimeFactorChain hp hodd hRp hE hplane hrank
  have := hchar
  exact prime_dvd_sub_one_of_dvd_natCard_of_characteristic_chain
    (K := fun i => commutatorChain H i) hp hq hqp hc hfix hdvd

theorem orderOf_dvd_sub_one_of_coprime_of_maximal_plane [Finite R] (hp : p.Prime) (hodd : Odd p)
    (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R)
    {B : Subgroup (MulAut R)} {b : MulAut R} (hbB : b ∈ B)
    (hcop : Nat.Coprime (orderOf b) p) : orderOf b ∣ p - 1 := by
  obtain ⟨H, hchar, m, hc, hfix⟩ :=
    exists_characteristic_isPrimeFactorChain hp hodd hRp hE hplane hrank
  have := hchar
  exact orderOf_dvd_sub_one_of_coprime_of_characteristic_chain
    (K := fun i => commutatorChain H i) hp hc hfix hbB hcop

theorem commutator_isPGroup_and_dvd_sub_one_of_maximal_plane [Finite R] (hp : p.Prime)
    (hodd : Odd p) (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative ↥A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R)
    (B : Subgroup (MulAut R)) :
    (∃ a : ℕ, Nat.card ↥(⁅B, B⁆ : Subgroup (MulAut R)) = p ^ a) ∧
      (∀ q : ℕ, q.Prime → q ≠ p → q ∣ Nat.card ↥B → q ∣ p - 1) ∧
      (∀ b ∈ B, Nat.Coprime (orderOf b) p → orderOf b ∣ p - 1) :=
  ⟨exists_natCard_commutator_eq_pow_of_maximal_plane hp hodd hRp hE hplane hrank B,
    fun _ hq hqp hdvd =>
      prime_dvd_sub_one_of_dvd_natCard_of_maximal_plane hp hodd hRp hE hplane hrank hq hqp hdvd,
    fun _ hbB hcop =>
      orderOf_dvd_sub_one_of_coprime_of_maximal_plane hp hodd hRp hE hplane hrank hbB hcop⟩

end

end CFSG.FeitThompson
