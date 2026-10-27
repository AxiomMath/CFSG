module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson.Prep03 Subgroup
  Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem mul_comm_of_mem_kappaA {KT : Subgroup G → Subgroup G} {V : Subgroup G} {a b : G}
    (ha : a ∈ kappaA KT V) (hb : b ∈ KT V) : a * b = b * a :=
  (mem_centralizer_iff.1 (Subgroup.mem_inf.1 ha).2 b hb).symm

theorem kappaHall_le_normalizer_kappaA {KT : Subgroup G → Subgroup G} {V : Subgroup G} :
    KT V ≤ normalizer ((kappaA KT V : Subgroup G) : Set G) :=
  le_trans (fun _ hb => mem_centralizer_iff.2 fun _ ha => mul_comm_of_mem_kappaA ha hb)
    (centralizer_le_normalizer _)

theorem exists_mul_eq_of_mem_sup_kappaA {KT : Subgroup G → Subgroup G} {V : Subgroup G} {t : G}
    (ht : t ∈ (KT V ⊔ kappaA KT V : Subgroup G)) :
    ∃ a ∈ kappaA KT V, ∃ b ∈ KT V, t = a * b := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left (kappaA KT V) (KT V)
    kappaHall_le_normalizer_kappaA
  have ht' : t ∈ ((kappaA KT V ⊔ KT V : Subgroup G) : Set G) := by rw [sup_comm]; exact ht
  rw [h] at ht'
  obtain ⟨a, ha, b, hb, hab⟩ := ht'
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem exists_prime_card_subgroup_le_zpowers {t : G} (ht : t ≠ 1) :
    ∃ X : Subgroup G, X ≤ zpowers t ∧ (Nat.card X).Prime := by
  have hord : orderOf t ≠ 1 := by simpa [orderOf_eq_one_iff] using ht
  have hq : Nat.Prime (orderOf t).minFac := Nat.minFac_prime hord
  obtain ⟨x, hx, hxo⟩ := exists_mem_orderOf_eq_of_dvd (H := zpowers t) hq
    (by rw [Nat.card_zpowers]; exact Nat.minFac_dvd _)
  exact ⟨zpowers x, zpowers_le.2 hx, by rw [Nat.card_zpowers, hxo]; exact hq⟩

theorem not_le_kappaHall_of_le_sigmaCore {T L X : Subgroup G}
    (hHall : IsHallPiOf (kappaPrimes T) L T) (hp : (Nat.card X).Prime)
    (hXS : X ≤ sigmaCore T) : ¬ X ≤ L := by
  intro hXL
  have hκ : Nat.card X ∈ kappaPrimes T :=
    hHall.2.1 _ (Nat.mem_primeFactors.2 ⟨hp, card_dvd_of_le hXL, Nat.card_pos.ne'⟩)
  have hσ : Nat.card X ∈ sigmaPrimes T :=
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore T) _
      (Nat.mem_primeFactors.2 ⟨hp, card_dvd_of_le hXS, Nat.card_pos.ne'⟩)
  exact Set.disjoint_left.1 (disjoint_kappaPrimes_sigmaPrimes T) hκ hσ

theorem mul_mem_mixedTorusSet {Z : Subgroup G} {I : Set (Subgroup G)}
    {KT : Subgroup G → Subgroup G}
    (hKZ : ∀ V ∈ I, KT V ≤ Z) (hAZ : ∀ V ∈ I, kappaA KT V ≤ Z)
    (hKA : ∀ V ∈ I, KT V ⊓ kappaA KT V = ⊥)
    (hAK : ∀ V ∈ I, ∀ W ∈ I, V ≠ W → kappaA KT V ≤ KT W)
    {V : Subgroup G} (hV : V ∈ I) {a b : G} (ha : a ∈ kappaA KT V) (ha1 : a ≠ 1)
    (hb : b ∈ KT V) (hb1 : b ≠ 1) : a * b ∈ mixedTorusSet Z I KT := by
  have hdisj : ∀ W ∈ I, ∀ x : G, x ∈ KT W → x ∈ kappaA KT W → x = 1 := by
    intro W hW x hx hx'
    simpa using ((hKA W hW) ▸ Subgroup.mem_inf.2 ⟨hx, hx'⟩ : x ∈ (⊥ : Subgroup G))
  have hab1 : a * b ≠ 1 := fun h =>
    hb1 (hdisj V hV b hb (by simpa [eq_inv_of_mul_eq_one_right h] using inv_mem ha))
  refine ⟨⟨mul_mem (hAZ V hV ha) (hKZ V hV hb), hab1⟩, ?_⟩
  simp only [Set.mem_iUnion, not_exists]
  intro W hW hmem
  obtain ⟨hW', -⟩ := hmem
  by_cases hWV : W = V
  ·
    subst hWV
    exact hb1 (hdisj W hW b hb (by
      have hbe : b = a⁻¹ * (a * b) := by group
      rw [hbe]; exact mul_mem (inv_mem ha) hW'))
  ·
    exact ha1 (hdisj V hV a (by
      have hae : a = a * b * b⁻¹ := by group
      rw [hae]
      exact mul_mem (hAK W hW V hV hWV hW') (inv_mem hb)) ha)

theorem mixedTorusSet_eq {M K Z : Subgroup G} {I : Set (Subgroup G)}
    {KT : Subgroup G → Subgroup G}
    (hM : M ∈ I) (hKTM : KT M = K)
    (hKZ : ∀ V ∈ I, KT V ≤ Z) (hAZ : ∀ V ∈ I, kappaA KT V ≤ Z)
    (hsup : ∀ V ∈ I, KT V ⊔ kappaA KT V = Z)
    (hKA : ∀ V ∈ I, KT V ⊓ kappaA KT V = ⊥)
    (hAK : ∀ V ∈ I, ∀ W ∈ I, V ≠ W → kappaA KT V ≤ KT W)
    (hHall : ∀ T ∈ I, T ≠ M → IsHallPiOf (kappaPrimes T) (KT T) T)
    (hprime : ∀ X : Subgroup G, X ≤ K → (Nat.card X).Prime →
      ∃ T ∈ I, T ≠ M ∧ X ≤ sigmaCore T) :
    mixedTorusSet Z I KT
      = ⋃ V ∈ I, {x : G | ∃ a ∈ kappaA KT V, a ≠ 1 ∧ ∃ b ∈ KT V, b ≠ 1 ∧ x = a * b} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro t ht
    obtain ⟨⟨htZ, ht1⟩, htA⟩ := ht
    have ht1' : t ≠ 1 := by simpa using ht1
    obtain ⟨V, hV, htKV⟩ : ∃ V ∈ I, t ∉ KT V := by
      by_cases htK : t ∈ K
      · obtain ⟨X, hXt, hXp⟩ := exists_prime_card_subgroup_le_zpowers ht1'
        obtain ⟨T, hT, hTM, hTS⟩ := hprime X (hXt.trans (zpowers_le.2 htK)) hXp
        exact ⟨T, hT, fun htKT => not_le_kappaHall_of_le_sigmaCore (hHall T hT hTM) hXp hTS
          (hXt.trans (zpowers_le.2 htKT))⟩
      · exact ⟨M, hM, by rwa [hKTM]⟩
    refine Set.mem_biUnion hV ?_
    have htZ' : t ∈ (KT V ⊔ kappaA KT V : Subgroup G) := by rw [hsup V hV]; exact htZ
    obtain ⟨a, ha, b, hb, hba⟩ := exists_mul_eq_of_mem_sup_kappaA htZ'
    have hb1 : b ≠ 1 := by
      intro h
      subst h
      rw [mul_one] at hba
      exact htA (Set.mem_biUnion hV ⟨hba ▸ ha, by simpa [← hba] using ht1'⟩)
    have ha1 : a ≠ 1 := by
      intro h
      subst h
      rw [one_mul] at hba
      exact htKV (hba ▸ hb)
    exact ⟨a, ha, ha1, b, hb, hb1, hba⟩
  · refine Set.iUnion₂_subset fun V hV => ?_
    rintro x ⟨a, ha, ha1, b, hb, hb1, rfl⟩
    exact mul_mem_mixedTorusSet hKZ hAZ hKA hAK hV ha ha1 hb hb1

theorem ncard_sdiff_one_add_one {X : Subgroup G} :
    (((X : Set G)) \ {1}).ncard + 1 = Nat.card X := by
  have h : Nat.card X = ((X : Set G)).ncard := by rw [← Nat.card_coe_set_eq]; rfl
  rw [h]
  exact Set.ncard_sdiff_singleton_add_one X.one_mem (Set.toFinite _)

theorem ncard_mixedTorusSet {Z : Subgroup G} {I : Set (Subgroup G)}
    {KT : Subgroup G → Subgroup G} (hI : I.Finite)
    (hAZ : ∀ V ∈ I, kappaA KT V ≤ Z)
    (hpd : ∀ V ∈ I, ∀ W ∈ I, V ≠ W → kappaA KT V ⊓ kappaA KT W = ⊥) :
    ((mixedTorusSet Z I KT).ncard : ℤ)
      = (Nat.card Z : ℤ) + (I.ncard : ℤ) - 1 - ∑ᶠ V ∈ I, (Nat.card (kappaA KT V) : ℤ) := by
  classical
  set U : Set G := ⋃ V ∈ I, ((kappaA KT V : Set G) \ {1}) with hU
  have hUsub : U ⊆ ((Z : Set G)) \ {1} := by
    simp only [hU, Set.iUnion_subset_iff]
    exact fun V hV x hx => ⟨hAZ V hV hx.1, hx.2⟩
  have hsplit : (mixedTorusSet Z I KT).ncard + U.ncard = (((Z : Set G)) \ {1}).ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hUsub (Set.toFinite _)
  have hpdisj : I.PairwiseDisjoint (fun V => ((kappaA KT V : Set G) \ {1})) := by
    intro V hV W hW hVW
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    have hmem : x ∈ (kappaA KT V ⊓ kappaA KT W : Subgroup G) := Subgroup.mem_inf.2 ⟨hx.1, hx'.1⟩
    rw [hpd V hV W hW hVW] at hmem
    exact hx.2 (by simpa using hmem)
  have hUcard : U.ncard = ∑ V ∈ hI.toFinset, (((kappaA KT V : Set G)) \ {1}).ncard := by
    rw [hU, Set.Finite.ncard_biUnion hI (fun _ _ => Set.toFinite _) hpdisj,
      finsum_mem_eq_finite_toFinset_sum _ hI]
  have hsum : ∑ᶠ V ∈ I, (Nat.card (kappaA KT V) : ℤ)
      = ∑ V ∈ hI.toFinset, (Nat.card (kappaA KT V) : ℤ) :=
    finsum_mem_eq_finite_toFinset_sum _ hI
  have hIcard : (I.ncard : ℤ) = (hI.toFinset.card : ℤ) := by
    rw [Set.ncard_eq_toFinset_card I hI]
  have hZ : (((Z : Set G)) \ {1}).ncard + 1 = Nat.card Z := ncard_sdiff_one_add_one
  have hstep : ∀ V ∈ hI.toFinset, ((((kappaA KT V : Set G)) \ {1}).ncard : ℤ)
      = (Nat.card (kappaA KT V) : ℤ) - 1 := by
    intro V _
    have := ncard_sdiff_one_add_one (X := kappaA KT V)
    omega
  have hUz : (U.ncard : ℤ)
      = (∑ V ∈ hI.toFinset, (Nat.card (kappaA KT V) : ℤ)) - (hI.toFinset.card : ℤ) := by
    rw [hUcard]
    push_cast
    rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have h1 : ((mixedTorusSet Z I KT).ncard : ℤ) + (U.ncard : ℤ)
      = ((((Z : Set G)) \ {1}).ncard : ℤ) := by
    push_cast [← hsplit]
    ring
  rw [hsum, hIcard]
  omega

theorem FNI_kappa_candidate_mixed_set_description
    (h₁ : Statements.FNI_kappa_candidate_family_common_factors.{u}) :
    Statements.FNI_kappa_candidate_mixed_set_description.{u} := by
  intro G _ _ M K A Z I KT hs
  obtain ⟨-, hIcard, hmain, hprime⟩ := h₁ G M K A Z I hs.base hs.I_eq
  obtain ⟨-, hb, hc⟩ := hmain KT hs.KT_self hs.KT_hall
  have hM : M ∈ I := by rw [hs.I_eq]; exact Or.inl rfl
  have hKZ : ∀ V ∈ I, KT V ≤ Z := fun V hV => (hb V hV).2.1.1
  have hAZ : ∀ V ∈ I, kappaA KT V ≤ Z := fun V hV => (hb V hV).2.1.2.1
  have hsup : ∀ V ∈ I, KT V ⊔ kappaA KT V = Z := fun V hV => (hb V hV).2.1.2.2.1
  have hKA : ∀ V ∈ I, KT V ⊓ kappaA KT V = ⊥ := fun V hV => (hb V hV).2.1.2.2.2.1
  have hAK : ∀ V ∈ I, ∀ W ∈ I, V ≠ W → kappaA KT V ≤ KT W :=
    fun V hV W hW hVW => (hc V hV W hW hVW).2.1
  have hpd : ∀ V ∈ I, ∀ W ∈ I, V ≠ W → kappaA KT V ⊓ kappaA KT W = ⊥ :=
    fun V hV W hW hVW => (hc V hV W hW hVW).1
  refine ⟨mixedTorusSet_eq hM hs.KT_self hKZ hAZ hsup hKA hAK
      (fun T hT hTM => (hs.KT_hall T hT hTM).1)
      (fun X hXK hXp => by
        obtain ⟨T, hT, hTM, -, hTS⟩ := hprime X hXK hXp
        exact ⟨T, hT, hTM, hTS⟩), ?_,
    ncard_mixedTorusSet (Set.toFinite I) hAZ hpd⟩
  obtain ⟨V, hV, hVM⟩ := Set.exists_ne_of_one_lt_ncard (s := I) (by omega) M
  obtain ⟨⟨a, haM⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hb M hM).1
  obtain ⟨⟨c, hcV⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hb V hV).1
  exact ⟨c * a, mul_mem_mixedTorusSet hKZ hAZ hKA hAK hV hcV (by simpa using hc1)
    (hAK M hM V hV (Ne.symm hVM) haM) (by simpa using ha1)⟩

end

end CFSG.FeitThompson.Proofs
