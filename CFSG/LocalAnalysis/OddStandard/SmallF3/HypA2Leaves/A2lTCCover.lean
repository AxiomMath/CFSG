module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCBasic
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatAltCover
public import CFSG.Holt.OddCoreTwoGroupBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint Equiv

private theorem isSimple_of_lieModel {Q : Type} [Group Q] {t : Open.StatedLieTag} {n p f : ℕ}
    (hn : n ≠ 0) (h : LieModel Q t n p f) : IsSimpleGroup Q :=
  (CFSG.LieType.Simplicity.fam_classical_converse Q
    ⟨t, n, p, f, GH74.statedClassicalModel_of_lieModel hn h⟩).2.2

private theorem center_eq_bot_of_simple_of_quot {Q : Type} [Group Q] [IsSimpleGroup Q]
    (h : 1 < Nat.card (Q ⧸ center Q)) : center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with hb | ht
  · exact hb
  · exfalso
    have : Subsingleton (Q ⧸ center Q) := by
      rw [ht]
      exact QuotientGroup.subsingleton_quotient_top
    exact absurd h (by rw [Nat.card_unique]; exact lt_irrefl _)

private theorem one_lt_card_of_tcSmall {Q : Type} [Group Q] (h : TCSmall Q) : 1 < Nat.card Q := by
  rcases a2l_card_tcSmall h with h | h | h <;> omega

theorem a2l_center_core_quot {X : Type} [Group X] [Finite X] (hX : HypA2.IsFStar X)
    (hS : TCSmall (X ⧸ Open.fusionZStar X)) : center (X ⧸ pPrimeCore 2 X) = ⊥ := by
  have hQ : TCSmall ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) :=
    hS.of_mulEquiv (ComponentClassification.Sol78.coreQuotientCenterEquiv X).symm
  have key : ∀ [IsSimpleGroup (X ⧸ pPrimeCore 2 X)], center (X ⧸ pPrimeCore 2 X) = ⊥ :=
    fun {_} => center_eq_bot_of_simple_of_quot (one_lt_card_of_tcSmall hQ)
  unfold HypA2.IsFStar at hX
  rcases hX with h1 | h2 | h3 | h4 | h5 | ⟨-, h6⟩
  · haveI := isSimple_of_lieModel (by norm_num) h1; exact key
  · haveI := isSimple_of_lieModel (by norm_num) h2; exact key
  · haveI := isSimple_of_lieModel (by norm_num) h3; exact key
  · haveI := isSimple_of_lieModel (by norm_num) h4; exact key
  · unfold SmallF3OmegaQuotient at h5
    rcases h5 with h | h | h | h | h | h <;>
      · haveI := isSimple_of_lieModel (by norm_num) h; exact key
  · exfalso
    have hc : Nat.card ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) = 3265920 := by
      rw [GH74.card_of_lieModel_PSU (G := (X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X))
        (n := 4) (p := 3) (f := 1) (by norm_num) (by norm_num) h6]
      decide
    rcases a2l_card_tcSmall hQ with h | h | h <;> omega

theorem a2l_eq_one_of_mem_center {K : Type} [Group K] [Finite K] (hZ : IsPGroup 2 ↥(center K))
    {X : Subgroup K} (hX : HypA2.IsFStar ↥X) (hS : TCSmall (↥X ⧸ Open.fusionZStar ↥X)) {x : ↥X}
    (hx : (x : K) ∈ center K) : x = 1 := by
  have hcen := a2l_center_core_quot hX hS
  have hxc : (QuotientGroup.mk' (pPrimeCore 2 ↥X)) x ∈ center (↥X ⧸ pPrimeCore 2 ↥X) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥X) q
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hx (y : K)
  rw [hcen, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Holt.OddCoreHull.eq_one_of_mem_pPrimeCore (W := X) (P := center K) hZ hx hxc

theorem a2l_center_eq_bot_of_lift {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ : IsPGroup 2 ↥(center K)) {m : ℕ} (hm : 4 ≤ m)
    (θ : K ⧸ center K ≃* alternatingGroup (Fin (m + 2))) {g : K} (hg : g * g = 1)
    {p q s t : Fin (m + 2)} (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t) (hqs : q ≠ s) (hqt : q ≠ t)
    (hst : s ≠ t)
    (hgθ : ((θ (QuotientGroup.mk g) : alternatingGroup (Fin (m + 2))) : Perm (Fin (m + 2))) =
      swap p q * swap s t) : center K = ⊥ := by
  haveI : Group.IsPerfect K := hK.1
  let η : K →* alternatingGroup (Fin (m + 2)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hη : Function.Surjective η :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (center K))
  have hker : η.ker = center K := by
    ext k
    rw [MonoidHom.mem_ker]
    change θ (QuotientGroup.mk k) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hK2 : IsPGroup 2 η.ker := by rw [hker]; exact hZ
  have hbot := ComponentClassification.SolMax.FiveCat.altCover_ker_eq_bot_of_involution_lift hm η
    hη (hker ▸ le_rfl) hK2 hpq hps hpt hqs hqt hst hg hgθ
  rwa [hker] at hbot

theorem a2l_center_eq_bot_of_lift_deg {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ : IsPGroup 2 ↥(center K)) {n : ℕ} (hn : 6 ≤ n)
    (θ : K ⧸ center K ≃* alternatingGroup (Fin n)) {g : K} (hg : g * g = 1)
    {p q s t : Fin n} (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t) (hqs : q ≠ s) (hqt : q ≠ t)
    (hst : s ≠ t)
    (hgθ : ((θ (QuotientGroup.mk g) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      swap p q * swap s t) : center K = ⊥ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact a2l_center_eq_bot_of_lift hK hZ (by omega) θ hg hpq hps hpt hqs hqt hst hgθ

theorem a2l_doubleSwap_sq {n : ℕ} {p q s t : Fin n} (hpq : p ≠ q) (hst : s ≠ t) (hps : p ≠ s)
    (hpt : p ≠ t) (hqs : q ≠ s) (hqt : q ≠ t) :
    (swap p q * swap s t) * (swap p q * swap s t) = (1 : Perm (Fin n)) := by
  have hd : (swap p q).Disjoint (swap s t) := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support, Equiv.Perm.support_swap hpq,
      Equiv.Perm.support_swap hst, Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl <;> simp_all
  rw [← sq, hd.commute.mul_pow, sq, sq, swap_mul_self, swap_mul_self, mul_one]

theorem a2l_exists_involution_lift {K : Type} [Group K] [Finite K] (hZ : IsPGroup 2 ↥(center K))
    {X : Subgroup K} (hX : HypA2.IsFStar ↥X) (hS : TCSmall (↥X ⧸ Open.fusionZStar ↥X))
    {u : K ⧸ center K} (hu : u ∈ X.map (QuotientGroup.mk' (center K))) (hu2 : u * u = 1) :
    ∃ g : K, g * g = 1 ∧ QuotientGroup.mk' (center K) g = u := by
  obtain ⟨x, hx, rfl⟩ := hu
  refine ⟨x, ?_, rfl⟩
  have hc : ((⟨x * x, X.mul_mem hx hx⟩ : ↥X) : K) ∈ center K := by
    change x * x ∈ center K
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (center K) (x * x) = 1
    rw [map_mul]
    exact hu2
  exact congrArg Subtype.val (a2l_eq_one_of_mem_center hZ hX hS hc)

end CFSG.OddStandard.SmallF3.HypA2Leaves
