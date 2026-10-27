module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporSieve
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporInner
import CFSG.Sporadic.Bridge.MonsterModelsGriess
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Ree.Duality
public import CFSG.Open.MonsterDefs

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

section LieSearch

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3

private def mCheck (t : StatedLieTag) (n ℓ f o : ℕ) : Bool :=
  outerFree 7 t n ℓ f && (o % 16807 != 0 || (t == .PSL && n == 4 && ℓ == 7 && f == 1))

private def mPrimes : List (ℕ × ℕ) :=
  [(2, 46), (3, 20), (5, 9), (7, 6), (11, 2), (13, 3), (17, 1), (19, 1), (23, 1), (29, 1),
    (31, 1), (41, 1), (47, 1), (59, 1), (71, 1)]

private theorem m_search :
    lieSearchV mPrimes 808017424794512875886459904961710757005754368000000000 mCheck = true := by
  decide +kernel

private theorem mCheck_of_dvd {t : StatedLieTag} {n p f : ℕ} (ht : t ∈ searchTags)
    (hp : p.Prime) (hf : 1 ≤ f) (hn : lieMin t ≤ n) (hn0 : lieMin t = 0 → n = 0)
    (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true)
    (hd : lieOrd t n (p ^ f) ∣ 808017424794512875886459904961710757005754368000000000) :
    mCheck t n p f (lieOrd t n (p ^ f)) = true := by
  refine lieSearchV_sound ?_ m_search ht hp hf hn hn0 hnB hadm hd
  refine primes_of_factorization ?_ (by decide +kernel) (by decide +kernel)
  simp only [mPrimes, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq]
  norm_num

end LieSearch

private theorem m_sporadic_orders (s : TauCeti.SporadicName) (hs : s ≠ .M) :
    ¬ 7 ^ 5 ∣ CFSG.AGLEmbeddingD2.d2SporadicOrder s := by
  cases s <;> first | exact absurd rfl hs | decide

section Monster

private theorem m_sieve_lie {T : Type} [Group T] [Finite T] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ CFSG.EvenSmallLie.CatalogOrders.searchTags) (hp : p.Prime) (hf : 1 ≤ f)
    (hn : CFSG.EvenSmallLie.CatalogOrders.lieMin t ≤ n)
    (hn0 : CFSG.EvenSmallLie.CatalogOrders.lieMin t = 0 → n = 0)
    (hnB : n ≤ CFSG.EvenSmallLie.CatalogOrders.lieExp t n + 1)
    (hadm : CFSG.EvenSmallLie.CatalogOrders.lieAdm t p f = true)
    (hcard : Nat.card T = CFSG.EvenSmallLie.CatalogOrders.lieOrd t n (p ^ f))
    (hM : CFSG.Blueprint.LieModel T t n p f)
    (hord : Nat.card T ∣ 808017424794512875886459904961710757005754368000000000) :
    (∀ α : MulAut T, α ^ 7 = 1 → α ∈ inner T) ∧ (7 ^ 5 ∣ Nat.card T →
      Nat.card T = 808017424794512875886459904961710757005754368000000000 ∨
        (Nat.card T = 2317591180800 ∧ CFSG.Blueprint.LieModel T .PSL 4 7 1)) := by
  have hC := mCheck_of_dvd ht hp hf hn hn0 hnB hadm (hcard ▸ hord)
  rw [mCheck, Bool.and_eq_true] at hC
  obtain ⟨h7free, hrest⟩ := hC
  refine ⟨fun α hα => mem_inner_of_outerFree Nat.prime_seven (by norm_num) hM ht h7free hα, ?_⟩
  intro h75
  have hmod : CFSG.EvenSmallLie.CatalogOrders.lieOrd t n (p ^ f) % 16807 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero, ← hcard]
    exact h75
  have hspec : (t == .PSL && n == 4 && p == 7 && f == 1) = true := by
    simpa [hmod] using hrest
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hspec
  obtain ⟨htPSL, hn4, hp7, hf1⟩ := hspec
  refine Or.inr ⟨?_, ?_⟩
  · rw [hcard, htPSL, hn4, hp7, hf1]
    decide +kernel
  · simpa [htPSL, hn4, hp7, hf1] using hM

private theorem false_of_reeTitsModel_twistedF4_M {T : Type} [Group T] {p f : ℕ}
    (h : CFSG.Blueprint.ReeTitsModel T .twistedF4 p f)
    (hord : Nat.card T ∣ 808017424794512875886459904961710757005754368000000000) : False := by
  obtain ⟨-, -, -, hp2, -, hiso⟩ := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier T p f h
  obtain ⟨hadm, a, hfa, K, _, _, hK, ⟨e⟩⟩ := h
  subst hp2
  have ha : 1 ≤ a := by
    have := hadm.2.2.2.2.2
    omega
  have : Fintype K := Fintype.ofFinite K
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hc := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    a K hK').1
  rw [Nat.card_congr E.toEquiv, hc] at hord
  rcases (show a = 1 ∨ 2 ≤ a by omega) with rfl | ha2
  · exact absurd ((by decide : 37 ∣ _).trans hord) (by decide)
  · have h47 : 2 ^ 47 ∣ 808017424794512875886459904961710757005754368000000000 := by
      refine (pow_dvd_pow 2 (by omega : 47 ≤ (2 * a + 1) * 12)).trans ?_
      rw [pow_mul]
      refine dvd_trans ?_ hord
      simp only [mul_assoc]
      exact dvd_mul_right _ _
    exact absurd h47 (by decide)

theorem m_sieve {T : Type} [Group T] [Finite T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a)
    (hord : Nat.card T ∣ 808017424794512875886459904961710757005754368000000000) :
    (∀ α : MulAut T, α ^ 7 = 1 → α ∈ inner T) ∧
      (7 ^ 5 ∣ Nat.card T →
        Nat.card T = 808017424794512875886459904961710757005754368000000000 ∨
          (Nat.card T = 2317591180800 ∧ CFSG.Blueprint.LieModel T .PSL 4 7 1)) := by
  rcases CFSG.EvenSmallLie.Child3.catalog_model_cases hT hnonab with
    ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, ht, hp, hf, hn, hn0, hnB, hadm, hcard, hM⟩ |
      ⟨p, f, h⟩ | ⟨p, f, h⟩ | ⟨s, ⟨e⟩⟩
  · obtain ⟨hinn, hk⟩ := alternating_sieve (r := 11) (j := 3) (k := 5) Nat.prime_seven
      (by norm_num) hn e hord (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    exact ⟨hinn, fun h75 => absurd h75 hk⟩
  · exact m_sieve_lie ht hp hf hn hn0 hnB hadm hcard hM hord
  · exact (false_of_reeTitsModel_twistedF4_M h hord).elim
  · refine ⟨fun α hα => mem_inner_of_reeTitsModel_Tits h Nat.prime_seven (by norm_num) hα,
      fun h75 => ?_⟩
    exact absurd ((dvd_pow_self 7 (by norm_num)).trans h75)
      (CFSG.EvenSmallLie.Child3.not_seven_dvd_of_reeTitsModel_Tits h)
  · by_cases hs : s = .M
    · subst hs
      have : IsSimpleGroup (Carrier .M) :=
        CFSG.Blueprint.NativeSporadic.MonsterModel.isSimpleGroup_y443Derived
      have : IsSimpleGroup T := MulEquiv.isSimpleGroup e
      have hO : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) ≤ 2 :=
        (CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple e).le.trans (by norm_num)
      refine ⟨fun α hα => mem_inner_of_card_outer_le_two Nat.prime_seven (by norm_num) hO hα,
        fun _ => Or.inl ?_⟩
      obtain ⟨g⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
      rw [Nat.card_congr g.toEquiv, CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]
      norm_num [CFSG.Open.monsterOrder]
    · refine ⟨fun α hα => mem_inner_of_mulEquiv_carrier e hs Nat.prime_seven (by norm_num) hα,
        fun h75 => ?_⟩
      rw [Nat.card_congr e.toEquiv, CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder s hs]
        at h75
      exact absurd h75 (m_sporadic_orders s hs)

end Monster

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
