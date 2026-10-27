module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporSieve
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporInner
import CFSG.Quasithin.Background.FourListSporadicPfM

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section LieSearchB

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)

private def bCheck (t : StatedLieTag) (n ℓ f o : ℕ) : Bool :=
  o % 5 != 0 || (outerFree 5 t n ℓ f && (o % 3125 != 0 ||
    ((t == .PSL && n == 4 && ℓ == 5 && f == 1) ||
     (t == .PSU && n == 4 && ℓ == 5 && f == 1) ||
     (t == .PSL && n == 3 && ℓ == 5 && f == 2) ||
     (t == .G2 && n == 0 && ℓ == 5 && f == 1))))

private def bPrimes : List (ℕ × ℕ) :=
  [(2, 41), (3, 13), (5, 6), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1),
    (47, 1)]

private theorem b_search :
    lieSearchV bPrimes 4154781481226426191177580544000000 bCheck = true := by
  decide +kernel

private theorem bCheck_of_dvd {t : StatedLieTag} {n p f : ℕ} (ht : t ∈ searchTags)
    (hp : p.Prime) (hf : 1 ≤ f) (hn : lieMin t ≤ n) (hn0 : lieMin t = 0 → n = 0)
    (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true)
    (hd : lieOrd t n (p ^ f) ∣ 4154781481226426191177580544000000) :
    bCheck t n p f (lieOrd t n (p ^ f)) = true := by
  refine lieSearchV_sound ?_ b_search ht hp hf hn hn0 hnB hadm hd
  refine primes_of_factorization ?_ (by decide +kernel) (by decide +kernel)
  simp only [bPrimes, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq]
  norm_num

end LieSearchB

private theorem b_sporadic_orders (s : TauCeti.SporadicName) (hs : s ≠ .M)
    (hsB : s ≠ .B) (hsHN : s ≠ .HN)
    (hd : CFSG.AGLEmbeddingD2.d2SporadicOrder s ∣ 4154781481226426191177580544000000) :
    ¬ 5 ^ 5 ∣ CFSG.AGLEmbeddingD2.d2SporadicOrder s := by
  revert s hs hsB hsHN hd
  decide +kernel

section LieBSieve

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3


private theorem b_sieve_lie {T : Type} [Group T] [Finite T] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ searchTags) (hp : p.Prime) (hf : 1 ≤ f) (hn : lieMin t ≤ n)
    (hn0 : lieMin t = 0 → n = 0) (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true)
    (hcard : Nat.card T = lieOrd t n (p ^ f)) (hM : CFSG.Blueprint.LieModel T t n p f)
    (hord : Nat.card T ∣ 4154781481226426191177580544000000) :
    ¬ 5 ∣ Nat.card T ∨
      ((∀ α : MulAut T, α ^ 5 = 1 → α ∈ inner T) ∧ (5 ^ 5 ∣ Nat.card T →
        Nat.card T = 4154781481226426191177580544000000 ∨ Nonempty (T ≃* Carrier .HN) ∨
          CFSG.Blueprint.LieModel T .PSL 4 5 1 ∨ CFSG.Blueprint.LieModel T .PSU 4 5 1 ∨
          CFSG.Blueprint.LieModel T .PSL 3 5 2 ∨
          (Nat.card T = 5859000000 ∧ CFSG.Blueprint.LieModel T .G2 0 5 1))) := by
  have hC := bCheck_of_dvd ht hp hf hn hn0 hnB hadm (hcard ▸ hord)
  rw [bCheck, Bool.or_eq_true] at hC
  rcases hC with hA | hB
  · left
    rw [Nat.dvd_iff_mod_eq_zero]
    simpa [hcard, bne_iff_ne] using hA
  · rw [Bool.and_eq_true] at hB
    obtain ⟨h5free, hrest⟩ := hB
    refine Or.inr ⟨fun α hα => mem_inner_of_outerFree Nat.prime_five le_rfl hM ht h5free hα, ?_⟩
    intro h55
    have hmod : lieOrd t n (p ^ f) % 3125 = 0 := by
      rw [← Nat.dvd_iff_mod_eq_zero, ← hcard]
      exact h55
    rw [Bool.or_eq_true, bne_iff_ne, hmod] at hrest
    rcases hrest with hzero | hspec
    · exact absurd rfl hzero
    · have hspec' : (t = .PSL ∧ n = 4 ∧ p = 5 ∧ f = 1) ∨
          (t = .PSU ∧ n = 4 ∧ p = 5 ∧ f = 1) ∨
          (t = .PSL ∧ n = 3 ∧ p = 5 ∧ f = 2) ∨
          (t = .G2 ∧ n = 0 ∧ p = 5 ∧ f = 1) := by
        simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, and_assoc, or_assoc]
          using hspec
      rcases hspec' with ⟨htPSL, hn4, hp5, hf1⟩ | ⟨htPSU, hn4, hp5, hf1⟩ |
        ⟨htPSL, hn3, hp5, hf2⟩ | ⟨htG2, hn0', hp5, hf1⟩
      · exact Or.inr (Or.inr (Or.inl (by simpa [htPSL, hn4, hp5, hf1] using hM)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by
          simpa [htPSU, hn4, hp5, hf1] using hM))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
          simpa [htPSL, hn3, hp5, hf2] using hM)))))
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))))
        · rw [hcard, htG2, hn0', hp5, hf1]
          decide +kernel
        · simpa [htG2, hn0', hp5, hf1] using hM

end LieBSieve

section SieveB

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3


theorem b_sieve {T : Type} [Group T] [Finite T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a)
    (hord : Nat.card T ∣ 4154781481226426191177580544000000) :
    ¬ 5 ∣ Nat.card T ∨
      ((∀ α : MulAut T, α ^ 5 = 1 → α ∈ inner T) ∧ (5 ^ 5 ∣ Nat.card T →
        Nat.card T = 4154781481226426191177580544000000 ∨ Nonempty (T ≃* Carrier .HN) ∨
          CFSG.Blueprint.LieModel T .PSL 4 5 1 ∨ CFSG.Blueprint.LieModel T .PSU 4 5 1 ∨
          CFSG.Blueprint.LieModel T .PSL 3 5 2 ∨
          (Nat.card T = 5859000000 ∧ CFSG.Blueprint.LieModel T .G2 0 5 1))) := by
  rcases CFSG.EvenSmallLie.Child3.catalog_model_cases hT hnonab with
    ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, ht, hp, hf, hn, hn0, hnB, hadm, hcard, hM⟩ |
      ⟨p, f, h⟩ | ⟨p, f, h⟩ | ⟨s, ⟨e⟩⟩
  · obtain ⟨hinn, hk⟩ := alternating_sieve (p := 5) (r := 7) (j := 3) (k := 5)
      Nat.prime_five (by norm_num) hn e hord (by norm_num : Nat.Prime 7) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    exact Or.inr ⟨hinn, fun h55 => absurd h55 hk⟩
  · exact b_sieve_lie ht hp hf hn hn0 hnB hadm hcard hM hord
  · exact (CFSG.EvenSmallLie.Child3.false_of_reeTitsModel_twistedF4 h hord
      (by norm_num) (by norm_num) (by norm_num)).elim
  · refine Or.inr ⟨fun α hα => mem_inner_of_reeTitsModel_Tits h Nat.prime_five ?_ hα, ?_⟩
    · norm_num
    · intro h55
      exact absurd (h55.trans (CFSG.EvenSmallLie.Child3.card_dvd_of_reeTitsModel_Tits h))
        (by decide +kernel)
  · by_cases hsM : s = .M
    · subst s
      have hcard : Nat.card T =
          808017424794512875886459904961710757005754368000000000 := by
        rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.FourListSporadic.card_carrier_monster]
      exact absurd (hcard ▸ hord) (by
        intro h
        exact absurd (Nat.le_of_dvd (by norm_num) h) (by norm_num))
    · have hcard : Nat.card T = CFSG.AGLEmbeddingD2.d2SporadicOrder s := by
        rw [Nat.card_congr e.toEquiv,
          CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder s hsM]
      refine Or.inr ⟨fun α hα => mem_inner_of_mulEquiv_carrier e hsM Nat.prime_five
        (by norm_num) hα, ?_⟩
      intro h55
      by_cases hsB : s = .B
      · subst s
        exact Or.inl (by rw [hcard]; decide +kernel)
      by_cases hsHN : s = .HN
      · subst s
        exact Or.inr (Or.inl ⟨e⟩)
      · have hd : CFSG.AGLEmbeddingD2.d2SporadicOrder s ∣
            4154781481226426191177580544000000 := by rwa [hcard] at hord
        have h5 : 5 ^ 5 ∣ CFSG.AGLEmbeddingD2.d2SporadicOrder s := by rwa [hcard] at h55
        exact absurd h5 (b_sporadic_orders s hsM hsB hsHN hd)

end SieveB

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
