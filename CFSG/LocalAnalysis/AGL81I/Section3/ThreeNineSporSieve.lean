module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicTable
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporInner
import CFSG.Quasithin.Background.FourListSporadicPfM
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section LieSearch

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)

@[expose] def outerFree (p : ℕ) (t : StatedLieTag) (n ℓ f : ℕ) : Bool :=
  !(f % p == 0 || lieOrderDivisor t n (ℓ ^ f) % p == 0)

private def co1Check (t : StatedLieTag) (n ℓ f o : ℕ) : Bool :=
  outerFree 5 t n ℓ f && (o % 625 != 0 || (t == .PSp && n == 2 && ℓ == 5 && f == 1))

private def hnCheck (t : StatedLieTag) (n ℓ f o : ℕ) : Bool :=
  outerFree 5 t n ℓ f && o % 3125 != 0

private def lyCheck (t : StatedLieTag) (n ℓ f o : ℕ) : Bool :=
  (o % 5 != 0 && (o % 7 == 0 || o % 11 == 0 || o % 31 == 0 || o % 37 == 0 || o % 67 == 0)) ||
    (outerFree 5 t n ℓ f && (o % 3125 != 0 || (t == .G2 && ℓ == 5 && f == 1)))

private def co1Primes : List (ℕ × ℕ) :=
  [(2, 21), (3, 9), (5, 4), (7, 2), (11, 1), (13, 1), (23, 1)]

private def hnPrimes : List (ℕ × ℕ) :=
  [(2, 14), (3, 6), (5, 6), (7, 1), (11, 1), (19, 1)]

private def lyPrimes : List (ℕ × ℕ) :=
  [(2, 8), (3, 7), (5, 6), (7, 1), (11, 1), (31, 1), (37, 1), (67, 1)]

private theorem co1_search : lieSearchV co1Primes 4157776806543360000 co1Check = true := by
  decide +kernel

private theorem hn_search : lieSearchV hnPrimes 273030912000000 hnCheck = true := by
  decide +kernel

private theorem ly_search : lieSearchV lyPrimes 51765179004000000 lyCheck = true := by
  decide +kernel

private theorem co1Check_of_dvd {t : StatedLieTag} {n p f : ℕ} (ht : t ∈ searchTags)
    (hp : p.Prime) (hf : 1 ≤ f) (hn : lieMin t ≤ n) (hn0 : lieMin t = 0 → n = 0)
    (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true)
    (hd : lieOrd t n (p ^ f) ∣ 4157776806543360000) :
    co1Check t n p f (lieOrd t n (p ^ f)) = true := by
  refine lieSearchV_sound ?_ co1_search ht hp hf hn hn0 hnB hadm hd
  refine primes_of_factorization ?_ (by decide +kernel) (by decide +kernel)
  simp only [co1Primes, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq]
  norm_num

private theorem hnCheck_of_dvd {t : StatedLieTag} {n p f : ℕ} (ht : t ∈ searchTags)
    (hp : p.Prime) (hf : 1 ≤ f) (hn : lieMin t ≤ n) (hn0 : lieMin t = 0 → n = 0)
    (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true)
    (hd : lieOrd t n (p ^ f) ∣ 273030912000000) :
    hnCheck t n p f (lieOrd t n (p ^ f)) = true := by
  refine lieSearchV_sound ?_ hn_search ht hp hf hn hn0 hnB hadm hd
  refine primes_of_factorization ?_ (by decide +kernel) (by decide +kernel)
  simp only [hnPrimes, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq]
  norm_num

private theorem lyCheck_of_dvd {t : StatedLieTag} {n p f : ℕ} (ht : t ∈ searchTags)
    (hp : p.Prime) (hf : 1 ≤ f) (hn : lieMin t ≤ n) (hn0 : lieMin t = 0 → n = 0)
    (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true)
    (hd : lieOrd t n (p ^ f) ∣ 51765179004000000) :
    lyCheck t n p f (lieOrd t n (p ^ f)) = true := by
  refine lieSearchV_sound ?_ ly_search ht hp hf hn hn0 hnB hadm hd
  refine primes_of_factorization ?_ (by decide +kernel) (by decide +kernel)
  simp only [lyPrimes, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq]
  norm_num

end LieSearch

section LieInner

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3

theorem mem_inner_of_outerFree {T : Type} [Group T] [Finite T] {t : StatedLieTag}
    {n ℓ f p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : CFSG.Blueprint.LieModel T t n ℓ f)
    (ht : t ∈ searchTags) (hfree : outerFree p t n ℓ f = true) {α : MulAut T}
    (hα : α ^ p = 1) : α ∈ inner T := by
  have ht' : t ≠ .Tits := by
    rintro rfl
    simp [searchTags] at ht
  have hf : ¬ p ∣ f := by
    intro hd
    have h5' := hfree
    unfold outerFree at h5'
    rw [show (f % p == 0) = true by simpa using Nat.dvd_iff_mod_eq_zero.mp hd] at h5'
    simp at h5'
  have hdv : ¬ p ∣ CFSG.ComponentClassification.CatLeaf.lieOrderDivisor t n (ℓ ^ f) := by
    intro hd
    have h5' := hfree
    unfold outerFree at h5'
    rw [show (CFSG.ComponentClassification.CatLeaf.lieOrderDivisor t n (ℓ ^ f) % p == 0) = true by
      simpa using Nat.dvd_iff_mod_eq_zero.mp hd] at h5'
    simp at h5'
  exact mem_inner_of_lieModel h ht' hp (by omega)
    (by rintro ⟨-, -, h⟩; omega) (by rintro ⟨-, h⟩; omega) hf hdv hα

private theorem co1_sieve_lie {T : Type} [Group T] [Finite T] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ searchTags) (hp : p.Prime) (hf : 1 ≤ f) (hn : lieMin t ≤ n)
    (hn0 : lieMin t = 0 → n = 0) (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true)
    (hcard : Nat.card T = lieOrd t n (p ^ f)) (hM : CFSG.Blueprint.LieModel T t n p f)
    (hord : Nat.card T ∣ 4157776806543360000) :
    (∀ α : MulAut T, α ^ 5 = 1 → α ∈ inner T) ∧ (5 ^ 4 ∣ Nat.card T →
      Nat.card T = 4157776806543360000 ∨
        (Nat.card T = 4680000 ∧ CFSG.Blueprint.LieModel T .PSp 2 5 1)) := by
  have hC := co1Check_of_dvd ht hp hf hn hn0 hnB hadm (hcard ▸ hord)
  rw [co1Check, Bool.and_eq_true] at hC
  obtain ⟨h5free, hrest⟩ := hC
  refine ⟨fun α hα => mem_inner_of_outerFree Nat.prime_five le_rfl hM ht h5free hα, ?_⟩
  intro h54
  have hmod : lieOrd t n (p ^ f) % 625 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero, ← hcard]
    exact h54
  have hspec : (t == .PSp && n == 2 && p == 5 && f == 1) = true := by
    simpa [hmod] using hrest
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hspec
  obtain ⟨htPSp, hn2, hp5, hf1⟩ := hspec
  refine Or.inr ⟨?_, ?_⟩
  · rw [hcard, htPSp, hn2, hp5, hf1]
    decide +kernel
  · simpa [htPSp, hn2, hp5, hf1] using hM

private theorem hn_sieve_lie {T : Type} [Group T] [Finite T] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ searchTags) (hp : p.Prime) (hf : 1 ≤ f) (hn : lieMin t ≤ n)
    (hn0 : lieMin t = 0 → n = 0) (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true)
    (hcard : Nat.card T = lieOrd t n (p ^ f)) (hM : CFSG.Blueprint.LieModel T t n p f)
    (hord : Nat.card T ∣ 273030912000000) :
    (∀ α : MulAut T, α ^ 5 = 1 → α ∈ inner T) ∧
      (5 ^ 5 ∣ Nat.card T → Nat.card T = 273030912000000) := by
  have hC := hnCheck_of_dvd ht hp hf hn hn0 hnB hadm (hcard ▸ hord)
  rw [hnCheck, Bool.and_eq_true] at hC
  obtain ⟨h5free, hrest⟩ := hC
  refine ⟨fun α hα => mem_inner_of_outerFree Nat.prime_five le_rfl hM ht h5free hα, ?_⟩
  intro h55
  have hmod : lieOrd t n (p ^ f) % 3125 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero, ← hcard]
    exact h55
  rw [bne_iff_ne, hmod] at hrest
  exact absurd rfl hrest

private theorem ly_sieve_lie {T : Type} [Group T] [Finite T] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ searchTags) (hp : p.Prime) (hf : 1 ≤ f) (hn : lieMin t ≤ n)
    (hn0 : lieMin t = 0 → n = 0) (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true)
    (hcard : Nat.card T = lieOrd t n (p ^ f)) (hM : CFSG.Blueprint.LieModel T t n p f)
    (hord : Nat.card T ∣ 51765179004000000) :
    (¬ 5 ∣ Nat.card T ∧ ∃ r ∈ ({7, 11, 31, 37, 67} : Finset ℕ), r ∣ Nat.card T) ∨
      ((∀ α : MulAut T, α ^ 5 = 1 → α ∈ inner T) ∧ (5 ^ 5 ∣ Nat.card T →
        Nat.card T = 51765179004000000 ∨
          (Nat.card T = 5859000000 ∧ CFSG.Blueprint.LieModel T .G2 0 5 1))) := by
  have hC := lyCheck_of_dvd ht hp hf hn hn0 hnB hadm (hcard ▸ hord)
  rw [lyCheck, Bool.or_eq_true] at hC
  rcases hC with hA | hB
  · rw [Bool.and_eq_true, bne_iff_ne] at hA
    obtain ⟨h5mod, hdiv⟩ := hA
    rw [← hcard] at hdiv
    have h5 : ¬ 5 ∣ Nat.card T := by
      rw [Nat.dvd_iff_mod_eq_zero]
      simpa [hcard] using h5mod
    have hpr : ∃ r ∈ ({7, 11, 31, 37, 67} : Finset ℕ), r ∣ Nat.card T := by
      by_cases h7 : Nat.card T % 7 = 0
      · exact ⟨7, by simp, Nat.dvd_iff_mod_eq_zero.mpr h7⟩
      by_cases h11 : Nat.card T % 11 = 0
      · exact ⟨11, by simp, Nat.dvd_iff_mod_eq_zero.mpr h11⟩
      by_cases h31 : Nat.card T % 31 = 0
      · exact ⟨31, by simp, Nat.dvd_iff_mod_eq_zero.mpr h31⟩
      by_cases h37 : Nat.card T % 37 = 0
      · exact ⟨37, by simp, Nat.dvd_iff_mod_eq_zero.mpr h37⟩
      by_cases h67 : Nat.card T % 67 = 0
      · exact ⟨67, by simp, Nat.dvd_iff_mod_eq_zero.mpr h67⟩
      exfalso
      revert hdiv
      simp [h7, h11, h31, h37, h67]
    exact Or.inl ⟨h5, hpr⟩
  · rw [Bool.and_eq_true] at hB
    obtain ⟨h5free, hrest⟩ := hB
    refine Or.inr ⟨fun α hα => mem_inner_of_outerFree Nat.prime_five le_rfl hM ht h5free hα, ?_⟩
    intro h55
    have hmod : lieOrd t n (p ^ f) % 3125 = 0 := by
      rw [← Nat.dvd_iff_mod_eq_zero, ← hcard]
      exact h55
    have hspec : (t == .G2 && p == 5 && f == 1) = true := by
      simpa [hmod] using hrest
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hspec
    obtain ⟨htG2, hp5, hf1⟩ := hspec
    have hn0' : n = 0 := hn0 (by rw [htG2]; rfl)
    refine Or.inr ⟨?_, ?_⟩
    · rw [hcard, htG2, hn0', hp5, hf1]
      decide +kernel
    · simpa [htG2, hn0', hp5, hf1] using hM

end LieInner

private lemma pow_mul_factorial_dvd_factorial {r j : ℕ} (hr : r.Prime) :
    r ^ j * j.factorial ∣ (j * r).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hle : r ≤ (j + 1) * r := by
      rw [Nat.succ_mul]
      exact Nat.le_add_left r (j * r)
    have hsub : (j + 1) * r - r = j * r := by
      rw [Nat.succ_mul]
      omega
    have hfac := Nat.factorial_mul_descFactorial (n := (j + 1) * r) (k := r) hle
    rw [hsub] at hfac
    have hdvd_desc : ∀ k, 1 ≤ k → (j + 1) * r ∣ ((j + 1) * r).descFactorial k := by
      intro k
      induction k with
      | zero => intro hk; omega
      | succ k ihk =>
        intro hk
        rw [Nat.descFactorial_succ]
        cases k with
        | zero => simp
        | succ k => exact dvd_mul_of_dvd_right (ihk (by omega)) _
    have hdesc : r * (j + 1) ∣ ((j + 1) * r).descFactorial r := by
      rw [Nat.mul_comm r (j + 1)]
      exact hdvd_desc r hr.one_lt.le
    have hmul := Nat.mul_dvd_mul ih hdesc
    rw [hfac] at hmul
    simpa [Nat.factorial_succ, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using hmul

private lemma pow_dvd_factorial_mul {r j : ℕ} (hr : r.Prime) :
    r ^ j ∣ (j * r).factorial :=
  (Nat.dvd_mul_right _ _).trans (pow_mul_factorial_dvd_factorial hr)

theorem alternating_sieve {T : Type} [Group T] [Finite T] {n N r j k p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 5 ≤ n) (e : T ≃* alternatingGroup (Fin n)) (hord : Nat.card T ∣ N)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrN : ¬ r ^ j ∣ N)
    (hk : ¬ p ^ k ∣ (j * r - 1).factorial) :
    (∀ α : MulAut T, α ^ p = 1 → α ∈ inner T) ∧ ¬ p ^ k ∣ Nat.card T := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard : Nat.card T = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hcop : Nat.Coprime r 2 := by
    rw [hr.coprime_iff_not_dvd]
    intro h
    have hle2 : r ≤ 2 := Nat.le_of_dvd (by norm_num) h
    have hge2 : 2 ≤ r := hr.two_le
    exact hr2 (by omega)
  have hnle : ¬ j * r ≤ n := by
    intro hle
    have hrn' : r ^ j ∣ n.factorial :=
      (pow_dvd_factorial_mul hr).trans (Nat.factorial_dvd_factorial hle)
    have hrT : r ^ j ∣ n.factorial / 2 := by
      refine (hcop.pow_left j).dvd_of_dvd_mul_left ?_
      rwa [Nat.mul_div_cancel' h2]
    have hTdvdN : n.factorial / 2 ∣ N := by rwa [hcard] at hord
    exact hrN (hrT.trans hTdvdN)
  have hnr : n < j * r := Nat.not_le.mp hnle
  have hle : n ≤ j * r - 1 := Nat.le_sub_one_of_lt hnr
  have hdvd : Nat.card T ∣ (j * r - 1).factorial := by
    rw [hcard]
    exact (Nat.div_dvd_of_dvd h2).trans (Nat.factorial_dvd_factorial hle)
  refine ⟨?_, ?_⟩
  · intro α hα
    exact mem_inner_of_mulEquiv_alternating hp hp2 hn e hα
  · intro h
    exact hk (h.trans hdvd)

private theorem co1_sporadic_orders (s : TauCeti.SporadicName) (hs : s ≠ .M)
    (hd : CFSG.AGLEmbeddingD2.d2SporadicOrder s ∣ 4157776806543360000)
    (h5 : 5 ^ 4 ∣ CFSG.AGLEmbeddingD2.d2SporadicOrder s) :
    CFSG.AGLEmbeddingD2.d2SporadicOrder s = 4157776806543360000 := by
  revert s hs hd h5
  decide +kernel

private theorem hn_sporadic_orders (s : TauCeti.SporadicName) (hs : s ≠ .M)
    (hd : CFSG.AGLEmbeddingD2.d2SporadicOrder s ∣ 273030912000000)
    (h5 : 5 ^ 5 ∣ CFSG.AGLEmbeddingD2.d2SporadicOrder s) :
    CFSG.AGLEmbeddingD2.d2SporadicOrder s = 273030912000000 := by
  revert s hs hd h5
  decide +kernel

private theorem ly_sporadic_orders (s : TauCeti.SporadicName) (hs : s ≠ .M)
    (hd : CFSG.AGLEmbeddingD2.d2SporadicOrder s ∣ 51765179004000000)
    (h5 : 5 ^ 5 ∣ CFSG.AGLEmbeddingD2.d2SporadicOrder s) :
    CFSG.AGLEmbeddingD2.d2SporadicOrder s = 51765179004000000 := by
  revert s hs hd h5
  decide +kernel

section Sporadic

theorem sporadic_sieve {T : Type} [Group T] [Finite T] {s : TauCeti.SporadicName}
    (e : T ≃* Carrier s) {N k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hord : Nat.card T ∣ N)
    (hM : ¬ 808017424794512875886459904961710757005754368000000000 ∣ N)
    (hs : ∀ s' : TauCeti.SporadicName, s' ≠ .M →
      CFSG.AGLEmbeddingD2.d2SporadicOrder s' ∣ N →
        p ^ k ∣ CFSG.AGLEmbeddingD2.d2SporadicOrder s' →
          CFSG.AGLEmbeddingD2.d2SporadicOrder s' = N) :
    (∀ α : MulAut T, α ^ p = 1 → α ∈ inner T) ∧ (p ^ k ∣ Nat.card T → Nat.card T = N) := by
  by_cases hsM : s = .M
  · subst s
    have hcard : Nat.card T = 808017424794512875886459904961710757005754368000000000 := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.Quasithin.FourListSporadic.card_carrier_monster]
    exact absurd (hcard ▸ hord) hM
  · have hcard : Nat.card T = CFSG.AGLEmbeddingD2.d2SporadicOrder s := by
      rw [Nat.card_congr e.toEquiv, CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder s hsM]
    refine ⟨fun α hα => mem_inner_of_mulEquiv_carrier e hsM hp hp2 hα, ?_⟩
    intro h5
    rw [hcard] at h5 ⊢
    exact hs s hsM (by rwa [hcard] at hord) h5

end Sporadic

section TitsCo1

private theorem tits_sieve_co1 {T : Type} [Group T] [Finite T] {p f : ℕ}
    (h : CFSG.Blueprint.ReeTitsModel T .Tits p f) :
    (∀ α : MulAut T, α ^ 5 = 1 → α ∈ inner T) ∧ ¬ 5 ^ 4 ∣ Nat.card T := by
  refine ⟨fun α hα => mem_inner_of_reeTitsModel_Tits h Nat.prime_five (by norm_num) hα, ?_⟩
  intro h54
  exact absurd (h54.trans (CFSG.EvenSmallLie.Child3.card_dvd_of_reeTitsModel_Tits h))
    (by decide +kernel)

end TitsCo1

section Co1

theorem co1_sieve {T : Type} [Group T] [Finite T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a) (hord : Nat.card T ∣ 4157776806543360000) :
    (∀ α : MulAut T, α ^ 5 = 1 → α ∈ inner T) ∧ (5 ^ 4 ∣ Nat.card T →
      Nat.card T = 4157776806543360000 ∨
        (Nat.card T = 4680000 ∧ CFSG.Blueprint.LieModel T .PSp 2 5 1)) := by
  rcases CFSG.EvenSmallLie.Child3.catalog_model_cases hT hnonab with
    ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, ht, hp, hf, hn, hn0, hnB, hadm, hcard, hM⟩ |
      ⟨p, f, h⟩ | ⟨p, f, h⟩ | ⟨s, ⟨e⟩⟩
  · obtain ⟨hinn, hk⟩ := alternating_sieve (p := 5) (r := 17) (j := 1) (k := 4)
      Nat.prime_five (by norm_num) hn e hord (by norm_num : Nat.Prime 17) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    exact ⟨hinn, fun h54 => absurd h54 hk⟩
  · exact co1_sieve_lie ht hp hf hn hn0 hnB hadm hcard hM hord
  · exact (CFSG.EvenSmallLie.Child3.false_of_reeTitsModel_twistedF4 h hord
      (by norm_num) (by norm_num) (by norm_num)).elim
  · obtain ⟨hinn, hk⟩ := tits_sieve_co1 h
    exact ⟨hinn, fun h54 => absurd h54 hk⟩
  · have hM' : ¬ 808017424794512875886459904961710757005754368000000000 ∣
        4157776806543360000 := fun h =>
      absurd (Nat.le_of_dvd (by norm_num) h) (by norm_num)
    obtain ⟨hinn, hN⟩ := sporadic_sieve (p := 5) (N := 4157776806543360000) (k := 4) e
      Nat.prime_five (by norm_num) hord hM'
      (fun s' hs' hd h5 => co1_sporadic_orders s' hs' hd h5)
    exact ⟨hinn, fun h54 => Or.inl (hN h54)⟩

end Co1

section HNLy

theorem hn_sieve {T : Type} [Group T] [Finite T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a) (hord : Nat.card T ∣ 273030912000000) :
    (∀ α : MulAut T, α ^ 5 = 1 → α ∈ inner T) ∧
      (5 ^ 5 ∣ Nat.card T → Nat.card T = 273030912000000) := by
  rcases CFSG.EvenSmallLie.Child3.catalog_model_cases hT hnonab with
    ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, ht, hp, hf, hn, hn0, hnB, hadm, hcard, hM⟩ |
      ⟨p, f, h⟩ | ⟨p, f, h⟩ | ⟨s, ⟨e⟩⟩
  · obtain ⟨hinn, hk⟩ := alternating_sieve (p := 5) (r := 13) (j := 1) (k := 5)
      Nat.prime_five (by norm_num) hn e hord (by norm_num : Nat.Prime 13) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    exact ⟨hinn, fun h55 => absurd h55 hk⟩
  · exact hn_sieve_lie ht hp hf hn hn0 hnB hadm hcard hM hord
  · have h13 : 13 ∣ 273030912000000 :=
      (CFSG.EvenSmallLie.CatalogOrders.thirteen_dvd_card_of_reeTitsModel_twistedF4 h).trans hord
    exact absurd h13 (by decide +kernel)
  · have h13 : 13 ∣ 273030912000000 :=
      (CFSG.EvenSmallLie.CatalogOrders.thirteen_dvd_card_of_reeTitsModel_Tits h).trans hord
    exact absurd h13 (by decide +kernel)
  · have hM' : ¬ 808017424794512875886459904961710757005754368000000000 ∣
        273030912000000 := fun h =>
      absurd (Nat.le_of_dvd (by norm_num) h) (by norm_num)
    exact sporadic_sieve (p := 5) (N := 273030912000000) (k := 5) e
      Nat.prime_five (by norm_num) hord hM'
      (fun s' hs' hd h5 => hn_sporadic_orders s' hs' hd h5)

theorem ly_sieve {T : Type} [Group T] [Finite T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a) (hord : Nat.card T ∣ 51765179004000000) :
    (¬ 5 ∣ Nat.card T ∧ ∃ r ∈ ({7, 11, 31, 37, 67} : Finset ℕ), r ∣ Nat.card T) ∨
      ((∀ α : MulAut T, α ^ 5 = 1 → α ∈ inner T) ∧ (5 ^ 5 ∣ Nat.card T →
        Nat.card T = 51765179004000000 ∨
          (Nat.card T = 5859000000 ∧ CFSG.Blueprint.LieModel T .G2 0 5 1))) := by
  rcases CFSG.EvenSmallLie.Child3.catalog_model_cases hT hnonab with
    ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, ht, hp, hf, hn, hn0, hnB, hadm, hcard, hM⟩ |
      ⟨p, f, h⟩ | ⟨p, f, h⟩ | ⟨s, ⟨e⟩⟩
  · obtain ⟨hinn, hk⟩ := alternating_sieve (p := 5) (r := 13) (j := 1) (k := 5)
      Nat.prime_five (by norm_num) hn e hord (by norm_num : Nat.Prime 13) (by norm_num)
      (by decide +kernel) (by decide +kernel)
    exact Or.inr ⟨hinn, fun h55 => absurd h55 hk⟩
  · exact ly_sieve_lie ht hp hf hn hn0 hnB hadm hcard hM hord
  · have h13 : 13 ∣ 51765179004000000 :=
      (CFSG.EvenSmallLie.CatalogOrders.thirteen_dvd_card_of_reeTitsModel_twistedF4 h).trans hord
    exact absurd h13 (by decide +kernel)
  · have h13 : 13 ∣ 51765179004000000 :=
      (CFSG.EvenSmallLie.CatalogOrders.thirteen_dvd_card_of_reeTitsModel_Tits h).trans hord
    exact absurd h13 (by decide +kernel)
  · have hM' : ¬ 808017424794512875886459904961710757005754368000000000 ∣
        51765179004000000 := fun h =>
      absurd (Nat.le_of_dvd (by norm_num) h) (by norm_num)
    obtain ⟨hinn, hN⟩ := sporadic_sieve (p := 5) (N := 51765179004000000) (k := 5) e
      Nat.prime_five (by norm_num) hord hM'
      (fun s' hs' hd h5 => ly_sporadic_orders s' hs' hd h5)
    exact Or.inr ⟨hinn, fun h55 => Or.inl (hN h55)⟩

end HNLy

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
