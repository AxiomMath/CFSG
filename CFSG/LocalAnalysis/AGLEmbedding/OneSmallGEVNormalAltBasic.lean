module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltDefs
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalCoprimePreimages

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

theorem two_mul_card_alternatingGroup_fin {n : ℕ} (hn : 2 ≤ n) :
    2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have h := two_mul_nat_card_alternatingGroup (α := Fin n)
  rwa [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h

theorem not_dvd_card_alt_prod {p : ℕ} (hp : p.Prime) :
    ¬ p ^ 3 ∣ Nat.card (alternatingGroup (Fin p) × alternatingGroup (Fin p)) := by
  intro h
  rw [Nat.card_prod] at h
  have h2 := two_mul_card_alternatingGroup_fin hp.two_le
  rw [← Nat.mul_factorial_pred hp.ne_zero] at h2
  set a := Nat.card (alternatingGroup (Fin p))
  set f := (p - 1).factorial
  have h3 : p ^ 2 * p ∣ p ^ 2 * (f * f) := by
    have : p ^ 3 ∣ (2 * a) * (2 * a) := h.trans ⟨4, by ring⟩
    rw [h2] at this
    have e1 : p ^ 2 * p = p ^ 3 := by ring
    have e2 : p * f * (p * f) = p ^ 2 * (f * f) := by ring
    rwa [e1, ← e2]
  have h4 : p ∣ f * f := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 2) h3
  have h5 : p ∣ f := (Nat.Prime.dvd_mul hp).mp h4 |>.elim id id
  have := (Nat.Prime.dvd_factorial hp).mp h5
  have := hp.pos
  omega

theorem PerfectSectionsAltSq.not_dvd_card {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] {J : Subgroup X} (hJ : PerfectSectionsAltSq p J) {V : Subgroup X} (hVJ : V ≤ J)
    (hV : ⁅V, V⁆ = V) : ¬ p ^ 3 ∣ Nat.card V := by
  obtain ⟨V₀, hV₀V, -, hcop, f, hf⟩ := hJ V hVJ hV
  intro h
  have hcard : Nat.card V = Nat.card f.range * Nat.card V₀ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hf,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₀V).toEquiv]
  rw [hcard] at h
  have h1 : p ^ 3 ∣ Nat.card f.range := Nat.Coprime.dvd_of_dvd_mul_right (hcop.pow_left 3) h
  exact not_dvd_card_alt_prod hp (h1.trans (Subgroup.card_subgroup_dvd_card _))

theorem not_dvd_card_of_surjective_of_perfect {Y X : Type*} [Group Y] [Finite Y] [Group X]
    {J : Subgroup Y} {n : ℕ} (hJ : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → ¬ n ∣ Nat.card V)
    (ψ : ↥J →* X) (hψ : Function.Surjective ψ) (B : Subgroup X) (hB : ⁅B, B⁆ = B) :
    ¬ n ∣ Nat.card B := by
  have hBp : Group.IsPerfect B := Subgroup.isPerfect_iff.mpr hB
  set R₀ := perfectResidualOf (B.comap ψ)
  have hR₀ : R₀.map ψ = B := finite_canonical_perfect_preimage_image_eq ψ hψ B hBp
  have hR₀p : ⁅R₀, R₀⁆ = R₀ :=
    Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect (B.comap ψ))
  have hV := hJ _ (Subgroup.map_subtype_le _) (by rw [← Subgroup.map_commutator, hR₀p])
  rw [Subgroup.card_map_of_injective J.subtype_injective] at hV
  rw [← hR₀]
  exact fun h => hV (h.trans (Subgroup.card_map_dvd R₀ ψ))

theorem pow_dvd_card_quotient_pCore_two {Y : Type*} [Group Y] [Finite Y] {J : Subgroup Y}
    {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ k ∣ Nat.card J) :
    p ^ k ∣ Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥J)] at h
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥J))
  rw [hj] at h
  exact Nat.Coprime.dvd_of_dvd_mul_right
    (((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow k j) h

theorem pow_three_dvd_card_alternatingGroup {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n)
    (h : p ^ 3 ∣ n.factorial) : p ^ 3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  rw [← two_mul_card_alternatingGroup_fin hn] at h
  exact Nat.Coprime.dvd_of_dvd_mul_left
    (((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_left 3) h

theorem le_of_pow_three_dvd_factorial {p n : ℕ} (hp : p.Prime) (h : p ^ 3 ∣ n.factorial) :
    p ≤ n :=
  (Nat.Prime.dvd_factorial hp).mp ((dvd_pow_self p (by norm_num)).trans h)

theorem false_of_quotient_perm {Y : Type*} [Group Y] [Finite Y] {J : Subgroup Y} {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hJ : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → ¬ p ^ 3 ∣ Nat.card V)
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin n)) (hdvd : p ^ 3 ∣ Nat.card J) : False := by
  have h1 := pow_dvd_card_quotient_pCore_two hp (by omega) hdvd
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n),
    Fintype.card_fin] at h1
  have hn := le_of_pow_three_dvd_factorial hp h1
  have h5 : 5 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  exact not_dvd_card_of_surjective_of_perfect hJ
    (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (alternatingGroup (Fin n))
    (commutator_alternatingGroup_eq_self h5)
    (pow_three_dvd_card_alternatingGroup hp (by omega) (by omega) h1)

theorem false_of_quotient_perm_prod {Y : Type*} [Group Y] [Finite Y] {J : Subgroup Y}
    {p r m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hJ : ∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → ¬ p ^ 3 ∣ Nat.card V)
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* (Equiv.Perm (Fin r) × Equiv.Perm (Fin m)))
    (hdvd : p ^ 3 ∣ Nat.card J) : False := by
  have hp2 : p ≠ 2 := by omega
  have h1 := pow_dvd_card_quotient_pCore_two hp hp2 hdvd
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_perm,
    Nat.card_eq_fintype_card (α := Fin r), Nat.card_eq_fintype_card (α := Fin m),
    Fintype.card_fin, Fintype.card_fin] at h1
  set ψ := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J))
  have hs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcop : ∀ k : ℕ, k < p → (p ^ 3).Coprime k.factorial := fun k hk =>
    Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h =>
      absurd ((Nat.Prime.dvd_factorial hp).mp h) (by omega))
  rcases Nat.lt_or_ge r p with hr | hr
  · have h2 : p ^ 3 ∣ m.factorial := Nat.Coprime.dvd_of_dvd_mul_left (hcop r hr) h1
    have hm := le_of_pow_three_dvd_factorial hp h2
    have h5 : 5 ≤ Nat.card (Fin m) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
    exact not_dvd_card_of_surjective_of_perfect hJ ((MonoidHom.snd _ _).comp ψ)
      (Prod.snd_surjective.comp hs) (alternatingGroup (Fin m))
      (commutator_alternatingGroup_eq_self h5)
      (pow_three_dvd_card_alternatingGroup hp hp2 (by omega) h2)
  rcases Nat.lt_or_ge m p with hm | hm
  · have h2 : p ^ 3 ∣ r.factorial := Nat.Coprime.dvd_of_dvd_mul_right (hcop m hm) h1
    have h5 : 5 ≤ Nat.card (Fin r) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
    exact not_dvd_card_of_surjective_of_perfect hJ ((MonoidHom.fst _ _).comp ψ)
      (Prod.fst_surjective.comp hs) (alternatingGroup (Fin r))
      (commutator_alternatingGroup_eq_self h5)
      (pow_three_dvd_card_alternatingGroup hp hp2 (by omega) h2)
  have h5r : 5 ≤ Nat.card (Fin r) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  have h5m : 5 ≤ Nat.card (Fin m) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  refine not_dvd_card_of_surjective_of_perfect hJ ψ hs
    ((alternatingGroup (Fin r)).prod (alternatingGroup (Fin m))) ?_ ?_
  · rw [Subgroup.commutator_prod_prod, commutator_alternatingGroup_eq_self h5r,
      commutator_alternatingGroup_eq_self h5m]
  · rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
    rw [← two_mul_card_alternatingGroup_fin (by omega : 2 ≤ r),
      ← two_mul_card_alternatingGroup_fin (by omega : 2 ≤ m)] at h1
    have h4 : (2 * Nat.card (alternatingGroup (Fin r))) * (2 * Nat.card (alternatingGroup
        (Fin m))) = 4 * (Nat.card (alternatingGroup (Fin r)) *
          Nat.card (alternatingGroup (Fin m))) := by ring
    rw [h4] at h1
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow 3 2
      ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)) (by simpa using h1)

theorem not_pow_three_dvd_of_five_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 3 ∣ 1080 ∧ ¬ p ^ 3 ∣ 2520 := by
  have key : ∀ n : ℕ, n ≤ 2520 → p ^ 3 ∣ n → n ≠ 0 → p ≤ 13 := by
    intro n hn h hn0
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h
    by_contra h13
    have : 14 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := key 1080 (by norm_num) h (by norm_num)
    interval_cases p <;> revert hp h <;> norm_num
  · have := key 2520 (by norm_num) h (by norm_num)
    interval_cases p <;> revert hp h <;> norm_num

end CFSG.AGLEmbedding
