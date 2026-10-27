module

public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.ProjectiveIndex
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.UnitaryInvolutionIndex

open Matrix

section Transfer

variable {G L : Type*} [Group G] [Group L]

theorem relIndex_centralizer_map_eq [Finite G] (π : G →* L) (hker : π.ker ≤ Subgroup.center G)
    (hodd : Odd (Nat.card π.ker)) (P : Subgroup G) {t : G} (ht : t ^ 2 = 1) :
    (P.map π ⊓ Subgroup.centralizer {π t}).relIndex (P.map π) =
      (P ⊓ Subgroup.centralizer {t}).relIndex P := by
  set C' := (P.map π ⊓ Subgroup.centralizer {π t}).subgroupOf (P.map π)
  have hcomap : (C'.comap (π.subgroupMap P)).index = C'.index :=
    Subgroup.index_comap_of_surjective C' (π.subgroupMap_surjective P)
  have htt : t * t = 1 := by rw [← sq, ht]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have heq : C'.comap (π.subgroupMap P) = (P ⊓ Subgroup.centralizer {t}).subgroupOf P := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    change (π x ∈ P.map π ∧ π x * π t = π t * π x) ↔ ((x : G) ∈ P ∧ (x : G) * t = t * x)
    constructor
    swap
    · rintro ⟨-, hxt⟩
      exact ⟨Subgroup.mem_map_of_mem π x.2, by rw [← map_mul, ← map_mul, hxt]⟩
    rintro ⟨-, hxt⟩
    refine ⟨x.2, ?_⟩
    generalize (x : G) = y at hxt ⊢
    obtain ⟨n, hn⟩ : ∃ n, n = y⁻¹ * (t * y * t⁻¹) := ⟨_, rfl⟩
    have hnker : n ∈ π.ker := by
      rw [MonoidHom.mem_ker, hn, map_mul, map_inv, map_mul, map_mul, map_inv, ← hxt,
        mul_inv_cancel_right, inv_mul_cancel]
    have hnc := Subgroup.mem_center_iff.mp (hker hnker)
    have htn : t * n * t⁻¹ = n := by rw [hnc t, mul_inv_cancel_right]
    have hty : t * y * t⁻¹ = y * n := by rw [hn, mul_inv_cancel_left]
    have h1 : y = y * n * n := by
      calc y = (t * t) * y * (t * t) := by rw [htt, one_mul, mul_one]
        _ = t * (t * y * t⁻¹) * t⁻¹ := by rw [htinv]; group
        _ = t * (y * n) * t⁻¹ := by rw [hty]
        _ = (t * y * t⁻¹) * (t * n * t⁻¹) := by group
        _ = y * n * n := by rw [hty, htn]
    have hnn : n * n = 1 := by
      have h2 : y * (n * n) = y * 1 := by rw [mul_one, ← mul_assoc, ← h1]
      exact mul_left_cancel h2
    have hn1 : n = 1 := by
      have hN : n ^ Nat.card π.ker = 1 := by
        have := pow_card_eq_one' (G := π.ker) (x := ⟨n, hnker⟩)
        exact congrArg Subtype.val this
      have h2 : n ^ 2 = 1 := by rw [sq, hnn]
      have h := pow_gcd_eq_one.mpr ⟨h2, hN⟩
      rwa [Nat.coprime_two_left.mpr hodd, pow_one] at h
    rw [hn1, mul_one] at hty
    calc y * t = t * y * t⁻¹ * t := by rw [hty]
      _ = t * y := by group
  rw [Subgroup.relIndex, Subgroup.relIndex, ← hcomap, heq]

theorem relIndex_centralizer_le_card_map [Finite G] (π : G →* L)
    (hker : π.ker ≤ Subgroup.center G) (P : Subgroup G) (t : G) :
    (P ⊓ Subgroup.centralizer {t}).relIndex P ≤ Nat.card (P.map π) := by
  have hle : (π.comp P.subtype).ker ≤ (P ⊓ Subgroup.centralizer {t}).subgroupOf P := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨x.2, (Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hx)) t).symm⟩
  have hidx : (π.comp P.subtype).ker.index = Nat.card (P.map π) := by
    rw [Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [Subgroup.relIndex, ← hidx]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
    (Subgroup.index_dvd_of_le hle)

end Transfer

@[expose] def signScalars (K : Type*) [Field K] : Subgroup (SpecialLinearGroup (Fin 2) K) where
  carrier := {g | ∃ c : Kˣ, c ^ 2 = 1 ∧
    (g : Matrix (Fin 2) (Fin 2) K) = scalar (Fin 2) (c : K)}
  one_mem' := ⟨1, one_pow 2, by simp⟩
  mul_mem' := by
    rintro g g' ⟨c, hc2, hc⟩ ⟨d, hd2, hd⟩
    refine ⟨c * d, by rw [mul_pow, hc2, hd2, one_mul], ?_⟩
    rw [SpecialLinearGroup.coe_mul, hc, hd, Units.val_mul, map_mul]
  inv_mem' := by
    rintro g ⟨c, hc2, hc⟩
    refine ⟨c⁻¹, by rw [inv_pow, hc2, inv_one], ?_⟩
    have h1 : (g : Matrix (Fin 2) (Fin 2) K) * scalar (Fin 2) ((c⁻¹ : Kˣ) : K) = 1 := by
      rw [hc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    calc ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        = ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            ((g : Matrix (Fin 2) (Fin 2) K) * scalar (Fin 2) ((c⁻¹ : Kˣ) : K)) := by
          rw [h1, Matrix.mul_one]
      _ = scalar (Fin 2) ((c⁻¹ : Kˣ) : K) := by
          rw [← Matrix.mul_assoc, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
            SpecialLinearGroup.coe_one, Matrix.one_mul]

instance (K : Type*) [Field K] : (signScalars K).Normal where
  conj_mem g hg x := by
    obtain ⟨c, hc2, hc⟩ := hg
    refine ⟨c, hc2, ?_⟩
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hc,
      ((scalar_commute (c : K) (fun r => Commute.all _ r) _).eq).symm, Matrix.mul_assoc,
      ← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one, Matrix.mul_one]

theorem card_specialLinearGroup_fin_two (K : Type*) [Field K] [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem pow_dvd_succ_of_dvd_card {p q r j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1)
    (hr : r = q ∨ r = q ^ 2) (h : p ^ j ∣ r * (r ^ 2 - 1)) : p ^ j ∣ q + 1 := by
  have hq0 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact absurd (Nat.dvd_one.mp hpq) hp.one_lt.ne'
    · exact hq
  have hcop : ∀ m : ℕ, ¬p ∣ m → Nat.Coprime (p ^ j) m := fun m hm =>
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  have hnq : ¬p ∣ q := fun hd => hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hd).mp hpq))
  have hnq1 : ¬p ∣ q - 1 := by
    intro hd
    have h2 : q + 1 = (q - 1) + 2 := by omega
    rw [h2] at hpq
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((Nat.dvd_add_right hd).mp hpq))
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [hq0, Nat.one_le_pow 2 q hq0]
    ring
  rcases hr with rfl | rfl
  · rw [hfac] at h
    exact (hcop _ hnq1).dvd_of_dvd_mul_left ((hcop _ hnq).dvd_of_dvd_mul_left h)
  · have hnq2 : ¬p ∣ q ^ 2 + 1 := by
      intro hd
      have h2 : q ^ 2 + 1 = (q - 1) * (q + 1) + 2 := by
        rw [← hfac]
        have := Nat.one_le_pow 2 q hq0
        omega
      rw [h2] at hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        ((Nat.dvd_add_right (Dvd.dvd.mul_left hpq _)).mp hd))
    have hfac2 : (q ^ 2) ^ 2 - 1 = (q ^ 2 + 1) * ((q - 1) * (q + 1)) := by
      rw [← hfac]
      have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq0
      zify [h1, Nat.one_le_pow 2 (q ^ 2) h1]
      ring
    rw [hfac2] at h
    have h1 := (Nat.Coprime.pow_right 2 (hcop _ hnq)).dvd_of_dvd_mul_left h
    exact (hcop _ hnq1).dvd_of_dvd_mul_left ((hcop _ hnq2).dvd_of_dvd_mul_left h1)

variable {G L : Type*} [Group G] [Finite G] [Group L] {p q : ℕ}

theorem relIndex_centralizer_le_of_mulEquiv_linear (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ q + 1) (π : G →* L) (hker : π.ker ≤ Subgroup.center G) (K : Type*) [Field K]
    [Finite K] (hK : Nat.card K = q ∨ Nat.card K = q ^ 2)
    (e : L ≃* SpecialLinearGroup (Fin 2) K ⧸ signScalars K) (P : Subgroup G)
    (hP : IsPGroup p P) (t : G) :
    (P ⊓ Subgroup.centralizer {t}).relIndex P ≤ p ^ (q + 1).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  refine (relIndex_centralizer_le_card_map π hker P t).trans ?_
  have : Finite (P.map π) := Finite.of_surjective _ (π.subgroupMap_surjective P)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hP.of_surjective _ (π.subgroupMap_surjective P))
  have hdvd : Nat.card (P.map π) ∣ Nat.card (SpecialLinearGroup (Fin 2) K) := by
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact (Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)
  rw [card_specialLinearGroup_fin_two, hj] at hdvd
  have h1 := pow_dvd_succ_of_dvd_card hp hp2 hpq hK hdvd
  rw [hj]
  refine Nat.le_of_dvd (pow_pos hp.pos _) (pow_dvd_pow p ?_)
  exact (hp.pow_dvd_iff_le_factorization (Nat.succ_ne_zero q)).mp h1

theorem relIndex_centralizer_le_of_mulEquiv_unitary (hq : IsPrimePow q) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ q + 1) (π : G →* L) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hodd : Odd (Nat.card π.ker)) {F : Type*} [Field F]
    [Finite F] (hF : Nat.card F = q ^ 2) {σ : F →+* F} (hσ : ∀ c, σ c = c ^ q)
    {h : (Fin 3 → F) →ₛₗ[σ] (Fin 3 → F) →ₗ[F] F} (hh : h.Nondegenerate)
    (e : L ≃* projectiveSpecialUnitaryGroup h) (P : Subgroup G) (hP : IsPGroup p P) (t : G)
    (ht : t ^ 2 = 1) (htP : t ∈ Subgroup.normalizer (P : Set G)) :
    (P ⊓ Subgroup.centralizer {t}).relIndex P ≤ 3 * p ^ (q + 1).factorization p ∧
      (p ≠ 3 → (P ⊓ Subgroup.centralizer {t}).relIndex P ≤ p ^ (q + 1).factorization p) := by
  set ψ : G →* projectiveSpecialUnitaryGroup h := e.toMonoidHom.comp π
  have hψker : ψ.ker = π.ker := by
    ext x
    simp only [ψ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hψ : Function.Surjective ψ := e.surjective.comp hπ
  rw [← relIndex_centralizer_map_eq ψ (hψker ▸ hker) (hψker ▸ hodd) P ht]
  exact projective_unitary_three_odd_subgroup_involution_index_bound hq hF hσ hh hp hp2 hpq
    (P.map ψ) (hP.of_surjective _ (ψ.subgroupMap_surjective P)) (ψ t)
    (by rw [← map_pow, ht, map_one]) (Subgroup.le_normalizer_map ψ (Subgroup.mem_map_of_mem ψ htP))

theorem exists_odd_prime_dvd_succ_three_lt (hq2 : Even q) (hq4 : 4 ≤ q) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ q + 1 ∧ 3 < p ^ (q + 1).factorization p := by
  have hodd : ¬2 ∣ q + 1 := by
    rw [← even_iff_two_dvd, Nat.even_add_one, not_not]
    exact hq2
  have hne2 : ∀ d, d ∣ q + 1 → d ≠ 2 := fun d hd h => hodd (h ▸ hd)
  by_cases h : ∃ d, d.Prime ∧ d ∣ q + 1 ∧ d ≠ 3
  · obtain ⟨d, hd, hdq, hd3⟩ := h
    refine ⟨d, hd, hne2 d hdq, hdq, ?_⟩
    have hv := hd.factorization_pos_of_dvd (Nat.succ_ne_zero q) hdq
    have hd4 : 3 < d := by
      have := hd.two_le
      have := hne2 d hdq
      omega
    calc 3 < d := hd4
      _ = d ^ 1 := (pow_one d).symm
      _ ≤ d ^ (q + 1).factorization d := Nat.pow_le_pow_right hd.pos hv
  · push Not at h
    have h3 : q + 1 = 3 ^ (q + 1).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd (Nat.succ_ne_zero q) fun hd hdq => h _ hd hdq
    have h3dvd : 3 ∣ q + 1 := by
      have hne : (q + 1).primeFactorsList.length ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at h3
        omega
      rw [h3]
      exact dvd_pow_self 3 hne
    refine ⟨3, Nat.prime_three, by norm_num, h3dvd, ?_⟩
    have hfac : (q + 1).factorization 3 = (q + 1).primeFactorsList.length := by
      conv_lhs => rw [h3]
      rw [Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
    rw [hfac, ← h3]
    omega

theorem even_rank_one_central_odd_extension_involution_index_bound (hq : IsPrimePow q)
    (hq2 : Even q) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1) (π : G →* L)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (hodd : Odd (Nat.card π.ker)) (P : Subgroup G) (hP : IsPGroup p P) (t : G) (ht : t ^ 2 = 1)
    (htP : t ∈ Subgroup.normalizer (P : Set G)) :
    (∀ (K : Type*) [Field K] [Finite K], (Nat.card K = q ∨ Nat.card K = q ^ 2) →
        Nonempty (L ≃* SpecialLinearGroup (Fin 2) K ⧸ signScalars K) →
        (P ⊓ Subgroup.centralizer {t}).relIndex P ≤ p ^ (q + 1).factorization p ∧
          (3 < p ^ (q + 1).factorization p →
            (P ⊓ Subgroup.centralizer {t}).relIndex P < (p ^ (q + 1).factorization p) ^ 2)) ∧
    (∀ (F : Type*) [Field F] [Finite F] (σ : F →+* F)
        (h : (Fin 3 → F) →ₛₗ[σ] (Fin 3 → F) →ₗ[F] F), Nat.card F = q ^ 2 →
        (∀ c, σ c = c ^ q) → h.Nondegenerate →
        Nonempty (L ≃* projectiveSpecialUnitaryGroup h) →
        (P ⊓ Subgroup.centralizer {t}).relIndex P ≤ 3 * p ^ (q + 1).factorization p ∧
          (p ≠ 3 →
            (P ⊓ Subgroup.centralizer {t}).relIndex P ≤ p ^ (q + 1).factorization p) ∧
          (3 < p ^ (q + 1).factorization p →
            (P ⊓ Subgroup.centralizer {t}).relIndex P < (p ^ (q + 1).factorization p) ^ 2)) ∧
    (4 ≤ q → ∃ p' : ℕ, p'.Prime ∧ p' ≠ 2 ∧ p' ∣ q + 1 ∧ 3 < p' ^ (q + 1).factorization p') := by
  refine ⟨fun K _ _ hK ⟨e⟩ => ?_, fun F _ _ σ h hF hσ hh ⟨e⟩ => ?_,
    fun hq4 => exists_odd_prime_dvd_succ_three_lt hq2 hq4⟩
  · have h1 := relIndex_centralizer_le_of_mulEquiv_linear hp hp2 hpq π hker K hK e P hP t
    refine ⟨h1, fun ha => h1.trans_lt ?_⟩
    calc p ^ (q + 1).factorization p = p ^ (q + 1).factorization p * 1 := (mul_one _).symm
      _ < p ^ (q + 1).factorization p * p ^ (q + 1).factorization p :=
          Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      _ = (p ^ (q + 1).factorization p) ^ 2 := (sq _).symm
  · obtain ⟨h3, h1⟩ := relIndex_centralizer_le_of_mulEquiv_unitary hq hp hp2 hpq π hπ hker hodd
      hF hσ hh e P hP t ht htP
    refine ⟨h3, h1, fun ha => h3.trans_lt ?_⟩
    rw [sq]
    exact Nat.mul_lt_mul_of_pos_right ha (by omega)

end CFSG.UnitaryInvolutionIndex
