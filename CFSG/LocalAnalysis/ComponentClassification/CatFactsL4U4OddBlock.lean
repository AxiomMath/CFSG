module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupPSL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open Matrix Subgroup

theorem sq_eq_one_of_mem_center_SL2 {K : Type} [Field K] {z : SpecialLinearGroup (Fin 2) K}
    (hz : z ∈ center (SpecialLinearGroup (Fin 2) K)) : z ^ 2 = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  rw [sq]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, ← hrz, ← map_mul, ← sq, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem odd_card_of_forall_odd {G : Type*} [Group G] [Finite G]
    (h : ∀ g : G, Odd (orderOf g)) : Odd (Nat.card G) := by
  rcases Nat.even_or_odd (Nat.card G) with he | ho
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (even_iff_two_dvd.1 he)
    have := h g
    rw [hg] at this
    exact (Nat.not_odd_iff_even.2 even_two) this
  · exact ho

theorem eq_bot_of_normal_odd {K : Type} [Field K] [Finite K]
    (hK : GorensteinWalter.IsOddPrimePower (Nat.card K))
    (R : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) K)) (hRn : R.Normal)
    (hodd : Odd (Nat.card R)) : R = ⊥ := by
  have hcard := GorensteinWalter.psl2_card_formula K hK
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hK
  have hqodd : Odd (Nat.card K) := hq ▸ hpodd.pow
  have hq3 : 3 ≤ Nat.card K := by
    rw [hq]
    have := hp.two_le
    have h3 : 3 ≤ p := by
      rcases hpodd with ⟨k, rfl⟩
      omega
    calc 3 ≤ p := h3
      _ ≤ p ^ n := Nat.le_self_pow (by omega) p
  obtain ⟨k, hk⟩ := hqodd
  have hcard' : Nat.card (ProjectiveSpecialLinearGroup (Fin 2) K) =
      (2 * k + 1) * (2 * (k * (k + 1))) := by
    rw [hcard, hk]
    have e1 : (2 * k + 1) ^ 2 - 1 = 2 * (2 * (k * (k + 1))) := by
      have : (2 * k + 1) ^ 2 = 2 * (2 * (k * (k + 1))) + 1 := by ring
      omega
    rw [e1, show (2 * k + 1) * (2 * (2 * (k * (k + 1)))) = 2 * ((2 * k + 1) * (2 * (k * (k + 1))))
      by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  by_cases h4 : 4 ≤ Nat.card K
  · have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    rcases hRn.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      rw [h, card_top, hcard'] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (by
        refine Even.mul_left ?_ _
        exact ⟨k * (k + 1), by ring⟩)
  · have h3 : Nat.card K = 3 := by omega
    have hk1 : k = 1 := by omega
    subst hk1
    have hdvd : Nat.card R ∣ 3 := by
      have h12 := card_subgroup_dvd_card R
      rw [hcard', show (2 * 1 + 1) * (2 * (1 * (1 + 1))) = 2 ^ 2 * 3 by norm_num] at h12
      exact (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)).symm.dvd_of_dvd_mul_left h12
    have hR3 : IsPGroup 3 R := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
      · exact IsPGroup.of_card (n := 0) (by rw [h1, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [h1, pow_one])
    exact GorensteinWalter.normal_pSubgroup_eq_bot_of_psl2_odd K ⟨p, n, hp, hpodd, hn, hq⟩ 3
      Nat.prime_three (by decide) R hRn hR3

theorem eq_bot_of_odd_block {K : Type} [Field K] [Finite K]
    (hK : GorensteinWalter.IsOddPrimePower (Nat.card K)) {G : Type} [Group G] [Finite G]
    (β : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K →* G)
    (hker : ∀ x ∈ β.ker, x.1 ∈ center (SpecialLinearGroup (Fin 2) K) ∧
      x.2 ∈ center (SpecialLinearGroup (Fin 2) K))
    (R : Subgroup G) (hRS : R ≤ β.range) (hR : ∀ g ∈ β.range, ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (hodd : Odd (Nat.card R)) : R = ⊥ := by
  classical
  set R' := R.comap β with hR'
  have hR'n : R'.Normal := ⟨fun x hx y => by
    rw [hR', mem_comap] at hx ⊢
    rw [map_mul, map_mul, map_inv]
    exact hR _ ⟨y, rfl⟩ _ hx⟩
  have hoddR : ∀ x ∈ R', Odd (orderOf (β x)) := fun x hx =>
    Odd.of_dvd_nat hodd (by
      have := orderOf_dvd_natCard (⟨β x, hx⟩ : R)
      rw [← Subgroup.orderOf_coe] at this
      exact this)
  have hproj : ∀ (ρ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K →*
      SpecialLinearGroup (Fin 2) K), Function.Surjective ρ →
      (∀ x ∈ β.ker, ρ x ∈ center (SpecialLinearGroup (Fin 2) K)) →
      ∀ x ∈ R', ρ x ∈ center (SpecialLinearGroup (Fin 2) K) := by
    intro ρ hρ hρk
    set π₂ := QuotientGroup.mk' (center (SpecialLinearGroup (Fin 2) K)) with hπ₂
    set R₁ := R'.map (π₂.comp ρ) with hR₁
    have hR₁n : R₁.Normal := hR'n.map _ ((QuotientGroup.mk'_surjective _).comp hρ)
    have hR₁odd : Odd (Nat.card R₁) := by
      apply odd_card_of_forall_odd
      rintro ⟨y, x, hx, rfl⟩
      set m := orderOf (β x) with hm
      have hxm : x ^ m ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_pow, hm, pow_orderOf_eq_one]
      have hym : (π₂.comp ρ) x ^ m = 1 := by
        rw [← map_pow, MonoidHom.comp_apply, hπ₂, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
        exact hρk _ hxm
      have h1 : orderOf (⟨(π₂.comp ρ) x, mem_map_of_mem _ hx⟩ : R₁) ∣ m := by
        rw [← Subgroup.orderOf_coe]
        exact orderOf_dvd_of_pow_eq_one hym
      exact Odd.of_dvd_nat (hoddR x hx) h1
    have hR₁bot := eq_bot_of_normal_odd hK R₁ hR₁n hR₁odd
    intro x hx
    have : (π₂.comp ρ) x ∈ R₁ := ⟨x, hx, rfl⟩
    rw [hR₁bot, mem_bot, MonoidHom.comp_apply, hπ₂, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at this
    exact this
  have h1 := hproj (MonoidHom.fst _ _) Prod.fst_surjective fun x hx => (hker x hx).1
  have h2 := hproj (MonoidHom.snd _ _) Prod.snd_surjective fun x hx => (hker x hx).2
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨x, rfl⟩ := hRS hr
  have hx : x ∈ R' := hr
  have hx2 : x ^ 2 = 1 := Prod.ext (sq_eq_one_of_mem_center_SL2 (h1 x hx))
    (sq_eq_one_of_mem_center_SL2 (h2 x hx))
  have ho := hoddR x hx
  have hd : orderOf (β x) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx2, map_one])
  rw [mem_bot, ← orderOf_eq_one_iff]
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
  · exact h
  · rw [h] at ho
    exact absurd ho (by decide)

end CFSG.ComponentClassification.CatFactsL4U4
