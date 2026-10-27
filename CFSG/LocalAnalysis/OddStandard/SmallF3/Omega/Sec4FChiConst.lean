module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FFiber
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FTrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

private lemma sec4F_units_conj (u v : ℤˣ) : u * v * u⁻¹ = v := by
  rw [mul_comm u v, mul_assoc, mul_inv_cancel, mul_one]

private lemma sec4F_units_eq_one_of_odd {H : Type*} [Group H] (ψ : H →* ℤˣ) {o : H}
    (hodd : Odd (orderOf o)) : ψ o = 1 := by
  have hpow : ψ o ^ orderOf o = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨k, hk⟩ := hodd
  have h1 : ψ o ^ (2 * k + 1) = ψ o := by
    rw [pow_add, pow_mul, Int.units_sq, one_pow, one_mul, pow_one]
  rw [hk, h1] at hpow
  exact hpow

theorem Sec4FSetup.chi0_pt (h : Sec4FSetup t L S z A B φ)
    (χ₀ : ↥(normalizer (A : Set G)) →* ℤˣ)
    (ht : ∀ ht' : t ∈ normalizer (A : Set G), χ₀ ⟨t, ht'⟩ = -1) (p : Option (Fin 7))
    (hp : sec4MPt t φ p ∈ normalizer (A : Set G)) : χ₀ ⟨sec4MPt t φ p, hp⟩ = -1 := by
  obtain ⟨n, hn, hnpt⟩ := h.exists_conj_pt p
  have htM : t ∈ normalizer (A : Set G) := Subgroup.le_normalizer h.t_mem_A
  have hsub : (⟨sec4MPt t φ p, hp⟩ : ↥(normalizer (A : Set G))) =
      ⟨n, hn⟩ * ⟨t, htM⟩ * ⟨n, hn⟩⁻¹ := by
    apply Subtype.ext
    change sec4MPt t φ p = n * t * n⁻¹
    exact hnpt
  rw [hsub, map_mul, map_mul, map_inv, ht htM]
  exact sec4F_units_conj (χ₀ ⟨n, hn⟩) (-1)

theorem Sec4FSetup.chi0_swap (h : Sec4FSetup t L S z A B φ)
    (χ₀ : ↥(normalizer (A : Set G)) →* ℤˣ)
    (ht : ∀ ht' : t ∈ normalizer (A : Set G), χ₀ ⟨t, ht'⟩ = -1) {y y' : G}
    (hy : ∃ g : G, y = g⁻¹ * t * g) (hy' : ∃ g : G, y' = g⁻¹ * t * g)
    (hyN : y ∈ normalizer (A : Set G)) (hy'N : y' ∈ normalizer (A : Set G))
    {a b a' b' : Option (Fin 7)} (hab : a ≠ b) (hab' : a' ≠ b')
    (hσ : Sec4MRealizes t φ y (Equiv.swap a b))
    (hσ' : Sec4MRealizes t φ y' (Equiv.swap a' b')) : χ₀ ⟨y, hyN⟩ = χ₀ ⟨y', hy'N⟩ := by
  obtain ⟨m, ν, hm, hν, hνa, hνb⟩ := h.exists_two_trans hab hab'
  set y'' : G := m * y' * m⁻¹ with hy''def
  have hy''N : y'' ∈ normalizer (A : Set G) := by
    rw [hy''def]
    exact (normalizer (A : Set G)).mul_mem
      ((normalizer (A : Set G)).mul_mem hm hy'N) ((normalizer (A : Set G)).inv_mem hm)
  have hy'' : ∃ g : G, y'' = g⁻¹ * t * g := by
    obtain ⟨g, hg⟩ := hy'
    refine ⟨g * m⁻¹, ?_⟩
    rw [hy''def, hg]
    group
  have hσ'' : Sec4MRealizes t φ y'' (Equiv.swap a b) := by
    have h1 : Sec4MRealizes t φ (m * y' * m⁻¹) ((ν * Equiv.swap a' b') * ν⁻¹) :=
      Sec4MRealizes.mul (Sec4MRealizes.mul hν hσ') (Sec4MRealizes.inv hν)
    have hperm : (ν * Equiv.swap a' b') * ν⁻¹ = Equiv.swap a b := by
      rw [← Equiv.swap_apply_apply ν a' b', hνa, hνb]
    rw [← hy''def, hperm] at h1
    exact h1
  have hχ'' : χ₀ ⟨y'', hy''N⟩ = χ₀ ⟨y', hy'N⟩ := by
    have hconj : (⟨m, hm⟩ * ⟨y', hy'N⟩ * ⟨m, hm⟩⁻¹ : ↥(normalizer (A : Set G))) =
        ⟨y'', hy''N⟩ := by
      apply Subtype.ext
      change m * y' * m⁻¹ = y''
      rw [hy''def]
    rw [← hconj, map_mul, map_mul, map_inv]
    exact sec4F_units_conj (χ₀ ⟨m, hm⟩) (χ₀ ⟨y', hy'N⟩)
  obtain ⟨o, hoC, hodd, hcase⟩ := h.fiber hy hy'' hyN hy''N hab hσ hσ''
  have hoM : o ∈ normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer (A : Set G) hoC
  have ho_one : χ₀ ⟨o, hoM⟩ = 1 :=
    sec4F_units_eq_one_of_odd χ₀ (by simpa using hodd)
  have hwM : y⁻¹ * y'' ∈ normalizer (A : Set G) :=
    (normalizer (A : Set G)).mul_mem ((normalizer (A : Set G)).inv_mem hyN) hy''N
  have hw_one : χ₀ ⟨y⁻¹ * y'', hwM⟩ = 1 := by
    rcases hcase with hw | hw
    · have hsub : (⟨y⁻¹ * y'', hwM⟩ : ↥(normalizer (A : Set G))) = ⟨o, hoM⟩ := by
        apply Subtype.ext
        change y⁻¹ * y'' = o
        exact hw
      rw [hsub, ho_one]
    · have hpaM : sec4MPt t φ a ∈ normalizer (A : Set G) :=
        Subgroup.le_normalizer (sec4MPt_mem_A h.data a)
      have hpbM : sec4MPt t φ b ∈ normalizer (A : Set G) :=
        Subgroup.le_normalizer (sec4MPt_mem_A h.data b)
      have hsub : (⟨y⁻¹ * y'', hwM⟩ : ↥(normalizer (A : Set G))) =
          ⟨sec4MPt t φ a, hpaM⟩ * ⟨sec4MPt t φ b, hpbM⟩ * ⟨o, hoM⟩ := by
        apply Subtype.ext
        change y⁻¹ * y'' = sec4MPt t φ a * sec4MPt t φ b * o
        exact hw
      rw [hsub, map_mul, map_mul, h.chi0_pt χ₀ ht a hpaM, h.chi0_pt χ₀ ht b hpbM,
        ho_one]
      simp
  have hdecomp : χ₀ ⟨y'', hy''N⟩ = χ₀ ⟨y, hyN⟩ * χ₀ ⟨y⁻¹ * y'', hwM⟩ := by
    have hsub : (⟨y'', hy''N⟩ : ↥(normalizer (A : Set G))) =
        ⟨y, hyN⟩ * ⟨y⁻¹ * y'', hwM⟩ := by
      apply Subtype.ext
      change y'' = y * (y⁻¹ * y'')
      group
    rw [hsub, map_mul]
  have hfinal : χ₀ ⟨y'', hy''N⟩ = χ₀ ⟨y, hyN⟩ := by
    rw [hdecomp, hw_one, mul_one]
  rw [← hfinal, hχ'']

end CFSG.OddStandard.SmallF3.Omega
