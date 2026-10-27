module

public import CFSG.LocalAnalysis.ComponentClassification.SolvableKernelContainment
public import CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux
public import CFSG.Open.Defs
public import CFSG.Sporadic.Schreier.RuElemAut

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open Subgroup
open CFSG.HardMathSupport.Cooperstein.Coordinator

theorem eq_one_of_card_mulAut_lt {Lg Λ A : Type*} [Group Lg] [Finite Lg] [Group Λ] [Group A]
    [Finite A] (hperf : Group.IsPerfect Lg) (ψ : Lg →* Λ) (hψ : Function.Surjective ψ)
    (h2 : IsPGroup 2 ψ.ker) (hΛ : CFSG.Open.IsQuasisimple Λ)
    (hidx : 2520 ≤ (Subgroup.center Λ).index) (ρ : Lg →* MulAut A)
    (hA : Nat.card (MulAut A) < 2520) : ρ = 1 := by
  have : Finite Λ := Finite.of_surjective ψ hψ
  have := hperf
  set K := ρ.ker with hK
  have hKb : (K.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
  rcases StarAux.normal_le_center_or_eq_top hΛ.1 hΛ.2 (K.map ψ) hKb with hc | htop
  · exfalso
    have h1 : (Subgroup.center Λ).index ∣ (K.map ψ).index := Subgroup.index_dvd_of_le hc
    have hne : (K.map ψ).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h3 : 2520 ≤ (K.map ψ).index := hidx.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h1)
    have h4 : ((K.map ψ).comap ψ).index = (K.map ψ).index :=
      Subgroup.index_comap_of_surjective _ hψ
    have h5 : ((K.map ψ).comap ψ).index ∣ K.index :=
      Subgroup.index_dvd_of_le (Subgroup.le_comap_map ψ K)
    have h6 : K.index = Nat.card ρ.range := Subgroup.index_ker ρ
    have h7 : Nat.card ρ.range ≤ Nat.card (MulAut A) := Subgroup.card_le_card_group _
    have hKne : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h8 := Nat.le_of_dvd (Nat.pos_of_ne_zero hKne) h5
    omega
  ·
    have hrange2 : IsPGroup 2 ↥ρ.range := by
      rintro ⟨x, hx⟩
      obtain ⟨l, rfl⟩ := ρ.mem_range.1 hx
      have hl : ψ l ∈ K.map ψ := by rw [htop]; trivial
      obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.1 hl
      have hn : k⁻¹ * l ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkl, inv_mul_cancel]
      obtain ⟨e, he⟩ := h2 ⟨k⁻¹ * l, hn⟩
      refine ⟨e, ?_⟩
      have he' : (k⁻¹ * l) ^ 2 ^ e = 1 := congrArg Subtype.val he
      have hρk : ρ k = 1 := hk
      have : ρ l = ρ (k⁻¹ * l) := by
        rw [map_mul, map_inv, hρk, inv_one, one_mul]
      apply Subtype.ext
      show (ρ l) ^ 2 ^ e = 1
      rw [this, ← map_pow, he', map_one]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite ↥ρ.range := inferInstance
    have : Group.IsNilpotent ↥ρ.range := hrange2.isNilpotent
    have : Group.IsPerfect ↥ρ.range := Group.IsPerfect.ofSurjective ρ.rangeRestrict_surjective
    have := CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
      (G := ↥ρ.range)
    refine MonoidHom.ext fun l => ?_
    have : (⟨ρ l, ρ.mem_range.2 ⟨l, rfl⟩⟩ : ↥ρ.range) = 1 := Subsingleton.elim _ _
    rw [MonoidHom.one_apply]
    exact congrArg Subtype.val this

theorem eq_one_of_map_ker_eq_top {Lg Λ A : Type*} [Group Lg] [Finite Lg] [Group Λ] [Group A]
    [Finite A] (hperf : Group.IsPerfect Lg) (ψ : Lg →* Λ) (h2 : IsPGroup 2 ψ.ker)
    (ρ : Lg →* MulAut A) (htop : ρ.ker.map ψ = ⊤) : ρ = 1 := by
  have := hperf
  set K := ρ.ker with hK
  have hrange2 : IsPGroup 2 ↥ρ.range := by
    rintro ⟨x, hx⟩
    obtain ⟨l, rfl⟩ := ρ.mem_range.1 hx
    have hl : ψ l ∈ K.map ψ := by rw [htop]; trivial
    obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.1 hl
    have hn : k⁻¹ * l ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkl, inv_mul_cancel]
    obtain ⟨e, he⟩ := h2 ⟨k⁻¹ * l, hn⟩
    refine ⟨e, ?_⟩
    have he' : (k⁻¹ * l) ^ 2 ^ e = 1 := congrArg Subtype.val he
    have hρk : ρ k = 1 := hk
    have : ρ l = ρ (k⁻¹ * l) := by
      rw [map_mul, map_inv, hρk, inv_one, one_mul]
    apply Subtype.ext
    show (ρ l) ^ 2 ^ e = 1
    rw [this, ← map_pow, he', map_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥ρ.range := inferInstance
  have : Group.IsNilpotent ↥ρ.range := hrange2.isNilpotent
  have : Group.IsPerfect ↥ρ.range := Group.IsPerfect.ofSurjective ρ.rangeRestrict_surjective
  have := CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
    (G := ↥ρ.range)
  refine MonoidHom.ext fun l => ?_
  have : (⟨ρ l, ρ.mem_range.2 ⟨l, rfl⟩⟩ : ↥ρ.range) = 1 := Subsingleton.elim _ _
  rw [MonoidHom.one_apply]
  exact congrArg Subtype.val this

theorem card_mulAut_sixteen {A : Type*} [Group A] [Finite A] (hcomm : ∀ a b : A, a * b = b * a)
    (hpow : ∀ a : A, a ^ 2 = 1) (hcard : Nat.card A = 16) : Nat.card (MulAut A) = 20160 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.Sporadic.RuSchreier.ru_card_mulAut_elementary hcomm hpow (n := 4) (by rw [hcard]; norm_num)]
  simp [Fin.prod_univ_succ]

theorem card_mulAut_le_168 {A : Type*} [Group A] [Finite A] (hcomm : ∀ a b : A, a * b = b * a)
    (hpow : ∀ a : A, a ^ 2 = 1) (hcard : Nat.card A ≤ 8) : Nat.card (MulAut A) ≤ 168 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 A := fun a => ⟨1, by simpa using hpow a⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
  have hn3 : n ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [CFSG.Sporadic.RuSchreier.ru_card_mulAut_elementary hcomm hpow hn]
  interval_cases n <;> simp [Fin.prod_univ_succ]

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
