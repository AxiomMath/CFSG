module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

namespace A10Perm

open Equiv Equiv.Perm

theorem spt_ν₁_mem : ν₁ ∈ normalizer (S₀ : Set A10) :=
  mem_normalizer_of_mem_list (by simp)

theorem spt_ν₂_mem : ν₂ ∈ normalizer (S₀ : Set A10) :=
  mem_normalizer_of_mem_list (by simp)

theorem spt_a₁_pow_eq_one {i : ℕ} (h : i % 5 = 0) : a₁ ^ i = 1 := by
  rw [pow_eq_pow_mod i a₁_pow, h, pow_zero]

theorem spt_a₂_pow_eq_one {j : ℕ} (h : j % 5 = 0) : a₂ ^ j = 1 := by
  rw [pow_eq_pow_mod j a₂_pow, h, pow_zero]

theorem a10_swap : ∃ n ∈ normalizer (S₀ : Set A10),
    line₁.map (MulAut.conj n).toMonoidHom = line₂ ∧
      line₂.map (MulAut.conj n).toMonoidHom = line₁ := by
  have e1 : line₁ = zpowers a₁ := by
    simpa using (zpowers_a₁_pow (i := 1) (by simpa using a₁_ne)).symm
  have e2 : line₂ = zpowers a₂ := by
    simpa using (zpowers_a₂_pow (j := 1) (by simpa using a₂_ne)).symm
  refine ⟨ν₂, spt_ν₂_mem, ?_, ?_⟩
  · rw [e1, MonoidHom.map_zpowers]
    have h : (MulAut.conj ν₂).toMonoidHom a₁ = a₂ ^ 2 := by
      simpa [MulAut.conj_apply] using ν₂_a₁
    rw [h, e2]
    exact zpowers_pow_eq (orderOf_eq_five a₂_pow a₂_ne) (by norm_num)
  · rw [e2, MonoidHom.map_zpowers]
    have h : (MulAut.conj ν₂).toMonoidHom a₂ = a₁ := by
      simpa [MulAut.conj_apply] using ν₂_a₂
    rw [h, e1]

theorem spt_ν₁_conj (i j : ℕ) : ν₁ * (a₁ ^ i * a₂ ^ j) * ν₁⁻¹ = a₁ ^ (4 * i) * a₂ ^ j := by
  rw [conj_gen, ν₁_a₁, ν₁_a₂]
  simp [← pow_mul]

theorem spt_ν₂_conj (i j : ℕ) : ν₂ * (a₁ ^ i * a₂ ^ j) * ν₂⁻¹ = a₁ ^ j * a₂ ^ (2 * i) := by
  rw [conj_gen, ν₂_a₁, ν₂_a₂]
  simp only [pow_zero, one_mul, mul_one, pow_one, ← pow_mul]
  exact (a₁₂_commute.symm.pow_pow (2 * i) j).eq

theorem spt_pow_normal (i j m : ℕ) : (a₁ ^ i * a₂ ^ j) ^ m = a₁ ^ (i * m) * a₂ ^ (j * m) := by
  rw [(a₁₂_commute.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul]

theorem spt_moves_arith (i j m m' : ℕ) (hij : ¬ (i % 5 = 0 ∧ j % 5 = 0))
    (h1 : (4 * i) % 5 = (i * m) % 5) (h2 : j % 5 = (j * m) % 5)
    (h3 : j % 5 = (i * m') % 5) (h4 : (2 * i) % 5 = (j * m') % 5) : False := by
  have key : ∀ a < 5, ∀ b < 5, ∀ c < 5, ∀ d < 5, ¬ (a = 0 ∧ b = 0) →
      ¬ ((4 * a) % 5 = (a * c) % 5 ∧ b % 5 = (b * c) % 5 ∧ b % 5 = (a * d) % 5 ∧
        (2 * a) % 5 = (b * d) % 5) := by
    intro a ha b hb c hc d hd
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> decide
  refine key (i % 5) (Nat.mod_lt _ (by norm_num)) (j % 5) (Nat.mod_lt _ (by norm_num))
    (m % 5) (Nat.mod_lt _ (by norm_num)) (m' % 5) (Nat.mod_lt _ (by norm_num)) hij ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Nat.mul_mod] using h1
  · simpa [Nat.mul_mod] using h2
  · simpa [Nat.mul_mod] using h3
  · simpa [Nat.mul_mod] using h4

theorem spt_a10_moves {t : A10} (ht : t ∈ S₀) (ht1 : t ≠ 1) :
    ∃ n ∈ normalizer (S₀ : Set A10), n * t * n⁻¹ ∉ zpowers t := by
  obtain ⟨i, j, rfl⟩ := mem_S₀.1 ht
  have hij : ¬ (i % 5 = 0 ∧ j % 5 = 0) := by
    rintro ⟨hi, hj⟩
    exact ht1 (by rw [spt_a₁_pow_eq_one hi, spt_a₂_pow_eq_one hj, one_mul])
  by_contra hcon
  push Not at hcon
  obtain ⟨m, hm⟩ := mem_zpowers_nat.1 (hcon ν₁ spt_ν₁_mem)
  obtain ⟨m', hm'⟩ := mem_zpowers_nat.1 (hcon ν₂ spt_ν₂_mem)
  rw [spt_pow_normal, spt_ν₁_conj] at hm
  rw [spt_pow_normal, spt_ν₂_conj] at hm'
  obtain ⟨h1, h2⟩ := exp_inj hm.symm
  obtain ⟨h3, h4⟩ := exp_inj hm'.symm
  exact spt_moves_arith i j m m' hij h1 h2 h3 h4

end A10Perm

theorem a10_movesLines :
    ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → NormalizerMovesLines 5 K := by
  intro K _ _ hK S t ht ht1
  obtain ⟨-, ⟨e⟩⟩ := hK
  obtain ⟨ψ, hψ⟩ := A10Perm.exists_iso_sylow (e : K ≃* alternatingGroup (Fin 10)) S
  have htS : ψ t ∈ A10Perm.S₀ := (hψ t).1 ht
  have ht1' : ψ t ≠ 1 := fun h => ht1 (ψ.injective (by rw [h, map_one]))
  obtain ⟨n₀, hn₀, hmov⟩ := A10Perm.spt_a10_moves htS ht1'
  refine ⟨ψ.symm n₀, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hψ, hψ]
    have := (Subgroup.mem_normalizer_iff.1 hn₀) (ψ y)
    simpa [map_mul, map_inv] using this
  · intro hmem
    apply hmov
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have := congrArg ψ hk
    simpa [map_mul, map_inv, map_zpow] using this

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
