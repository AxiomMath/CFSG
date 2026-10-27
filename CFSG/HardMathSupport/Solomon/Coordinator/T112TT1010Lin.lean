module

public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.OutStructure

theorem cube_mod_nine (c : ℕ) : c ^ 3 % 9 = 0 ∨ c ^ 3 % 9 = 1 ∨ c ^ 3 % 9 = 8 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt c (show 0 < 9 by norm_num)
  interval_cases (c % 9) <;> simp

theorem not_three_dvd_degree {F : Type} [Field F] [Finite F] {p n : ℕ}
    (hF : Nat.card F % 9 = 4 ∨ Nat.card F % 9 = 7) (hn : Nat.card F = p ^ n) : ¬ 3 ∣ n := by
  rintro ⟨m, rfl⟩
  have h := cube_mod_nine (p ^ m)
  rw [← pow_mul, mul_comm, ← hn] at h
  omega

section Main

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem conj_pow_three (B : GL (Fin 3) F) (τ : F ≃+* F) :
    ∃ C : GL (Fin 3) F, (conjAut 3 F B * fieldAut 3 F τ) ^ 3 = conjAut 3 F C * fieldAut 3 F (τ ^ 3) := by
  refine ⟨B * GeneralLinearGroup.map (τ : F →+* F) B *
    GeneralLinearGroup.map ((τ * τ : F ≃+* F) : F →+* F) B, ?_⟩
  have h2 := conjAut_mul_fieldAut_mul B B τ τ
  have h3 := conjAut_mul_fieldAut_mul (B * GeneralLinearGroup.map (τ : F →+* F) B) B (τ * τ) τ
  rw [pow_succ, pow_two, h2, h3]
  congr 2

theorem le_linearAutGroup_of_elemAbelian {p n : ℕ} (hn : Nat.card F = p ^ n) (hp : p.Prime)
    (h3n : ¬ 3 ∣ n) (H : Subgroup (MulAut (projectiveSL 3 F))) (hH : ∀ α ∈ H, α ^ 3 = 1) :
    H ≤ linearAutGroup 3 F := by
  intro α hα
  have : Finite (MulAut (projectiveSL 3 F)) := finite_mulAut_projectiveSL 3
  obtain ⟨hgenTop, hgen⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := 3) (K := F)
  have hαE : α ∈ semilinearAutGroup 3 F := by
    have hidx' : (semilinearAutGroup 3 F).index ≤ 2 := by
      have h2 : (semilinearAutGroup 3 F).relIndex (standardAutGroup 3 F) ≤ 2 := hidx
      rwa [hgenTop, Subgroup.relIndex_top_right] at h2
    refine mem_of_pow_mem_of_index_le_two _ hidx' (N := 3) (by decide) ?_
    rw [hH α hα]
    exact (semilinearAutGroup 3 F).one_mem
  obtain ⟨B, τ, rfl⟩ := mem_semilinearAutGroup_iff.1 hαE
  obtain ⟨C, hC⟩ := conj_pow_three B τ
  have h1 := hH _ hα
  rw [hC] at h1
  have hD : ∀ C : GL (Fin 3) F, conjAut 3 F C ∈ linearAutGroup 3 F := fun C =>
    mem_linearAutGroup_iff.2 ⟨C, rfl⟩
  have hτ3 : fieldAut 3 F (τ ^ 3) ∈ linearAutGroup 3 F := by
    have : fieldAut 3 F (τ ^ 3) = (conjAut 3 F C)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact (linearAutGroup 3 F).inv_mem (hD C)
  have hm : orderOf τ ∣ n := by
    have := (card_ringAut_and_isCyclic hp F hn).1
    rw [← this]
    exact orderOf_dvd_natCard τ
  have hcopN : Nat.Coprime 3 (orderOf τ) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (fun h => h3n (h.trans hm))
  obtain ⟨u, v, huv⟩ : IsCoprime (3 : ℤ) (orderOf τ : ℤ) := by
    exact_mod_cast Nat.isCoprime_iff_coprime.2 hcopN
  have hτ : τ = (τ ^ 3) ^ u := by
    have e1 : τ ^ (u * 3) = (τ ^ 3) ^ u := by
      rw [mul_comm, _root_.zpow_mul]; norm_num
    have e2 : τ ^ (v * (orderOf τ : ℤ)) = 1 := by
      rw [mul_comm, _root_.zpow_mul, zpow_natCast, pow_orderOf_eq_one, _root_.one_zpow]
    calc τ = τ ^ (u * 3 + v * (orderOf τ : ℤ)) := by rw [huv, _root_.zpow_one]
      _ = τ ^ (u * 3) * τ ^ (v * (orderOf τ : ℤ)) := _root_.zpow_add _ _ _
      _ = (τ ^ 3) ^ u := by rw [e1, e2, mul_one]
  have hfτ : fieldAut 3 F τ ∈ linearAutGroup 3 F := by
    rw [hτ, map_zpow]
    exact zpow_mem hτ3 u
  exact (linearAutGroup 3 F).mul_mem (hD B) hfτ

open CFSG.HardMathSupport.Timmesfeld.LinearRank in
theorem pRank_mulAut_projectiveSL_le_two
    (hF : Nat.card F % 9 = 4 ∨ Nat.card F % 9 = 7) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (projectiveSL 3 F))) ≤ 2 := by
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hn'⟩ := FiniteField.card F (ringChar F)
  have hn : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn']
  have h3n := not_three_dvd_degree hF hn
  refine CFSG.SectionRank.pRank_le (by norm_num) ?_
  intro H _ hH
  have hHD := le_linearAutGroup_of_elemAbelian hn hp h3n H hH.2
  have hpK : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units]; omega
  let ρ : ↥(⊤ : Subgroup (GL (Fin 3) F)) →* MulAut (projectiveSL 3 F) :=
    (conjAut 3 F).comp (⊤ : Subgroup (GL (Fin 3) F)).subtype
  have hker : ∀ A : ↥(⊤ : Subgroup (GL (Fin 3) F)), ρ A = 1 ↔
      (A : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) := by
    intro A
    rw [mem_center_iff]
    exact conjAut_eq_one_iff le_rfl _
  have hHρ : H ≤ ρ.range := by
    intro α hα
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hHD hα)
    exact ⟨⟨A, trivial⟩, hA⟩
  have := card_le_of_scalar_kernel Nat.prime_three (by norm_num) hpK (by norm_num) _ ρ hker H hHρ hH
  simpa using this

end Main

end CFSG.HardMathSupport.Solomon.Coordinator
