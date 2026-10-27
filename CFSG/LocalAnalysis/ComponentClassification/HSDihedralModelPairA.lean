module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralModelGen3
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralAutPair
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralModelGen
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralModelInv

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral.Model

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F]

theorem ringAut_eq_of_sq {σ τ : F ≃+* F} (hσ : σ ^ 2 = 1) (hτ : τ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hτ1 : τ ≠ 1) : σ = τ := by
  classical
  have := isCyclic_ringAut F
  have : Fintype (F ≃+* F) := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := F ≃+* F) (n := 2) two_pos
  by_contra hne
  have h3 : ({1, σ, τ} : Finset (F ≃+* F)) ⊆ Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hσ
    · exact hτ
  have h4 := Finset.card_le_card h3
  rw [Finset.card_insert_of_notMem (by simp [hσ1.symm, hτ1.symm]), Finset.card_pair hne] at h4
  omega

theorem sixteen_dvd_of_order_four {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) {τ : F ≃+* F} (hτ2 : τ ^ 2 ≠ 1) (hτ4 : τ ^ 4 = 1) :
    16 ∣ Nat.card F - 1 := by
  have hord : orderOf τ = 2 ^ 2 := by
    have hdvd : orderOf τ ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by norm_num; exact hτ4)
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hi']
    interval_cases i
    · rw [pow_zero, orderOf_eq_one_iff] at hi'
      exact absurd (by rw [hi', one_pow]) hτ2
    · rw [pow_one] at hi'
      exact absurd (by rw [← hi', pow_orderOf_eq_one]) hτ2
    · rfl
  obtain ⟨t, -, ht, -, hcard, -⟩ := exists_odd_pow_of_orderOf_two_pow hp hp2 hF τ (by norm_num)
    hord
  rw [hcard]
  obtain ⟨m, rfl⟩ := ht
  have h1 : (2 * m + 1) ^ 2 ^ 2 - 1 = 16 * (m * (m + 1) / 2) * (2 * m ^ 2 + 2 * m + 1) := by
    obtain ⟨c, hc⟩ := Nat.even_mul_succ_self m
    rw [hc, show (c + c) / 2 = c by omega]
    have : (2 * m + 1) ^ 2 ^ 2 = 16 * c * (2 * m ^ 2 + 2 * m + 1) + 1 := by
      have hc' : m * (m + 1) = 2 * c := by omega
      have : (2 * m + 1) ^ 4 = 8 * (m * (m + 1)) * (2 * m ^ 2 + 2 * m + 1) + 1 := by ring
      rw [show 2 ^ 2 = 4 by norm_num, this, hc']
      ring
    omega
  rw [h1, mul_assoc]
  exact dvd_mul_right 16 _

theorem sixteen_le_card (hodd : IsOddPrimePower (Nat.card F)) (h16 : 16 ∣ Nat.card F - 1)
    (T : Sylow 2 (PSL2 F)) : 16 ≤ Nat.card ((T : Subgroup (PSL2 F)).map (incl F)) := by
  have hq1 := Finite.one_lt_card (α := F)
  have hq4 : Nat.card F % 4 = 1 := by omega
  have hsq : IsSquare (-1 : F) := by
    have : Fintype F := Fintype.ofFinite F
    classical
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    omega
  have hn : 4 ≤ twoVal F := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
    (by omega)).mp (by simpa using h16)
  rw [card_D0 hodd hsq hq4]
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ twoVal F := Nat.pow_le_pow_right (by norm_num) hn

theorem mem_D0_iff (T : Sylow 2 (PSL2 F)) {P : Subgroup (PGammaL2 F)} (hP : IsPGroup 2 P)
    (hTP : (T : Subgroup (PSL2 F)).map (incl F) ≤ P) {x : PGammaL2 F} (hx : x ∈ P) :
    x ∈ (T : Subgroup (PSL2 F)).map (incl F) ↔ x.right = 1 ∧ SqLeft x := by
  rw [← inf_pslRange_eq T P hP hTP, mem_inf, mem_pslRange_iff]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

omit [Finite F] in
theorem right_of_mem_D0 (T : Sylow 2 (PSL2 F)) {x : PGammaL2 F}
    (hx : x ∈ (T : Subgroup (PSL2 F)).map (incl F)) : x.right = 1 := by
  obtain ⟨t, -, rfl⟩ := hx
  rfl

theorem autPair_linear
    (hodd : IsOddPrimePower (Nat.card F)) (T : Sylow 2 (PSL2 F)) {P : Subgroup (PGammaL2 F)}
    (hP : IsPGroup 2 P) (hTP : (T : Subgroup (PSL2 F)).map (incl F) ≤ P)
    (hlin : ∀ x ∈ P, x.right = 1) : AutPair P ((T : Subgroup (PSL2 F)).map (incl F)) := by
  set D₀ := (T : Subgroup (PSL2 F)).map (incl F)
  have h1 : PairCaseOne P D₀ := fun c hc hcD =>
    mem_of_centralizes hodd T (hlin c hc) hcD
  refine ⟨fun R' hR' => gen3_model hodd (hP.to_le hR'), Or.inl h1,
    fun _ r₁ hr₁ r₂ hr₂ hn₁ hn₂ => ?_, fun _ E hED hE4 hEsq c hc hcE => ?_,
    fun _ σ hσ hσD hσ2 => ?_,
    fun k hk => absurd (h1 k hk.1 hk.2.1) hk.2.2.1⟩
  · have hs₁ : ¬ SqLeft r₁ := fun h => hn₁ ((mem_D0_iff T hP hTP hr₁).mpr ⟨hlin r₁ hr₁, h⟩)
    have hs₂ : ¬ SqLeft r₂ := fun h => hn₂ ((mem_D0_iff T hP hTP hr₂).mpr ⟨hlin r₂ hr₂, h⟩)
    refine (mem_D0_iff T hP hTP (mul_mem hr₁ (inv_mem hr₂))).mpr
      ⟨hlin _ (mul_mem hr₁ (inv_mem hr₂)), ?_⟩
    rw [sqLeft_mul, sqLeft_inv]
    tauto
  · exact hED (klein_centralizer hodd (fun e he => right_of_mem_D0 T (hED he)) hE4 hEsq
      (hlin c hc) hcE)
  · refine card_centralizer_le_two hodd T (hlin σ hσ) (fun hL => hσD ?_) hσ2
    exact (mem_D0_iff T hP hTP hσ).mpr ((mem_pslRange_iff σ).mp hL)

end CFSG.ComponentClassification.HSDihedral.Model
