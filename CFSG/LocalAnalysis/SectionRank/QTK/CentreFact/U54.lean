module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Pair
public import CFSG.Open.StatedDefs
import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
import CFSG.RankThree.Classical.EvenSurvivingScalarRank
import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Matrix CFSG.Open CFSG.SectionRank.OddCover CFSG.RankThree.Classical
  CFSG.RankThree.Classical2

section Matrices

variable {K : Type} [Field K]

private theorem diagHom_mem_statedSU {n q : ℕ} (hq : q ≠ 0) {d : Fin n → Kˣ}
    (hd : ∀ i, d i ^ (q + 1) = 1) (hdet : ∏ i, d i = 1) :
    diagHom n d ∈ StatedSU n q K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [det_diagHom, ← Units.coe_prod, hdet, Units.val_one]
  · rw [coe_diagHom, Matrix.diagonal_map (by simp [zero_pow hq]), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← pow_succ, ← Units.val_pow_eq_pow_val, hd i, Units.val_one]

private theorem permGL_swap_mem_statedSU {n q : ℕ} (hq : q ≠ 0) (h2 : (2 : K) = 0) (a b : Fin n) :
    permGL (K := K) (Equiv.swap a b) ∈ StatedSU n q K := by
  refine Subgroup.subset_closure ⟨det_permGL_swap h2 a b, ?_⟩
  have hmap : ((permGL (Equiv.swap a b) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map
      (· ^ q) = ((permGL (Equiv.swap a b) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    ext i j
    rw [Matrix.map_apply, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs <;> simp [zero_pow hq]
  rw [hmap]
  exact permGL_swap_transpose_mul a b

private theorem scalar_eq_diagHom {n : ℕ} (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin n) c = diagHom n (fun _ => c) :=
  Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom, Matrix.scalar_apply])

private def uA (ζ : Kˣ) : Fin 5 → Kˣ := ![1, 1, ζ, ζ⁻¹, 1]

private def uB (ζ : Kˣ) : Fin 5 → Kˣ := ![1, 1, 1, ζ, ζ⁻¹]

private theorem diagHom_mul_permGL_comm {n : ℕ} (π : Equiv.Perm (Fin n)) (d : Fin n → Kˣ)
    (h : d ∘ π.symm = d) : diagHom n d * permGL π = permGL π * diagHom n d := by
  have h1 := permGL_mul_diagHom_mul_inv (K := K) π d
  rw [h] at h1
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

end Matrices

theorem exists_pair_statedProj_su_five {q : ℕ} (hq : q ≠ 0) (h5 : 5 ∣ q + 1) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = q ^ 2) (h2 : (2 : K) = 0) :
    ∃ t a b d₁ d₂ : StatedProj (StatedSU 5 q K), t ^ 2 = 1 ∧ t ≠ 1 ∧ Commute a t ∧
      Commute b t ∧ a ^ 5 = 1 ∧ b ^ 5 = 1 ∧ a * b = b * a ∧
      (∀ i j : ℕ, i < 5 → j < 5 → a ^ i * b ^ j = 1 → i = 0 ∧ j = 0) ∧
      d₁ * a * d₁⁻¹ = a⁻¹ ∧ d₁ * b * d₁⁻¹ = a ^ 1 * b ^ 1 ∧ d₂ * b * d₂⁻¹ = b⁻¹ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
  have h5c : 5 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      zify [hq1, Nat.one_le_pow 2 _ hq1]
      ring
    rw [this]
    exact Dvd.dvd.mul_right h5 _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 5 h5c
  have hζ5 : ζ ^ 5 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζq : ζ ^ (q + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (hζ ▸ h5)
  have huA5 : uA ζ ^ 5 = 1 := by
    funext i
    fin_cases i <;> simp [uA, hζ5, inv_pow]
  have huB5 : uB ζ ^ 5 = 1 := by
    funext i
    fin_cases i <;> simp [uB, hζ5, inv_pow]
  set H : Subgroup (GL (Fin 5) K) := StatedSU 5 q K
  have hAm : diagHom 5 (uA ζ) ∈ H := diagHom_mem_statedSU hq
    (fun i => by fin_cases i <;> simp [uA, hζq, inv_pow]) (by simp [uA, Fin.prod_univ_five])
  have hBm : diagHom 5 (uB ζ) ∈ H := diagHom_mem_statedSU hq
    (fun i => by fin_cases i <;> simp [uB, hζq, inv_pow]) (by simp [uB, Fin.prod_univ_five])
  have hTm : permGL (K := K) (Equiv.swap (0 : Fin 5) 1) ∈ H := permGL_swap_mem_statedSU hq h2 _ _
  have hD₁m : permGL (K := K) (Equiv.swap (2 : Fin 5) 3) ∈ H :=
    permGL_swap_mem_statedSU hq h2 _ _
  have hD₂m : permGL (K := K) (Equiv.swap (3 : Fin 5) 4) ∈ H :=
    permGL_swap_mem_statedSU hq h2 _ _
  set A : H := ⟨diagHom 5 (uA ζ), hAm⟩
  set B : H := ⟨diagHom 5 (uB ζ), hBm⟩
  set T₀ : H := ⟨permGL (Equiv.swap (0 : Fin 5) 1), hTm⟩
  set D₁ : H := ⟨permGL (Equiv.swap (2 : Fin 5) 3), hD₁m⟩
  set D₂ : H := ⟨permGL (Equiv.swap (3 : Fin 5) 4), hD₂m⟩
  have hAc : (A : GL (Fin 5) K) = diagHom 5 (uA ζ) := rfl
  have hBc : (B : GL (Fin 5) K) = diagHom 5 (uB ζ) := rfl
  have hTc : (T₀ : GL (Fin 5) K) = permGL (Equiv.swap (0 : Fin 5) 1) := rfl
  have hD₁c : (D₁ : GL (Fin 5) K) = permGL (Equiv.swap (2 : Fin 5) 3) := rfl
  have hD₂c : (D₂ : GL (Fin 5) K) = permGL (Equiv.swap (3 : Fin 5) 4) := rfl
  let mk : H →* StatedProj H := QuotientGroup.mk' _
  refine ⟨mk T₀, mk A, mk B, mk D₁, mk D₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [← map_pow, show T₀ ^ 2 = 1 from Subtype.ext (by
      rw [Subgroup.coe_pow, hTc, ← map_pow, pow_two, Equiv.swap_mul_self, map_one]
      rfl), map_one]
  ·
    intro h
    have h1 : T₀ ∈ (StatedScalars (Fin 5) K).subgroupOf H := (QuotientGroup.eq_one_iff T₀).mp h
    refine permGL_not_mem_statedScalars (π := Equiv.swap (0 : Fin 5) 1) (fun h3 => ?_)
      (Subgroup.mem_subgroupOf.mp h1)
    exact absurd (Equiv.swap_eq_one_iff.mp h3) (by decide)
  ·
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hAc, hTc]
    exact diagHom_mul_permGL_comm _ _ (by funext i; fin_cases i <;> simp [uA, Equiv.swap_apply_def])
  ·
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hBc, hTc]
    exact diagHom_mul_permGL_comm _ _ (by funext i; fin_cases i <;> simp [uB, Equiv.swap_apply_def])
  ·
    rw [← map_pow, show A ^ 5 = 1 from Subtype.ext (by
      rw [Subgroup.coe_pow, hAc, ← map_pow, huA5, map_one]
      rfl), map_one]
  ·
    rw [← map_pow, show B ^ 5 = 1 from Subtype.ext (by
      rw [Subgroup.coe_pow, hBc, ← map_pow, huB5, map_one]
      rfl), map_one]
  ·
    rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hAc, hBc, ← map_mul, ← map_mul, mul_comm]
  ·
    intro i j hi hj h
    rw [← map_pow, ← map_pow, ← map_mul] at h
    have h1 : A ^ i * B ^ j ∈ (StatedScalars (Fin 5) K).subgroupOf H :=
      (QuotientGroup.eq_one_iff _).mp h
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp h1
    have hcoe : ((A ^ i * B ^ j : H) : GL (Fin 5) K) = diagHom 5 (uA ζ ^ i * uB ζ ^ j) := by
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hAc, hBc, map_mul, map_pow,
        map_pow]
    rw [hcoe, scalar_eq_diagHom] at hc
    have hv := diagHom_injective 5 hc
    have e0 := congrFun hv 0
    have e2 := congrFun hv 2
    have e4 := congrFun hv 4
    simp [uA, uB] at e0 e2 e4
    have hi1 : ζ ^ i = 1 := by rw [← e2, e0]
    have hj1 : ζ ^ j = 1 := by
      have h' : (ζ ^ j)⁻¹ = 1 := by rw [← e4, e0]
      exact inv_eq_one.mp h'
    have h5i := orderOf_dvd_of_pow_eq_one hi1
    have h5j := orderOf_dvd_of_pow_eq_one hj1
    rw [hζ] at h5i h5j
    exact ⟨Nat.eq_zero_of_dvd_of_lt h5i hi, Nat.eq_zero_of_dvd_of_lt h5j hj⟩
  ·
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hD₁c, hAc,
      permGL_mul_diagHom_mul_inv, ← map_inv]
    congr 1
    funext i
    fin_cases i <;> simp [uA, Equiv.swap_apply_def]
  ·
    rw [← map_inv, ← map_mul, ← map_mul, pow_one, pow_one, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, hD₁c, hBc, hAc,
      permGL_mul_diagHom_mul_inv, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [uA, uB, Equiv.swap_apply_def]
  ·
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hD₂c, hBc,
      permGL_mul_diagHom_mul_inv, ← map_inv]
    congr 1
    funext i
    fin_cases i <;> simp [uB, Equiv.swap_apply_def]

variable {G : Type} [Group G] [Finite G]

theorem not_five_dvd_card_center_of_U54 (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    (h : StatedClassicalModel (↥Y ⧸ Subgroup.center ↥Y) .PSU 5 2 2) :
    ¬ 5 ∣ Nat.card (Subgroup.center ↥Y) := by
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 4) (by
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num)
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨t, a, b, d₁, d₂, ht, ht1, hta, htb, har, hbr, hab, hind, hd₁a, hd₁b, hd₂b⟩ :=
    exists_pair_statedProj_su_five (q := 2 ^ 2) (by norm_num) (by norm_num) hcard h2
  exact not_dvd_card_center_of_pair_inv he e Nat.prime_five (by norm_num) ht ht1 hta htb har hbr
    hab hind hd₁a hd₁b (by norm_num) hd₂b

end CFSG.SectionRank.QTK.CentreFact
