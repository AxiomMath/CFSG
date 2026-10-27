module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

section Group

theorem eq_of_mem_zpowers_of_pow_three {G : Type*} [Group G] {a b : G} (ha : a ^ 3 = 1)
    (hb : b ∈ Subgroup.zpowers a) : b = 1 ∨ b = a ∨ b = a ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have ha' : a ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact ha
  rw [zpow_eq_zpow_emod k ha']
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with hk | hk | hk <;> rw [hk]
  · exact Or.inl (zpow_zero a)
  · exact Or.inr (Or.inl (zpow_one a))
  · exact Or.inr (Or.inr (by rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]))

end Group

section Field

variable {K : Type} [Field K]

theorem ringAut_apply_eq_of_pow_three {σ : K ≃+* K} (hσ : orderOf σ = 3) {τ : K}
    (hτ : τ ^ 3 = 1) : σ τ = τ := by
  by_cases h1 : τ = 1
  · rw [h1, map_one]
  have hs : τ ^ 2 + τ + 1 = 0 := by
    have : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)
  set t := σ τ with ht
  have ht3 : t ^ 3 = 1 := by rw [ht, ← map_pow, hτ, map_one]
  have ht1 : t ≠ 1 := fun h => h1 (σ.injective (h.trans (map_one σ).symm))
  have hts : t ^ 2 + t + 1 = 0 := by
    have : (t - 1) * (t ^ 2 + t + 1) = 0 := by linear_combination ht3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ht1)
  have hcases : (t - τ) * (t - τ ^ 2) = 0 := by linear_combination hts - t * hs + hτ
  rcases mul_eq_zero.1 hcases with h | h
  · exact sub_eq_zero.1 h
  · exfalso
    have h2 : t = τ ^ 2 := sub_eq_zero.1 h
    have hστ : σ τ = τ ^ 2 := ht.symm.trans h2
    have h3 := ringAut_apply_three hσ τ
    simp only [hστ, map_pow] at h3
    have hτ0 : τ ≠ 0 := by
      rintro rfl
      simp at hτ
    have h5 : ((τ ^ 2) ^ 2) ^ 2 = τ ^ 2 := by
      calc ((τ ^ 2) ^ 2) ^ 2 = (τ ^ 3) ^ 2 * τ ^ 2 := by ring
        _ = τ ^ 2 := by rw [hτ, one_pow, one_mul]
    have h6 : τ * (τ - 1) = 0 := by linear_combination h3 - h5
    rcases mul_eq_zero.1 h6 with h | h
    · exact hτ0 h
    · exact h1 (sub_eq_zero.1 h)

theorem diagUnits_pow (a b c : Kˣ) (n : ℕ) :
    diagUnits a b c ^ n = diagUnits (a ^ n) (b ^ n) (c ^ n) := by
  induction n with
  | zero =>
    apply Units.ext
    rw [pow_zero, Units.val_one, coe_diagUnits, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  | succ n ih => rw [pow_succ, ih, diagUnits_mul, ← pow_succ, ← pow_succ, ← pow_succ]

theorem diagUnits_commute (a b c a' b' c' : Kˣ) :
    diagUnits a b c * diagUnits a' b' c' = diagUnits a' b' c' * diagUnits a b c := by
  rw [diagUnits_mul, diagUnits_mul, mul_comm a, mul_comm b, mul_comm c]

theorem diagUnits_mem_statedScalars_iff (a b c : Kˣ) :
    diagUnits a b c ∈ StatedScalars (Fin 3) K ↔ b = a ∧ c = a := by
  have h := diagHom_mem_statedScalars_iff (a, b, c)
  change diagUnits a b c ∈ StatedScalars (Fin 3) K ↔ _ at h
  rw [h]
  simp only [ratioHom, MonoidHom.coe_mk, OneHom.coe_mk, Prod.mk_eq_one, mul_inv_eq_one]

theorem not_mem_statedScalars_of_entry_eq_zero {A : GL (Fin 3) K} (i : Fin 3)
    (h : (A : Matrix (Fin 3) (Fin 3) K) i i = 0) : A ∉ StatedScalars (Fin 3) K := by
  rintro ⟨c, rfl⟩
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at h
  exact c.ne_zero h

theorem conj_mem_statedScalars_iff (g A : GL (Fin 3) K) :
    g * A * g⁻¹ ∈ StatedScalars (Fin 3) K ↔ A ∈ StatedScalars (Fin 3) K := by
  have h := inv_conj_mem_statedScalars_iff g⁻¹ A
  rwa [inv_inv] at h

theorem diagTau_eq_diagUnits' {τ : K} (hτ : τ ^ 3 = 1) :
    ∃ t : Kˣ, (t : K) = τ ∧ diagTau hτ = diagUnits t (t ^ 2) 1 := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  exact ⟨Units.mk0 τ hτ0, rfl, diagTau_eq_diagUnits hτ hτ0⟩

theorem diagTau_pow_three {τ : K} (hτ : τ ^ 3 = 1) : diagTau hτ ^ 3 = 1 := by
  obtain ⟨t, ht, he⟩ := diagTau_eq_diagUnits' hτ
  have ht3 : t ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, ht, hτ, Units.val_one])
  rw [he, diagUnits_pow, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, ht3, one_pow,
    one_pow]
  apply Units.ext
  rw [Units.val_one, coe_diagUnits, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diagTau_not_mem_statedScalars {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    diagTau hτ ∉ StatedScalars (Fin 3) K := by
  obtain ⟨t, ht, he⟩ := diagTau_eq_diagUnits' hτ
  rw [he, diagUnits_mem_statedScalars_iff]
  rintro ⟨-, h⟩
  exact hτ1 (by rw [← ht, ← h, Units.val_one])

theorem cycThree_pow_three : (cycThree : GL (Fin 3) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_cycThree, Units.val_one, pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem cycThree_mul_diagUnits_not_mem (a b c : Kˣ) :
    cycThree * diagUnits a b c ∉ StatedScalars (Fin 3) K := by
  refine not_mem_statedScalars_of_entry_eq_zero 0 ?_
  rw [Units.val_mul, coe_cycThree, coe_diagUnits]
  simp [mul_apply, Fin.sum_univ_three]

theorem diagTau_conj_cycThree {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) :
    diagTau hτ * cycThree * (diagTau hτ)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * cycThree := by
  have h4 : τ ^ 2 * τ ^ 2 = τ := by
    calc τ ^ 2 * τ ^ 2 = τ ^ 3 * τ := by ring
      _ = τ := by rw [hτ, one_mul]
  apply Units.ext
  have hinv : (((diagTau hτ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![τ ^ 2, 0, 0; 0, τ, 0; 0, 0, 1] := rfl
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hinv, coe_diagTau, coe_cycThree,
    GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h4]

theorem frobGL_diagUnits (σ : K ≃+* K) (a b c : Kˣ) :
    frobGL σ (diagUnits a b c) = diagUnits (Units.map (σ : K →* K) a)
      (Units.map (σ : K →* K) b) (Units.map (σ : K →* K) c) := by
  apply Units.ext
  rw [coe_frobGL, coe_diagUnits, coe_diagUnits, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem frobGL_diagTau {σ : K ≃+* K} (hσ : orderOf σ = 3) {τ : K} (hτ : τ ^ 3 = 1) :
    frobGL σ (diagTau hτ) = diagTau hτ := by
  have h := ringAut_apply_eq_of_pow_three hσ hτ
  apply Units.ext
  rw [coe_frobGL, coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h]

theorem frobGL_cycThree (σ : K ≃+* K) : frobGL σ cycThree = cycThree := by
  apply Units.ext
  rw [coe_frobGL, coe_cycThree]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem frobGL_scalar_of_pow_three {σ : K ≃+* K} (hσ : orderOf σ = 3) {ζ : Kˣ}
    (hζ : (ζ : K) ^ 3 = 1) :
    frobGL σ (GeneralLinearGroup.scalar (Fin 3) ζ) = GeneralLinearGroup.scalar (Fin 3) ζ := by
  rw [frobGL_scalar]
  congr 1
  exact Units.ext (ringAut_apply_eq_of_pow_three hσ hζ)

variable {π : Bool} {p f : ℕ}

theorem exists_mem_slPi_mul_diag (hK : PiField π p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) :
    ∃ t : Kˣ, t ∈ rootsOfUnity (qSubPi π (p ^ f)) K ∧ g * diagUnits t 1 1 ∈ slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hdet := det_mem_rootsOfUnity hK hg
  refine ⟨(GeneralLinearGroup.det g)⁻¹, inv_mem hdet, ?_⟩
  rw [mem_slPi_iff hπ]
  refine ⟨mul_mem hg (diagUnits_mem_glPi hK (inv_mem hdet) (one_mem _) (one_mem _)), ?_⟩
  rw [Units.val_mul, det_mul, coe_diagUnits, det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Units.val_one, mul_one]
  rw [Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply]
  exact mul_inv_cancel₀ (g.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero

theorem exists_slPi_conj_diagUnits (hK : PiField π p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) :
    ∃ s ∈ slPi π 3 (p ^ f) K, ∀ a b c : Kˣ,
      s * diagUnits a b c * s⁻¹ = g * diagUnits a b c * g⁻¹ := by
  obtain ⟨t, -, hs⟩ := exists_mem_slPi_mul_diag hK hg
  refine ⟨_, hs, fun a b c => ?_⟩
  have hc := diagUnits_commute t 1 1 a b c
  calc g * diagUnits t 1 1 * diagUnits a b c * (g * diagUnits t 1 1)⁻¹
      = g * (diagUnits t 1 1 * diagUnits a b c) * (diagUnits t 1 1)⁻¹ * g⁻¹ := by group
    _ = g * (diagUnits a b c * diagUnits t 1 1) * (diagUnits t 1 1)⁻¹ * g⁻¹ := by rw [hc]
    _ = g * diagUnits a b c * g⁻¹ := by group

end Field

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
