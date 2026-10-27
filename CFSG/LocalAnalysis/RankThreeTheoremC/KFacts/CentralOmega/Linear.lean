module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.CentralOmega.Tools
public import CFSG.Open.StatedCenterThree
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.CentralOmega

open Matrix CFSG.Open.StatedCenterThree

variable {F : Type} [Field F]

theorem diagGL_pow_three {ω : Fˣ} (hω : ω ^ 3 = 1) : diagGL ω ^ 3 = 1 := by
  have h1 : (ω : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω, Units.val_one]
  have h2 : ((ω⁻¹ : Fˣ) : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hω, inv_one, Units.val_one]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  change (diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F), 1]) ^ 3 = 1
  rw [diagonal_pow, ← diagonal_one]
  congr 1
  funext i
  fin_cases i
  · exact h1
  · exact h2
  · simp

theorem cyc3GL_pow_three : (cyc3GL : GL (Fin 3) F) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  change (cyc3 : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyc3, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem cyc3GL_conj_diagGL {ω : Fˣ} (hω : ω ^ 3 = 1) :
    cyc3GL * diagGL ω * cyc3GL⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ω * diagGL ω := by
  have hinv : ((ω⁻¹ : Fˣ) : F) = (ω : F) * (ω : F) := by
    have h : ω⁻¹ = ω * ω := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hω)
    rw [h, Units.val_mul]
  have hcube : (ω : F) * ((ω : F) * (ω : F)) = 1 := by
    rw [← Units.val_mul, ← Units.val_mul, ← pow_three, hω, Units.val_one]
  have hcube' : (ω : F) * (ω : F) * (ω : F) = 1 := by rw [mul_assoc, hcube]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul]
  change cyc3 * diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F), 1] * cyc3ᵀ =
    Matrix.scalar (Fin 3) (ω : F) * diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F), 1]
  rw [Matrix.scalar_apply, diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyc3, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.vecMul_diagonal,
      Matrix.diagonal_apply, Fin.sum_univ_three, hinv, hcube, hcube']

theorem diagGL_mul_cyc3GL_ne {ω : Fˣ} (hord : orderOf ω = 3) :
    diagGL ω * cyc3GL ≠ cyc3GL * diagGL ω := by
  have hω : ω ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one ω
  intro h
  have hconj := cyc3GL_conj_diagGL hω
  rw [← h, mul_inv_cancel_right] at hconj
  have hs : Matrix.GeneralLinearGroup.scalar (Fin 3) ω = 1 := by
    calc Matrix.GeneralLinearGroup.scalar (Fin 3) ω
        = Matrix.GeneralLinearGroup.scalar (Fin 3) ω * diagGL ω * (diagGL ω)⁻¹ := by group
      _ = diagGL ω * (diagGL ω)⁻¹ := by rw [← hconj]
      _ = 1 := mul_inv_cancel _
  have h00 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) hs
  have hω1 : ω = 1 := by simpa using h00
  rw [hω1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem exists_pair_of_mem {H : Subgroup (GL (Fin 3) F)} {ω : Fˣ} (hord : orderOf ω = 3)
    (hD : diagGL ω ∈ H) (hC : cyc3GL ∈ H)
    (hS : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ H) :
    ∃ x y : H, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x ∧
      IsPGroup 3 (Subgroup.closure ({x, y} : Set H)) := by
  have hω : ω ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one ω
  let x : H := ⟨diagGL ω, hD⟩
  let y : H := ⟨cyc3GL, hC⟩
  let c : H := ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) ω, hS⟩
  have hcZ : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨ω, rfl⟩
  have hc : c ∈ Subgroup.center H :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp hcZ g)
  have hc3 : c ^ 3 = 1 := Subtype.ext (by
    change Matrix.GeneralLinearGroup.scalar (Fin 3) ω ^ 3 = 1
    rw [← map_pow, hω, map_one])
  have hx3 : x ^ 3 = 1 := Subtype.ext (diagGL_pow_three hω)
  have hy3 : y ^ 3 = 1 := Subtype.ext cyc3GL_pow_three
  have hconj : y * x * y⁻¹ = c * x := Subtype.ext (cyc3GL_conj_diagGL hω)
  refine ⟨x, y, hx3, hy3, fun h => diagGL_mul_cyc3GL_ne hord (congrArg Subtype.val h), ?_⟩
  exact isPGroup_closure_of_conj_eq_mul hc hc3 hx3 hy3 hconj

theorem not_forall_commute_of_mulEquiv {L : Type} [Group L] [Finite L]
    {H : Subgroup (GL (Fin 3) F)} (ψ : L ≃* H) {ω : Fˣ} (hord : orderOf ω = 3)
    (hD : diagGL ω ∈ H) (hC : cyc3GL ∈ H)
    (hS : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ H) (S : Sylow 3 L) :
    ¬ ∀ a ∈ (S : Subgroup L), ∀ b ∈ (S : Subgroup L), a ^ 3 = 1 → b ^ 3 = 1 →
      a * b = b * a := by
  obtain ⟨x, y, hx, hy, hxy, hP⟩ := exists_pair_of_mem hord hD hC hS
  refine not_forall_commute_of_isPGroup (x := ψ.symm x) (y := ψ.symm y)
    (by rw [← map_pow, hx, map_one]) (by rw [← map_pow, hy, map_one])
    (fun h => hxy (ψ.symm.injective (by rw [map_mul, map_mul, h])))
    (hP.map ψ.symm.toMonoidHom)
    (Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (Set.mem_insert x {y})))
    (Subgroup.mem_map_of_mem _ (Subgroup.subset_closure
      (Set.mem_insert_of_mem x (Set.mem_singleton y)))) S

theorem not_forall_commute_of_isSLThreePi {L : Type} [Group L] [Finite L]
    (hL : CFSG.RankThree.PartTwo.Sec4.IsSLThreePi L) (S : Sylow 3 L) :
    ¬ ∀ a ∈ (S : Subgroup L), ∀ b ∈ (S : Subgroup L), a ^ 3 = 1 → b ^ 3 = 1 →
      a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, K, _, _, h⟩ := hL
  rcases h with ⟨hK, hq3, ⟨ψ⟩⟩ | ⟨hK, hq3, ⟨ψ⟩⟩
  ·
    have h3 : 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hK]
      omega
    obtain ⟨ω, hord⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
    have hω : ω ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one ω
    exact not_forall_commute_of_mulEquiv ψ hord
      (CFSG.Open.StatedAPI.statedSU_le_statedSL 3 2 K (diagGL_mem (by norm_num) hω))
      (CFSG.Open.StatedAPI.statedSU_le_statedSL 3 2 K (cyc3GL_mem (by norm_num)))
      (CFSG.Open.StatedAPI.statedSU_le_statedSL 3 2 K (scalar_mem (by norm_num) (by norm_num) hω))
      S
  ·
    have hq0 : q ≠ 0 := by omega
    have hq1 : 3 ∣ q + 1 := by omega
    have h3 : 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hK]
      obtain ⟨k, rfl⟩ : ∃ k, q = 3 * k + 2 := ⟨q / 3, by omega⟩
      have : (3 * k + 2) ^ 2 = 3 * (3 * k ^ 2 + 4 * k + 1) + 1 := by ring
      rw [this, Nat.add_sub_cancel]
      exact dvd_mul_right _ _
    obtain ⟨ω, hord⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
    have hω : ω ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one ω
    have hωq : ω ^ (q + 1) = 1 := by
      obtain ⟨m, hm⟩ := hq1
      rw [hm, pow_mul, hω, one_pow]
    exact not_forall_commute_of_mulEquiv ψ hord (diagGL_mem hq0 hωq) (cyc3GL_mem hq0)
      (scalar_mem hq0 hq1 hω) S

end CFSG.LocalAnalysis.RankThreeTheoremC.CentralOmega
