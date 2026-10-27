module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FNotL2
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6CUniqAux2
public import CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open scoped Pointwise
open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine

theorem card_sylow_three_lThreeFour {X : Type} [Group X] (h : IsLThreeFour X) (P : Sylow 3 X) :
    Nat.card P = 9 := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : Nat.card X = 20160 := card_eq_of_isLThreeFour h
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  rw [Sylow.card_eq_multiplicity, hX]
  have : (20160 : ℕ) = 3 ^ 2 * 2240 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply]
  rw [Nat.Prime.factorization_pow Nat.prime_three]
  have : (2240 : ℕ).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [this]

theorem inputL34Facts_proved : InputL34Facts := by
  intro X _ _ h
  refine ⟨(isSimpleGroup_of_isLThreeFour h).1, fun P => ?_⟩
  have h9 := card_sylow_three_lThreeFour h P
  obtain ⟨⟨⟨hc⟩⟩, hp⟩ := Sec6C.isElemAbelian_of_card_nine h (P : Subgroup X) h9
  exact ⟨h9, fun a b => Subtype.ext (by
    have := hc a b
    simpa using congrArg Subtype.val this), fun g => Subtype.ext (by
    simpa using hp g g.2)⟩

private theorem exists_equiv_sl {X : Type} [Group X] (h : IsSLThreeFour X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) K) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm⟩⟩

theorem card_center_slThreeFour {X : Type} [Group X] (h : IsSLThreeFour X) :
    Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_sl h
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, ← scalars_eq_center]
  exact card_scalars hK

section Sylow

variable {K : Type} [Field K] [Finite K]

private theorem rSL_not_comm (hK : Nat.card K = 4) :
    ∃ p : Kˣ × Kˣ, (rSL : Matrix.SpecialLinearGroup (Fin 3) K) * dHom p ≠ dHom p * rSL := by
  have h3 : Nat.card Kˣ = 3 := LinearThreeFourOuter.card_units_eq_three hK
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨u, hu⟩ := exists_ne (1 : Kˣ)
  refine ⟨(u, 1), fun hc => hu ?_⟩
  rw [rSL_mul_dHom] at hc
  have := mul_right_cancel hc
  have h00 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K =>
    (g : Matrix (Fin 3) (Fin 3) K) 1 1) this
  simp [coe_dHom, rot, Matrix.diagonal] at h00
  exact h00

end Sylow

theorem inputSL34Facts_proved : InputSL34Facts := by
  intro X _ _ h
  refine ⟨card_center_slThreeFour h, fun P => ?_⟩
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_sl h
  have hX : Nat.card X = 60480 := card_slThreeFour h
  let φ : Matrix.SpecialLinearGroup (Fin 3) K →* X := e.symm.toMonoidHom
  set Q' : Subgroup X := (qSub (k := K)).map φ with hQ'
  have hQ'card : Nat.card Q' = 27 := by
    rw [hQ', Subgroup.card_map_of_injective e.symm.injective, card_qSub hK]
  have hfac : Nat.card Q' = 3 ^ (Nat.card X).factorization 3 := by
    rw [hQ'card, hX]
    have : (60480 : ℕ) = 3 ^ 3 * 2240 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply]
    rw [Nat.Prime.factorization_pow Nat.prime_three]
    have : (2240 : ℕ).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    simp [this]
  let Q : Sylow 3 X := Sylow.ofCard Q' hfac
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  have hP : (P : Subgroup X) = Q'.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  obtain ⟨p, hpc⟩ := rSL_not_comm (K := K) hK
  have hmem : ∀ y ∈ qSub (k := K), g * φ y * g⁻¹ ∈ (P : Subgroup X) := by
    intro y hy
    rw [hP]
    exact ⟨φ y, ⟨y, hy, rfl⟩, rfl⟩
  refine ⟨⟨g * φ rSL * g⁻¹, hmem _ (Subgroup.subset_closure (Or.inr rfl)), g * φ (dHom p) * g⁻¹,
    hmem _ (Subgroup.subset_closure (Or.inl (mem_dSet_iff.2 ⟨p, rfl⟩))), ?_⟩, ?_, ?_⟩
  · intro hc
    apply hpc
    apply e.symm.injective
    have : g * (φ rSL * φ (dHom p)) * g⁻¹ = g * (φ (dHom p) * φ rSL) * g⁻¹ := by
      calc _ = (g * φ rSL * g⁻¹) * (g * φ (dHom p) * g⁻¹) := by group
        _ = (g * φ (dHom p) * g⁻¹) * (g * φ rSL * g⁻¹) := hc
        _ = _ := by group
    have := mul_left_cancel (mul_right_cancel this)
    simpa [φ] using this
  · rw [hP, Subgroup.card_map_of_injective (MulAut.conj g).injective, hQ'card]
  · intro x hx
    rw [hP] at hx
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hx
    have hy3 : y ^ 3 = 1 := by
      rw [coe_qSub] at hy
      obtain ⟨z, rfl⟩ := hy
      exact qElt_pow_three hK z
    show (g * φ y * g⁻¹) ^ 3 = 1
    rw [conj_pow, ← map_pow, hy3, map_one, mul_one, mul_inv_cancel]

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
