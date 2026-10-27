module

public import CFSG.LargeExtraspecial.DWFldSL2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LargeExtraspecial.DW

open Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint

section Field

theorem charP_two_of_card_eq {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem exists_ne_zero_ne_one_of_card {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) : ∃ s : K, s ≠ 0 ∧ s ≠ 1 := by
  by_contra! h
  have hsurj : Function.Surjective fun b : Bool => if b then (1 : K) else 0 := by
    intro s
    by_cases hs : s = 0
    · exact ⟨false, by simp [hs]⟩
    · exact ⟨true, by simp [h s hs]⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [hK, show Nat.card Bool = 2 by simp] at hle
  have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

theorem exists_sq_eq_of_charTwo {K : Type} [Field K] [Finite K] [CharP K 2] (a : K) :
    ∃ μ : K, μ * μ = a := by
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
  exact ⟨μ, hμ.symm⟩

end Field

section Model

variable {X : Type} [Group X] {D : Set X} {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
  [Field K] {H : Subgroup (GL ι K)}

theorem mem_statedScalars_iff {g : GL ι K} :
    g ∈ StatedScalars ι K ↔ ∃ c : K, (g : Matrix ι ι K) = c • 1 := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal]⟩
  · rintro ⟨c, hc⟩
    by_cases hι : IsEmpty ι
    · refine ⟨1, Units.ext ?_⟩
      ext i
      exact hι.elim i
    rw [not_isEmpty_iff] at hι
    obtain ⟨i⟩ := hι
    have : Nonempty ι := ⟨i⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := g.isUnit.map (Matrix.detMonoidHom (n := ι) (R := K))
      simp only [Matrix.coe_detMonoidHom, hc, zero_smul, det_zero] at this
      exact not_isUnit_zero this
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, hc, smul_one_eq_diagonal]
    rfl

theorem IsTransClass34.false_of_statedProj [Finite X] (hD : IsTransClass34 D)
    (e : X ≃* StatedProj H) {B C : H} (hB : e.symm (QuotientGroup.mk B : StatedProj H) ∈ D)
    (hBC : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → (((B * (C * B * C⁻¹)) ^ k : H) : GL ι K) ∉
      StatedScalars ι K) : False := by
  set c : X := e.symm (QuotientGroup.mk C : StatedProj H)
  have he : c * e.symm (QuotientGroup.mk B : StatedProj H) * c⁻¹ ∈ D := hD.conj_mem c hB
  obtain ⟨k, hk1, hk4, hk⟩ := hD.exists_pow_eq_one hB he
  apply hBC k hk1 hk4
  have : ((B * (C * B * C⁻¹)) ^ k : H) ∈ (StatedScalars ι K).subgroupOf H := by
    rw [← QuotientGroup.eq_one_iff]
    apply e.symm.injective
    rw [map_one, ← hk]
    simp only [c, QuotientGroup.mk_pow, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_pow,
      map_mul, map_inv]
  exact Subgroup.mem_subgroupOf.1 this

theorem IsTransClass34.exists_lift (hD : IsTransClass34 D) (e : X ≃* StatedProj H) :
    ∃ B : H, e.symm (QuotientGroup.mk B : StatedProj H) ∈ D ∧
      (∃ c : K, (((B * B : H) : GL ι K) : Matrix ι ι K) = c • 1) ∧
      ∀ c : K, (((B : H) : GL ι K) : Matrix ι ι K) ≠ c • 1 := by
  obtain ⟨d₀, hd₀, -⟩ := hD.2.1
  obtain ⟨hne, hsq⟩ := hD.2.2.1 d₀ hd₀
  obtain ⟨B, hB⟩ := QuotientGroup.mk_surjective (e d₀)
  have hBd : e.symm (QuotientGroup.mk B : StatedProj H) = d₀ := by
    rw [hB, MulEquiv.symm_apply_apply]
  refine ⟨B, hBd ▸ hd₀, ?_, fun c hc => hne ?_⟩
  · have : (B * B : H) ∈ (StatedScalars ι K).subgroupOf H := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hB, ← map_mul, hsq, map_one]
    exact mem_statedScalars_iff.1 (Subgroup.mem_subgroupOf.1 this)
  · have : B ∈ (StatedScalars ι K).subgroupOf H :=
      Subgroup.mem_subgroupOf.2 (mem_statedScalars_iff.2 ⟨c, hc⟩)
    rw [← hBd, (QuotientGroup.eq_one_iff B).2 this, map_one]

end Model

section Linear

variable {X : Type} [Group X] {D : Set X}

theorem mem_statedSL_iff_det {n : ℕ} {K : Type} [Field K] {g : GL (Fin n) K} :
    g ∈ StatedSL n K ↔ (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem false_of_statedProj_statedSL [Finite X] {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {s : K} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (e : X ≃* StatedProj (StatedSL n K))
    (hD : IsTransClass34 D) : False := by
  obtain ⟨B, hBD, ⟨l, hl⟩, hB1⟩ := hD.exists_lift e
  obtain ⟨μ, hμ⟩ := exists_sq_eq_of_charTwo l
  set M : Matrix (Fin n) (Fin n) K := (((B : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
    with hMdef
  have hMM : M * M = l • 1 := by
    rw [← hl, hMdef]
    simp
  have hn : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hB1 0 (Subsingleton.elim _ _)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hμ
    subst hμ
    have hdet := congrArg Matrix.det hMM
    rw [det_mul, zero_smul, det_zero] at hdet
    exact Matrix.GeneralLinearGroup.det_ne_zero (B : GL (Fin n) K)
      (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by rw [sq]; exact hdet))
  set B' : Matrix (Fin n) (Fin n) K := μ⁻¹ • M with hB'def
  have hM : M = μ • B' := by rw [hB'def, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  have hB'2 : B' * B' = 1 := by
    rw [hB'def, smul_mul_smul_comm, hMM, smul_smul, ← hμ, ← mul_inv, inv_mul_cancel₀
      (mul_ne_zero hμ0 hμ0), one_smul]
  have hB'1 : B' ≠ 1 := fun h => hB1 μ (by rw [hM, h])
  obtain ⟨w, u, Hm, hind, hBw, hBu, hHw, hHu, hdet⟩ := exists_plane_transvection hB'2 hB'1 s
  let C : StatedSL n K := ⟨Matrix.SpecialLinearGroup.toGL ⟨Hm, hdet⟩, mem_statedSL_iff_det.2 hdet⟩
  have hC : (((C : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Hm := rfl
  have hCi : (((C⁻¹ : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Hm = 1 := by
    rw [← hC]
    simp
  refine hD.false_of_statedProj e hBD (C := C) fun k hk1 hk4 hmem => ?_
  obtain ⟨c, hc⟩ := mem_statedScalars_iff.1 hmem
  apply conj_pow_ne_smul_one hCi hind hs0 hs1 hBw hBu hHw hHu hk1 hk4 (((μ * μ) ^ k)⁻¹ * c)
  have hmat : ((((B * (C * B * C⁻¹)) ^ k : StatedSL n K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (μ * μ) ^ k • (B' * Hm * B' *
        (((C⁻¹ : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ k := by
    rw [← smul_pow]
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Units.val_pow_eq_pow_val, Units.val_mul]
    rw [← hMdef, hC, hM]
    congr 1
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  rw [hmat] at hc
  rw [mul_smul, ← hc, smul_smul, inv_mul_cancel₀ (pow_ne_zero k (mul_ne_zero hμ0 hμ0)), one_smul]

theorem false_of_lieModel_PSL [Finite X] {n f : ℕ} (hf : 2 ≤ f) (h : LieModel X .PSL n 2 f)
    (hD : IsTransClass34 D) : False := by
  rcases h with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl
    have := charP_two_of_card_eq hK
    obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne_one_of_card hK hf
    exact false_of_statedProj_statedSL hs0 hs1 e hD
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end Linear

end CFSG.LargeExtraspecial.DW
