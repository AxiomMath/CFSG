module

public import CFSG.RankThree.PartOne.CTP.SeitzUToral

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.CTP
  CFSG.ClassicalInvolution.Phan CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem eq_top_of_block_centralizers (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f ≠ 2)
    (P : primeFormUnitary h (idGram K (n + 1))) (S : Subgroup (unitarySU ℓ f K (n + 1)))
    (hS : ∀ i : Fin n, ∃ g : GL (Fin (n + 1)) K,
      (∀ A : Matrix (Fin 2) (Fin 2) K,
        blockMat (n + 1) i A * (((P : GL (Fin (n + 1)) K)⁻¹ * g * P : GL (Fin (n + 1)) K) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
          (((P : GL (Fin (n + 1)) K)⁻¹ * g * P : GL (Fin (n + 1)) K) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) K) * blockMat (n + 1) i A) ∧
      ∀ w : unitarySU ℓ f K (n + 1), (w : GL (Fin (n + 1)) K) * g = g * w → w ∈ S) :
    S = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  let Pg : GL (Fin (n + 1)) K := (P : GL (Fin (n + 1)) K)
  let φ := conjSU h P
  have hblock : ∀ (i : Fin n) (y : unitarySU ℓ f K (n + 1)) (A : Matrix (Fin 2) (Fin 2) K),
      (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) = blockMat (n + 1) i A → φ y ∈ S := by
    intro i y A hA
    obtain ⟨g, hcomm, hw⟩ := hS i
    apply hw
    have hYD : ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * (Pg⁻¹ * g * Pg) =
        (Pg⁻¹ * g * Pg) * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) := by
      apply Units.ext
      simp only [Units.val_mul]
      rw [hA]
      simpa only [Units.val_mul] using hcomm A
    have hgeq : g = Pg * (Pg⁻¹ * g * Pg) * Pg⁻¹ := by group
    show Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ * g =
      g * (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹)
    rw [hgeq]
    calc Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
          (Pg * (Pg⁻¹ * g * Pg) * Pg⁻¹)
        = Pg * (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * (Pg⁻¹ * g * Pg)) * Pg⁻¹ := by
          group
      _ = Pg * ((Pg⁻¹ * g * Pg) * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)) * Pg⁻¹ := by
          rw [hYD]
      _ = _ := by group
  let ε : Su K ℓ f (n + 1) ≃* unitarySU ℓ f K (n + 1) :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq (n + 1))
  let ι : Fin n → (Su K ℓ f 2 →* unitarySU ℓ f K (n + 1)) := fun i =>
    ε.toMonoidHom.comp (blockEmb2 K ℓ f n i)
  have hgen : ⨆ i : Fin n, (ι i).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := ℓ) (f := f) h.card_eq_sq hq n
    have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
    simpa [ι, MonoidHom.range_comp] using h2
  have hle : (⨆ i : Fin n, (ι i).range).map φ.toMonoidHom ≤ S := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hblock i _ ((a : Su K ℓ f 2) : GL (Fin 2) K) rfl
  rw [hgen, Subgroup.map_top_of_surjective _ φ.surjective] at hle
  exact top_unique hle

theorem bar_mul_eq_one_of_cube (h : UnitaryFieldData ℓ f K) (hq3 : 3 ∣ ℓ ^ f + 1) {μ lam : K}
    (hμ0 : μ ≠ 0) (hμ : μ ^ 3 = lam) (hlam : lam ^ (ℓ ^ f + 1) = 1) : h.bar μ * μ = 1 := by
  have hfin := h.finite
  have := Fintype.ofFinite K
  have hq2 : 2 ≤ ℓ ^ f := Nat.succ_le_of_lt (Nat.one_lt_pow (by have := h.one_le; omega)
    h.prime.one_lt)
  have hNe : h.bar μ * μ = μ ^ (ℓ ^ f + 1) := by rw [h.bar_apply, ← pow_succ]
  have h1 : (h.bar μ * μ) ^ 3 = 1 := by rw [hNe, ← pow_mul, mul_comm, pow_mul, hμ, hlam]
  have h2 : (h.bar μ * μ) ^ (ℓ ^ f - 1) = 1 := by
    rw [hNe, ← pow_mul]
    have h3 : (ℓ ^ f + 1) * (ℓ ^ f - 1) = Fintype.card K - 1 := by
      rw [← Nat.card_eq_fintype_card, h.card_eq_sq, sq]
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      simpa using this.symm
    rw [h3]
    exact FiniteField.pow_card_sub_one_eq_one μ hμ0
  have hcop : Nat.gcd 3 (ℓ ^ f - 1) = 1 := by
    obtain ⟨m, hm⟩ := hq3
    have h4 : ℓ ^ f - 1 = 3 * (m - 1) + 1 := by omega
    rw [h4]
    simp
  have := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rwa [hcop, pow_one] at this

theorem barTranspose_smul_mul_smul (h : UnitaryFieldData ℓ f K) (c : K)
    (X : Matrix (Fin n) (Fin n) K) :
    ((c • X).map h.bar)ᵀ * 1 * (c • X) = (h.bar c * c) • ((X.map h.bar)ᵀ * 1 * X) := by
  ext i j
  simp only [Matrix.mul_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem smul_mem_primeFormUnitary (h : UnitaryFieldData ℓ f K) {g : GL (Fin n) K}
    (hg : g ∈ primeFormUnitary h (idGram K n)) {c : K} (hc0 : c ≠ 0) (hc : h.bar c * c = 1) :
    (GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0) * g) ∈
      primeFormUnitary h (idGram K n) := by
  have hg' := mem_primeFormUnitary.1 hg
  rw [mem_primeFormUnitary, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0,
    Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  simp only [idGram, Units.val_one] at hg' ⊢
  rw [barTranspose_smul_mul_smul, hg', hc, one_smul]

end CFSG.LieType.SeitzGeneration
