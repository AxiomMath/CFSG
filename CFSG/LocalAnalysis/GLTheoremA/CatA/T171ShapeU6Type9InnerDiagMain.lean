module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9InnerDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD
open CFSG.StandardType.Line63.H5 CFSG.SectionRank.OddCover

variable {K : Type} [Field K] {n d : ℕ}

theorem isBlockDiag_of_isBlockOn {d : ℕ} {S : Finset (Fin d)}
    {M : Matrix (Fin d) (Fin d) K} (hM : IsBlockOn S M) : IsBlockDiag S M := by
  intro i j hij
  rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rw [hM i j (Or.inr hj)]
    exact Matrix.one_apply_ne (fun h => hj (h ▸ hi))
  · rw [hM i j (Or.inl hi)]
    exact Matrix.one_apply_ne (fun h => hi (h ▸ hj))

theorem u6Type9LayerInner_diag [Finite K] (h : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {τ : Fin 6 → Kˣ} (hτ3 : ∀ i, τ i ^ 3 = 1)
    (hD : diagHom 6 τ ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    {v : Kˣ} {S : Finset (Fin 6)} (hS : ∀ i, i ∈ S ↔ τ i = v)
    (hSv : S.card = 4 ∨ S.card = 5)
    {N : GL (Fin 6) K} (hNgu : N ∈ LargeEvenGUSet (Fin 6) K (2 ^ n))
    (hNN : N ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hcomm : N * diagHom 6 τ * N⁻¹ * (diagHom 6 τ)⁻¹ ∈ LargeEvenScalars (Fin 6) K)
    (hcomp : IsComponentOf
      (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨diagHom 6 τ, hD⟩)))
      (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨diagHom 6 τ, hD⟩))) :
    ∃ (g : GL (Fin 6) K) (hg : g ∈ unitarySU 2 n K 6),
      (LargeEvenProjMk (unitarySU 2 n K 6) ⟨g, hg⟩ ∈
        LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨diagHom 6 τ, hD⟩))) ∧
      ∀ t ∈ LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨diagHom 6 τ, hD⟩)),
        TableB.projConj (unitarySU 2 n K 6) ⟨N, hNN⟩ t =
          TableB.projConj (unitarySU 2 n K 6) ⟨g, Subgroup.le_normalizer hg⟩ t := by
  classical
  obtain ⟨ν0, hν0ne, hν0q, hNrel0⟩ := hNgu
  have hNrel : ((N : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ * (N : Matrix (Fin 6) (Fin 6) K) =
      (ν0 : K) • (1 : Matrix (Fin 6) (Fin 6) K) := by
    simpa [map_pow_eq_map_bar h] using hNrel0
  rw [largeEvenScalars_def] at hcomm
  obtain ⟨c, hc⟩ := hcomm
  have hNconj : N * diagHom 6 τ * N⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) c *
      diagHom 6 τ := by
    calc N * diagHom 6 τ * N⁻¹ = (N * diagHom 6 τ * N⁻¹ * (diagHom 6 τ)⁻¹) *
        diagHom 6 τ := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) c * diagHom 6 τ := by rw [hc]
  have hNDgl : N * diagHom 6 τ = Matrix.GeneralLinearGroup.scalar (Fin 6) c *
      (diagHom 6 τ * N) := by
    calc N * diagHom 6 τ = (N * diagHom 6 τ * N⁻¹) * N := by group
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 6) c * diagHom 6 τ) * N := by rw [hNconj]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) c * (diagHom 6 τ * N) := by group
  have hτpow : τ ^ 3 = 1 := funext hτ3
  have hD3 : diagHom 6 τ ^ 3 = 1 := by rw [← map_pow, hτpow, map_one]
  have hc3 : c ^ 3 = 1 := by
    have h2 : (N * diagHom 6 τ * N⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hD3, mul_one, mul_inv_cancel]
    have h3 : (Matrix.GeneralLinearGroup.scalar (Fin 6) c * diagHom 6 τ) ^ 3 = 1 := by
      rw [← hNconj]; exact h2
    have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin 6) c) (diagHom 6 τ) :=
      (commute_scalar c (diagHom 6 τ)).symm
    have hsp : (Matrix.GeneralLinearGroup.scalar (Fin 6) c) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin 6) (c ^ 3) :=
      (map_pow (Matrix.GeneralLinearGroup.scalar (Fin 6) : Kˣ →* GL (Fin 6) K) c 3).symm
    rw [hcomm.mul_pow, hsp, hD3, mul_one] at h3
    refine Units.ext ?_
    have h4 := congrArg (fun g : GL (Fin 6) K => ((g : Matrix (Fin 6) (Fin 6) K) 0 0)) h3
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at h4
    simpa using h4
  have hND : (N : Matrix (Fin 6) (Fin 6) K) * (diagHom 6 τ : Matrix (Fin 6) (Fin 6) K) =
      (c : K) • ((diagHom 6 τ : Matrix (Fin 6) (Fin 6) K) * (N : Matrix (Fin 6) (Fin 6) K)) := by
    calc (N : Matrix (Fin 6) (Fin 6) K) * (diagHom 6 τ : Matrix (Fin 6) (Fin 6) K)
        = ((N * diagHom 6 τ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) :=
          (Units.val_mul _ _).symm
      _ = ((Matrix.GeneralLinearGroup.scalar (Fin 6) c * (diagHom 6 τ * N) : GL (Fin 6) K) :
            Matrix (Fin 6) (Fin 6) K) := by rw [hNDgl]
      _ = (c : K) • ((diagHom 6 τ : Matrix (Fin 6) (Fin 6) K) *
            (N : Matrix (Fin 6) (Fin 6) K)) := by
          rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
            ← Matrix.smul_eq_diagonal_mul, Units.val_mul]
  have hS4 : 4 ≤ S.card := by rcases hSv with h' | h' <;> omega
  have hc1 : c = 1 :=
    eq_one_of_conj_diag_eq_scalar hND (Matrix.GeneralLinearGroup.det_ne_zero N) hc3 hS hS4
  have hNDcomm : N * diagHom 6 τ = diagHom 6 τ * N := by
    rw [hNDgl, hc1, map_one, one_mul]
  have hNdiag : IsBlockDiag S (N : Matrix (Fin 6) (Fin 6) K) := by
    intro i j hij
    have hτij : τ i ≠ τ j := by
      rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · intro h
        exact hj (by rw [hS j, ← h]; exact (hS i).mp hi)
      · intro h
        exact hi (by rw [hS i, h]; exact (hS j).mp hj)
    exact entry_eq_zero_of_commute hNDcomm hτij
  have hS3 : 3 ≤ S.card := by omega
  have hcard3 : S.card ≠ 3 := by rcases hSv with h' | h' <;> omega
  have hSq : (S.card, 2 ^ n) ≠ (3, 2) := fun hcon => hcard3 (congrArg Prod.fst hcon)
  have hlayer := layer_eq_map_blockSU_of_fiber h hD hS hS3 hSq hcomp
  have hNdiagbar : IsBlockDiag S ((N : Matrix (Fin 6) (Fin 6) K).map h.bar) := by
    intro i j hij
    rw [Matrix.map_apply, hNdiag i j hij, map_zero]
  have hAb : ((blockRes S (N : Matrix (Fin 6) (Fin 6) K)).map h.bar)ᵀ *
      blockRes S (N : Matrix (Fin 6) (Fin 6) K) =
        (ν0 : K) • (1 : Matrix (Fin S.card) (Fin S.card) K) :=
    blockRes_similitude h hNdiag hNrel
  set AN : GL (Fin S.card) K := blockResGL hNdiag with hANdef
  have hνq : ((Units.mk0 ν0 hν0ne : Kˣ) : K) ^ 2 ^ n = ((Units.mk0 ν0 hν0ne : Kˣ) : K) := hν0q
  have hk : Nat.Coprime S.card (2 ^ n + 1) :=
    coprime_four_or_five_two_pow_add_one h.one_le hpq hSv
  obtain ⟨z, hh, hhSU, hANeq⟩ :=
    exists_scalar_mul_mem_unitarySU_of_similitude (k := S.card) (U := AN)
      (ν := Units.mk0 ν0 hν0ne) h hk hνq (by rw [coe_blockResGL]; exact hAb)
  set hhU : ↥(unitarySU 2 n K S.card) := ⟨hh, hhSU⟩ with hhhU
  set gSU : ↥(unitarySU 2 n K 6) := blockExtSU S h hhU with hgSUdef
  have hgmat : ((gSU : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) =
      Units.map (blockExtHom S) hh := rfl
  have hgB : IsBlockOn S (((gSU : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) := by
    rw [hgmat]
    exact isBlockOn_blockExt (S := S) (N := (hh : Matrix (Fin S.card) (Fin S.card) K))
  have hGdiag : IsBlockDiag S (((gSU : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) := isBlockDiag_of_isBlockOn hgB
  have hG_eq : blockResGL hGdiag = hh := by
    apply Units.ext
    rw [coe_blockResGL, hgmat]
    exact blockRes_blockExt (S := S) (N := (hh : Matrix (Fin S.card) (Fin S.card) K))
  refine ⟨(gSU : GL (Fin 6) K), gSU.2, ?_, ?_⟩
  · rw [hlayer]
    exact Subgroup.mem_map_of_mem _ (mem_blockSU.mpr hgB)
  · intro t ht
    rw [hlayer] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    have hu_block : IsBlockOn S (((u : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) := mem_blockSU.mp hu
    rw [projConj_mk_coe, projConj_mk_coe]
    have hNblock : IsBlockOn S (((N : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        (((u : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((N⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :=
      isBlockOn_conj_of_isBlockDiag hNdiag hu_block
    have hGblock : IsBlockOn S ((((gSU : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) *
        (((u : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((((gSU : GL (Fin 6) K))⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :=
      isBlockOn_conj_of_isBlockDiag hGdiag hu_block
    have hbr : blockRes S (((N : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        (((u : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((N⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) =
        blockRes S ((((gSU : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) *
          (((u : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          ((((gSU : GL (Fin 6) K))⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) := by
      rw [blockRes_conj_eq hNdiag hu_block, blockRes_conj_eq hGdiag hu_block, hG_eq]
      have hzmat : (AN : Matrix (Fin S.card) (Fin S.card) K) =
          (z : K) • ((hh : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) := by
        rw [hANeq, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul]
      have hzinv : (((AN)⁻¹ : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) =
          (z : K)⁻¹ • (((hh)⁻¹ : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) := by
        have h2 : (AN)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin S.card) z⁻¹ * hh⁻¹ := by
          calc (AN)⁻¹ = (Matrix.GeneralLinearGroup.scalar (Fin S.card) z * hh)⁻¹ := by
                rw [hANeq]
            _ = hh⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin S.card) z)⁻¹ := mul_inv_rev _ _
            _ = hh⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin S.card) z⁻¹ := by rw [map_inv]
            _ = Matrix.GeneralLinearGroup.scalar (Fin S.card) z⁻¹ * hh⁻¹ :=
                (commute_scalar z⁻¹ hh⁻¹).eq
        rw [h2, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, scalar_mul_eq_smul,
          Units.val_inv_eq_inv_val]
      rw [hzmat, hzinv, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        mul_inv_cancel₀ z.ne_zero, one_smul]
    have hfinal : (((N : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) *
        (((u : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((N⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        ((((gSU : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) *
          (((u : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          ((((gSU : GL (Fin 6) K))⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) := by
      calc (((N : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) *
            (((u : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
            ((N⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
          = blockExt S (blockRes S ((((N : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) *
              (((u : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
              ((N⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))) :=
            (blockExt_blockRes hNblock).symm
        _ = blockExt S (blockRes S ((((gSU : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) *
              (((u : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
              ((((gSU : GL (Fin 6) K))⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))) := by
            rw [hbr]
        _ = ((((gSU : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) *
              (((u : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
              ((((gSU : GL (Fin 6) K))⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :=
            blockExt_blockRes hGblock
    apply congrArg (LargeEvenProjMk (unitarySU 2 n K 6))
    apply Subtype.ext
    apply Units.ext
    exact hfinal

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
