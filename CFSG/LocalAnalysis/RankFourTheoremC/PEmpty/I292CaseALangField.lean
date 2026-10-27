module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALangBase
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALang

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.RankThree.UnitaryDescent
open CFSG.RankThree.LinearDescent (conjAut_mul_fieldAut_pow map_eq_glAut)

theorem exists_conj_of_pow_orderOf_eq_one {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (A : GL (Fin n) K) (σ : K ≃+* K) (h : (conjAut n K A * fieldAut n K σ) ^ orderOf σ = 1) :
    ∃ M : GL (Fin n) K, conjAut n K A * fieldAut n K σ =
      conjAut n K M * fieldAut n K σ * (conjAut n K M)⁻¹ := by
  classical
  obtain ⟨ℓ, f, hℓ, hf, hK⟩ := exists_card_eq_prime_pow K
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have : Finite (K ≃+* K) := finite_ringEquiv K
  obtain ⟨m, hm⟩ : ∃ m, orderOf σ = m := ⟨_, rfl⟩
  have hmpos : 0 < m := hm ▸ orderOf_pos σ
  have hσm : σ ^ m = 1 := hm ▸ pow_orderOf_eq_one σ
  rw [hm, conjAut_mul_fieldAut_pow, hσm, map_one, mul_one] at h
  have h' : conjAut n K (twistedNorm σ A m) * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one]
    exact h
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h'
  have hcL : twistedNorm σ A m = GeneralLinearGroup.scalar (Fin n) c := hc.symm
  have hσc : σ (c : K) = c := by
    have e1 := twistedNorm_succ σ A m
    have e2 := twistedNorm_succ' σ A m
    rw [hσm, map_one, MulAut.one_apply, hcL] at e1
    rw [hcL, glAut_scalar] at e2
    have e3 : GeneralLinearGroup.scalar (Fin n) c * A =
        GeneralLinearGroup.scalar (Fin n) (Units.map (σ : K →* K) c) * A := by
      rw [← e1, e2, scalar_mul_comm]
    have e4 := mul_right_cancel e3
    have e5 := congrArg (fun g : GL (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) e4
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.coe_map] at e5
    exact e5.symm
  obtain ⟨b, hb⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ (c := (c : K)⁻¹)
    (by rw [map_inv₀, hσc])
  rw [hm] at hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [Finset.prod_eq_zero (Finset.mem_range.mpr hmpos) (map_zero (σ ^ 0))] at hb
    exact inv_ne_zero c.ne_zero hb.symm
  set A' : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0) * A with hA'
  have hcA' : conjAut n K A' = conjAut n K A := by rw [hA', map_mul, conjAut_scalar, one_mul]
  have hL' : twistedNorm σ A' m = 1 := by
    rw [hA', twistedNorm_scalar_mul, hcL, ← map_mul]
    rw [← map_one (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K)]
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.coe_prod]
    simp only [Units.coe_map, Units.val_mk0, Units.val_one]
    change (∏ i ∈ Finset.range m, (σ ^ i) b) * c = 1
    rw [hb, inv_mul_cancel₀ c.ne_zero]
  set γ := semilin σ A' with hγ
  have hγp : ∀ v, (⇑γ)^[m] v = v := fun v => by
    rw [hγ, iterate_semilin, hL', Units.val_one, Matrix.one_mulVec, hσm]
    rfl
  obtain ⟨-, _k₀, -, -, bb, hbb, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis hℓ hf hK σ hm (Module.finrank_fin_fun K) γ
      (semilin_smul σ _) hγp
  set Bm : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => bb j i with hBm
  have hBmT : Bm = (Pi.basisFun K (Fin n)).toMatrix bb := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rfl
  have hBm1 : Bm * bb.toMatrix (Pi.basisFun K (Fin n)) = 1 := by
    rw [hBmT, Module.Basis.toMatrix_mul_toMatrix_flip]
  have hBm2 : bb.toMatrix (Pi.basisFun K (Fin n)) * Bm = 1 := by
    rw [hBmT, Module.Basis.toMatrix_mul_toMatrix_flip]
  set Mg : GL (Fin n) K := ⟨Bm, bb.toMatrix (Pi.basisFun K (Fin n)), hBm1, hBm2⟩ with hMg
  have hfixM : A' * glAut σ Mg = Mg := by
    apply Units.ext
    rw [Units.val_mul, coe_glAut]
    ext i j
    have := congrFun (hbb j) i
    rw [hγ, semilin_apply] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hMg, hBm] using this
  refine ⟨Mg, ?_⟩
  have e1 : fieldAut n K σ * conjAut n K (Mg⁻¹) * (fieldAut n K σ)⁻¹ =
      conjAut n K (glAut σ (Mg⁻¹)) := by
    rw [htrans.2.2.1, map_eq_glAut]
  have e2 : Mg * glAut σ (Mg⁻¹) = A' := by
    rw [map_inv, mul_inv_eq_iff_eq_mul]
    exact hfixM.symm
  calc conjAut n K A * fieldAut n K σ = conjAut n K A' * fieldAut n K σ := by rw [hcA']
    _ = conjAut n K (Mg * glAut σ (Mg⁻¹)) * fieldAut n K σ := by rw [e2]
    _ = conjAut n K Mg * (fieldAut n K σ * conjAut n K (Mg⁻¹) * (fieldAut n K σ)⁻¹) *
          fieldAut n K σ := by rw [e1, map_mul]
    _ = conjAut n K Mg * fieldAut n K σ * (conjAut n K Mg)⁻¹ := by rw [map_inv]; group

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALang
