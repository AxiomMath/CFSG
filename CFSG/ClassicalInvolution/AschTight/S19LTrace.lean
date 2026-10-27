module

public import CFSG.ClassicalInvolution.AschTight.S1916CSR
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
public import CFSG.ClassicalInvolution.AschTight.S1911FusC

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19L

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups

section Matrix

variable {F : Type} [Field F]

theorem trace_inv_sl2 (M : SL(2, F)) :
    Matrix.trace ((M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (M : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two,
    Matrix.trace_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

theorem mul_self_eq_neg_one_of_trace_eq_zero (M : SL(2, F))
    (h : Matrix.trace (M : Matrix (Fin 2) (Fin 2) F) = 0) :
    (M : Matrix (Fin 2) (Fin 2) F) * M = -1 := by
  have hdet : (M : Matrix (Fin 2) (Fin 2) F).det = 1 := M.2
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), neg_zero, Fin.zero_eta, Fin.mk_one,
      Fin.isValue]
  · linear_combination (M : Matrix (Fin 2) (Fin 2) F) 0 0 * h - hdet
  · linear_combination (M : Matrix (Fin 2) (Fin 2) F) 0 1 * h
  · linear_combination (M : Matrix (Fin 2) (Fin 2) F) 1 0 * h
  · linear_combination (M : Matrix (Fin 2) (Fin 2) F) 1 1 * h - hdet

theorem mul_self_eq_neg_one_of_conj (h2 : (2 : F) ≠ 0) (g : GL (Fin 2) F) (M : SL(2, F))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h : (g : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        -((M ^ ε : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) :
    (M : Matrix (Fin 2) (Fin 2) F) * M = -1 := by
  apply mul_self_eq_neg_one_of_trace_eq_zero
  have h1 := congrArg Matrix.trace h
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul,
    Matrix.trace_neg] at h1
  have h3 : Matrix.trace ((M ^ ε : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (M : Matrix (Fin 2) (Fin 2) F) := by
    rcases hε with rfl | rfl
    · rw [zpow_one]
    · rw [zpow_neg_one, trace_inv_sl2]
  rw [h3] at h1
  have h4 : (2 : F) * Matrix.trace (M : Matrix (Fin 2) (Fin 2) F) = 0 := by
    linear_combination h1
  exact (mul_eq_zero.mp h4).resolve_left h2

end Matrix

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem false_of_field_eq_one (hd : Sec19DataT p f K z S W L t V) {p' e' : ℕ} [Fact p'.Prime]
    (hp'2 : p' ≠ 2)
    (eY : ↥(sec19Y K z) ⧸ classicalInvolutionOddCore ↥(sec19Y K z) ≃* SL(2, GaloisField p' e'))
    (hFcard : Nat.card (GaloisField p' e') = p' ^ e')
    (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p' e')))
    (h3 : 3 < Nat.card (GaloisField p' e')) {b : G}
    (hbN : b ∈ Subgroup.normalizer ((sec19Y K z : Subgroup G) : Set G))
    (hfield : (normalizerToPGammaL2Mod eY hFcard hF h3 ⟨b, hbN⟩).right = 1) {c : G}
    (hc : c ∈ W ⊓ sec19Y K z) (hc8 : 8 ≤ orderOf c) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hbc : b * c * b⁻¹ = z * c ^ ε) : False := by
  have hzZ := S1916.isUniqueInvolution_W_inf hd
  have hbot : W ⊓ sec19Y K z ⊓ oddCoreOf (sec19Y K z) = ⊥ :=
    S1916.inf_oddCoreOf_eq_bot (S.isPGroup'.to_le (inf_le_left.trans hd.hWS)) _
  have h2 : (2 : GaloisField p' e') ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p' e') p']; exact hp'2)
  obtain ⟨g, hg⟩ := S1911.exists_semilinHom_of_mem eY hFcard hF h3 ⟨b, hbN⟩
  rw [hfield] at hg
  set cY : ↥(sec19Y K z) := ⟨c, hc.2⟩ with hcY
  set zY : ↥(sec19Y K z) := ⟨z, hzZ.mem.2⟩ with hzY
  set M := S1911.slProj (sec19Y K z) eY cY with hM
  have hz1 : S1911.slProj (sec19Y K z) eY zY ≠ 1 := by
    intro h
    rw [S1911.slProj_eq_one_iff] at h
    have hmem : z ∈ W ⊓ sec19Y K z ⊓ oddCoreOf (sec19Y K z) := ⟨hzZ.mem, h⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hzZ.ne_one hmem
  have hz2 : S1911.slProj (sec19Y K z) eY zY ^ 2 = 1 := by
    rw [← map_pow, sq, show zY * zY = 1 from Subtype.ext hzZ.sq, map_one]
  have hzneg := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 _ hz2 hz1
  have hbM : S1911.slAut (sec19Y K z) eY ⟨b, hbN⟩ M =
      S1911.slProj (sec19Y K z) eY zY * M ^ ε := by
    rw [hM, S1911.slAut_slProj, ← map_zpow, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [normalizerConj_apply_coe]
    exact hbc
  rw [hg] at hbM
  have hmat := congrArg
    (fun A : SL(2, GaloisField p' e') => (A : Matrix (Fin 2) (Fin 2) (GaloisField p' e'))) hbM
  simp only [coe_semilinHom, Matrix.SpecialLinearGroup.coe_mul, hzneg, neg_one_mul] at hmat
  have hmap : (M : Matrix (Fin 2) (Fin 2) (GaloisField p' e')).map
      ((1 : GaloisField p' e' ≃+* GaloisField p' e') : GaloisField p' e' → GaloisField p' e') =
        (M : Matrix (Fin 2) (Fin 2) (GaloisField p' e')) := by
    ext i j
    rfl
  rw [hmap] at hmat
  have hsq := mul_self_eq_neg_one_of_conj h2 g M hε hmat
  have hcc : S1911.slProj (sec19Y K z) eY (cY * cY) = S1911.slProj (sec19Y K z) eY zY := by
    apply Subtype.ext
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hsq, hzneg]
  have h1 : S1911.slProj (sec19Y K z) eY (cY * cY * zY⁻¹) = 1 := by
    rw [map_mul, hcc, map_inv, mul_inv_cancel]
  rw [S1911.slProj_eq_one_iff] at h1
  have hmem : c * c * z⁻¹ ∈ W ⊓ sec19Y K z ⊓ oddCoreOf (sec19Y K z) :=
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hc) (Subgroup.inv_mem _ hzZ.mem), h1⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have hc4 : c ^ 4 = 1 := by
    have hcz : c * c = z := by
      calc c * c = c * c * z⁻¹ * z := by group
        _ = z := by rw [hmem, one_mul]
    calc c ^ 4 = (c * c) * (c * c) := by rw [pow_succ, pow_succ, pow_succ, pow_one]; group
      _ = 1 := by rw [hcz, hzZ.sq]
  have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc4)
  omega

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19L
