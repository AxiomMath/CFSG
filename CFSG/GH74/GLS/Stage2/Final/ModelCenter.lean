module

public import CFSG.GH74.GLS.Stage2.Final.ModelBlock
public import CFSG.GH74.GLS.Stage2.Final.ModelTransport
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.GH74.GLS.Stage2.Final.ModelSpData
public import CFSG.GH74.GLS.Stage2.Final.ModelDisjoint

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] noncomputable def rhoQ {a b : F} (h : a ^ 2 + b ^ 2 = -1) :
    CFSG.GH74.Filter.ClassicalOdd.Q8 →* GL (Fin 2) F :=
  (SpecialLinearGroup.toGL : SL(2, F) →* GL (Fin 2) F).comp (quatHom h)

theorem coe_rhoQ_a_one {a b : F} (h : a ^ 2 + b ^ 2 = -1) :
    ((rhoQ h (QuaternionGroup.a 1) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = quatI F :=
  quatHom_a_one h

theorem coe_rhoQ_xa_zero {a b : F} (h : a ^ 2 + b ^ 2 = -1) :
    ((rhoQ h (QuaternionGroup.xa 0) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = quatJ a b :=
  quatHom_xa_zero h

theorem rhoQ_irr {a b : F} (h : a ^ 2 + b ^ 2 = -1) (h2 : (2 : F) ≠ 0) (x : GL (Fin 2) F)
    (hx : ∀ c, x * rhoQ h c = rhoQ h c * x) : ∃ l : Fˣ, x = sc2 l := by
  have hI := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F))
    (hx (QuaternionGroup.a 1))
  have hJ := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F))
    (hx (QuaternionGroup.xa 0))
  simp only [Units.val_mul, coe_rhoQ_a_one, coe_rhoQ_xa_zero] at hI hJ
  have e00 := congrFun₂ hI 0 0
  have e01 := congrFun₂ hI 0 1
  have f00 := congrFun₂ hJ 0 0
  have f01 := congrFun₂ hJ 0 1
  simp [quatI, quatJ, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 f00 f01
  have hb : (2 : F) * ((x : Matrix (Fin 2) (Fin 2) F) 0 1 * b) = 0 := by
    linear_combination f00 - b * e00
  have ha : (2 : F) * ((x : Matrix (Fin 2) (Fin 2) F) 0 1 * a) = 0 := by
    linear_combination b * e01 - f01
  have hq2 : (2 : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    linear_combination (-a) * ha - b * hb + (2 * (x : Matrix (Fin 2) (Fin 2) F) 0 1) * h
  have hq : (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := (mul_eq_zero.1 hq2).resolve_left h2
  have hr : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination -e00 - hq
  have hdet : IsUnit (x : Matrix (Fin 2) (Fin 2) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  have hp : (x : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h0
    have : (x : Matrix (Fin 2) (Fin 2) F).det = 0 := by
      rw [Matrix.det_fin_two, hq, hr, h0]; ring
    rw [this] at hdet
    exact not_isUnit_zero hdet
  refine ⟨Units.mk0 _ hp, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hq, hr, e01]

theorem rhoQ_nc {a b : F} (h : a ^ 2 + b ^ 2 = -1) :
    ∃ c, ∀ l : Fˣ, rhoQ h c ≠ sc2 l := by
  refine ⟨QuaternionGroup.a 1, fun l hl => ?_⟩
  have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F) 0 1) hl
  simp [coe_rhoQ_a_one, quatI, sc2, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply] at this

theorem isPGroup_q8q8 : IsPGroup 2 (CFSG.GH74.Filter.ClassicalOdd.Q8 × CFSG.GH74.Filter.ClassicalOdd.Q8) := by
  apply IsPGroup.of_card (n := 6)
  rw [Nat.card_prod]
  have : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  change Nat.card (QuaternionGroup 2) * Nat.card (QuaternionGroup 2) = 2 ^ 6
  rw [this]
  norm_num

theorem odd_index_Nsub [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0)
    (h : ∃ m, Odd m ∧ Nat.card ↥M.K4 = 2 * Nat.card ↥(Dsub M) * m) : Odd (Nsub M).index := by
  obtain ⟨m, hm, hcard⟩ := h
  have h1 : (Nsub M).index * Nat.card ↥(Nsub M) = Nat.card ↥M.K4 := Subgroup.index_mul_card _
  rw [card_Nsub M h2] at h1
  have hD : 0 < Nat.card ↥(Dsub M) := Nat.card_pos
  have : (Nsub M).index = m := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 * Nat.card ↥(Dsub M) by positivity)
    rw [h1, hcard]
    ring
  rw [this]
  exact hm

theorem exists_sylow_center_of_quat [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0)
    (hodd : ∃ m, Odd m ∧ Nat.card ↥M.K4 = 2 * Nat.card ↥(Dsub M) * m) {a b : F}
    (hab : a ^ 2 + b ^ 2 = -1) (hH : ∀ g, rhoQ hab g ∈ M.H2) :
    ∃ S : Sylow 2 (PG M), (Subgroup.center ↥(S : Subgroup (PG M))).map
      (S : Subgroup (PG M)).subtype = Subgroup.zpowers (yP M) :=
  exists_sylow_center M h2 (odd_index_Nsub M h2 hodd) (rhoQ hab) hH (rhoQ_irr hab h2)
    (rhoQ_nc hab) isPGroup_q8q8

theorem rhoQ_mem_H2_lin {a b : F} (h : a ^ 2 + b ^ 2 = -1) (g : CFSG.GH74.Filter.ClassicalOdd.Q8) :
    rhoQ h g ∈ (ModelData.lin F).H2 := by
  change _ ∈ StatedSL 2 F
  rw [statedSL_eq_detOne, mem_detOne]
  exact (quatHom h g).2

theorem exists_rhoQ_uni {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    ∃ (a b : F) (h : a ^ 2 + b ^ 2 = -1), ∀ g, rhoQ h g ∈ (ModelData.uni hF).H2 := by
  obtain ⟨a, b, ha, hb, hab⟩ := CFSG.GH74.Filter.ClassicalOdd.exists_quat_unitary (f := f) hp2 hF
  have hσ : ∀ x, (CFSG.LieType.BorelTits.unitaryInvolution F p f : F →+* F) x = x ^ (p ^ f) :=
    CFSG.LieType.BorelTits.unitaryInvolution_apply F p f
  refine ⟨a, b, hab, fun g => ?_⟩
  refine ((ModelData.uni hF).mem_H2 _).2 ⟨?_, (quatHom hab g).2⟩
  exact CFSG.GH74.Filter.ClassicalOdd.isUni_quatHom hab
    (σ := (CFSG.LieType.BorelTits.unitaryInvolution F p f : F →+* F))
    (by rw [hσ]; exact ha) (by rw [hσ]; exact hb) g

end CFSG.GH74.GLS.Stage2.Final.ModelBlock

namespace CFSG.GH74.GLS.Stage2.Final

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelBlock

theorem modelCenter : ModelCenter := by
  intro Gs _ _ p f hGs S'
  obtain ⟨hp, hp2, -, hcases⟩ := hGs
  rcases hcases with hS | ⟨-, hL⟩ | ⟨-, hU⟩
  · obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psp_unpack hS
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
    obtain ⟨a, b, hab, hH⟩ := ModelSp.exists_rho_sp h2
    obtain ⟨S₁, hS₁⟩ := exists_sylow_center_of_quat (ModelData.sp F) h2 (ModelSp.odd_index_sp h2)
      hab hH
    exact sylow_center_transport (e.trans (ModelSp.spEquiv F)) S₁ (yP _) (orderOf_yP _ h2)
      ((centerIs_iff _ _).1 hS₁) S'
  · obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psl_unpack hL
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
    obtain ⟨a, b, hab⟩ := (CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.odd_field_two_dimensional_quaternion_matrices
      (ringChar_ne_two_of_two_ne_zero h2)).1
    obtain ⟨S₁, hS₁⟩ := exists_sylow_center_of_quat (ModelData.lin F) h2 (ModelOrd.odd_index_lin F h2)
      hab (rhoQ_mem_H2_lin hab)
    exact sylow_center_transport (show Gs ≃* PG (ModelData.lin F) from e) S₁ (yP _)
      (orderOf_yP _ h2) ((centerIs_iff _ _).1 hS₁) S'
  · obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psu_unpack hU
    have : Fact p.Prime := ⟨hp⟩
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    have : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF'
    obtain ⟨a, b, hab, hH⟩ := exists_rhoQ_uni hF hp2
    obtain ⟨S₁, hS₁⟩ := exists_sylow_center_of_quat (ModelData.uni hF) h2
      (ModelOrd.odd_index_uni hF hp2) hab hH
    exact sylow_center_transport (show Gs ≃* PG (ModelData.uni hF) from e) S₁ (yP _)
      (orderOf_yP _ h2) ((centerIs_iff _ _).1 hS₁) S'

end CFSG.GH74.GLS.Stage2.Final
