module

public import CFSG.Dihedral.Glauberman.DicksonMaxTrace
public import CFSG.GH74.GLS.IVK.L2.FixedSL
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core

public section

open CFSG CFSG.PSL2Table CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped MatrixGroups

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Lemma12hbM

section Basic

variable {F : Type} [Field F]

theorem psl2FieldAut_mk (σ : F ≃+* F) (X : SL(2, F)) :
    psl2FieldAut F σ (mk X) = mk (Matrix.SpecialLinearGroup.map σ.toRingHom X) := by
  rw [psl2FieldAut_apply]
  exact psl2RingEquiv_mk σ X

theorem slMap_neg (σ : F ≃+* F) (A : SL(2, F)) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (-A) =
      -Matrix.SpecialLinearGroup.map σ.toRingHom A := by
  apply Subtype.ext
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem slMap_slMap {σ : F ≃+* F} (hσ : σ * σ = 1) (A : SL(2, F)) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.map σ.toRingHom A) =
      A := by
  have h : ∀ a : F, σ (σ a) = a := fun a => congrArg (fun τ : F ≃+* F => τ a) hσ
  apply Subtype.ext
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe, h]

theorem orderOf_eq_two_of_mul_self {σ : F ≃+* F} (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    orderOf σ = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hσ) hσ1

theorem transvection_pow {i j : Fin 2} (hij : i ≠ j) (c : F) (m : ℕ) :
    Matrix.SpecialLinearGroup.transvection hij c ^ m =
      Matrix.SpecialLinearGroup.transvection hij (m • c) := by
  induction m with
  | zero => rw [pow_zero, zero_smul, Matrix.SpecialLinearGroup.transvection_coeff_zero]
  | succ m ih =>
    rw [pow_succ, ih, ← Matrix.SpecialLinearGroup.transvection_add, succ_nsmul]

end Basic

section O2

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem mk_transvection_mem_O2 (hF : ringChar F ≠ 2) {c : F} (hc : σ c = c) {i j : Fin 2}
    (hij : i ≠ j) :
    mk (Matrix.SpecialLinearGroup.transvection hij c) ∈
      (oResidual 2 ↥(fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ))).map
        (fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ)).subtype := by
  have hp : (ringChar F).Prime := CharP.prime_ringChar F
  have hy : psl2FieldAut F σ (mk (Matrix.SpecialLinearGroup.transvection hij c)) =
      mk (Matrix.SpecialLinearGroup.transvection hij c) := by
    rw [psl2FieldAut_mk, Matrix.SpecialLinearGroup.map_transvection]
    exact congrArg (fun a : F => mk (Matrix.SpecialLinearGroup.transvection hij a)) hc
  have hpow : mk (Matrix.SpecialLinearGroup.transvection hij c) ^ ringChar F = 1 := by
    rw [← map_pow, transvection_pow, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul,
      Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]
  have hcop : Nat.Coprime (orderOf (mk (Matrix.SpecialLinearGroup.transvection hij c))) 2 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hpow)
      ((Nat.coprime_primes hp Nat.prime_two).2 hF)
  have hyC : mk (Matrix.SpecialLinearGroup.transvection hij c) ∈
      fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ) := hy
  have hyord : Nat.Coprime
      (orderOf (⟨_, hyC⟩ : ↥(fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ)))) 2 := by
    rw [Subgroup.orderOf_mk]
    exact hcop
  exact Subgroup.mem_map.2 ⟨⟨_, hyC⟩, Subgroup.subset_closure hyord, rfl⟩

omit [Finite F] in
theorem exists_fixed_lift_of_odd (hF : ringChar F ≠ 2) {x : PSL(2, F)}
    (hx : psl2FieldAut F σ x = x) (hodd : Odd (orderOf x)) :
    ∃ X : SL(2, F), mk X = x ∧ Matrix.SpecialLinearGroup.map σ.toRingHom X = X := by
  obtain ⟨X, rfl⟩ := mk_surjective x
  rw [psl2FieldAut_mk] at hx
  rcases (mk_eq_mk_iff _ _).1 hx.symm with h | h
  · exact ⟨X, rfl, h⟩
  · exfalso
    apply neg_one_ne_one_SL (Ring.two_ne_zero hF)
    have hm : mk X ^ orderOf (mk X) = 1 := pow_orderOf_eq_one _
    rcases CFSG.Glauberman.Dickson.MaxTrace.pow_lift hm with h1 | h1
    · have := congrArg (Matrix.SpecialLinearGroup.map σ.toRingHom) h1
      rw [map_pow, h, hodd.neg_pow, h1, map_one] at this
      exact this
    · have := congrArg (Matrix.SpecialLinearGroup.map σ.toRingHom) h1
      rw [map_pow, h, hodd.neg_pow, h1, slMap_neg, map_one, neg_neg] at this
      exact this.symm

omit [Finite F] in
theorem O2_le_fixedLift (hF : ringChar F ≠ 2) :
    (oResidual 2 ↥(fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ))).map
        (fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ)).subtype ≤
      (MonoidHom.eqLocus (Matrix.SpecialLinearGroup.map σ.toRingHom)
        (MonoidHom.id SL(2, F))).map mk := by
  rw [Subgroup.map_le_iff_le_comap]
  show Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  intro x hx
  have hodd : Odd (orderOf (x : PSL(2, F))) := by
    rw [Subgroup.orderOf_coe]
    exact Nat.coprime_two_right.1 hx
  obtain ⟨X, hXx, hX⟩ := exists_fixed_lift_of_odd (σ := σ) hF (x := (x : PSL(2, F))) x.2 hodd
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  exact Subgroup.mem_map.2 ⟨X, hX, hXx⟩

theorem mk_mem_O2_of_fixed (hF : ringChar F ≠ 2) {X : SL(2, F)}
    (hX : Matrix.SpecialLinearGroup.map σ.toRingHom X = X) :
    mk X ∈ (oResidual 2 ↥(fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ))).map
      (fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ)).subtype := by
  have hS : ∀ i j, σ ((X : Matrix (Fin 2) (Fin 2) F) i j) = (X : Matrix (Fin 2) (Fin 2) F) i j :=
    fun i j => congrArg (fun S : SL(2, F) => (S : Matrix (Fin 2) (Fin 2) F) i j) hX
  obtain ⟨M, rfl⟩ := exists_specialLinear_map_eq σ X hS
  set C := fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ)
  let Φ : SL(2, fixedField σ) →* PSL(2, F) :=
    mk.comp (Matrix.SpecialLinearGroup.map (fixedField σ).subtype)
  have htop : Subgroup.comap Φ ((oResidual 2 ↥C).map C.subtype) = ⊤ := by
    have hcl := Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
      (ι := Fin 2) (K := fixedField σ)
    rw [eq_top_iff, ← hcl, Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show mk (Matrix.SpecialLinearGroup.map (fixedField σ).subtype
      (Matrix.SpecialLinearGroup.transvection t.hij t.c)) ∈ _
    rw [Matrix.SpecialLinearGroup.map_transvection]
    exact mk_transvection_mem_O2 hF (fixedField_apply σ t.c) t.hij
  have hM : M ∈ Subgroup.comap Φ ((oResidual 2 ↥C).map C.subtype) := by
    rw [htop]
    exact Subgroup.mem_top M
  exact Subgroup.mem_comap.1 hM

omit [Finite F] in
theorem no_twist (hσ : σ * σ = 1) (hF : ringChar F ≠ 2) {X D : SL(2, F)}
    (hX : Matrix.SpecialLinearGroup.map σ.toRingHom X = X) (hXX : X * X = -1)
    (hδ : D * X * (Matrix.SpecialLinearGroup.map σ.toRingHom D)⁻¹ = 1 ∨
      D * X * (Matrix.SpecialLinearGroup.map σ.toRingHom D)⁻¹ = -1) : False := by
  obtain ⟨δ, hδdef⟩ : ∃ δ : SL(2, F),
      δ = D * X * (Matrix.SpecialLinearGroup.map σ.toRingHom D)⁻¹ := ⟨_, rfl⟩
  rw [← hδdef] at hδ
  have hσδ : Matrix.SpecialLinearGroup.map σ.toRingHom δ = δ := by
    rcases hδ with h | h
    · rw [h, map_one]
    · rw [h, slMap_neg, map_one]
  have hδδ : δ * δ = 1 := by
    rcases hδ with h | h <;> simp [h]
  have hσδ' : Matrix.SpecialLinearGroup.map σ.toRingHom δ =
      Matrix.SpecialLinearGroup.map σ.toRingHom D * X * D⁻¹ := by
    rw [hδdef, map_mul, map_mul, map_inv, slMap_slMap hσ, hX]
  have key : δ * Matrix.SpecialLinearGroup.map σ.toRingHom δ = -1 := by
    rw [hσδ', hδdef]
    calc D * X * (Matrix.SpecialLinearGroup.map σ.toRingHom D)⁻¹ *
          (Matrix.SpecialLinearGroup.map σ.toRingHom D * X * D⁻¹)
        = D * (X * X) * D⁻¹ := by group
      _ = -1 := by rw [hXX, mul_neg, mul_one, neg_mul, mul_inv_cancel]
  rw [hσδ, hδδ] at key
  exact neg_one_ne_one_SL (Ring.two_ne_zero hF) key.symm

theorem exists_twist_sl (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) (X : SL(2, F))
    (hX : X * Matrix.SpecialLinearGroup.map σ.toRingHom X = 1) :
    ∃ E ε : SL(2, F), (ε = 1 ∨ ε = -1) ∧
      E = ε * (X * Matrix.SpecialLinearGroup.map σ.toRingHom E) := by
  have hord : orderOf σ = 2 := orderOf_eq_two_of_mul_self hσ hσ1
  have hAi : H90.Ai σ (X : Matrix (Fin 2) (Fin 2) F) 2 = 1 := by
    have h1 : H90.Ai σ (X : Matrix (Fin 2) (Fin 2) F) 1 = X := by
      show (X : Matrix (Fin 2) (Fin 2) F) * (1 : Matrix (Fin 2) (Fin 2) F).map σ = X
      rw [Matrix.map_one σ (map_zero σ) (map_one σ), mul_one]
    show (X : Matrix (Fin 2) (Fin 2) F) *
      (H90.Ai σ (X : Matrix (Fin 2) (Fin 2) F) 1).map σ = 1
    rw [h1]
    have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hX
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe] using this
  obtain ⟨B, hBdet, hXB⟩ :=
    H90.speiser σ (X : Matrix (Fin 2) (Fin 2) F) 2 hord (by norm_num) hAi
  have hdet : σ B.det = B.det := by
    have h1 := congrArg Matrix.det hXB
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul] at h1
    have h2 : (B.map σ).det = σ B.det := (RingHom.map_det σ.toRingHom B).symm
    rw [h2] at h1
    exact h1
  have hfix : B.det ∈ fixedField σ := (mem_fixedField_iff σ _).2 hdet
  obtain ⟨e, he⟩ := isSquare_of_mem_fixedField_of_even σ (by rw [hord]; exact even_two) hfix
  have he0 : e ≠ 0 := by
    rintro rfl
    apply hBdet
    rw [he, mul_zero]
  have hσe : σ e = e ∨ σ e = -e := by
    apply mul_self_eq_mul_self_iff.1
    rw [← map_mul, ← he]
    exact hdet
  have hdetE : (e⁻¹ • B).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, he]
    calc (e⁻¹) ^ 2 * (e * e) = (e⁻¹ * e) ^ 2 := by ring
      _ = 1 := by rw [inv_mul_cancel₀ he0, one_pow]
  obtain ⟨E, hEc⟩ : ∃ E : SL(2, F), (E : Matrix (Fin 2) (Fin 2) F) = e⁻¹ • B :=
    ⟨⟨_, hdetE⟩, rfl⟩
  have hσE : ((Matrix.SpecialLinearGroup.map σ.toRingHom E : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F) = (σ e)⁻¹ • B.map σ := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, hEc, Matrix.map_apply, Matrix.smul_apply]
  rcases hσe with h | h
  · refine ⟨E, 1, Or.inl rfl, ?_⟩
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hσE, h,
      Matrix.SpecialLinearGroup.coe_one, one_mul, Matrix.mul_smul, hXB, hEc]
  · refine ⟨E, -1, Or.inr rfl, ?_⟩
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hσE, h,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, neg_mul, one_mul,
      Matrix.mul_smul, hXB, hEc, inv_neg, neg_smul, neg_neg]

end O2

end Lemma12hbM

section Main

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem mem_O2_fixed_iff (hF : ringChar F ≠ 2) (g : PSL(2, F)) (_hg : psl2FieldAut F σ g = g) :
    g ∈ (oResidual 2 ↥(fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ))).map
        (fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ)).subtype ↔
      ∃ X : SL(2, F), CFSG.PSL2Table.mk X = g ∧
        Matrix.SpecialLinearGroup.map σ.toRingHom X = X := by
  constructor
  · intro hg
    obtain ⟨X, hX, hXg⟩ := Subgroup.mem_map.1 (Lemma12hbM.O2_le_fixedLift hF hg)
    exact ⟨X, hXg, hX⟩
  · rintro ⟨X, rfl, hX⟩
    exact Lemma12hbM.mk_mem_O2_of_fixed hF hX

theorem twisted_ne_one_of_mem (hσ : σ * σ = 1) (_hσ1 : σ ≠ 1) (hF : ringChar F ≠ 2)
    (g : PSL(2, F)) (hg : psl2FieldAut F σ g = g) (hg2 : g * g = 1) (hg1 : g ≠ 1)
    (hL : g ∈ (oResidual 2 ↥(fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ))).map
        (fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ)).subtype) :
    ∀ c : PSL(2, F), c * g * (psl2FieldAut F σ c)⁻¹ ≠ 1 := by
  intro c hc
  obtain ⟨X, rfl, hX⟩ := (mem_O2_fixed_iff hF g hg).1 hL
  obtain ⟨D, rfl⟩ := mk_surjective c
  have hXX : X * X = -1 :=
    CFSG.Glauberman.Dickson.MaxTrace.lift_involution (Ring.two_ne_zero hF) hg2 hg1
  rw [Lemma12hbM.psl2FieldAut_mk, ← map_inv, ← map_mul, ← map_mul, mk_eq_one_iff] at hc
  exact Lemma12hbM.no_twist hσ hF hX hXX hc

theorem exists_twisted_eq_one (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) (hF : ringChar F ≠ 2)
    (g : PSL(2, F)) (hg : psl2FieldAut F σ g = g) (hg2 : g * g = 1) (hg1 : g ≠ 1)
    (hL : g ∉ (oResidual 2 ↥(fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ))).map
        (fixedSubgroup (PSL(2, F)) (psl2FieldAut F σ)).subtype) :
    ∃ c : PSL(2, F), c * g * (psl2FieldAut F σ c)⁻¹ = 1 := by
  obtain ⟨X, rfl⟩ := mk_surjective g
  have hXX : X * X = -1 :=
    CFSG.Glauberman.Dickson.MaxTrace.lift_involution (Ring.two_ne_zero hF) hg2 hg1
  have hneg : Matrix.SpecialLinearGroup.map σ.toRingHom X = -X := by
    have h := hg
    rw [Lemma12hbM.psl2FieldAut_mk] at h
    rcases (mk_eq_mk_iff _ _).1 h.symm with h' | h'
    · exact absurd (Lemma12hbM.mk_mem_O2_of_fixed hF h') hL
    · exact h'
  have hXσ : X * Matrix.SpecialLinearGroup.map σ.toRingHom X = 1 := by
    rw [hneg, mul_neg, hXX, neg_neg]
  obtain ⟨E, ε, hε, hE⟩ := Lemma12hbM.exists_twist_sl hσ hσ1 X hXσ
  have hmkε : mk ε = 1 := by
    rcases hε with rfl | rfl
    · exact map_one _
    · exact (mk_eq_one_iff _).2 (Or.inr rfl)
  have h1 : mk E = mk X * psl2FieldAut F σ (mk E) := by
    rw [Lemma12hbM.psl2FieldAut_mk, ← map_mul]
    conv_lhs => rw [hE]
    rw [map_mul, hmkε, one_mul]
  refine ⟨(mk E)⁻¹, ?_⟩
  rw [map_inv, inv_inv, mul_assoc, ← h1, inv_mul_cancel]

end Main

end CFSG.GH74.GLS.IVK.Proofs2
