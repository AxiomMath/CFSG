module

public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergBISL2SylowCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergBIQuaternionCommutant

public section

namespace CFSG.QuasithinUnique

open Matrix CFSG.LinearGroups

variable {K : Type*} [Field K]

@[expose] def slConjAut (A : GL (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun X := ⟨(A : Matrix (Fin 2) (Fin 2) K) * X *
      ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
      rw [det_mul, det_mul, X.2, mul_one, ← det_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, det_one]⟩
  invFun X := ⟨((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X *
      (A : Matrix (Fin 2) (Fin 2) K), by
      rw [det_mul, det_mul, X.2, mul_one, ← det_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, det_one]⟩
  left_inv X := by
    apply Subtype.ext
    change ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((A : Matrix (Fin 2) (Fin 2) K) *
      X * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * (A : Matrix (Fin 2) (Fin 2) K) = X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one]
  right_inv X := by
    apply Subtype.ext
    change (A : Matrix (Fin 2) (Fin 2) K) * (((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      X * (A : Matrix (Fin 2) (Fin 2) K)) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]
  map_mul' X Y := by
    apply Subtype.ext
    change (A : Matrix (Fin 2) (Fin 2) K) * ((X : Matrix (Fin 2) (Fin 2) K) * Y) *
        ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) * X * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((A : Matrix (Fin 2) (Fin 2) K) * Y * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    simp only [Matrix.mul_assoc]
    congr 2
    rw [← Matrix.mul_assoc ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem coe_slConjAut (A : GL (Fin 2) K) (X : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((slConjAut A X : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) * X * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

@[expose] noncomputable def pslConjAut (A : GL (Fin 2) K) :
    ProjectiveSpecialLinearGroup (Fin 2) K ≃* ProjectiveSpecialLinearGroup (Fin 2) K :=
  QuotientGroup.congr _ _ (slConjAut A) (Subgroup.map_center_eq _)

theorem pslConjAut_mk (A : GL (Fin 2) K) (X : Matrix.SpecialLinearGroup (Fin 2) K) :
    pslConjAut A (QuotientGroup.mk X : ProjectiveSpecialLinearGroup (Fin 2) K) =
      QuotientGroup.mk (slConjAut A X) :=
  QuotientGroup.congr_mk _ _ _ _ X

theorem mk_eq_mk_iff {u v : Matrix.SpecialLinearGroup (Fin 2) K} :
    (QuotientGroup.mk u : ProjectiveSpecialLinearGroup (Fin 2) K) = QuotientGroup.mk v ↔
      v = u ∨ v = -u := by
  rw [QuotientGroup.eq]
  have hc : ∀ w, w ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) ↔ w = 1 ∨ w = -1 := by
    intro w
    rw [← scalarSubgroup_eq_center, ← SetLike.mem_coe, coe_scalarSubgroup_two]
    simp
  rw [hc]
  constructor
  · rintro (h | h)
    · left
      calc v = u * (u⁻¹ * v) := by group
        _ = u := by rw [h, mul_one]
    · right
      calc v = u * (u⁻¹ * v) := by group
        _ = -u := by rw [h, mul_neg, mul_one]
  · rintro (rfl | rfl)
    · left
      group
    · right
      rw [mul_neg, inv_mul_cancel]

@[expose] def signRep (x y : Matrix.SpecialLinearGroup (Fin 2) K) (δ η : Bool) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  (if η then 1 else x) * (if δ then 1 else y)

theorem conj_signRep {x y : Matrix.SpecialLinearGroup (Fin 2) K} (hq : IsQuaternionPair x y)
    (δ η : Bool) :
    signRep x y δ η * x * (signRep x y δ η)⁻¹ = (if δ then x else -x) ∧
      signRep x y δ η * y * (signRep x y δ η)⁻¹ = (if η then y else -y) := by
  obtain ⟨hx, hy, hxy⟩ := hq
  have hx' : x * x = -1 := by rw [← sq, hx]
  have hy' : y * y = -1 := by rw [← sq, hy]
  have hxinv : x⁻¹ = -x := inv_eq_of_mul_eq_one_right (by rw [mul_neg, hx', neg_neg])
  have hyinv : y⁻¹ = -y := inv_eq_of_mul_eq_one_right (by rw [mul_neg, hy', neg_neg])
  have hxx : x * x * x⁻¹ = x := by group
  have hyy : y * y * y⁻¹ = y := by group
  have hxy' : x * y * x⁻¹ = -y := by
    rw [hxy, hxinv, mul_neg, neg_mul, neg_neg, mul_assoc, hx', mul_neg, mul_one]
  have hyx : y * x * y⁻¹ = -x := by
    have h1 : y * x = -(x * y) := by rw [hxy, neg_neg]
    rw [h1, hyinv, mul_neg, neg_mul, neg_neg, mul_assoc, hy', mul_neg, mul_one]
  have hneg : ∀ u w : Matrix.SpecialLinearGroup (Fin 2) K, w * (-u) * w⁻¹ = -(w * u * w⁻¹) :=
    fun u w => by rw [mul_neg, neg_mul]
  cases δ <;> cases η <;> simp only [signRep, ite_true, Bool.false_eq_true, ite_false, one_mul,
    mul_one, inv_one]
  · constructor
    · rw [show x * y * x * (x * y)⁻¹ = x * (y * x * y⁻¹) * x⁻¹ by group, hyx, hneg, hxx]
    · rw [show x * y * y * (x * y)⁻¹ = x * (y * y * y⁻¹) * x⁻¹ by group, hyy, hxy']
  · exact ⟨hyx, hyy⟩
  · exact ⟨hxx, hxy'⟩
  · constructor <;> group

theorem odd_linear_two_projective_Sylow_centralizer_inner [Finite K] (hK : ringChar K ≠ 2)
    (Q : Sylow 2 (ProjectiveSpecialLinearGroup (Fin 2) K)) (A : GL (Fin 2) K)
    (hA : ∀ q ∈ Q, pslConjAut A q = q) :
    ∃ (l : Kˣ) (c : Matrix.SpecialLinearGroup (Fin 2) K),
      (A : Matrix (Fin 2) (Fin 2) K) = (l : K) • (c : Matrix (Fin 2) (Fin 2) K) ∧
      IsSquare (Matrix.GeneralLinearGroup.det A) ∧
      pslConjAut A =
        MulAut.conj (QuotientGroup.mk c : ProjectiveSpecialLinearGroup (Fin 2) K) := by
  classical
  set π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) with hπ
  have hker : IsPGroup 2 π.ker := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hπ, QuotientGroup.ker_mk', ← scalarSubgroup_eq_center, ← SetLike.coe_sort_coe,
      coe_scalarSubgroup_two, Nat.card_eq_card_toFinset]
    have hne : (1 : Matrix.SpecialLinearGroup (Fin 2) K) ≠ -1 :=
      (CFSG.LocalAnalysis.ComponentInitial.sl2_neg_one_ne_one hK).symm
    simp [Set.toFinset_insert, hne]
  have hrange : (Q : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) K)) ≤ π.range := by
    rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]
    exact le_top
  let P := Q.comapOfKerIsPGroup π hker hrange
  obtain ⟨x, hxP, y, hyP, hq⟩ := exists_quaternion_pair_mem_sylow hK P
  have hPQ : ∀ u ∈ P, (QuotientGroup.mk u : ProjectiveSpecialLinearGroup (Fin 2) K) ∈ Q := by
    intro u hu
    have : u ∈ (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) := hu
    rw [Sylow.coe_comapOfKerIsPGroup, Subgroup.mem_comap] at this
    exact this
  have hsign : ∀ u ∈ P, ∃ δ : Bool, slConjAut A u = if δ then u else -u := by
    intro u hu
    have h := hA _ (hPQ u hu)
    rw [pslConjAut_mk, mk_eq_mk_iff] at h
    rcases h with h | h
    · exact ⟨true, by simpa using h.symm⟩
    · refine ⟨false, ?_⟩
      have h' := congrArg Neg.neg h
      rw [neg_neg] at h'
      simpa using h'.symm
  obtain ⟨δ, hδ⟩ := hsign x hxP
  obtain ⟨η, hη⟩ := hsign y hyP
  set c := signRep x y δ η with hc
  obtain ⟨hcx, hcy⟩ := conj_signRep hq δ η
  set B : Matrix (Fin 2) (Fin 2) K :=
    ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A with hB
  have hcomm : ∀ (u w : Matrix.SpecialLinearGroup (Fin 2) K),
      slConjAut A u = w → c * u * c⁻¹ = w → Commute B u := by
    intro u w h1 h2
    have e1 := congrArg Subtype.val h1
    have e2 := congrArg Subtype.val h2
    rw [coe_slConjAut] at e1
    simp only [Matrix.SpecialLinearGroup.coe_mul] at e2
    have hAu : (A : Matrix (Fin 2) (Fin 2) K) * u = (w : Matrix (Fin 2) (Fin 2) K) * A := by
      rw [← e1, Matrix.mul_assoc _ _ (A : Matrix (Fin 2) (Fin 2) K), ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.mul_one]
    have hcu : ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * w =
        u * ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      rw [← e2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
        inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    change B * u = u * B
    rw [hB, Matrix.mul_assoc, hAu, ← Matrix.mul_assoc, hcu, Matrix.mul_assoc]
  obtain ⟨r, hr⟩ := eq_scalar_of_commute_quaternion hK hq.matrix.1 hq.matrix.2.1
    hq.matrix.2.2 (hcomm x _ hδ hcx) (hcomm y _ hη hcy)
  have hAc : (A : Matrix (Fin 2) (Fin 2) K) = r • (c : Matrix (Fin 2) (Fin 2) K) := by
    have : (A : Matrix (Fin 2) (Fin 2) K) = (c : Matrix (Fin 2) (Fin 2) K) * B := by
      rw [hB, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    rw [this, hr, scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hr0 : r ≠ 0 := by
    intro h0
    have hu := Matrix.GeneralLinearGroup.det A |>.ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply, hAc, h0, zero_smul, det_zero] at hu
    exact hu rfl
  refine ⟨Units.mk0 r hr0, c, hAc, ⟨Units.mk0 r hr0, ?_⟩, ?_⟩
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hAc, det_smul, c.2, Fintype.card_fin,
      Units.val_mul, Units.val_mk0, mul_one, sq]
  · ext q
    induction q using QuotientGroup.induction_on with
    | H X =>
      rw [pslConjAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      rw [coe_slConjAut, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      have hinv : ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          r⁻¹ • ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
        rw [Matrix.coe_units_inv, hAc]
        refine Matrix.inv_eq_left_inv ?_
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hr0, one_smul,
          ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      rw [hinv, hAc]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hr0, one_smul]

end CFSG.QuasithinUnique
