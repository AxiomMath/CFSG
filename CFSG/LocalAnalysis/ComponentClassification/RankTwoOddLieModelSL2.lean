module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModelDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieSL2Facts

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b CFSG.ClassicalInvolution
  CFSG.ABGLocalTools
open scoped MatrixGroups commutatorElement

variable {F : Type*} [Field F]

@[expose] def qI : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

@[expose] def qJ {a b : F} (hab : a ^ 2 + b ^ 2 = -1) : SL(2, F) :=
  ⟨!![a, b; b, -a], by simp [Matrix.det_fin_two]; linear_combination -hab⟩

theorem qI_coe : ((qI : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem qJ_coe {a b : F} (hab : a ^ 2 + b ^ 2 = -1) :
    ((qJ hab : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![a, b; b, -a] := rfl

theorem qI_sq : (qI : SL(2, F)) ^ 2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, qI_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem qJ_sq {a b : F} (hab : a ^ 2 + b ^ 2 = -1) : qJ hab ^ 2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, qJ_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination hab | ring1

theorem qJ_mul_qI {a b : F} (hab : a ^ 2 + b ^ 2 = -1) :
    qJ hab * qI = (qI : SL(2, F)) ^ 3 * qJ hab := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, qI_coe, qJ_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem qI_pow_four : (qI : SL(2, F)) ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, qI_sq, neg_one_sq]

theorem commutator_qI_qJ {a b : F} (hab : a ^ 2 + b ^ 2 = -1) :
    ⁅(qI : SL(2, F)), qJ hab⁆ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutatorElement_def, qI_coe, qJ_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] <;>
    first | linear_combination hab | linear_combination -hab | ring1

theorem eq_one_or_neg_one_of_commute (h2 : (2 : F) ≠ 0) {a b : F} (hab : a ^ 2 + b ^ 2 = -1)
    {x : SL(2, F)} (hxi : x * qI = qI * x) (hxj : x * qJ hab = qJ hab * x) : x = 1 ∨ x = -1 := by
  have hI := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hxi
  have hJ := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hxj
  simp only [Matrix.SpecialLinearGroup.coe_mul, qI_coe, qJ_coe] at hI hJ
  have e00 := congrFun (congrFun hI 0) 0
  have e01 := congrFun (congrFun hI 0) 1
  have e10 := congrFun (congrFun hI 1) 0
  have f00 := congrFun (congrFun hJ 0) 0
  have f01 := congrFun (congrFun hJ 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 f00 f01
  set A := (x : Matrix (Fin 2) (Fin 2) F)
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := x.2
    rwa [Matrix.det_fin_two] at this
  have hb1 : b * A 0 1 = 0 := by
    have : 2 * (b * A 0 1) = 0 := by linear_combination f00 - b * e00
    exact (mul_eq_zero.mp this).resolve_left h2
  have ha1 : a * A 0 1 = 0 := by
    have : 2 * (a * A 0 1) = 0 := by linear_combination -f01 + b * e01
    exact (mul_eq_zero.mp this).resolve_left h2
  have hA01 : A 0 1 = 0 := by
    have h0 : (a ^ 2 + b ^ 2) * A 0 1 = 0 := by linear_combination a * ha1 + b * hb1
    rw [hab, neg_one_mul, neg_eq_zero] at h0
    exact h0
  have hA10 : A 1 0 = 0 := by linear_combination -e00 - hA01
  have hA11 : A 1 1 = A 0 0 := by linear_combination -e01
  have hsq : A 0 0 ^ 2 = 1 := by
    rw [hA01, hA10, hA11] at hdet
    linear_combination hdet
  rcases mul_self_eq_one_iff.mp (by rw [← sq]; exact hsq : A 0 0 * A 0 0 = 1) with h1 | h1
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A] at * <;> simp_all
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A] at * <;> simp_all

theorem qI_mul_qJ {a b : F} (hab : a ^ 2 + b ^ 2 = -1) :
    (qI : SL(2, F)) * qJ hab = qJ hab * qI ^ 3 := by
  have h := congrArg (fun x => qI * x * qI ^ 3) (qJ_mul_qI hab)
  rw [show (qI : SL(2, F)) * (qJ hab * qI) * qI ^ 3 = qI * qJ hab * qI ^ 4 by group,
    show (qI : SL(2, F)) * (qI ^ 3 * qJ hab) * qI ^ 3 = qI ^ 4 * qJ hab * qI ^ 3 by group,
    qI_pow_four, mul_one, one_mul] at h
  exact h

theorem qI_pow_mul_qJ {a b : F} (hab : a ^ 2 + b ^ 2 = -1) (m : ℕ) :
    (qI : SL(2, F)) ^ m * qJ hab = qJ hab * qI ^ (3 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_assoc, qI_mul_qJ hab, ← mul_assoc, ih, mul_assoc, ← pow_add]
    ring_nf

theorem qI_pow_eq_of_cast_eq {m n : ℕ} (h : (m : ZMod 4) = n) :
    (qI : SL(2, F)) ^ m = qI ^ n := by
  rw [pow_eq_pow_mod m qI_pow_four, pow_eq_pow_mod n qI_pow_four,
    (ZMod.natCast_eq_natCast_iff' m n 4).mp h]

@[expose] def quatFun {a b : F} (hab : a ^ 2 + b ^ 2 = -1) : QuaternionGroup 2 → SL(2, F)
  | .a k => qI ^ k.val
  | .xa k => qJ hab * qI ^ k.val

@[expose] def quatHom {a b : F} (hab : a ^ 2 + b ^ 2 = -1) : QuaternionGroup 2 →* SL(2, F) where
  toFun := quatFun hab
  map_one' := by
    rw [QuaternionGroup.one_def]
    simp [quatFun]
  map_mul' := by
    have hc : ∀ k : ZMod (2 * 2), ((k.val : ℕ) : ZMod 4) = k := fun k => ZMod.natCast_zmod_val k
    rintro (i | i) (j | j)
    · rw [QuaternionGroup.a_mul_a]
      simp only [quatFun]
      rw [← pow_add]
      exact qI_pow_eq_of_cast_eq (by push_cast; rw [hc, hc, hc])
    · rw [QuaternionGroup.a_mul_xa]
      simp only [quatFun]
      rw [← mul_assoc, qI_pow_mul_qJ hab, mul_assoc, ← pow_add]
      congr 1
      refine qI_pow_eq_of_cast_eq ?_
      push_cast
      rw [hc, hc, hc]
      have h4 : (4 : ZMod (2 * 2)) = 0 := rfl
      first | linear_combination i * h4 | linear_combination -i * h4
    · rw [QuaternionGroup.xa_mul_a]
      simp only [quatFun]
      rw [mul_assoc, ← pow_add]
      congr 1
      exact qI_pow_eq_of_cast_eq (by push_cast; rw [hc, hc, hc])
    · rw [QuaternionGroup.xa_mul_xa]
      simp only [quatFun]
      rw [show qJ hab * qI ^ i.val * (qJ hab * qI ^ j.val) =
          qJ hab * (qI ^ i.val * qJ hab) * qI ^ j.val by group, qI_pow_mul_qJ hab,
        show qJ hab * (qJ hab * qI ^ (3 * i.val)) * qI ^ j.val =
          qJ hab ^ 2 * (qI ^ (3 * i.val) * qI ^ j.val) by rw [sq]; simp only [mul_assoc],
        qJ_sq hab, ← qI_sq, ← pow_add, ← pow_add]
      refine qI_pow_eq_of_cast_eq ?_
      push_cast
      rw [hc, hc, hc]
      have h4 : (4 : ZMod (2 * 2)) = 0 := rfl
      first | linear_combination i * h4 | linear_combination -i * h4

theorem quatHom_a_one {a b : F} (hab : a ^ 2 + b ^ 2 = -1) :
    quatHom hab (.a 1) = qI := by
  show qI ^ (1 : ZMod (2 * 2)).val = qI
  rw [show (1 : ZMod (2 * 2)).val = 1 from rfl, pow_one]

theorem quatHom_xa_zero {a b : F} (hab : a ^ 2 + b ^ 2 = -1) :
    quatHom hab (.xa 0) = qJ hab := by
  show qJ hab * qI ^ (0 : ZMod (2 * 2)).val = qJ hab
  rw [ZMod.val_zero, pow_zero, mul_one]

theorem isPGroup_range_quatHom {a b : F} (hab : a ^ 2 + b ^ 2 = -1) :
    IsPGroup 2 (quatHom hab).range := by
  have h8 : Nat.card (QuaternionGroup 2) = 2 ^ 3 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hQ : IsPGroup 2 (QuaternionGroup 2) := IsPGroup.of_card h8
  rw [MonoidHom.range_eq_map]
  exact hQ.to_subgroup ⊤ |>.map _

theorem exists_sq_add_sq_eq_neg_one [Finite F] : ∃ a b : F, a ^ 2 + b ^ 2 = -1 := by
  have : NeZero (ringChar F) := ⟨CharP.char_ne_zero_of_finite F (ringChar F)⟩
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq F (ringChar F) (-1)
  exact ⟨a, b, by exact_mod_cast hab⟩

section Pair

variable {H : Type*} [Group H]

theorem exists_quaternion_pair [Finite F] (hF : Odd (Nat.card F)) {J : Subgroup H}
    (e : J ≃* SL(2, F)) {Q : Subgroup H} (hQ : IsSylowOf 2 Q J) :
    ∃ i ∈ Q, ∃ j ∈ Q, ⁅i, j⁆ = centralInv e ∧
      ∀ y ∈ J, y * i = i * y → y * j = j * y → y ∈ centralizer (J : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite J := Finite.of_equiv _ e.symm.toEquiv
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd hF)
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_eq_neg_one (F := F)
  set P₀ : Subgroup J := (quatHom hab).range.map e.symm.toMonoidHom
  have hP₀ : IsPGroup 2 P₀ := (isPGroup_range_quatHom hab).map _
  obtain ⟨Qs, hQs⟩ := hQ
  obtain ⟨S₀, hS₀⟩ := hP₀.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq J S₀ Qs
  set i₀ : J := e.symm qI
  set j₀ : J := e.symm (qJ hab)
  have hi₀ : i₀ ∈ P₀ := ⟨qI, ⟨.a 1, quatHom_a_one hab⟩, rfl⟩
  have hj₀ : j₀ ∈ P₀ := ⟨qJ hab, ⟨.xa 0, quatHom_xa_zero hab⟩, rfl⟩
  have hmem : ∀ x ∈ P₀, c * x * c⁻¹ ∈ (Qs : Subgroup J) := by
    intro x hx
    rw [← hc, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul x (MulAut.conj c) (S₀ : Subgroup J) (hS₀ hx)
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hz : ∀ g : J, g * e.symm (-1) * g⁻¹ = e.symm (-1) := fun g => by
    have h : e.symm (-1) ∈ center J := by
      rw [mem_center_iff_of_equiv_sl2 e, MulEquiv.apply_symm_apply, mem_center_sl2_iff]
      exact Or.inr rfl
    rw [Subgroup.mem_center_iff.mp h g, mul_inv_cancel_right]
  refine ⟨((c * i₀ * c⁻¹ : J) : H), ?_, ((c * j₀ * c⁻¹ : J) : H), ?_, ?_, ?_⟩
  · rw [← hQs]
    exact mem_map_of_mem _ (hmem _ hi₀)
  · rw [← hQs]
    exact mem_map_of_mem _ (hmem _ hj₀)
  · have h1 : ⁅c * i₀ * c⁻¹, c * j₀ * c⁻¹⁆ = e.symm (-1) := by
      rw [show ⁅c * i₀ * c⁻¹, c * j₀ * c⁻¹⁆ = c * ⁅i₀, j₀⁆ * c⁻¹ by
        simp only [commutatorElement_def]; group]
      rw [show ⁅i₀, j₀⁆ = e.symm ⁅qI, qJ hab⁆ from (map_commutatorElement e.symm _ _).symm,
        commutator_qI_qJ, hz]
    have h2 := congrArg Subtype.val h1
    rw [show ((⁅c * i₀ * c⁻¹, c * j₀ * c⁻¹⁆ : J) : H) =
      ⁅((c * i₀ * c⁻¹ : J) : H), ((c * j₀ * c⁻¹ : J) : H)⁆ from
        map_commutatorElement J.subtype _ _] at h2
    exact h2
  · intro y hy hyi hyj
    set y' : J := c⁻¹ * ⟨y, hy⟩ * c
    have hyi' : ⟨y, hy⟩ * (c * i₀ * c⁻¹) = (c * i₀ * c⁻¹) * ⟨y, hy⟩ := Subtype.ext hyi
    have hyj' : ⟨y, hy⟩ * (c * j₀ * c⁻¹) = (c * j₀ * c⁻¹) * ⟨y, hy⟩ := Subtype.ext hyj
    have hi : y' * i₀ = i₀ * y' := by
      calc y' * i₀ = c⁻¹ * (⟨y, hy⟩ * (c * i₀ * c⁻¹)) * c := by simp only [y']; group
        _ = c⁻¹ * ((c * i₀ * c⁻¹) * ⟨y, hy⟩) * c := by rw [hyi']
        _ = i₀ * y' := by simp only [y']; group
    have hj : y' * j₀ = j₀ * y' := by
      calc y' * j₀ = c⁻¹ * (⟨y, hy⟩ * (c * j₀ * c⁻¹)) * c := by simp only [y']; group
        _ = c⁻¹ * ((c * j₀ * c⁻¹) * ⟨y, hy⟩) * c := by rw [hyj']
        _ = j₀ * y' := by simp only [y']; group
    have hei : e y' * qI = qI * e y' := by
      have h1 : e (y' * i₀) = e (i₀ * y') := congrArg e hi
      rw [map_mul e y' i₀, map_mul e i₀ y'] at h1
      simpa [i₀] using h1
    have hej : e y' * qJ hab = qJ hab * e y' := by
      have h1 : e (y' * j₀) = e (j₀ * y') := congrArg e hj
      rw [map_mul e y' j₀, map_mul e j₀ y'] at h1
      simpa [j₀] using h1
    have hy'c : y' ∈ center J := by
      rw [mem_center_iff_of_equiv_sl2 e, mem_center_sl2_iff]
      exact eq_one_or_neg_one_of_commute h2F hab hei hej
    have hyc : (⟨y, hy⟩ : J) ∈ center J := by
      have : (⟨y, hy⟩ : J) = c * y' * c⁻¹ := by simp only [y']; group
      rw [this]
      exact (inferInstance : (center J).Normal).conj_mem _ hy'c c
    rw [mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hyc) ⟨g, hg⟩)

end Pair

@[expose] def mulAutCongr {J S : Type*} [Group J] [Group S] (e : J ≃* S) :
    MulAut J →* MulAut S where
  toFun γ := e.symm.trans (γ.trans e)
  map_one' := by
    ext x
    simp
  map_mul' γ δ := by
    ext x
    simp

theorem mulAutCongr_apply {J S : Type*} [Group J] [Group S] (e : J ≃* S) (γ : MulAut J) (x : J) :
    mulAutCongr e γ (e x) = e (γ x) := by
  simp [mulAutCongr]

theorem commutator_mem_centralizer_of_sl2 (h3 : SL2OuterComm) {H : Type*} [Group H] {F : Type}
    [Field F] [Finite F] (hF : Odd (Nat.card F)) {J : Subgroup H} (e : J ≃* SL(2, F)) {i j : H}
    (hiJ : i ∈ J) (hjJ : j ∈ J)
    (hC : ∀ y ∈ J, y * i = i * y → y * j = j * y → y ∈ centralizer (J : Set H)) {a b : H}
    (ha : a ∈ normalizer (J : Set H)) (hb : b ∈ normalizer (J : Set H)) (hai : a * i = i * a)
    (haj : a * j = j * a) (hbi : b * i = i * b) (hbj : b * j = j * b) :
    ⁅a, b⁆ ∈ centralizer (J : Set H) := by
  set ρ := J.normalizerMonoidHom
  have hρ : ∀ (g : normalizer (J : Set H)) (x : J), ((ρ g x : J) : H) = g * x * g⁻¹ :=
    fun g x => rfl
  set α := ρ ⟨a, ha⟩
  set β := ρ ⟨b, hb⟩
  obtain ⟨y', hy'⟩ := h3 F hF (mulAutCongr e α) (mulAutCongr e β)
  set y : J := e.symm y'
  have hcomm : ∀ x : J, (α * β * α⁻¹ * β⁻¹) x = y * x * y⁻¹ := by
    intro x
    apply e.injective
    rw [← mulAutCongr_apply, map_mul, map_mul, map_mul, map_inv, map_inv, hy',
      MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hfix : ∀ (g : normalizer (J : Set H)), (g : H) * i = i * g → (g : H) * j = j * g →
      ρ g ⟨i, hiJ⟩ = ⟨i, hiJ⟩ ∧ ρ g ⟨j, hjJ⟩ = ⟨j, hjJ⟩ := fun g hgi hgj =>
    ⟨Subtype.ext (by rw [hρ, Subgroup.coe_inv, hgi, mul_inv_cancel_right]),
      Subtype.ext (by rw [hρ, Subgroup.coe_inv, hgj, mul_inv_cancel_right])⟩
  have hai' : α ⟨i, hiJ⟩ = ⟨i, hiJ⟩ := (hfix ⟨a, ha⟩ hai haj).1
  have haj' : α ⟨j, hjJ⟩ = ⟨j, hjJ⟩ := (hfix ⟨a, ha⟩ hai haj).2
  have hbi' : β ⟨i, hiJ⟩ = ⟨i, hiJ⟩ := (hfix ⟨b, hb⟩ hbi hbj).1
  have hbj' : β ⟨j, hjJ⟩ = ⟨j, hjJ⟩ := (hfix ⟨b, hb⟩ hbi hbj).2
  have hinvfix : ∀ (γ : MulAut J) (x : J), γ x = x → γ⁻¹ x = x := fun γ x h => by
    rw [← h, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply, h]
  have hci : (α * β * α⁻¹ * β⁻¹) ⟨i, hiJ⟩ = ⟨i, hiJ⟩ := by
    simp only [MulAut.mul_apply, hinvfix β _ hbi', hinvfix α _ hai', hbi', hai']
  have hcj : (α * β * α⁻¹ * β⁻¹) ⟨j, hjJ⟩ = ⟨j, hjJ⟩ := by
    simp only [MulAut.mul_apply, hinvfix β _ hbj', hinvfix α _ haj', hbj', haj']
  rw [hcomm] at hci hcj
  have hyi : (y : H) * i = i * y := by
    have := congrArg Subtype.val hci
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    calc (y : H) * i = ((y : H) * i * (y : H)⁻¹) * y := by group
      _ = i * y := by rw [this]
  have hyj : (y : H) * j = j * y := by
    have := congrArg Subtype.val hcj
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    calc (y : H) * j = ((y : H) * j * (y : H)⁻¹) * y := by group
      _ = j * y := by rw [this]
  have hyC := hC y y.2 hyi hyj
  set na : normalizer (J : Set H) := ⟨a, ha⟩
  set nb : normalizer (J : Set H) := ⟨b, hb⟩
  have hρab : ρ ⁅na, nb⁆ = α * β * α⁻¹ * β⁻¹ := by
    rw [map_commutatorElement, commutatorElement_def]
  rw [mem_centralizer_iff]
  intro x hx
  have h1 := congrArg Subtype.val (hcomm ⟨x, hx⟩)
  rw [← hρab, hρ] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  have hyx : (y : H) * x * (y : H)⁻¹ = x := by
    rw [(mem_centralizer_iff.mp hyC x hx).symm, mul_inv_cancel_right]
  rw [hyx] at h1
  have h1' : ⁅a, b⁆ * x * ⁅a, b⁆⁻¹ = x := by
    have e1 : ((⁅na, nb⁆ : normalizer (J : Set H)) : H) = ⁅a, b⁆ :=
      map_commutatorElement (normalizer (J : Set H)).subtype na nb
    rw [← e1]
    exact h1
  calc x * ⁅a, b⁆ = (⁅a, b⁆ * x * ⁅a, b⁆⁻¹) * ⁅a, b⁆ := by rw [h1']
    _ = ⁅a, b⁆ * x := by group

end CFSG.ComponentClassification.RankTwoOddLie
