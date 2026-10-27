module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLc
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabOrd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L4Center

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] noncomputable def kG {l : F} (hl : l ≠ 0) : GL (Fin 4) F :=
  GeneralLinearGroup.mkOfDetNeZero (kZero l) (by rw [det_kZero]; exact pow_ne_zero 2 hl)

theorem coe_kG {l : F} (hl : l ≠ 0) : ((kG hl : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
    kZero l := GeneralLinearGroup.val_mkOfDetNeZero _ _

variable (F) in
@[expose] noncomputable def CK {l : F} (hl : l ≠ 0) : Subgroup (SpecialLinearGroup (Fin 4) F) :=
  (Subgroup.centralizer {kG hl}).comap SpecialLinearGroup.toGL

variable (F) in
@[expose] noncomputable def SK {l : F} (hl : l ≠ 0) : Subgroup (SpecialLinearGroup (Fin 4) F) :=
  ⁅CK F hl, CK F hl⁆

variable (F) in
@[expose] noncomputable def JK {l : F} (hl : l ≠ 0) : Subgroup (projectiveSL 4 F) :=
  (SK F hl).map (proj 4 F)

theorem mem_CK_iff {l : F} (hl : l ≠ 0) {x : SpecialLinearGroup (Fin 4) F} :
    x ∈ CK F hl ↔ (x : Matrix (Fin 4) (Fin 4) F) * kZero l = kZero l * x := by
  rw [CK, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg (fun A : GL (Fin 4) F => (A : Matrix (Fin 4) (Fin 4) F)) h
    simpa [coe_kG] using this
  · intro h
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_kG]
    exact h

@[expose] def slUK (l a b : F) : SpecialLinearGroup (Fin 4) F := ⟨uK l a b, det_uK l a b⟩

@[expose] def slLK (l a b : F) : SpecialLinearGroup (Fin 4) F := ⟨lK l a b, det_lK l a b⟩

@[expose] noncomputable def slHK {l : F} (hl : l ≠ 0) : SpecialLinearGroup (Fin 4) F :=
  ⟨hK l, det_hK hl⟩

theorem coe_inv_eq' {x : SpecialLinearGroup (Fin 4) F} {M : Matrix (Fin 4) (Fin 4) F}
    (h : (x : Matrix (Fin 4) (Fin 4) F) * M = 1) :
    ((x⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = M :=
  StabL.coe_inv_eq h

theorem coe_slHK_inv {l : F} (hl : l ≠ 0) :
    ((slHK hl)⁻¹ : SpecialLinearGroup (Fin 4) F) = (hKinv l : Matrix (Fin 4) (Fin 4) F) :=
  coe_inv_eq' (hK_mul_hKinv hl)

theorem coe_slUK_inv (l a b : F) :
    (((slUK l a b)⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      uK l (-a) (-b) :=
  coe_inv_eq' (by
    change uK l a b * uK l (-a) (-b) = 1
    rw [uK_mul_uK, add_neg_cancel, add_neg_cancel, uK_zero])

theorem coe_slLK_inv (l a b : F) :
    (((slLK l a b)⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      lK l (-a) (-b) :=
  coe_inv_eq' (by
    change lK l a b * lK l (-a) (-b) = 1
    rw [lK_mul_lK, add_neg_cancel, add_neg_cancel, lK_zero])

theorem slUK_mem_CK {l : F} (hl : l ≠ 0) (a b : F) : slUK l a b ∈ CK F hl :=
  (mem_CK_iff hl).2 (uK_comm l a b)

theorem slLK_mem_CK {l : F} (hl : l ≠ 0) (a b : F) : slLK l a b ∈ CK F hl :=
  (mem_CK_iff hl).2 (lK_comm l a b)

theorem slHK_mem_CK {l : F} (hl : l ≠ 0) : slHK hl ∈ CK F hl :=
  (mem_CK_iff hl).2 (hK_comm hl)

theorem slUK_mem_SK {l : F} (hl : l ≠ 0) (hl1 : l ≠ 1) (a b : F) : slUK l a b ∈ SK F hl := by
  have hm : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  have h : ⁅slHK hl, slUK l (a / (l - 1)) (b / (l - 1))⁆ = slUK l a b := by
    apply Subtype.ext
    rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, coe_slHK_inv hl, coe_slUK_inv]
    change hK l * uK l (a / (l - 1)) (b / (l - 1)) * hKinv l *
      uK l (-(a / (l - 1))) (-(b / (l - 1))) = uK l a b
    rw [hK_conj_uK hl, uK_mul_uK]
    congr 1 <;> field_simp <;> ring
  rw [← h]
  exact Subgroup.commutator_mem_commutator (slHK_mem_CK hl) (slUK_mem_CK hl _ _)

theorem slLK_mem_SK {l : F} (hl : l ≠ 0) (hl1 : l ≠ 1) (a b : F) : slLK l a b ∈ SK F hl := by
  have hm : l⁻¹ - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hl1 (by rw [← inv_inv l, h, inv_one])
  have h : ⁅slHK hl, slLK l (a / (l⁻¹ - 1)) (b / (l⁻¹ - 1))⁆ = slLK l a b := by
    apply Subtype.ext
    rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, coe_slHK_inv hl, coe_slLK_inv]
    change hK l * lK l (a / (l⁻¹ - 1)) (b / (l⁻¹ - 1)) * hKinv l *
      lK l (-(a / (l⁻¹ - 1))) (-(b / (l⁻¹ - 1))) = lK l a b
    rw [hK_conj_lK hl, lK_mul_lK]
    congr 1 <;> field_simp <;> ring
  rw [← h]
  exact Subgroup.commutator_mem_commutator (slHK_mem_CK hl) (slLK_mem_CK hl _ _)

theorem neg_one_mem_SK {l : F} (hl : l ≠ 0) (hl1 : l ≠ 1) :
    (-1 : SpecialLinearGroup (Fin 4) F) ∈ SK F hl := by
  set w : SpecialLinearGroup (Fin 4) F := slUK l 1 0 * slLK l (-1) 0 * slUK l 1 0 with hw
  have hwS : w ∈ SK F hl := mul_mem (mul_mem (slUK_mem_SK hl hl1 1 0)
    (slLK_mem_SK hl hl1 (-1) 0)) (slUK_mem_SK hl hl1 1 0)
  have hw2 : w * w = -1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hw, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    change (uK l 1 0 * lK l (-1) 0 * uK l 1 0) * (uK l 1 0 * lK l (-1) 0 * uK l 1 0) = -1
    rw [← wK_eq, wK_mul_wK]
  rw [← hw2]
  exact mul_mem hwS hwS

theorem mem_center_of_conjAut_fix (A : GL (Fin 4) F) {Z : SpecialLinearGroup (Fin 4) F}
    (hZ : conjAut 4 F A (proj 4 F Z) = proj 4 F Z) :
    SpecialLinearGroup.toGL Z * A * (SpecialLinearGroup.toGL Z)⁻¹ * A⁻¹ ∈
      Subgroup.center (GL (Fin 4) F) := by
  rw [conjAut_proj] at hZ
  have h1 : CatalogueBHigherLinearAction.slConjugation 4 F A Z * Z⁻¹ ∈ scalars 4 F := by
    rw [← proj_eq_one_iff, map_mul, hZ, map_inv, mul_inv_cancel]
  obtain ⟨c, -, hc⟩ := mem_scalars.1 h1
  have h2 : SpecialLinearGroup.toGL (CatalogueBHigherLinearAction.slConjugation 4 F A Z * Z⁻¹) =
      GeneralLinearGroup.scalar (Fin 4) c :=
    Units.ext (by rw [GeneralLinearGroup.coe_scalar, ← hc]; rfl)
  have h3 : SpecialLinearGroup.toGL Z * A * (SpecialLinearGroup.toGL Z)⁻¹ * A⁻¹ =
      (GeneralLinearGroup.scalar (Fin 4) c)⁻¹ := by
    rw [← h2, map_mul, CatalogueBHigherLinearAction.toGL_slConjugation, map_inv]
    group
  rw [h3, GeneralLinearGroup.center_eq_range_scalar]
  exact inv_mem ⟨c, rfl⟩

theorem commutator_mem_CK {l : F} (hl : l ≠ 0) {X Y : SpecialLinearGroup (Fin 4) F}
    (hX : conjAut 4 F (kG hl) (proj 4 F X) = proj 4 F X)
    (hY : conjAut 4 F (kG hl) (proj 4 F Y) = proj 4 F Y) : ⁅X, Y⁆ ∈ CK F hl := by
  rw [mem_CK_iff hl]
  have h := commutator_comm_of_comm_mod (le_refl (Subgroup.center (GL (Fin 4) F)))
    (mem_center_of_conjAut_fix _ hX) (mem_center_of_conjAut_fix _ hY)
  rw [← map_commutatorElement] at h
  have := congrArg (fun A : GL (Fin 4) F => (A : Matrix (Fin 4) (Fin 4) F)) h
  simp only [Units.val_mul, coe_kG] at this
  exact this

theorem le_JK {l : F} (hl : l ≠ 0) {J' : Subgroup (projectiveSL 4 F)}
    (hJk : ∀ x ∈ J', conjAut 4 F (kG hl) x = x) (hJp : ⁅J', J'⁆ = J') : J' ≤ JK F hl := by
  have hC : ⁅J', J'⁆ ≤ (CK F hl).map (proj 4 F) := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨X, rfl⟩ := proj_surjective 4 F u
    obtain ⟨Y, rfl⟩ := proj_surjective 4 F v
    exact ⟨⁅X, Y⁆, commutator_mem_CK hl (hJk _ hu) (hJk _ hv), by rw [map_commutatorElement]⟩
  have h1 : J' ≤ (CK F hl).map (proj 4 F) := by
    rw [← hJp]
    exact hC
  rw [JK, SK, Subgroup.map_commutator, ← hJp]
  exact Subgroup.commutator_mono h1 h1

theorem kG_sq {l : F} (hl : l ≠ 0) :
    kG hl ^ 2 = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 l hl) := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar, sq, coe_kG, kZero_mul_kZero,
    Units.val_mk0, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem card_SK_le [Fintype F] {l : F} (hl : l ≠ 0) (hns : ¬ IsSquare l) :
    Nat.card (SK F hl) ≤ Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) := by
  classical
  obtain ⟨E, _, _, ρ, hE, hρ⟩ :=
    StabL.exists_centralizer_embedding_card (kG hl) (Units.mk0 l hl) (kG_sq hl) (by simpa using hns)
  let ι : CK F hl →* Subgroup.centralizer {kG hl} :=
    (SpecialLinearGroup.toGL.comp (CK F hl).subtype).codRestrict _ fun x => x.2
  have hι : Function.Injective ι := fun a b hab => by
    apply Subtype.ext
    apply SpecialLinearGroup.toGL_injective
    exact congrArg Subtype.val hab
  set ψ : CK F hl →* Eˣ := GeneralLinearGroup.det.comp (ρ.comp ι) with hψ
  have hS : SK F hl ≤ ψ.ker.map (CK F hl).subtype := by
    rw [SK, Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : CK F hl), (⟨b, hb⟩ : CK F hl)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hSC : SK F hl ≤ CK F hl := Subgroup.commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  let f : SK F hl → SpecialLinearGroup (Fin 2) E := fun x =>
    ⟨(ρ (ι ⟨x, hSC x.2⟩) : Matrix (Fin 2) (Fin 2) E), by
      obtain ⟨y, hy, hyx⟩ := hS x.2
      have hy' : y = ⟨x, hSC x.2⟩ := Subtype.ext hyx
      rw [← hy']
      have := congrArg Units.val (MonoidHom.mem_ker.mp hy)
      rwa [hψ, MonoidHom.comp_apply, GeneralLinearGroup.val_det_apply, Units.val_one] at this⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ρ (ι ⟨x, hSC x.2⟩) = ρ (ι ⟨y, hSC y.2⟩) := Units.ext (congrArg Subtype.val hxy)
    have h2 := hι (hρ h1)
    exact Subtype.ext (congrArg (fun z : CK F hl => (z : SpecialLinearGroup (Fin 4) F)) h2)
  calc Nat.card (SK F hl) ≤ Nat.card (SpecialLinearGroup (Fin 2) E) :=
        Nat.card_le_card_of_injective f hf
    _ = Nat.card E * (Nat.card E ^ 2 - 1) := by
        let := Fintype.ofFinite E
        have hq : 1 < Fintype.card E := Fintype.one_lt_card
        rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
          Nat.card_eq_fintype_card, show Fintype.card E ^ 2 - Fintype.card E =
            Fintype.card E * (Fintype.card E - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
          Nat.mul_div_cancel _ (by omega), mul_comm]
    _ = Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) := by rw [hE]

theorem ne_one_of_not_isSquare {l : F} (hns : ¬ IsSquare l) : l ≠ 1 := by
  rintro rfl
  exact hns ⟨1, by rw [mul_one]⟩

theorem ne_zero_of_not_isSquare {l : F} (hns : ¬ IsSquare l) : l ≠ 0 := by
  rintro rfl
  exact hns ⟨0, by rw [mul_zero]⟩

theorem two_mul_card_JK_le [Fintype F] (h2 : (2 : F) ≠ 0) {l : F} (hl : l ≠ 0)
    (hns : ¬ IsSquare l) :
    2 * Nat.card (JK F hl) ≤ Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) := by
  classical
  have hl1 := ne_one_of_not_isSquare hns
  set φ : SK F hl →* projectiveSL 4 F := (proj 4 F).comp (SK F hl).subtype with hφ
  have hrange : φ.range = JK F hl := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype, JK]
  have hneg : (⟨-1, neg_one_mem_SK hl hl1⟩ : SK F hl) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, proj_eq_one_iff,
      mem_scalars]
    refine ⟨-1, by norm_num, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Units.val_neg,
      Units.val_one, map_neg, map_one]
  have hne : (⟨-1, neg_one_mem_SK hl hl1⟩ : SK F hl) ≠ 1 := by
    intro h
    have := congrFun (congrFun (congrArg (fun y : SK F hl =>
      ((y : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) h) 0) 0
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Subgroup.coe_one, Matrix.neg_apply, Matrix.one_apply_eq] at this
    apply h2
    linear_combination -this
  have hker : 2 ≤ Nat.card φ.ker := by
    have : 1 < Nat.card φ.ker := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hneg
      exact hne hneg
    omega
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hrange] at hmul
  calc 2 * Nat.card (JK F hl) ≤ Nat.card φ.ker * Nat.card (JK F hl) := Nat.mul_le_mul_right _ hker
    _ = Nat.card (SK F hl) := hmul
    _ ≤ _ := card_SK_le hl hns

theorem eq_JK [Fintype F] (h2 : (2 : F) ≠ 0) {l : F} (hl : l ≠ 0) (hns : ¬ IsSquare l)
    {J' : Subgroup (projectiveSL 4 F)} (hJk : ∀ x ∈ J', conjAut 4 F (kG hl) x = x)
    (hJp : ⁅J', J'⁆ = J') (hcard : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card J') :
    J' = JK F hl :=
  Subgroup.eq_of_le_of_card_ge (le_JK hl hJk hJp) (by
    have := two_mul_card_JK_le h2 hl hns
    omega)

end DiagL

end CFSG.ComponentClassification.CatFactsL4U4
