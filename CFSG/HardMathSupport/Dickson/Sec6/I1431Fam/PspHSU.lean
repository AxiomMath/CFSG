module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PspHGL

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSU StatedScalars)
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff)
open scoped commutatorElement

theorem t6psph_not_isTypeL2_sesqSU (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {ℓ f : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData ℓ f E) {W : Type} [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) (hm : 3 ≤ Module.finrank E W)
    (hnq : (Module.finrank E W, ℓ ^ f) ≠ (3, 2)) {r : ℕ} (hr : 10 ≤ r) :
    ¬ IsTypeL2 r (sesqSpecialUnitaryGroup Hf) := by
  intro hT
  have hfin := hE.finite
  have : Fact ℓ.Prime := ⟨hE.prime⟩
  have hF : Nat.card E = (ℓ ^ f) ^ 2 := hE.card_eq_sq
  obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
  obtain ⟨φ⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
    (G := (1 : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E))
    (fun i j => by rw [hb i j, Matrix.one_apply])
  let e3 : sesqSpecialUnitaryGroup Hf ≃* StatedSU (Module.finrank E W) (ℓ ^ f) E :=
    φ.trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)
  obtain ⟨hQ, hZc⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF hm hnq
  have h1 : IsTypeL2 r (StatedSU (Module.finrank E W) (ℓ ^ f) E) := p6_isTypeL2_of_equiv e3 hT
  have h2 : IsTypeL2 r (StatedProj (StatedSU (Module.finrank E W) (ℓ ^ f) E)) :=
    (isTypeL2_congr_of_central hQ.1 (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact hZc.ge)).1 h1
  have hadm : StatedLieAdmissible .PSU (Module.finrank E W) ℓ f :=
    ⟨hE.prime, hE.one_le, hm, hnq⟩
  have hmodel : LieModel (StatedProj (StatedSU (Module.finrank E W) (ℓ ^ f) E)) .PSU
      (Module.finrank E W) ℓ f :=
    (lieModel_classical_iff (by decide)).mpr ⟨hadm, E, inferInstance, inferInstance, hF,
      ⟨MulEquiv.refl _⟩⟩
  have hZ : Subgroup.center (StatedProj (StatedSU (Module.finrank E W) (ℓ ^ f) E)) = ⊥ := by
    let e := QuotientGroup.quotientMulEquivOfEq hZc
    haveI : IsSimpleGroup (StatedSU (Module.finrank E W) (ℓ ^ f) E ⧸
        Subgroup.center (StatedSU (Module.finrank E W) (ℓ ^ f) E)) := hQ.2.1
    have hc := center_eq_bot_of_simple hQ.2.2
    rw [← Subgroup.map_center_eq e, hc, Subgroup.map_bot]
  exact not_typeL2_of_lieModel hO hadm hmodel (by decide) (by simp) hZ hr h2

theorem t6psph_scalarGL_mem_sesqUnitaryGroup {ℓ f : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ f E) {W : Type} [AddCommGroup W] [Module E W]
    {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} {d : Eˣ} (hd : hE.norm (d : E) = 1) :
    t6psph_scalarGL (E := E) (W := W) d ∈ sesqUnitaryGroup Hf := by
  rw [mem_sesqUnitaryGroup]
  intro x y
  have h1 : ((t6psph_scalarGL (E := E) (W := W) d : LinearMap.GeneralLinearGroup E W) :
      W →ₗ[E] W) x = (d : E) • x := rfl
  have h2 : ((t6psph_scalarGL (E := E) (W := W) d : LinearMap.GeneralLinearGroup E W) :
      W →ₗ[E] W) y = (d : E) • y := rfl
  have e1 : Hf ((d : E) • x) = hE.bar (d : E) • Hf x := map_smulₛₗ Hf (d : E) x
  rw [h1, h2, e1, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul]
  have : hE.bar (d : E) * ((d : E) * Hf x y) = hE.norm (d : E) * Hf x y := by
    rw [UnitaryFieldData.norm]
    ring
  rw [this, hd, one_mul]

theorem t6psph_sqOK_sesqUnitary (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {ℓ f : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData ℓ f E) {W : Type} [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) {q : ℕ} (hq : 10 ≤ q) : t6psph_SqOK q ↥(sesqUnitaryGroup Hf) := by
  have hfin := hE.finite
  haveI := t6psph_finite_generalLinearGroup (E := E) (W := W)
  have hq2 : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := hE.one_le; omega : f ≠ 0) hE.prime.one_lt
    omega
  by_cases hm : 2 ≤ Module.finrank E W
  · obtain ⟨hcard, hSUcard, hrange, -, hker, -⟩ :=
      CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl (by omega : 1 ≤ Module.finrank E W)
    set D : ↥(sesqUnitaryGroup Hf) →* Eˣ := CFSG.LinearGroups.unitaryDet Hf with hD
    by_cases hQ : (Module.finrank E W = 2 → 4 ≤ ℓ ^ f) ∧ (Module.finrank E W = 3 → 3 ≤ ℓ ^ f)
    · have hSU : CFSG.IsQuasisimple (sesqSpecialUnitaryGroup Hf) :=
        isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl hm hQ
      have hkerq : CFSG.IsQuasisimple ↥D.ker := by
        rw [hD, hker]
        exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm hSU
      have hcomm : commutator ↥(sesqUnitaryGroup Hf) = D.ker := t6psph_commutator_eq_ker D hkerq.1
      intro hQ' hT g
      by_cases hm3 : 3 ≤ Module.finrank E W
      · exfalso
        have hnq : (Module.finrank E W, ℓ ^ f) ≠ (3, 2) := by
          intro h
          have h1 := congrArg Prod.snd h
          have h2 := congrArg Prod.fst h
          simp only at h1 h2
          have := hQ.2 h2
          omega
        rw [hcomm, hD, hker] at hT
        exact t6psph_not_isTypeL2_sesqSU hO hE hHf hHfl hm3 hnq hq
          (p6_isTypeL2_of_equiv (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)) hT)
      · have hm2 : Module.finrank E W = 2 := by omega
        rw [hcomm]
        refine t6psph_sq_of_scalar D (fun g => ?_) g
        have hnorm : hE.norm ((D g : Eˣ) : E) = 1 := (hrange (D g)).mp ⟨g, rfl⟩
        refine ⟨⟨t6psph_scalarGL (D g), t6psph_scalarGL_mem_sesqUnitaryGroup hE hnorm⟩, ?_, ?_⟩
        · rw [Subgroup.mem_center_iff]
          intro h
          exact Subtype.ext
            ((Subgroup.mem_center_iff.mp (t6psph_scalarGL_central (E := E) (W := W) (D g))) h)
        · have h3 := t6psph_det_scalarGL (E := E) (W := W) (D g)
          rw [hm2] at h3
          exact h3
    ·
      refine t6psph_sqOK_of_card_lt hq ?_
      have hexc : (Module.finrank E W = 2 ∧ ℓ ^ f = 2) ∨ (Module.finrank E W = 2 ∧ ℓ ^ f = 3) ∨
          (Module.finrank E W = 3 ∧ ℓ ^ f = 2) := by
        by_contra hn
        push Not at hn
        obtain ⟨h1, h2, h3⟩ := hn
        refine hQ ⟨fun h2' => ?_, fun h3' => ?_⟩
        · by_contra hlt
          rcases (show ℓ ^ f = 2 ∨ ℓ ^ f = 3 by omega) with hQ' | hQ'
          · exact h1 h2' hQ'
          · exact h2 h2' hQ'
        · by_contra hlt
          exact h3 h3' (by omega)
      have hle : commutator ↥(sesqUnitaryGroup Hf) ≤ D.ker := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
      have hkerfin : Finite ↥D.ker := inferInstance
      have h1 : Nat.card ↥(commutator ↥(sesqUnitaryGroup Hf)) ≤ Nat.card ↥D.ker :=
        Subgroup.card_le_of_le hle
      have h2 : Nat.card ↥D.ker = Nat.card ↥(sesqSpecialUnitaryGroup Hf) := by
        rw [hD, hker]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).toEquiv
      have hsq : Nat.card ↥(sesqSpecialUnitaryGroup Hf) < 495 := by
        rcases hexc with ⟨hm2, hQ⟩ | ⟨hm2, hQ⟩ | ⟨hm3, hQ⟩
        · rw [hm2, hQ] at hSUcard
          have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
              ∏ i ∈ Finset.Icc 2 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 6 := by
            norm_num [Finset.Icc_self]
          have h6 : Nat.card ↥(sesqSpecialUnitaryGroup Hf) = 6 := by
            exact_mod_cast hSUcard.trans e
          omega
        · rw [hm2, hQ] at hSUcard
          have e : ((3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
              ∏ i ∈ Finset.Icc 2 2, (((3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 24 := by
            norm_num [Finset.Icc_self]
          have h24 : Nat.card ↥(sesqSpecialUnitaryGroup Hf) = 24 := by
            exact_mod_cast hSUcard.trans e
          omega
        · rw [hm3, hQ] at hSUcard
          have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
              ∏ i ∈ Finset.Icc 2 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 216 := by
            rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
            norm_num
          have h216 : Nat.card ↥(sesqSpecialUnitaryGroup Hf) = 216 := by
            exact_mod_cast hSUcard.trans e
          omega
      omega
  · refine t6psph_sqOK_of_commutative hq fun a b => Subtype.ext (Units.ext ?_)
    have := (End_commute_of_finrank_le_one (E := E) (W := W) (by omega)
      ((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)
      ((b : LinearMap.GeneralLinearGroup E W) : Module.End E W)).eq
    simpa [Subgroup.coe_mul, Units.val_mul] using this

end CFSG.HardMathSupport.Dickson.Sec6.I1431
