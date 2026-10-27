module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXKlMain
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFormEven
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBInputs

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Kl

open Module Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.DX.Dr
open CFSG.LieType.Steinberg.CentralExt CliffordAlgebra
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem spinRGL_eq_neg_one (hF : ringChar F ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    (hS : SpinFacts (quadPlus n F) (StatedQuadPlus n F)) {d : ℕ} (eσ : (Fin n ⊕ Fin n) ≃ Fin d)
    {R : GL (Fin d) F}
    (hS₁ : ∀ v, oQ R ((1 : GL (Fin d) F).val *ᵥ v) =
      ((1 : Fˣ) : F) * reindexQuadraticForm eσ (quadPlus n F) v)
    {x₀ : spinGroup (quadPlus n F)} (hx₀Z : x₀ ∈ center (spinGroup (quadPlus n F)))
    (hx₀2 : orderOf x₀ = 2) (hx₀n : x₀ ≠ negOneR hS) : spinRGL hS eσ hS₁ x₀ = -1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hk : x₀ ∈ (spinToStatedProj (quadPlus n F) (range_spinMatrix_quadPlus hn)).ker := by
    rw [(spinToStatedProj_quadPlus hn).2.2]
    exact hx₀Z
  rw [(spinToStatedProj_quadPlus hn).2.1, Subgroup.mem_comap] at hk
  obtain ⟨l, hl⟩ := hk
  have hval : ((spinRGL hS eσ hS₁ x₀ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      (l : F) • 1 := by
    change ((spinR hS eσ hS₁ x₀ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = _
    rw [spinR_val]
    have hlv : ((spinMatrix (quadPlus n F) x₀ : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = (l : F) • 1 := by
      rw [← hl, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hlv]
    ext i j
    simp [Matrix.reindex_apply, Matrix.one_apply]
  have hd0 : 0 < d := by
    have := (eσ (Sum.inl ⟨0, by omega⟩)).2
    omega
  have hxx : x₀ * x₀ = 1 := by rw [← pow_two, ← hx₀2, pow_orderOf_eq_one]
  have hl2 : (l : F) * l = 1 := by
    have e := congrArg (fun B : GL (Fin d) F => (B : Matrix (Fin d) (Fin d) F) ⟨0, hd0⟩ ⟨0, hd0⟩)
      (show spinRGL hS eσ hS₁ x₀ * spinRGL hS eσ hS₁ x₀ = 1 by rw [← map_mul, hxx, map_one])
    simp only [Units.val_mul, hval, Matrix.mul_smul, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, Units.val_one] at e
    exact e
  rcases mul_self_eq_one_iff.1 hl2 with h | h
  · exfalso
    have h1 : spinRGL hS eσ hS₁ x₀ = 1 := Units.ext (by rw [hval, h, one_smul, Units.val_one])
    rcases (Dr.spinRGL_eq_one_iff hS eσ hS₁ x₀).1 h1 with h' | h'
    · rw [h', orderOf_one] at hx₀2
      exact absurd hx₀2 (by norm_num)
    · exact hx₀n h'
  · exact Units.ext (by rw [hval, h, neg_one_smul, Units.val_neg, Units.val_one])

theorem false_of_propBHypII_spin (hF : ringChar F ≠ 2) {n : ℕ} (hn : 5 ≤ n)
    (hS : SpinFacts (quadPlus n F) (StatedQuadPlus n F)) {x₀ : spinGroup (quadPlus n F)}
    (hx₀Z : x₀ ∈ center (spinGroup (quadPlus n F))) (hx₀2 : orderOf x₀ = 2)
    (hx₀n : x₀ ≠ negOneR hS) (hII : @PropBHypII (spinGroup (quadPlus n F)) _ hS.finite x₀) :
    False := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have : Finite (spinGroup (quadPlus n F)) := hS.finite
  have : Group.IsPerfect (spinGroup (quadPlus n F)) := hS.perfect
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs2, Q, hQs, hQc, ⟨p₁, n₁, _, hp₁, -, ⟨e⟩⟩, -, hx₀Q, -⟩ := hII
  have hF₁ : ringChar (GaloisField p₁ n₁) ≠ 2 := by
    rw [ringChar.eq (GaloisField p₁ n₁) p₁]
    exact hp₁
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n F)
    (regular_coordinateQuadPlus n F (by omega)).1
  have hS₁c : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
      ((1 : Fˣ) : F) * coordinateQuadPlus n F v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hS₁ : ∀ v, oQ R ((1 : GL (Fin (2 * n)) F).val *ᵥ v) =
      ((1 : Fˣ) : F) * reindexQuadraticForm (plusIndexEquiv n) (quadPlus n F) v := hS₁c
  have : Fintype F := Fintype.ofFinite F
  have : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨f, hp, hfc⟩ := FiniteField.card F (ringChar F)
  have hFc : Nat.card F = ringChar F ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hfc]
  have hmod : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n F))) .POmegaPlus n
      (ringChar F) f := ⟨⟨hp, f.pos, by omega⟩, F, inferInstance, inferInstance, hFc,
        ⟨MulEquiv.refl _⟩⟩
  have hker := (oKer_coordinatePlus hmod F hFc (MulEquiv.refl _)).transport 1 1 hS₁c
  have hsurj := (oSurj_coordinatePlus hmod F hFc hn (MulEquiv.refl _)).transport 1 1 hS₁c
  set π := piR hS (plusIndexEquiv n) hS₁ with hπ
  have hπs := piR_surjective hS (plusIndexEquiv n) hS₁
  have hπk := ker_piR hS (plusIndexEquiv n) hS₁
  have hks : π.ker.map (s : spinGroup (quadPlus n F) →* spinGroup (quadPlus n F)) = π.ker := by
    rw [hπk, ← MulEquiv.toMonoidHom_eq_coe]
    exact Subgroup.characteristic_iff_map_eq.mp inferInstance s
  set sb := descendAut π hπs s hks with hsb
  have hsb_apply : ∀ x, sb (π x) = π (s x) := fun x => descendAut_apply π hπs s hks x
  obtain ⟨gs, hgs⟩ := hsurj sb
  have hss : oκ _ (gs * gs) = 1 := by
    rw [map_mul, ← hgs]
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hπs y
    have h := pow_orderOf_eq_one s
    rw [hs2, pow_two] at h
    change sb (sb (π x)) = π x
    rw [hsb_apply, hsb_apply, ← MulAut.mul_apply, h, MulAut.one_apply]
  have hs1 : oκ _ gs ≠ 1 := by
    rw [← hgs]
    intro h1
    have h := CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect
      (θ := π) hπk.le (s : spinGroup (quadPlus n F) →* spinGroup (quadPlus n F))
      (MonoidHom.id _) fun x => by
        change π (s x) = π x
        rw [← hsb_apply, h1, MulAut.one_apply]
    have hs1' : s = 1 := MulEquiv.ext fun x => DFunLike.congr_fun h x
    rw [hs1', orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  obtain ⟨hQs', hQc'⟩ := Burgoyne.DX.isPComponent_map_autFixed π hπs hπk.le
    (hπk ▸ hS.center2) (fun x => (hsb_apply x).symm) hQs hQc
  rw [hgs] at hQs' hQc'
  set M := Q.map (spinRGL hS (plusIndexEquiv n) hS₁) with hM
  have hQM : Q.map π = (M.subgroupOf (matrixDerived (oQ R))).map (projH _) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨spinR hS (plusIndexEquiv n) hS₁ x, mem_subgroupOf.2 ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨X, hX, rfl⟩
      obtain ⟨x, hx, hxX⟩ := mem_subgroupOf.1 hX
      refine ⟨x, hx, ?_⟩
      change projH _ (spinR hS (plusIndexEquiv n) hS₁ x) = projH _ X
      congr 1
      exact Subtype.ext hxX
  rw [hQM] at hQs' hQc'
  have hQQ : ⁅Q, Q⁆ = Q := C.commutator_eq_of_isPComponent hQs hQc
  have hneg := spinRGL_eq_neg_one hF (by omega) hS (plusIndexEquiv n) hS₁ hx₀Z hx₀2 hx₀n
  have hd : K2Data R M := by
    refine ⟨?_, ?_, ⟨x₀, hx₀Q, hneg⟩, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact (spinR hS (plusIndexEquiv n) hS₁ x).2
    · rw [hM, ← Subgroup.map_commutator, hQQ]
    · rintro _ ⟨x, hx, rfl⟩ huu
      have hxx : spinR hS (plusIndexEquiv n) hS₁ (x * x) = 1 := by
        apply Subtype.ext
        rw [map_mul]
        exact huu
      rcases (spinR_eq_one_iff hS (plusIndexEquiv n) hS₁ _).1 hxx with h | h
      · by_cases hx1 : x = 1
        · left
          rw [hx1, map_one]
        · right
          have hxe := eq_of_mul_self_of_sl hF₁ e hx₀Z hx₀Q hx₀2 hx h hx1
          rw [hxe]
          exact hneg
      · exfalso
        have hnQ : negOneR hS ∈ Q := by
          rw [← h]
          exact mul_mem hx hx
        have hnn : negOneR hS * negOneR hS = 1 := spinGroup.negOne_mul_self _ _
        have : Invertible (2 : F) := invertibleOfNonzero h2
        have hn1 : negOneR hS ≠ 1 := spinGroup.negOne_ne_one _ _
        exact hx₀n (eq_of_mul_self_of_sl hF₁ e hx₀Z hx₀Q hx₀2 hnQ hnn hn1).symm
  have hp' : (ringChar F).Prime := hp
  exact false_of_k2 hF hn hp' f.pos hFc hR hker hd hss hs1 hQs' hQc'

end CFSG.ComponentClassification.Burgoyne.DX.Kl
