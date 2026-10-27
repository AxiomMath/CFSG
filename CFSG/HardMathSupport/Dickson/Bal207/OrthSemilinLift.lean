module

public import CFSG.HardMathSupport.Dickson.Bal207.UniLift
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.RankThree.PartOne.S11d.OrthLayer

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFix

open QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.RankThree.Classical2 CFSG.HardMathSupport.Dickson.Bal207.Uni
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Pairs

variable {F : Type} [Field F] {d : ℕ}

@[expose] def isometryPairs (Q : QuadraticForm F (Fin d → F)) :
    Subgroup ↥(similarityPairs Q) where
  carrier := {g | ∀ v, Q (coordinateSemilinearMap g.val v) = g.val.right (Q v)}
  one_mem' := by
    intro v
    change Q (coordinateSemilinearMap 1 v) = (1 : F ≃+* F) (Q v)
    rw [coordinateSemilinearMap_one]
    rfl
  mul_mem' := by
    intro g h hg hh v
    have hg' : ∀ w, Q (coordinateSemilinearMap g.val w) = g.val.right (Q w) := hg
    have hh' : ∀ w, Q (coordinateSemilinearMap h.val w) = h.val.right (Q w) := hh
    change Q (coordinateSemilinearMap (g.val * h.val) v) = (g.val.right * h.val.right) (Q v)
    rw [coordinateSemilinearMap_mul, hg', hh']
    rfl
  inv_mem' := by
    intro g hg v
    have hg' : ∀ w, Q (coordinateSemilinearMap g.val w) = g.val.right (Q w) := hg
    change Q (coordinateSemilinearMap g.val⁻¹ v) = g.val.right⁻¹ (Q v)
    have h1 := hg' ((coordinateSemilinearMap g.val).symm v)
    rw [AddEquiv.apply_symm_apply] at h1
    rw [coordinateSemilinearMap_inv, h1]
    exact (g.val.right.symm_apply_apply _).symm

theorem mem_isometryPairs_iff (Q : QuadraticForm F (Fin d → F)) (g : similarityPairs Q) :
    g ∈ isometryPairs Q ↔ ∀ v, Q (coordinateSemilinearMap g.val v) = g.val.right (Q v) :=
  Iff.rfl

variable [CharP F 2] {Q : QuadraticForm F (Fin d → F)}

theorem injective_isometryPairs_conj (hd : 0 < d) (hQ : (polarBilin Q).Nondegenerate)
    (hker : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Fˣ, g.val.left = Matrix.GeneralLinearGroup.scalar (Fin d) a) :
    Function.Injective ((matrixProjectiveConjugationHom Q).comp (isometryPairs Q).subtype) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨h1, a, ha⟩ := hker g.val hg
  obtain ⟨v, hv⟩ : ∃ v, Q v ≠ 0 := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    by_contra h
    push Not at h
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin d → F)
    exact hv (hQ.1 v fun w => by
      rw [polarBilin_apply_apply, QuadraticMap.polar, h, h, h, sub_zero, sub_zero])
  have hr : ∀ c : F, g.val.val.right c = c := fun c => by rw [h1]; rfl
  have hgv : Q (coordinateSemilinearMap g.val.val v) = g.val.val.right (Q v) := g.2 v
  have hsv : coordinateSemilinearMap g.val.val v = (a : F) • v := by
    rw [coordinateSemilinearMap_apply, ha]
    ext i
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal, hr]
  rw [hsv, QuadraticMap.map_smul, smul_eq_mul, hr] at hgv
  have haa : (a : F) * a = 1 := mul_right_cancel₀ hv (hgv.trans (one_mul _).symm)
  have h0 : ((a : F) - 1) ^ 2 = 0 := by
    linear_combination haa + (1 - (a : F)) * (CharTwo.two_eq_zero : (2 : F) = 0)
  have ha1 : a = 1 := Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0))
  apply Subtype.ext
  apply Subtype.ext
  refine SemidirectProduct.ext ?_ h1
  rw [ha, ha1, map_one]
  rfl

theorem range_isometryPairs_conj [Finite F] :
    ((matrixProjectiveConjugationHom Q).comp (isometryPairs Q).subtype).range =
      matrixProjectiveImage Q := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact ⟨g.val, rfl⟩
  · rintro _ ⟨g, rfl⟩
    obtain ⟨μ, hμ⟩ := g.property
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' ((μ : F)⁻¹)
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact inv_ne_zero μ.ne_zero (by rw [hr, mul_zero])
    obtain ⟨s, hsc, hsv⟩ : ∃ s : GL (Fin d) F, (∀ A, s * A = A * s) ∧
        ∀ w, coordinateSemilinearMap (SemidirectProduct.inl s) w = r • w :=
      ⟨Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 r hr0),
        fun A => Matrix.GeneralLinearGroup.scalar_commute _ A, fun w => by
          rw [coordinateSemilinearMap_apply]
          ext i
          simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
            Matrix.mulVec_diagonal]⟩
    have hs : SemidirectProduct.inl s ∈ similarityPairs Q :=
      ⟨Units.mk0 r hr0 * Units.mk0 r hr0, fun w => by
        rw [hsv, QuadraticMap.map_smul, smul_eq_mul]
        rfl⟩
    have hs1 : matrixProjectiveConjugationHom Q ⟨SemidirectProduct.inl s, hs⟩ = 1 := by
      apply MulEquiv.ext
      intro y
      obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q y
      change matrixProjectiveConjugation Q ⟨SemidirectProduct.inl s, hs⟩
        (matrixProjectiveProjection Q A) = matrixProjectiveProjection Q A
      rw [matrixProjectiveConjugation_mk]
      congr 1
      apply Subtype.ext
      rw [matrixDerivedConjugation_val]
      change s * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) F 1
        A.val * s⁻¹ = A.val
      rw [map_one, MulAut.one_apply, hsc, mul_inv_cancel_right]
    refine MonoidHom.mem_range.mpr
      ⟨⟨⟨SemidirectProduct.inl s, hs⟩ * g, (mem_isometryPairs_iff Q _).mpr fun v => ?_⟩, ?_⟩
    · change Q (coordinateSemilinearMap (SemidirectProduct.inl s * g.val) v) = g.val.right (Q v)
      rw [coordinateSemilinearMap_mul, hsv, QuadraticMap.map_smul, hμ, smul_eq_mul, ← mul_assoc,
        ← hr, inv_mul_cancel₀ μ.ne_zero, one_mul]
    · change matrixProjectiveConjugationHom Q (⟨SemidirectProduct.inl s, hs⟩ * g) =
        matrixProjectiveConjugationHom Q g
      rw [map_mul, hs1, one_mul]

end Pairs

theorem exists_semilin_of_mem_E {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    {Q : QuadraticForm F (Fin d → F)} {G : Type} [Group G] {K B : Subgroup G}
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hd : 0 < d)
    (hQ : (polarBilin Q).Nondegenerate)
    (hker : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Fˣ, g.val.left = Matrix.GeneralLinearGroup.scalar (Fin d) a)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ProjOrthDerived Q)
    (hE : ∀ b : ↥B, MulAut.congr (coordBridge Q hd).symm (uniAut e ⟨b, hBK b.2⟩) ∈
      matrixProjectiveImage Q)
    (x : orthDerived Q) (hBx : ∀ b : ↥B, uniAut e ⟨b, hBK b.2⟩ (piOrth Q x) = piOrth Q x) :
    ∃ (S : ↥B → (Fin d → F) ≃+ (Fin d → F)) (σ : ↥B →* (F ≃+* F)),
      (∀ b c v, S b (c • v) = σ b c • S b v) ∧
      (∀ b b' v, S (b * b') v = S b (S b' v)) ∧
      (∀ b v, Q (S b v) = σ b (Q v)) ∧
      (∀ b v, S b ((x : (Fin d → F) ≃ₗ[F] (Fin d → F)) v) =
        (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (S b v)) ∧
      ∀ b (g g' : orthDerived Q),
        (∀ v, (g' : (Fin d → F) ≃ₗ[F] (Fin d → F)) v =
          S b ((g : (Fin d → F) ≃ₗ[F] (Fin d → F)) ((S b).symm v))) →
        uniAut e ⟨b, hBK b.2⟩ (piOrth Q g) = piOrth Q g' := by
  obtain ⟨lift, hlift⟩ : ∃ lift : ↥B →* ↥(isometryPairs Q), ∀ b,
      matrixProjectiveConjugationHom Q (lift b).val =
        MulAut.congr (coordBridge Q hd).symm (uniAut e ⟨b, hBK b.2⟩) := by
    have hinj := injective_isometryPairs_conj hd hQ hker
    have hα : ∀ b, ((MulAut.congr (coordBridge Q hd).symm).toMonoidHom.comp
        ((uniAut e).comp (Subgroup.inclusion hBK))) b ∈
        ((matrixProjectiveConjugationHom Q).comp (isometryPairs Q).subtype).range := fun b => by
      rw [range_isometryPairs_conj]
      exact hE b
    refine ⟨(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (MonoidHom.codRestrict _ _ hα),
      fun b => ?_⟩
    have h := congrArg Subtype.val
      (MulEquiv.apply_symm_apply (MonoidHom.ofInjective hinj) (MonoidHom.codRestrict _ _ hα b))
    rw [MonoidHom.ofInjective_apply] at h
    exact h
  have hact : ∀ b (g g' : orthDerived Q),
      (∀ v, (g' : (Fin d → F) ≃ₗ[F] (Fin d → F)) v =
        coordinateSemilinearMap (lift b).val.val ((g : (Fin d → F) ≃ₗ[F] (Fin d → F))
          ((coordinateSemilinearMap (lift b).val.val).symm v))) →
      uniAut e ⟨b, hBK b.2⟩ (piOrth Q g) = piOrth Q g' := by
    intro b g g' h
    have h1 := coordBridge_conjugation Q hd (lift b).val g g' h
    rw [hlift b] at h1
    have h3 : (MulAut.congr (coordBridge Q hd).symm (uniAut e ⟨b, hBK b.2⟩))
        ((coordBridge Q hd).symm (QuotientGroup.mk g)) =
        (coordBridge Q hd).symm (uniAut e ⟨b, hBK b.2⟩ (QuotientGroup.mk g)) := by
      rw [MulAut.congr_apply]
      simp
    rw [h3, MulEquiv.apply_symm_apply] at h1
    exact h1
  refine ⟨fun b => coordinateSemilinearMap (lift b).val.val,
    SemidirectProduct.rightHom.comp
      ((similarityPairs Q).subtype.comp ((isometryPairs Q).subtype.comp lift)),
    fun b c v => coordinateSemilinearMap_smul _ c v, fun b b' v => ?_, fun b v => (lift b).2 v,
    fun b v => ?_, hact⟩
  · change coordinateSemilinearMap (lift (b * b')).val.val v = _
    rw [map_mul, Subgroup.coe_mul, Subgroup.coe_mul, coordinateSemilinearMap_mul]
  ·
    obtain ⟨A, hA⟩ := exists_matrixDerived Q x
    have hmem := (map_matrixDerived Q).le
      (Subgroup.mem_map_of_mem (matrixLinearIso (d := d) (K := F)).toMonoidHom
        (matrixDerivedConjugation Q (lift b).val A).2)
    have hx' : ∀ w, ((⟨_, hmem⟩ : orthDerived Q) : (Fin d → F) ≃ₗ[F] (Fin d → F)) w =
        coordinateSemilinearMap (lift b).val.val ((x : (Fin d → F) ≃ₗ[F] (Fin d → F))
          ((coordinateSemilinearMap (lift b).val.val).symm w)) := fun w => by
      rw [hA]
      exact matrixConjugation_vector (lift b).val.val A.val w
    have heq : (⟨_, hmem⟩ : orthDerived Q) = x := by
      haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      apply piOrth_injective hQ
      rw [← hact b x _ hx', hBx b]
    have h := hx' (coordinateSemilinearMap (lift b).val.val v)
    rw [AddEquiv.symm_apply_apply, heq] at h
    exact h.symm

end CFSG.HardMathSupport.Dickson.Bal207.OrthFix

end
