module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4GO3Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Out
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OddBlock

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.LieType.HighestRoot (closure_orderOf_three_eq_top)
open scoped MatrixGroups

section Three

variable {F : Type} [Field F] [Finite F]

theorem kaGO3S_sq_eq_one (hK : Nat.card F = 3) {a : F} (ha : a ≠ 0) : a * a = 1 := by
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rw [← Nat.card_eq_fintype_card, hK] at h
  simpa [sq] using h

theorem kaGO3S_unit_mul_self (hK : Nat.card F = 3) (u : Fˣ) : u * u = 1 :=
  Units.ext (by rw [Units.val_mul, Units.val_one]; exact kaGO3S_sq_eq_one hK u.ne_zero)

theorem kaGO3S_eq_one_of_odd (hK : Nat.card F = 3) {G : Type*} [Group G] (f : G →* Fˣ) {z : G}
    (hz : Odd (orderOf z)) : f z = 1 := by
  have h1 : orderOf (f z) ∣ orderOf z := orderOf_map_dvd f z
  have h2 : orderOf (f z) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact kaGO3S_unit_mul_self hK _)
  have hodd : Odd (orderOf (f z)) := Odd.of_dvd_nat hz h1
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem kaGO3S_closure_odd (hK : Nat.card F = 3) :
    Subgroup.closure {z : SL(2, F) × SL(2, F) | Odd (orderOf z)} = ⊤ := by
  set C := Subgroup.closure {z : SL(2, F) × SL(2, F) | Odd (orderOf z)} with hC
  have key : ∀ f : SL(2, F) →* SL(2, F) × SL(2, F), (∀ y, orderOf y = 3 → Odd (orderOf (f y))) →
      ∀ U, f U ∈ C := by
    intro f hf U
    have hU : U ∈ Subgroup.closure {y : SL(2, F) | orderOf y = 3} := by
      rw [closure_orderOf_three_eq_top hK]
      exact Subgroup.mem_top U
    induction hU using Subgroup.closure_induction with
    | mem y hy => exact Subgroup.subset_closure (hf y hy)
    | one =>
      rw [map_one]
      exact one_mem _
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
    | inv a _ ha =>
      rw [map_inv]
      exact inv_mem ha
  have hodd3 : ∀ f : SL(2, F) →* SL(2, F) × SL(2, F), ∀ y : SL(2, F), orderOf y = 3 →
      Odd (orderOf (f y)) := by
    intro f y hy
    refine Odd.of_dvd_nat (n := 3) (by decide) ?_
    rw [← hy]
    exact orderOf_map_dvd f y
  have hinl := key (MonoidHom.inl _ _) (hodd3 _)
  have hinr := key (MonoidHom.inr _ _) (hodd3 _)
  rw [eq_top_iff]
  rintro ⟨U, W⟩ -
  have h : ((U, W) : SL(2, F) × SL(2, F)) = MonoidHom.inl _ _ U * MonoidHom.inr _ _ W := by
    ext <;> simp
  rw [h]
  exact mul_mem (hinl U) (hinr W)

theorem kaGO3S_hom_units_trivial (hK : Nat.card F = 3) (f : SL(2, F) × SL(2, F) →* Fˣ)
    (z : SL(2, F) × SL(2, F)) : f z = 1 := by
  have hle : Subgroup.closure {z : SL(2, F) × SL(2, F) | Odd (orderOf z)} ≤ f.ker :=
    (Subgroup.closure_le _).2 fun x hx => kaGO3S_eq_one_of_odd hK f hx
  rw [kaGO3S_closure_odd hK] at hle
  exact hle (Subgroup.mem_top z)

theorem kaGO3S_gen (hK : Nat.card F = 3) {Y : Type} [Group Y] (β : SL(2, F) × SL(2, F) →* Y) :
    Subgroup.closure {x : Y | x ∈ β.range ∧ Odd (orderOf x)} = β.range := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx.1) ?_
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ Subgroup.closure {z : SL(2, F) × SL(2, F) | Odd (orderOf z)} := by
    rw [kaGO3S_closure_odd hK]
    exact Subgroup.mem_top z
  induction hz using Subgroup.closure_induction with
  | mem y hy => exact Subgroup.subset_closure ⟨⟨y, rfl⟩, Odd.of_dvd_nat hy (orderOf_map_dvd β y)⟩
  | one =>
    rw [map_one]
    exact one_mem _
  | mul a b _ _ ha hb =>
    rw [map_mul]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [map_inv]
    exact inv_mem ha

end Three

theorem ka_outTriv_pl4_three {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup (MulAut (projectiveSL 4 F)), IsPGroup p ↥P →
      (∀ e ∈ P, e ∈ innSub (projectiveSL 4 F) → e = 1) → P = ⊥ := by
  intro p hp hp2 P hPp hPinn
  rw [eq_bot_iff]
  intro e he
  rw [Subgroup.mem_bot]
  have hodd : Odd (orderOf e) := ka_odd_of_mem_pGroup hp hp2 hPp he
  obtain ⟨D, σ, rfl⟩ := exists_semilinear_of_odd (by norm_num : 3 ≤ 4) hodd
  have hσ : σ = 1 := ringEquiv_eq_one_of_prime_card (by rw [h3]; exact Nat.prime_three) σ
  subst hσ
  simp only [map_one, mul_one] at he hodd ⊢
  exact hPinn _ he (ka_conjAut_inner_of_odd_pl4 (ka_ringChar_ne_two_of_card_three h3) D hodd)

section OddIso

variable {F : Type} [Field F]

theorem kaGO3S_similitude_of_fix (A : GL (Fin 4) F) (g : SL(4, F))
    (hy : (conjAut 4 F A * dualAut 4 F) (proj 4 F g) = proj 4 F g) :
    ∃ z : Fˣ, CatalogueBGraphForm.glTranspose 4 F (SpecialLinearGroup.toGL g) * A⁻¹ *
      SpecialLinearGroup.toGL g = A⁻¹ * GeneralLinearGroup.scalar (Fin 4) z := by
  rw [conjAut_mul_dualAut_proj] at hy
  obtain ⟨z, hz⟩ := graphLiftGL_toGL_of_scalar (proj_eq_proj_iff.1 hy.symm)
  refine ⟨z⁻¹, ?_⟩
  set X := SpecialLinearGroup.toGL g with hX
  have hY : GeneralLinearGroup.inverseTranspose X =
      A⁻¹ * (X * GeneralLinearGroup.scalar (Fin 4) z) * A := by
    have h : A * GeneralLinearGroup.inverseTranspose X * A⁻¹ =
        X * GeneralLinearGroup.scalar (Fin 4) z := hz
    rw [← h]
    group
  have hT : CatalogueBGraphForm.glTranspose 4 F X = (GeneralLinearGroup.inverseTranspose X)⁻¹ :=
    rfl
  rw [hT, hY, map_inv]
  group

theorem kaGO3S_isometry_of_odd [Finite F] (h3 : Nat.card F = 3) (A : GL (Fin 4) F) (g : SL(4, F))
    (hy : (conjAut 4 F A * dualAut 4 F) (proj 4 F g) = proj 4 F g)
    (ho : Odd (orderOf (proj 4 F g))) :
    SpecialLinearGroup.toGL g ∈ CatalogueBGraphForm.isometryGroup 4 F A⁻¹ := by
  obtain ⟨z, hz⟩ := kaGO3S_similitude_of_fix A g hy
  set X := SpecialLinearGroup.toGL g with hX
  set R := A⁻¹ with hR
  let x : CatalogueBGraphForm.similitudeGroup 4 F R := ⟨X, ⟨z, hz⟩⟩
  have hmx : CatalogueBGraphForm.similitudeMultiplierHom 4 F R x = z :=
    CatalogueBGraphForm.similitudeMultiplier_unique 4 F R x z hz
  set m := orderOf (proj 4 F g) with hm
  have hgm : g ^ m ∈ scalars 4 F := by
    rw [← proj_eq_one_iff, map_pow]
    exact pow_orderOf_eq_one _
  obtain ⟨w, -, hw⟩ := mem_scalars.1 hgm
  have hXm : X ^ m = GeneralLinearGroup.scalar (Fin 4) w := by
    rw [hX, ← map_pow]
    exact Units.ext hw
  have hxm : ((x ^ m : CatalogueBGraphForm.similitudeGroup 4 F R) : GL (Fin 4) F) =
      GeneralLinearGroup.scalar (Fin 4) w := by
    rw [Subgroup.coe_pow]
    exact hXm
  have hmxm : CatalogueBGraphForm.similitudeMultiplierHom 4 F R (x ^ m) = w * w := by
    refine CatalogueBGraphForm.similitudeMultiplier_unique 4 F R (x ^ m) (w * w) ?_
    rw [hxm, CatalogueBGraphForm.glTranspose_scalar, GeneralLinearGroup.scalar_commute w R,
      mul_assoc, ← map_mul]
  have hzm : z ^ m = 1 := by
    rw [← hmx, ← map_pow, hmxm, kaGO3S_unit_mul_self h3]
  obtain ⟨k, hk⟩ := ho
  have hzz : z ^ m = z := by
    rw [hk, pow_succ, pow_mul, pow_two, kaGO3S_unit_mul_self h3, one_pow, one_mul]
  have hz1 : z = 1 := hzz.symm.trans hzm
  rw [hz1, map_one, mul_one] at hz
  exact hz

end OddIso

section Assembly

variable {F : Type} [Field F]

@[expose] def kaGO3SLift {H O : Type} [Group H] [Group O] (θ : O →* GL (Fin 4) F) (ρ : H →* O)
    (hdet : ∀ z, ((θ (ρ z) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1) :
    H →* SL(4, F) where
  toFun z := ⟨((θ (ρ z) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F), hdet z⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    change ((θ (ρ (a * b)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((θ (ρ a) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((θ (ρ b) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [map_mul, map_mul, Units.val_mul]

theorem toGL_kaGO3SLift {H O : Type} [Group H] [Group O] (θ : O →* GL (Fin 4) F) (ρ : H →* O)
    (hdet : ∀ z, ((θ (ρ z) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1) (z : H) :
    SpecialLinearGroup.toGL (kaGO3SLift θ ρ hdet z) = θ (ρ z) :=
  Units.ext rfl

theorem kaGO3S_of_model [Finite F] (h3 : Nat.card F = 3) (A : GL (Fin 4) F)
    {O : Type} [Group O] (θ : O →* GL (Fin 4) F) (ρ : SL(2, F) × SL(2, F) →* O)
    (hθI : ∀ d, θ d ∈ CatalogueBGraphForm.isometryGroup 4 F A⁻¹)
    (hθS : ∀ X ∈ CatalogueBGraphForm.isometryGroup 4 F A⁻¹, ∃ d, θ d = X)
    (hsq : ∀ d : O, d * d ∈ ρ.range)
    (hker : ∀ (z : SL(2, F) × SL(2, F)) (μ : Fˣ),
      θ (ρ z) = GeneralLinearGroup.scalar (Fin 4) μ →
        z.1 ∈ Subgroup.center SL(2, F) ∧ z.2 ∈ Subgroup.center SL(2, F)) :
    KAAll (conjAut 4 F A * dualAut 4 F) := by
  have hK : ringChar F ≠ 2 := ka_ringChar_ne_two_of_card_three h3
  have hdet : ∀ z, ((θ (ρ z) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    intro z
    have h := congrArg Units.val
      (kaGO3S_hom_units_trivial h3 (GeneralLinearGroup.det.comp (θ.comp ρ)) z)
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h
  set lift := kaGO3SLift θ ρ hdet with hlift_def
  have hlift : ∀ z, SpecialLinearGroup.toGL (lift z) = θ (ρ z) := toGL_kaGO3SLift θ ρ hdet
  set β : SL(2, F) × SL(2, F) →* projectiveSL 4 F := (proj 4 F).comp lift with hβ
  refine ka_all_of_oddcore_triv (ka_conj_inj_pl4 hK) β.range ?_ (kaGO3S_gen h3 β) ?_ ?_
    (ka_outTriv_pl4_three h3)
  · rintro _ ⟨z, rfl⟩
    rw [mem_fixSub]
    have hz : lift z ∈ isometrySL 4 A⁻¹ := by
      rw [isometrySL, Subgroup.mem_comap, hlift]
      exact hθI _
    show (conjAut 4 F A * dualAut 4 F) (proj 4 F (lift z)) = proj 4 F (lift z)
    rw [conjAut_mul_dualAut_proj, (graphLift_eq_iff A _).2 hz]
  · intro c hc ho
    rw [mem_fixSub] at hc
    obtain ⟨g, rfl⟩ := proj_surjective 4 F c
    obtain ⟨d, hd⟩ := hθS _ (kaGO3S_isometry_of_odd h3 A g hc ho)
    obtain ⟨z, hz⟩ := hsq d
    have hz2 : lift z = g * g := by
      apply SpecialLinearGroup.toGL_injective
      simp only [hlift, hz, map_mul, hd]
    refine ka_odd_mem_of_sq_mem ?_ ho
    rw [← map_mul, ← hz2]
    exact ⟨z, rfl⟩
  · intro p hp hp2 X hXp hXR hXn
    have : Fact p.Prime := ⟨hp⟩
    have hodd : Odd (Nat.card X) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hXp
      rw [hn]
      exact (hp.odd_of_ne_two hp2).pow
    refine CFSG.ComponentClassification.CatFactsL4U4.eq_bot_of_odd_block
      ⟨3, 1, Nat.prime_three, by decide, le_refl 1, by rw [h3]; norm_num⟩ β ?_ X hXR ?_ hodd
    · intro z hz
      obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hz)
      exact hker z c (by rw [← hlift]; exact Units.ext hc)
    · intro g hg r hr
      exact (Subgroup.mem_normalizer_iff.1 (hXn g hg) r).1 hr

end Assembly

section Model

variable {F : Type} [Field F]

@[expose] noncomputable def kaGO3STheta (hK : ringChar F ≠ 2) {R : GL (Fin 4) F}
    (hR : (R : Matrix (Fin 4) (Fin 4) F)ᵀ = R)
    (e : TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm R) ≃*
      DeterminantIsometries F) : DeterminantIsometries F →* GL (Fin 4) F :=
  (CatalogueBGraphForm.isometryGroup 4 F R).subtype.comp
    ((isoOrthGL hK R hR).toMonoidHom.comp e.symm.toMonoidHom)

theorem kaGO3STheta_mem (hK : ringChar F ≠ 2) {R : GL (Fin 4) F}
    (hR : (R : Matrix (Fin 4) (Fin 4) F)ᵀ = R)
    (e : TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm R) ≃*
      DeterminantIsometries F) (d : DeterminantIsometries F) :
    kaGO3STheta hK hR e d ∈ CatalogueBGraphForm.isometryGroup 4 F R :=
  (isoOrthGL hK R hR (e.symm d)).2

theorem kaGO3STheta_surj (hK : ringChar F ≠ 2) {R : GL (Fin 4) F}
    (hR : (R : Matrix (Fin 4) (Fin 4) F)ᵀ = R)
    (e : TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm R) ≃*
      DeterminantIsometries F) {X : GL (Fin 4) F}
    (hX : X ∈ CatalogueBGraphForm.isometryGroup 4 F R) :
    ∃ d, kaGO3STheta hK hR e d = X :=
  ⟨e ((isoOrthGL hK R hR).symm ⟨X, hX⟩), by simp [kaGO3STheta]⟩

theorem kaGO3STheta_mulVec (hK : ringChar F ≠ 2) {R : GL (Fin 4) F}
    (hR : (R : Matrix (Fin 4) (Fin 4) F)ᵀ = R)
    (e : TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm R) ≃*
      DeterminantIsometries F) (ψ : (Fin 4 → F) ≃ₗ[F] Matrix (Fin 2) (Fin 2) F)
    (hψ : ∀ g v, (e.symm g).val v = ψ.symm (g.val (ψ v))) (d : DeterminantIsometries F)
    (v : Fin 4 → F) :
    ((kaGO3STheta hK hR e d : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ v =
      ψ.symm (d.val (ψ v)) := by
  have h := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec
    (Pi.basisFun F (Fin 4)) (e.symm d).val v
  rw [← hψ]
  exact h

end Model

section Center

variable {F : Type} [Field F]

theorem kaGO3S_center_of_sandwich {a b : SL(2, F)} {μ : F} (hμ : μ ≠ 0)
    (h : ∀ X : Matrix (Fin 2) (Fin 2) F, (a : Matrix (Fin 2) (Fin 2) F) * X *
      ((b⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = μ • X) :
    a ∈ Subgroup.center SL(2, F) ∧ b ∈ Subgroup.center SL(2, F) := by
  have hbb : ((b⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F) =
      1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h1 := h 1
  rw [Matrix.mul_one] at h1
  have hab : (a : Matrix (Fin 2) (Fin 2) F) = μ • (b : Matrix (Fin 2) (Fin 2) F) := by
    calc (a : Matrix (Fin 2) (Fin 2) F)
        = (a : Matrix (Fin 2) (Fin 2) F) * ((b⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
            (b : Matrix (Fin 2) (Fin 2) F) := by rw [Matrix.mul_assoc, hbb, Matrix.mul_one]
      _ = μ • (b : Matrix (Fin 2) (Fin 2) F) := by rw [h1, Matrix.smul_mul, Matrix.one_mul]
  have hcomm : ∀ X : Matrix (Fin 2) (Fin 2) F,
      (b : Matrix (Fin 2) (Fin 2) F) * X = X * (b : Matrix (Fin 2) (Fin 2) F) := by
    intro X
    have h2 := h X
    rw [hab, Matrix.smul_mul, Matrix.smul_mul] at h2
    have h3 : (b : Matrix (Fin 2) (Fin 2) F) * X *
        ((b⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = X := by
      have := congrArg (fun M => μ⁻¹ • M) h2
      simpa [smul_smul, inv_mul_cancel₀ hμ] using this
    calc (b : Matrix (Fin 2) (Fin 2) F) * X
        = (b : Matrix (Fin 2) (Fin 2) F) * X *
            (((b⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F)) := by
          rw [hbb, Matrix.mul_one]
      _ = X * (b : Matrix (Fin 2) (Fin 2) F) := by rw [← Matrix.mul_assoc, h3]
  constructor
  · rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hab,
      Matrix.mul_smul, Matrix.smul_mul, hcomm]
  · rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hcomm]

end Center

theorem kaGO3S_inv_transpose {F : Type} [Field F] (A : GL (Fin 4) F)
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A) :
    ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = (A⁻¹ : GL (Fin 4) F) := by
  rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hA]

theorem kaL4GOrthThreeSp_thm :
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 → ∀ A : GL (Fin 4) F,
      (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A → KAL4Split A →
      KAAll (conjAut 4 F A * dualAut 4 F) := by
  intro F _ _ h3 A hA hsp
  have hK : ringChar F ≠ 2 := ka_ringChar_ne_two_of_card_three h3
  have hR := kaGO3S_inv_transpose A hA
  obtain ⟨S, hS2, hS0⟩ := hsp
  obtain ⟨ψ, e, -, -, hψ⟩ := split_four_determinant_form_isometry (matrixQuadraticForm A⁻¹)
    (polarBilin_matrixQuadraticForm_nondegenerate hK A⁻¹ hR) (Module.finrank_fin_fun F) S hS2 hS0
  refine kaGO3S_of_model h3 A (kaGO3STheta hK hR e) specialRho (kaGO3STheta_mem hK hR e)
    (fun X hX => kaGO3STheta_surj hK hR e hX) (fun d => ?_) (fun z μ hz => ?_)
  · rw [← pow_two]
    exact LocalAnalysis.ComponentInitial.determinant_sq_mem_specialImage d
  · have hmul := fun v => kaGO3STheta_mulVec hK hR e ψ hψ (specialRho z) v
    rw [hz] at hmul
    have hd : ∀ X : Matrix (Fin 2) (Fin 2) F, (specialRho z).val X = (μ : F) • X := by
      intro X
      apply ψ.symm.injective
      have h := hmul (ψ.symm X)
      rw [LinearEquiv.apply_symm_apply] at h
      rw [map_smul, ← h]
      simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    exact kaGO3S_center_of_sandwich μ.ne_zero fun X => by rw [← specialRho_apply]; exact hd X

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
