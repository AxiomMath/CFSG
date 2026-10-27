module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BenderGroupFactsAlternating
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankBoundField

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.GorensteinWalter CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

theorem card_le_two_of_forall_ne_one {H : Type*} [Group H]
    (h : ∀ x y : H, x ≠ 1 → y ≠ 1 → x = y) : Nat.card H ≤ 2 := by
  classical
  by_cases hH : ∃ x : H, x ≠ 1
  · obtain ⟨x₀, hx₀⟩ := hH
    calc Nat.card H ≤ Nat.card Bool :=
          Nat.card_le_card_of_surjective (fun b : Bool => if b then x₀ else 1) (fun y => by
            by_cases hy : y = 1
            · exact ⟨false, by simp [hy]⟩
            · exact ⟨true, by simp [h y x₀ hy hx₀]⟩)
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  · push Not at hH
    have : Subsingleton H := ⟨fun a b => (hH a).trans (hH b).symm⟩
    rw [Nat.card_unique]
    omega

variable {K : Type*} [Field K] [Fintype K]

@[expose] noncomputable def pglSquareClass (hK : ringChar K ≠ 2) : PGL2 K →* Kˣ :=
  QuotientGroup.lift (Subgroup.center (GL (Fin 2) K))
    ((powMonoidHom (Fintype.card K / 2)).comp Matrix.GeneralLinearGroup.det) (by
      classical
      intro z hz
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
      obtain ⟨u, rfl⟩ := hz
      have hodd : Fintype.card K % 2 = 1 := FiniteField.odd_card_of_char_ne_two hK
      have h2 : 2 * (Fintype.card K / 2) = Fintype.card Kˣ := by
        rw [Fintype.card_units]
        omega
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.det_scalar,
        powMonoidHom_apply, Fintype.card_fin, ← pow_mul, h2, pow_card_eq_one])

theorem pglSquareClass_mk (hK : ringChar K ≠ 2) (X : GL (Fin 2) K) :
    pglSquareClass hK (Matrix.ProjGenLinGroup.mk X) =
      Matrix.GeneralLinearGroup.det X ^ (Fintype.card K / 2) := rfl

theorem mem_range_toPGL_of_pglSquareClass_eq_one (hK : ringChar K ≠ 2) (g : PGL2 K)
    (hg : pglSquareClass hK g = 1) :
    g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk X => ?_
  rw [pglSquareClass_mk] at hg
  obtain ⟨μ, hμ⟩ := (FiniteField.unit_isSquare_iff hK _).mpr hg
  have hdet : (((μ⁻¹ : Kˣ) : K) • (X : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← Matrix.GeneralLinearGroup.val_det_apply, hμ,
      Units.val_mul, ← pow_two, ← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_pow]
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix.SpecialLinearGroup (Fin 2) K,
      (Y : Matrix (Fin 2) (Fin 2) K) = ((μ⁻¹ : Kˣ) : K) • (X : Matrix (Fin 2) (Fin 2) K) :=
    ⟨⟨_, hdet⟩, rfl⟩
  refine ⟨(QuotientGroup.mk Y : PSL2 K), ?_⟩
  simp only [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨μ, Units.ext ?_⟩
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hY]
  ext i j
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
    Units.val_inv_eq_inv_val]
  rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero μ), one_mul]

theorem pglSquareClass_eq_one_of_mul_fieldAut_eq_one (hK : ringChar K ≠ 2) (σ : K ≃+* K)
    (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) (g : PGL2 K) (hg : g * pgl2FieldAut K σ g = 1) :
    pglSquareClass hK g = 1 := by
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk X => ?_
  have h2 : pgl2FieldAut K σ (Matrix.ProjGenLinGroup.mk X) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map σ.toRingHom X) := by
    rw [pgl2FieldAut_apply]
    exact pgl2RingEquiv_mk σ X
  have h1 : Matrix.ProjGenLinGroup.mk
      (X * Matrix.GeneralLinearGroup.map σ.toRingHom X) = (1 : PGL2 K) := by
    rw [map_mul, ← h2]
    exact hg
  rw [Matrix.ProjGenLinGroup.mk_eq_one] at h1
  rw [pglSquareClass_mk]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact det_pow_card_div_two_eq_one_of_mul_map_mem_center hK σ hσ1 hσ2 X h1

theorem card_le_two_of_inf_pslRange_eq_bot (hK : ringChar K ≠ 2) (F : Subgroup (PGammaL2 K))
    (hF : ∀ x ∈ F, x * x = 1) (hFI : F ⊓ pGammaL2PSLRange K = ⊥) : Nat.card F ≤ 2 := by
  have hone : ∀ x ∈ F, x.right = 1 → pglSquareClass hK x.left = 1 → x = 1 := by
    intro x hx hr hθ
    obtain ⟨y, hy⟩ := mem_range_toPGL_of_pglSquareClass_eq_one hK x.left hθ
    have hmem : x ∈ F ⊓ pGammaL2PSLRange K :=
      ⟨hx, (mem_pGammaL2PSLRange_iff K x).mpr ⟨y, SemidirectProduct.ext (by simpa using hy)
        (by simpa using hr.symm)⟩⟩
    rwa [hFI, Subgroup.mem_bot] at hmem
  have hsq : ∀ x ∈ F, x.right * x.right = 1 ∧ x.left * pgl2FieldAut K x.right x.left = 1 := by
    intro x hx
    have h := hF x hx
    exact ⟨by simpa using congrArg SemidirectProduct.right h,
      by simpa using congrArg SemidirectProduct.left h⟩
  by_cases hA : ∃ x₁ ∈ F, x₁.right ≠ 1
  · obtain ⟨x₁, hx₁, hr₁⟩ := hA
    have hσ2 := (hsq x₁ hx₁).1
    have hker : ∀ x ∈ F, x.right = 1 → x = 1 := by
      intro x hx hr
      apply hone x hx hr
      have hθ1 := pglSquareClass_eq_one_of_mul_fieldAut_eq_one hK _ hr₁ hσ2 _ (hsq x₁ hx₁).2
      have hx₂ := F.mul_mem hx hx₁
      have hr₂ : (x * x₁).right = x₁.right := by simp [hr]
      have hθ2 := pglSquareClass_eq_one_of_mul_fieldAut_eq_one hK _ hr₁ hσ2 _
        (hr₂ ▸ (hsq _ hx₂).2)
      have hl : (x * x₁).left = x.left * x₁.left := by simp [hr]
      rwa [hl, map_mul, hθ1, mul_one] at hθ2
    apply card_le_two_of_forall_ne_one
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ha1 hb1
    have hra : a.right ≠ 1 := fun h => ha1 (Subtype.ext (hker a ha h))
    have hrb : b.right ≠ 1 := fun h => hb1 (Subtype.ext (hker b hb h))
    have hab : a.right = b.right :=
      ringEquiv_eq_of_involution hra (hsq a ha).1 hrb (hsq b hb).1
    have h1 := hker _ (F.mul_mem ha (F.inv_mem hb)) (by simp [hab])
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  · push Not at hA
    apply card_le_two_of_forall_ne_one
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ha1 hb1
    have hθa : pglSquareClass hK a.left ≠ 1 := fun h => ha1 (Subtype.ext (hone a ha (hA a ha) h))
    have hθb : pglSquareClass hK b.left ≠ 1 := fun h => hb1 (Subtype.ext (hone b hb (hA b hb) h))
    have hneg : ∀ x ∈ F, pglSquareClass hK x.left ≠ 1 →
        ((pglSquareClass hK x.left : Kˣ) : K) = -1 := by
      intro x hx hθ
      have h := (hsq x hx).2
      rw [hA x hx, map_one, MulAut.one_apply] at h
      have h2 := congrArg (fun g => ((pglSquareClass hK g : Kˣ) : K)) h
      simp only [map_mul, Units.val_mul, map_one, Units.val_one] at h2
      refine (mul_self_eq_one_iff.mp h2).resolve_left fun h1 => hθ (Units.ext h1)
    have hθ : pglSquareClass hK a.left = pglSquareClass hK b.left :=
      Units.ext ((hneg a ha hθa).trans (hneg b hb hθb).symm)
    have hab := F.mul_mem ha (F.inv_mem hb)
    have hl : (a * b⁻¹).left = a.left * b.left⁻¹ := by simp [hA b hb, hA a ha]
    have h1 := hone _ hab (hA _ hab) (by rw [hl, map_mul, map_inv, hθ, mul_inv_cancel])
    exact Subtype.ext (mul_inv_eq_one.mp h1)

omit [Fintype K] in
theorem card_le_two_of_mulEquiv_psl2 [Finite K] (hK : ringChar K ≠ 2) {S : Type*} [Group S]
    (e : S ≃* PSL2 K) (F : Subgroup (MulAut S)) (hF : ∀ x ∈ F, x * x = 1)
    (hFI : F ⊓ inner S = ⊥) : Nat.card F ≤ 2 := by
  let _ : Fintype K := Fintype.ofFinite K
  let Φ : MulAut S ≃* PGammaL2 K := (MulAut.congr e).trans (semilinearEquivAut K).symm
  rw [← Subgroup.card_map_of_injective (f := Φ.toMonoidHom) Φ.injective]
  apply card_le_two_of_inf_pslRange_eq_bot hK
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hF x hx, map_one]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hmem⟩
    obtain ⟨y, hy⟩ := (mem_pGammaL2PSLRange_iff K _).mp hmem
    have hy' : SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y) = Φ x := hy
    have hconj : MulAut.congr e x = MulAut.conj y := by
      have h1 : semilinearEquivAut K (Φ x) = MulAut.congr e x :=
        (semilinearEquivAut K).apply_symm_apply _
      have h2 : semilinearEquivAut K
          (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y)) =
            MulAut.conj y := by
        change semilinearAction K _ = _
        rw [semilinearAction_inl, pglAction_toPGL]
      rw [← h1, ← h2, hy']
    have hinner : MulAut.congr e x ∈
        (ComponentClassification.OuterAutomorphisms.inner S).map (MulAut.congr e).toMonoidHom := by
      rw [inner_map_congr]
      exact ⟨y, hconj.symm⟩
    obtain ⟨x', hx', hxx'⟩ := hinner
    have hx'x : x' = x := (MulAut.congr e).injective hxx'
    have hxF : x ∈ F ⊓ inner S := ⟨hx, hx'x ▸ hx'⟩
    rw [hFI, Subgroup.mem_bot] at hxF
    rw [hxF, map_one]
    exact Subgroup.one_mem _

theorem card_le_two_of_mulEquiv_alternatingGroup_seven {S : Type*} [Group S]
    (e : S ≃* alternatingGroup (Fin 7)) (F : Subgroup (MulAut S)) (hFI : F ⊓ inner S = ⊥) :
    Nat.card F ≤ 2 := by
  have hout := BenderFacts.card_outer_eq_two_of_mulEquiv_alternatingGroup_seven e
  have : Finite (Outer S) := Nat.finite_of_card_ne_zero (by rw [hout]; norm_num)
  rw [← hout]
  refine Nat.card_le_card_of_injective ((QuotientGroup.mk' (inner S)).comp F.subtype) ?_
  intro a b hab
  have hmem : (a : MulAut S)⁻¹ * b ∈ inner S :=
    QuotientGroup.eq.mp hab
  have hF : (a : MulAut S)⁻¹ * b ∈ F ⊓ inner S := ⟨F.mul_mem (F.inv_mem a.2) b.2, hmem⟩
  rw [hFI, Subgroup.mem_bot, inv_mul_eq_one] at hF
  exact Subtype.ext hF

theorem card_le_two_of_inf_inner_eq_bot {S : Type*} [Group S]
    (hS : Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        Nonempty (S ≃* PSL(2, GaloisField p k)))
    (F : Subgroup (MulAut S)) (hF : ∀ x ∈ F, x * x = 1) (hFI : F ⊓ inner S = ⊥) :
    Nat.card F ≤ 2 := by
  rcases hS with he | ⟨p, k, _hp, hodd, -, he⟩
  · obtain ⟨e⟩ := he
    exact card_le_two_of_mulEquiv_alternatingGroup_seven e F hFI
  · obtain ⟨e⟩ := he
    have hK : ringChar (GaloisField p k) ≠ 2 := by
      rw [ringChar.eq (GaloisField p k) p]
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    exact card_le_two_of_mulEquiv_psl2 hK e F hF hFI

end CFSG.ProperTwoGeneratedCore.Lemma37
