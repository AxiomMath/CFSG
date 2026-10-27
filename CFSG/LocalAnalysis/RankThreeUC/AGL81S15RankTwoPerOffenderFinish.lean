module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderDescent
public import CFSG.HardMathSupport.GuralnickMalle.Prop310
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open Matrix

theorem card_le_of_elemAbelian_commute_semilinear {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {σ : F ≃+* F} (hσ : ∃ c : F, σ c ≠ c) (hσ2 : ∀ c : F, σ (σ c) = c)
    {r : ℕ} (T : (Fin r → F) ≃+ (Fin r → F))
    (hT : ∀ (c : F) (u : Fin r → F), T (c • u) = σ c • T u) (hT2 : ∀ u : Fin r → F, T (T u) = u)
    (E : Subgroup (Matrix.GeneralLinearGroup (Fin r) F)) (hE : IsElemAbelian 2 E)
    (hcomm : ∀ e ∈ E, ∀ u : Fin r → F,
      (e : Matrix (Fin r) (Fin r) F) *ᵥ T u = T ((e : Matrix (Fin r) (Fin r) F) *ᵥ u)) :
    Nat.card E ≤ 2 ^ (r ^ 2 / 4) := by
  classical
  let M := Fin r → F
  have h2smul : ∀ u : M, (2 : ℕ) • u = 0 := by
    intro u
    funext i
    have h2 : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, h2, zero_mul]
  let : Module (ZMod 2) M := AddCommGroup.zmodModule h2smul
  let Y0 : AddSubgroup M :=
    { carrier := {y | T y = y}
      add_mem' := by
        intro a b ha hb
        show T (a + b) = a + b
        rw [map_add, ha, hb]
      zero_mem' := by
        show T 0 = (0 : M)
        exact map_zero T
      neg_mem' := by
        intro a ha
        show T (-a) = -a
        rw [map_neg, ha] }
  have memY0 : ∀ y : M, y ∈ Y0 ↔ T y = y := fun _ => Iff.rfl
  have hdescent := card_submodule_eq_sq_card_fixed (F := F) hσ hσ2 (M := M) T hT hT2
    (⊤ : Submodule F M) (fun _ _ => Submodule.mem_top)
  let S : Type := {m : M // m ∈ (⊤ : Submodule F M) ∧ T m = m}
  have htop : Nat.card (⊤ : Submodule F M) = Nat.card M :=
    Nat.card_congr (Submodule.topEquiv (R := F) (M := M)).toEquiv
  have hcardM : Nat.card M = 4 ^ r := by
    show Nat.card (Fin r → F) = 4 ^ r
    rw [Nat.card_fun, hF, Nat.card_fin]
  have hcardS_sq : Nat.card S ^ 2 = (2 ^ r) ^ 2 := by
    change Nat.card {m : M // m ∈ (⊤ : Submodule F M) ∧ T m = m} ^ 2 = (2 ^ r) ^ 2
    rw [← hdescent, htop, hcardM]
    simp only [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm 2 r]
  have hcardS : Nat.card S = 2 ^ r :=
    Nat.pow_left_injective (n := 2) (by norm_num) hcardS_sq
  have hcardY0 : Nat.card Y0 = 2 ^ r := by
    have h : Nat.card Y0 = Nat.card S := by
      apply Nat.card_congr
      exact
        { toFun := fun y => ⟨y.1, Submodule.mem_top, (memY0 y.1).mp y.2⟩
          invFun := fun y => ⟨y.1, (memY0 y.1).mpr y.2.2⟩
          left_inv := fun y => by ext; rfl
          right_inv := fun y => by ext; rfl }
    rw [h, hcardS]
  have hfinrank : Module.finrank (ZMod 2) Y0 = r := by
    have h := FiniteField.pow_finrank_eq_natCard 2 Y0
    rw [hcardY0] at h
    exact Nat.pow_right_injective (le_refl 2) h
  have : Module.Finite (ZMod 2) Y0 :=
    Module.Finite.of_fg_top (by
      rw [← Submodule.span_univ]
      exact Submodule.fg_span (Set.finite_univ))
  let W := Fin r → ZMod 2
  let b : Y0 ≃ₗ[ZMod 2] W :=
    LinearEquiv.ofFinrankEq Y0 W (by rw [hfinrank, Module.finrank_fin_fun])
  let A : E →* (M ≃ₗ[F] M) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F M).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin r) (R := F)).toMonoidHom.comp E.subtype)
  have hA (e : E) (u : M) :
      (A e) u =
        ((e : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F) *ᵥ u := rfl
  have hcomm_symm (e : E) (w : M) : T ((A e).symm w) = (A e).symm (T w) := by
    have h : (A e) (T ((A e).symm w)) = T w := by
      have h0 := hcomm (e : Matrix.GeneralLinearGroup (Fin r) F) e.2 ((A e).symm w)
      rw [← hA e (T ((A e).symm w)), ← hA e ((A e).symm w),
        LinearEquiv.apply_symm_apply] at h0
      exact h0
    calc T ((A e).symm w) = (A e).symm ((A e) (T ((A e).symm w))) :=
          ((A e).symm_apply_apply _).symm
      _ = (A e).symm (T w) := by rw [h]
  have hmem (e : E) : ∀ y ∈ Y0, (A e) y ∈ Y0 := by
    intro y hy
    rw [memY0] at hy ⊢
    rw [hA e y, ← hcomm (e : Matrix.GeneralLinearGroup (Fin r) F) e.2 y, hy]
  have hminv (e : E) : ∀ y ∈ Y0, (A e).symm y ∈ Y0 := by
    intro y hy
    rw [memY0] at hy ⊢
    rw [hcomm_symm e y, hy]
  let fe (e : E) : Y0 →+ Y0 :=
    { toFun := fun y => ⟨(A e) y.1, hmem e y.1 y.2⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun a b => by
        apply Subtype.ext
        simp }
  let feinv (e : E) : Y0 →+ Y0 :=
    { toFun := fun y => ⟨(A e).symm y.1, hminv e y.1 y.2⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun a b => by
        apply Subtype.ext
        simp }
  let phiEquiv (e : E) : Y0 ≃ₗ[ZMod 2] Y0 :=
    { toLinearMap := (fe e).toZModLinearMap 2
      invFun := fun y => feinv e y
      left_inv := fun y => Subtype.ext (by simp [fe, feinv])
      right_inv := fun y => Subtype.ext (by simp [fe, feinv]) }
  let C : E →* (Y0 ≃ₗ[ZMod 2] Y0) :=
    MonoidHom.mk' phiEquiv (by
      intro e1 e2
      apply LinearEquiv.ext
      intro y
      apply Subtype.ext
      show (A (e1 * e2)) y.1 = (A e1) ((A e2) y.1)
      rw [map_mul]
      rfl)
  have hCe (e : E) (y : Y0) : ((C e) y : M) = (A e) y.1 := rfl
  have hspan := span_fixed_eq_of_semilinear_involution (F := F) hσ hσ2 (M := M) T hT hT2
    (⊤ : Submodule F M) (fun _ _ => Submodule.mem_top)
  have hinjC : Function.Injective C := by
    intro e1 e2 h
    have hfix : ∀ y : Y0, (A e1) y.1 = (A e2) y.1 := by
      intro y
      have h2 := congrArg Subtype.val (congrArg (fun f : Y0 ≃ₗ[ZMod 2] Y0 => f y) h)
      rwa [hCe e1 y, hCe e2 y] at h2
    have hlin : (A e1).toLinearMap = (A e2).toLinearMap := by
      apply LinearMap.ext_on hspan
      intro m hm
      exact hfix ⟨m, (memY0 m).mpr hm.2⟩
    have hAeq : A e1 = A e2 := by
      apply LinearEquiv.ext
      intro m
      exact congrArg (fun f : M →ₗ[F] M => f m) hlin
    have htoLin := congrArg (fun f : M ≃ₗ[F] M =>
        (LinearMap.GeneralLinearGroup.generalLinearEquiv F M).symm f) hAeq
    have htoLin' : (Matrix.GeneralLinearGroup.toLin (n := Fin r) (R := F)) (E.subtype e1) =
        (Matrix.GeneralLinearGroup.toLin (n := Fin r) (R := F)) (E.subtype e2) := by
      simpa [A] using htoLin
    exact Subtype.ext ((Matrix.GeneralLinearGroup.toLin (n := Fin r) (R := F)).injective htoLin')
  let V : (Y0 ≃ₗ[ZMod 2] Y0) ≃* (W ≃ₗ[ZMod 2] W) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Y0).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv b).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W))
  let R : Matrix.GeneralLinearGroup (Fin r) (ZMod 2) ≃* (W ≃ₗ[ZMod 2] W) :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin r) (R := ZMod 2)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W)
  let Ψ : E →* Matrix.GeneralLinearGroup (Fin r) (ZMod 2) :=
    R.symm.toMonoidHom.comp (V.toMonoidHom.comp C)
  have hinjΨ : Function.Injective Ψ :=
    R.symm.injective.comp (V.injective.comp hinjC)
  have hE' : IsElemAbelian 2 Ψ.range := by
    have htopE : IsElemAbelian 2 (⊤ : Subgroup E) := by
      have h := CFSG.Open.IsElemAbelian.comap hE (f := E.subtype) E.subtype_injective
      simpa [Subgroup.comap_subtype, Subgroup.subgroupOf_self] using h
    have h := CFSG.Open.IsElemAbelian.map htopE Ψ
    rwa [Subgroup.map_top] at h
  have hcard : Nat.card E = Nat.card Ψ.range :=
    Nat.card_congr (MonoidHom.ofInjective hinjΨ).toEquiv
  have hbound :=
    CFSG.HardMathSupport.GuralnickMalle.card_le_pow_half_sq (K := ZMod 2) (n := r) (p := 2)
      Nat.prime_two hE'
  rw [Nat.card_zmod] at hbound
  rw [hcard]
  exact hbound

end CFSG.LocalAnalysis.RankThreeUC.S15

end
