module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open LinearMap (BilinForm)

theorem isometry_of_similitude_of_orderOf_three {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    {B : LinearMap.BilinForm (ZMod 3) W} (hB : B ≠ 0) {x : (Module.End (ZMod 3) W)ˣ} {k : ℕ}
    (hx : orderOf x = 3 ^ k) {c : ZMod 3}
    (hc : ∀ u v : W, B ((x : Module.End (ZMod 3) W) u) ((x : Module.End (ZMod 3) W) v) =
      c * B u v) :
    ∀ u v : W, B ((x : Module.End (ZMod 3) W) u) ((x : Module.End (ZMod 3) W) v) = B u v := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : Module.End (ZMod 3) W := x
  have hfpow : ∀ m : ℕ, ∀ u v : W, B ((f ^ m) u) ((f ^ m) v) = c ^ m * B u v := by
    intro m
    induction m with
    | zero => intro u v; simp
    | succ m ih =>
        intro u v
        have hstep : B ((f ^ (m + 1)) u) ((f ^ (m + 1)) v) =
            B ((f ^ m) (f u)) ((f ^ m) (f v)) := by
          rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply]
        rw [hstep, ih (f u) (f v), hc u v, pow_succ]
        ring
  have hfix : f ^ (3 ^ k) = 1 := by
    have h1 : x ^ (3 ^ k) = 1 := by rw [← hx, pow_orderOf_eq_one]
    simpa [f] using congrArg Units.val h1
  have hc1 : c ^ (3 ^ k) = 1 := by
    by_contra hne
    apply hB
    refine BilinForm.ext fun u v => ?_
    have h := hfpow (3 ^ k) u v
    rw [hfix, Module.End.one_apply] at h
    have hzero : (c ^ (3 ^ k) - 1) * B u v = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr h.symm
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)
  have hc_eq : c = 1 := by
    have h := ZMod.pow_card_pow (p := 3) (n := k) c
    rw [← h]
    exact hc1
  intro u v
  rw [hc u v, hc_eq, one_mul]

theorem le_isometryGroup_comap_of_similitudes {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    {B : LinearMap.BilinForm (ZMod 3) W} (hB : B ≠ 0)
    {H : Subgroup (Module.End (ZMod 3) W)ˣ} (hH : oPPrimeHull 3 H = H)
    (hsim : ∀ x ∈ H, ∃ c : ZMod 3, ∀ u v : W,
      B ((x : Module.End (ZMod 3) W) u) ((x : Module.End (ZMod 3) W) v) = c * B u v) :
    H ≤ (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B).comap
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W).toMonoidHom := by
  rw [oPPrimeHull] at hH
  rw [← hH]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxH, k, hk⟩
  change LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W x ∈
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B
  rw [CFSG.ComponentClassification.CatalogueBAlternatingIsometry.mem_isometryGroup_iff]
  intro u v
  obtain ⟨c, hc⟩ := hsim x hxH
  simpa using isometry_of_similitude_of_orderOf_three hB hk hc u v

private theorem exists_symp_hom_and_range {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    [Finite W] {B : LinearMap.BilinForm (ZMod 3) W} (hBne : B ≠ 0)
    {H : Subgroup (Module.End (ZMod 3) W)ˣ} (hH : oPPrimeHull 3 H = H)
    (hsim : ∀ x ∈ H, ∃ c : ZMod 3, ∀ u v : W,
      B ((x : Module.End (ZMod 3) W) u) ((x : Module.End (ZMod 3) W) v) = c * B u v)
    (b : Module.Basis (Fin 2 ⊕ Fin 2) (ZMod 3) W)
    (hbJ : BilinForm.toMatrix b B = Matrix.J (Fin 2) (ZMod 3)) :
    ∃ ψ : ↥H →* ↥(Matrix.symplecticGroup (Fin 2) (ZMod 3)),
      Function.Injective ψ ∧ oPPrimeHull 3 ψ.range = ψ.range := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Module.End (ZMod 3) W) := by
    haveI : Finite (W → W) := inferInstance
    exact Finite.of_injective (fun f : Module.End (ZMod 3) W => (f : W → W))
      (fun f g h => by ext x; exact congrFun h x)
  haveI : Finite ↥H := inferInstance
  let e : (Module.End (ZMod 3) W)ˣ ≃* (W ≃ₗ[ZMod 3] W) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W
  let ψ₁ : ↥H →* ↥(CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B) :=
    { toFun := fun x => ⟨e x, le_isometryGroup_comap_of_similitudes hBne hH hsim x.2⟩
      map_one' := Subtype.ext e.map_one
      map_mul' := fun x y => Subtype.ext (e.map_mul x y) }
  let E : ↥(CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B) ≃*
      ↥(Matrix.symplecticGroup (Fin 2) (ZMod 3)) :=
    (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv b B hbJ).trans
      (TauCeti.GLSymplectic.mulEquivSymplecticGroup (Fin 2) (ZMod 3))
  let ψ : ↥H →* ↥(Matrix.symplecticGroup (Fin 2) (ZMod 3)) := E.toMonoidHom.comp ψ₁
  have hψ_inj : Function.Injective ψ := by
    have h₁ : Function.Injective ψ₁ := by
      intro x y hxy
      exact Subtype.ext (e.injective (congrArg Subtype.val hxy))
    exact E.injective.comp h₁
  refine ⟨ψ, hψ_inj, ?_⟩
  have hmap := oPPrimeHull_map_eq ψ (H := ⊤) (oPPrimeHull_top_of_eq hH)
  rwa [Subgroup.map_top] at hmap

theorem sympListAt_three : SympListAt 3 := by
  intro W _ _ _ hdim B hnd halt H hH hsim
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBne : B ≠ 0 := by
    intro hB0
    have hsub : Subsingleton W := ⟨fun u v => by
      have hu : u = 0 := hnd u (by simp [hB0])
      have hv : v = 0 := hnd v (by simp [hB0])
      rw [hu, hv]⟩
    haveI : Subsingleton W := hsub
    have h0 : Module.finrank (ZMod 3) W = 0 := Module.finrank_zero_of_subsingleton
    omega
  have hBnd : B.Nondegenerate :=
    LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft (show B.SeparatingLeft from hnd)
  haveI : Finite W := (Module.finite_iff_finite (R := ZMod 3) (M := W)).mp (inferInstance)
  obtain ⟨m, b, hdim', hbJ⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis
      B (show B.IsAlt from halt) hBnd
  have hm : m = 2 := by omega
  subst m
  obtain ⟨ψ, hψ_inj, hψ_range⟩ := exists_symp_hom_and_range hBne hH hsim b hbJ
  rw [SixThreeOneList]
  exact Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr
    ⟨ψ.range, hψ_range,
      nonempty_quot_pCore_mulEquiv_of_mulEquiv (MonoidHom.ofInjective hψ_inj)⟩))⟩))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
