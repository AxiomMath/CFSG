module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors
import CFSG.HardMathSupport.Solomon.Proving.PSL2CentSolvableProof
import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.Assembly.OrderReductions.LinearOrders
import CFSG.LargeExtraspecial.O62Basic
public import CFSG.ClassicalGroups.Orthogonal.Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.RankThree.Classical2

private theorem isSolvable_of_ker_le_center' {G G' : Type*} [Group G] [Group G'] (π : G →* G')
    (hZ : π.ker ≤ Subgroup.center G) [Group.IsSolvable G'] : Group.IsSolvable G := by
  have : Group.IsSolvable ↥π.ker :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hZ b.2) a)
  exact Group.isSolvable_of_ker_le_range π.ker.subtype π (by rw [Subgroup.range_subtype])

private theorem centSolvable_statedProj {F : Type} [Field F] [Finite F]
    {c : StatedProj (StatedSL 2 F)} (hc : c ≠ 1) :
    Group.IsSolvable ↥(Subgroup.centralizer ({c} : Set (StatedProj (StatedSL 2 F)))) := by
  let φ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* StatedProj (StatedSL 2 F) :=
    projectiveSpecialLinearGroupEquivStatedProj 2 F
  have hc' : φ.symm c ≠ 1 := fun h => hc (by simpa using congrArg φ h)
  have : Group.IsSolvable ↥(Subgroup.centralizer
      ({φ.symm c} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) :=
    CFSG.HardMathSupport.Solomon.Proving.psl2CentSolvable_holds F (φ.symm c) hc'
  let f : ↥(Subgroup.centralizer ({c} : Set (StatedProj (StatedSL 2 F)))) →*
      ↥(Subgroup.centralizer ({φ.symm c} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) :=
    ((φ.symm.toMonoidHom).comp (Subgroup.subtype _)).codRestrict _ (fun x => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.1 x.2
      change φ.symm (x : StatedProj (StatedSL 2 F)) * φ.symm c = φ.symm c * φ.symm x
      rw [← map_mul, ← map_mul, this])
  exact Group.isSolvable_of_isSolvable_injective (f := f) (fun x y h =>
    Subtype.ext (φ.symm.injective (congrArg Subtype.val h)))

section Group

variable {Y : Type} [Group Y] [Finite Y] {r : ℕ}

private theorem not_isSolvable_of_quasisimple {G : Type*} [Group G] (hG : CFSG.IsQuasisimple G) :
    ¬ Group.IsSolvable G := by
  intro hs
  obtain ⟨-, hsimple, a, b, hab⟩ := hG
  have : Group.IsSolvable (G ⧸ Subgroup.center G) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (Subgroup.center G))
      (QuotientGroup.mk'_surjective _)
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := G ⧸ Subgroup.center G)).2 this a b)

theorem false_of_isTypeL2_of_commuting_homs (h : IsTypeL2 r Y) {G₁ G₂ : Type*} [Group G₁]
    [Group G₂] (f₁ : G₁ →* Y) (f₂ : G₂ →* Y) (hf₁ : Function.Injective f₁)
    (hf₂ : Function.Injective f₂) (hG₁ : ¬ Group.IsSolvable G₁) (hG₂ : ¬ Group.IsSolvable G₂)
    (hcomm : ∀ x y, f₁ x * f₂ y = f₂ y * f₁ x) : False := by
  obtain ⟨F, hFf, hFfin, hcF, ⟨e⟩⟩ := h
  have hy : ∃ y : G₂, f₂ y ∉ Subgroup.center Y := by
    by_contra hcon
    push Not at hcon
    refine hG₂ (Group.isSolvable_of_comm fun a b => hf₂ ?_)
    rw [map_mul, map_mul]
    exact ((Subgroup.mem_center_iff.1 (hcon a)) (f₂ b)).symm
  obtain ⟨y, hyZ⟩ := hy
  have hc : e (QuotientGroup.mk (f₂ y)) ≠ 1 := fun h1 =>
    hyZ ((QuotientGroup.eq_one_iff _).1 (e.map_eq_one_iff.1 h1))
  have hsol := centSolvable_statedProj hc
  have hcomm' : ∀ x : G₁, e (QuotientGroup.mk (f₁ x)) * e (QuotientGroup.mk (f₂ y)) =
      e (QuotientGroup.mk (f₂ y)) * e (QuotientGroup.mk (f₁ x)) := fun x => by
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm x y]
  let f : G₁ →* ↥(Subgroup.centralizer ({e (QuotientGroup.mk (f₂ y))} :
      Set (StatedProj (StatedSL 2 F)))) :=
    { toFun := fun x => ⟨e (QuotientGroup.mk (f₁ x)),
        Subgroup.mem_centralizer_singleton_iff.2 (hcomm' x)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x z => Subtype.ext (by simp) }
  have := hsol
  refine hG₁ (isSolvable_of_ker_le_center' f ?_)
  intro x hx
  have h1 : e (QuotientGroup.mk (f₁ x)) = 1 := congrArg Subtype.val hx
  have h2 : f₁ x ∈ Subgroup.center Y := (QuotientGroup.eq_one_iff _).1 (e.map_eq_one_iff.1 h1)
  rw [Subgroup.mem_center_iff] at h2 ⊢
  intro z
  apply hf₁
  rw [map_mul, map_mul]
  exact h2 (f₁ z)

theorem card_ge_of_isTypeL2 (h : IsTypeL2 r Y) (hr : 64 ≤ r) : 131040 ≤ Nat.card Y := by
  obtain ⟨F, hFf, hFfin, hcF, ⟨e⟩⟩ := h
  have h1 : Nat.card (StatedProj (StatedSL 2 F)) ≤ Nat.card Y := by
    rw [← Nat.card_congr e.toEquiv]
    exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 : 131040 ≤ Nat.card (StatedProj (StatedSL 2 F)) := by
    rw [← Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj 2 F).toEquiv,
      OrderReductions.LinearOrders.card_projectiveSpecialLinear F 2 (by norm_num)]
    simp only [Finset.Icc_self, Finset.prod_singleton]
    have hF : 64 ≤ Nat.card F := by rw [hcF]; exact hr
    generalize Nat.card F = q at hF ⊢
    have h1 : 2 * (2 - 1) / 2 = 1 := by norm_num
    rw [h1, pow_one]
    have hg : Nat.gcd 2 (q - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hgpos : 0 < Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    rw [Nat.le_div_iff_mul_le hgpos]
    have h4095 : 4095 ≤ q ^ 2 - 1 := by
      have : 64 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hF 2
      omega
    calc 131040 * Nat.gcd 2 (q - 1) ≤ 131040 * 2 := Nat.mul_le_mul_left _ hg
      _ = 64 * 4095 := by norm_num
      _ ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hF h4095
  omega

end Group

section Pairs

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

private def mapPair {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (ι : Q.IsometryEquiv Q') (P : HypPair Q) :
    HypPair Q' where
  e := ι P.e
  f := ι P.f
  Q_e := by rw [ι.map_app]; exact P.Q_e
  Q_f := by rw [ι.map_app]; exact P.Q_f
  polar_ef := by
    have : polar Q' (ι P.e) (ι P.f) = polar Q P.e P.f := by
      rw [polar, polar, ← map_add, ι.map_app, ι.map_app, ι.map_app]
    rw [this]
    exact P.polar_ef

private theorem mapPair_orth {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (ι : Q.IsometryEquiv Q')
    {P P' : HypPair Q} (h : P.Orth P') : (mapPair ι P).Orth (mapPair ι P') := by
  have key : ∀ x y, polar Q' (ι x) (ι y) = polar Q x y := fun x y => by
    rw [polar, polar, ← map_add, ι.map_app, ι.map_app, ι.map_app]
  exact ⟨(key _ _).trans h.ee, (key _ _).trans h.ef, (key _ _).trans h.fe, (key _ _).trans h.ff⟩

theorem exists_orth_hypPairs_six (R : QuadraticForm K W) (hR : (polarBilin R).Nondegenerate)
    (hd : finrank K W = 6) : ∃ P₁ P₂ : HypPair R, P₁.Orth P₂ := by
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus R hR (n := 3)
    (by norm_num) (by rw [hd]) with ⟨⟨e⟩⟩ | ⟨b, c, -, ⟨e⟩⟩
  · exact ⟨mapPair e.symm (plusPair K (⟨0, by norm_num⟩ : Fin 3)),
      mapPair e.symm (plusPair K (⟨1, by norm_num⟩ : Fin 3)),
      mapPair_orth e.symm (plusPair_orth (by simp [Fin.ext_iff]))⟩
  · exact ⟨mapPair e.symm (minusPair K b c (⟨0, by norm_num⟩ : Fin (3 - 1))),
      mapPair e.symm (minusPair K b c (⟨1, by norm_num⟩ : Fin (3 - 1))),
      mapPair_orth e.symm (minusPair_orth (by simp [Fin.ext_iff]))⟩

end Pairs

section Geometry

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W}

theorem not_isTypeL2_orthDerived_of_pairs (hR : (polarBilin R).Nondegenerate)
    (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) {P₁ P₂ : HypPair R} (h : P₁.Orth P₂)
    {r : ℕ} : ¬ IsTypeL2 r ↥(orthDerived R) := by
  intro hT
  classical
  haveI : Finite W := Module.finite_of_finite K
  haveI : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun f : W ≃ₗ[K] W => (f : W → W)) fun f g hfg =>
      LinearEquiv.ext (congrFun hfg)
  have hinj := matrixToOriginal_injective P₁ P₂ h
  set S : Submodule K W := LinearMap.range (matrixToOriginal P₁ P₂) with hS
  let ePsi : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] S :=
    LinearEquiv.ofInjective (matrixToOriginal P₁ P₂) hinj
  let psi : (R.comp S.subtype).IsometryEquiv (determinantForm K) :=
    { toLinearEquiv := ePsi.symm
      map_app' := fun w => by
        obtain ⟨X, rfl⟩ := ePsi.surjective w
        show determinantForm K (ePsi.symm (ePsi X)) = R ((ePsi X : S) : W)
        rw [LinearEquiv.symm_apply_apply, determinantForm_apply]
        exact (matrixToOriginal_form P₁ P₂ h X).symm }
  have hSnd : (polarBilin (R.comp S.subtype)).Nondegenerate :=
    nondegenerate_polarBilin_of_isometryEquiv_univ psi.symm determinantForm_nondegenerate
  have hSc : IsCompl S (orthPerp R S) := isCompl_orthPerp hSnd
  let Θ := TauCeti.QuadraticMap.orthogonalGroupCongr psi
  let F : DeterminantIsometries K →* (W ≃ₗ[K] W) :=
    (extendHom hSc).comp Θ.symm.toMonoidHom
  have hFinj : Function.Injective F := (extendHom_injective hSc).comp Θ.symm.injective
  have hFO : ∀ g, F g ∈ TauCeti.QuadraticMap.orthogonalGroup R := fun g => extendHom_mem hSc _
  have hperf : ⁅specialImage K, specialImage K⁆ = specialImage K :=
    Subgroup.isPerfect_iff.mp (determinantSpecialImage_isPerfect hK2 hK3)
  have hmapΩ : (specialImage K).map F ≤ orthDerived R := by
    have hle : (specialImage K).map F ≤ TauCeti.QuadraticMap.orthogonalGroup R := by
      rintro _ ⟨g, -, rfl⟩
      exact hFO g
    calc (specialImage K).map F = (⁅specialImage K, specialImage K⁆).map F := by rw [hperf]
      _ = ⁅(specialImage K).map F, (specialImage K).map F⁆ := Subgroup.map_commutator _ _ _
      _ ≤ orthDerived R := Subgroup.commutator_mono hle hle
  let f₁ : ↥(determinantLeftFactor K) →* ↥(orthDerived R) :=
    (F.comp (determinantLeftFactor K).subtype).codRestrict (orthDerived R) fun x =>
      hmapΩ ⟨x.1, determinantLeftFactor_le x.2, rfl⟩
  let f₂ : ↥(determinantRightFactor K) →* ↥(orthDerived R) :=
    (F.comp (determinantRightFactor K).subtype).codRestrict (orthDerived R) fun x =>
      hmapΩ ⟨x.1, determinantRightFactor_le x.2, rfl⟩
  refine false_of_isTypeL2_of_commuting_homs hT f₁ f₂ ?_ ?_
    (not_isSolvable_of_quasisimple (determinantLeftFactor_quasisimple hK2 hK3))
    (not_isSolvable_of_quasisimple (determinantRightFactor_quasisimple hK2 hK3)) ?_
  · intro a b hab
    have : F a.1 = F b.1 := congrArg Subtype.val hab
    exact Subtype.ext (hFinj this)
  · intro a b hab
    have : F a.1 = F b.1 := congrArg Subtype.val hab
    exact Subtype.ext (hFinj this)
  · intro x y
    apply Subtype.ext
    show F x.1 * F y.1 = F y.1 * F x.1
    rw [← map_mul, ← map_mul, determinantFactors_commute x.2 y.2]

end Geometry

section Two

open Module QuadraticMap

theorem card_orthogonalGroup_le_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W)
    (hR : (polarBilin R).Nondegenerate) (hd : finrank K W = 6) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) ≤ 51840 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  let σ : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hcard
  letI : Algebra (ZMod 2) K := σ.toRingHom.toAlgebra
  letI : Module (ZMod 2) W := Module.compHom W (algebraMap (ZMod 2) K)
  haveI : IsScalarTower (ZMod 2) K W := IsScalarTower.of_algebraMap_smul fun r x => rfl
  let fE : K ≃ₗ[ZMod 2] ZMod 2 :=
    { toFun := σ.symm
      map_add' := map_add σ.symm
      map_smul' := fun a x => by
        show σ.symm (a • x) = a • σ.symm x
        have h1 : algebraMap (ZMod 2) K a = σ a := rfl
        rw [Algebra.smul_def, map_mul, h1, σ.symm_apply_apply, smul_eq_mul]
      invFun := σ
      left_inv := σ.apply_symm_apply
      right_inv := σ.symm_apply_apply }
  haveI : FiniteDimensional (ZMod 2) W := by
    haveI : Finite W := Module.finite_of_finite K
    exact Module.Finite.of_finite
  have hfin : finrank (ZMod 2) W = 6 := by
    rw [← Module.finrank_mul_finrank (ZMod 2) K W, hd, fE.finrank_eq, finrank_self]
  let Q' : QuadraticForm (ZMod 2) W := fE.toLinearMap.compQuadraticMap' R
  have hQ'apply : ∀ x, Q' x = σ.symm (R x) := fun x => rfl
  have hp : ∀ x y, polar Q' x y = σ.symm (polar R x y) := fun x y => by
    simp only [polar, hQ'apply]
    rw [map_sub, map_sub]
  have hnd : ∀ x, (∀ y, polar Q' x y = 0) → x = 0 := by
    intro x hx
    refine hR.1 x fun y => ?_
    have h1 := hx y
    rw [hp] at h1
    rw [polarBilin_apply_apply]
    exact σ.symm.injective (by rw [h1, map_zero])
  have hQ'nd := CFSG.LargeExtraspecial.O62.nondegenerate_of_forall hnd
  let Φ : ↥(TauCeti.QuadraticMap.orthogonalGroup R) → ↥(TauCeti.QuadraticMap.orthogonalGroup Q') :=
    fun g => ⟨(g : W ≃ₗ[K] W).restrictScalars (ZMod 2), by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro x
      show σ.symm (R ((g : W ≃ₗ[K] W) x)) = σ.symm (R x)
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup g.2]⟩
  have hΦ : Function.Injective Φ := fun a b hab =>
    Subtype.ext (LinearEquiv.ext fun x => congrArg
      (fun g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q') => (g : W ≃ₗ[ZMod 2] W) x) hab)
  haveI : Finite W := Module.finite_of_finite K
  haveI : Finite (W ≃ₗ[ZMod 2] W) := CFSG.LargeExtraspecial.O62.finite_linearEquiv
  have hcardQ' := CFSG.LargeExtraspecial.O62.card_orthogonalGroup hfin hQ'nd
  calc Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R)
      ≤ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q') := Nat.card_le_card_of_injective Φ hΦ
    _ ≤ 51840 := by rcases hcardQ' with h | h <;> omega

end Two

theorem not_isTypeL2_orthDerived_six {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hd : Module.finrank K W = 6)
    (hK3 : ringChar K ≠ 3) {r : ℕ} (hr : 64 ≤ r) : ¬ IsTypeL2 r ↥(orthDerived R) := by
  by_cases hK2 : Nat.card K = 2
  · intro hT
    haveI : Finite W := Module.finite_of_finite K
    haveI : Finite (W ≃ₗ[K] W) :=
      Finite.of_injective (fun f : W ≃ₗ[K] W => (f : W → W)) fun f g hfg =>
        LinearEquiv.ext (congrFun hfg)
    have h1 := card_orthogonalGroup_le_of_card_two hK2 R hR hd
    have h2 := card_ge_of_isTypeL2 hT hr
    have h3 : Nat.card ↥(orthDerived R) ≤
        Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
      Subgroup.card_le_of_le (Subgroup.commutator_le_self _)
    omega
  · have hK3' : Nat.card K ≠ 3 := by
      intro h3
      apply hK3
      haveI := Fintype.ofFinite K
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      haveI : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact h3)
      exact ringChar.eq K 3
    obtain ⟨P₁, P₂, h⟩ := exists_orth_hypPairs_six R hR hd
    exact not_isTypeL2_orthDerived_of_pairs hR hK2 hK3' h

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
