module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019LinInnerThree
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

theorem eq_one_of_lastColHom_eq_scalar {E : Type*} [Field E] {m : ℕ} (last : Fin m)
    (c : Multiplicative (lastColVecs (E := E) last)) (r : E)
    (hr : ((lastColHom last c : Matrix.SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) =
      Matrix.scalar (Fin m) r) : c = 1 := by
  classical
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  funext b
  by_cases hb : b = last
  · rw [hb]
    exact (Multiplicative.toAdd c).2
  · have h1 := lastColHom_apply_ne last c hb
    rw [hr, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hb] at h1
    exact h1.symm

section Paired

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem sq_sub_one_eq_zero_of_paired (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (hne : (a : K[X]) ≠ dualPoly hK.bar (a : K[X]))
    {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])})
    (N : primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
      primaryComponent (x : Module.End K V) (a : K[X])) (hNN : ∀ w, N (N w) = 0)
    (hga : ∀ w : primaryComponent (x : Module.End K V) (a : K[X]),
      (g : Module.End K V) (w : V) = (w : V) +
        ((N w : primaryComponent (x : Module.End K V) (a : K[X])) : V)) :
    ((g : Module.End K V) - 1) ^ 2 = 0 := by
  classical
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  set W := primaryComponent (x : Module.End K V) (a : K[X]) with hW
  have hgC : Commute (g : Module.End K V) (x : Module.End K V) :=
    (mem_unitaryCentralizer.mp hg.1).2
  have hgB : ∀ v w, B ((g : Module.End K V) v) ((g : Module.End K V) w) = B v w :=
    (mem_unitaryCentralizer.mp hg.1).1
  refine ext_primaryComponent H.squarefree fun c hc v hv => ?_
  simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply]
  set G := (g : Module.End K V) with hG
  by_cases hca : c = a
  · subst hca
    set w : W := ⟨v, hv⟩
    have e1 := hga w
    have e2 := hga (N w)
    change _ = (w : V) + _ at e1
    rw [e1, add_sub_cancel_left, e2, hNN, Submodule.coe_zero, add_zero, sub_self]
  · by_cases hcd : c = dualPoly hK.bar (a : K[X])
    ·
      subst hcd
      have hz : G (G v - v) - (G v - v) ∈
          primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X])) := by
        have h1 := apply_mem_primaryComponent hgC hv
        have h2 := Submodule.sub_mem _ h1 hv
        exact Submodule.sub_mem _ (apply_mem_primaryComponent hgC h2) h2
      set z := G (G v - v) - (G v - v) with hzdef
      have hginv : ∀ u : W, G (((u - N u : W)) : V) = (u : V) := fun u => by
        rw [hga, map_sub, hNN, sub_zero, Submodule.coe_sub, sub_add_cancel]
      have hadj : ∀ (u : W) (y : V), B (u : V) (G y) = B (((u - N u : W)) : V) y := by
        intro u y
        rw [← hginv u, hgB]
      have hNsub : ∀ u : W, N (u - N u) = N u := fun u => by rw [map_sub, hNN, sub_zero]
      have hBz : ∀ u : W, B (u : V) z = 0 := by
        intro u
        have t1 : B (u : V) (G (G v - v)) =
            B ((u - N u : W) : V) (G v) - B ((u - N u : W) : V) v := by
          rw [hadj, map_sub]
        have t2 : B ((u - N u : W) : V) (G v) = B ((u - N u - N u : W) : V) v := by
          rw [hadj, hNsub]
        have t3 : B (u : V) (G v - v) = B ((u - N u : W) : V) v - B (u : V) v := by
          rw [map_sub, hadj]
        rw [hzdef, map_sub, t1, t2, t3]
        simp only [Submodule.coe_sub, map_sub, LinearMap.sub_apply]
        abel
      have hzsup : z ∈ primaryComponent (x : Module.End K V) (a : K[X]) ⊔
          primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X])) :=
        Submodule.mem_sup_right hz
      have hsep := separatingLeft_primaryComponent_sup H a.2 hne
      have hz0 : (⟨z, hzsup⟩ : ↥(primaryComponent (x : Module.End K V) (a : K[X]) ⊔
          primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X])))) = 0 := by
        refine hsep _ fun y => ?_
        change B z (y : V) = 0
        obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := Submodule.mem_sup.mp y.2
        rw [← hy, map_add]
        have h1 : B z y₁ = 0 := H.symm.eq_iff.1 (hBz ⟨y₁, hy₁⟩)
        have h2 : B z y₂ = 0 := by
          have hb := dualPoly_mem_primaryFactors H a.2
          have hne' : dualPoly hK.bar (a : K[X]) ≠
              dualPoly hK.bar (dualPoly hK.bar (a : K[X])) := by
            rw [dualPoly_dualPoly_of_mem H a.2]
            exact hne.symm
          exact isotropic_primaryComponent H hb hne' hz hy₂
        rw [h1, h2, add_zero]
      exact congrArg Subtype.val hz0
    · have e1 : G v = v := hg.2 c hc (by
        rintro (h | h)
        · exact hca h
        · exact hcd h) v hv
      rw [e1, sub_self, map_zero, sub_self]

theorem exists_pGroup_specialBlock_paired [CharP K 3] (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (hne : (a : K[X]) ≠ dualPoly hK.bar (a : K[X]))
    (hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])) (hq : 2 ≤ ℓ ^ f)
    (hfacts : SpecialBlockFacts B x a) :
    ∃ P : Subgroup (LinearMap.GeneralLinearGroup K V), P ≤ specialBlock B x (a : K[X]) ∧
      IsPGroup 3 P ∧ 9 ≤ Nat.card P ∧
      (∀ u ∈ P, (∀ g ∈ specialBlock B x (a : K[X]), u * g = g * u) → u = 1) ∧
      ∀ u ∈ P, (((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) - 1) ^ 2 = 0 := by
  classical
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  haveI := hK.finite
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  haveI : CharP (AdjoinRoot (a : K[X])) 3 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (a : K[X]))).injective 3
  set W := primaryComponent (x : Module.End K V) (a : K[X]) with hW
  let b : Module.Basis (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
      (AdjoinRoot (a : K[X])) W := Module.finBasisOfFinrankEq _ _ rfl
  let last : Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])) :=
    ⟨primaryMultiplicity (x : Module.End K V) (a : K[X]) - 1, by omega⟩
  let Ψ : Multiplicative (lastColVecs (E := AdjoinRoot (a : K[X])) last) →*
      LinearMap.GeneralLinearGroup K V :=
    (supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])}).subtype.comp
      ((pairedFactorEquiv H a.2 hne).symm.toMonoidHom.comp
        (_root_.SpecialLinearGroup.toGeneralLinearGroup.comp
          ((Matrix.SpecialLinearGroup.toLin_equiv b).toMonoidHom.comp (lastColHom last))))
  have hΨS : ∀ c, Ψ c ∈ supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])} :=
    fun c => ((pairedFactorEquiv H a.2 hne).symm (_root_.SpecialLinearGroup.toGeneralLinearGroup
      ((Matrix.SpecialLinearGroup.toLin_equiv b) (lastColHom last c)))).2
  have hΨinj : Function.Injective Ψ := by
    intro c c' hcc
    apply lastColHom_injective last
    apply (Matrix.SpecialLinearGroup.toLin_equiv b).injective
    apply _root_.SpecialLinearGroup.toGeneralLinearGroup_injective
    apply (pairedFactorEquiv H a.2 hne).symm.injective
    exact Subtype.ext hcc
  have hΨa : ∀ c (w : W), ((Ψ c : LinearMap.GeneralLinearGroup K V) : Module.End K V) (w : V) =
      ((Matrix.toLin b b ((lastColHom last c : Matrix.SpecialLinearGroup _ _) :
        Matrix _ _ (AdjoinRoot (a : K[X]))) w : W) : V) := by
    intro c w
    have h1 := blockApply_pairedFactorEquiv H a.2 hne
      ((pairedFactorEquiv H a.2 hne).symm (_root_.SpecialLinearGroup.toGeneralLinearGroup
        ((Matrix.SpecialLinearGroup.toLin_equiv b) (lastColHom last c)))) (w : V) w.2
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  refine ⟨Ψ.range, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨c, rfl⟩
    rw [mem_specialBlock]
    have hgS := hΨS c
    refine ⟨hgS, hgS.1.2, ?_⟩
    apply Units.ext
    change LinearMap.det ((blockRestrict x (a : K[X]) ⟨Ψ c, hgS.1.2⟩ :
      blockGL (x : Module.End K V) (a : K[X])) : Module.End (AdjoinRoot (a : K[X])) W) = 1
    have hres : blockRestrict x (a : K[X]) ⟨Ψ c, hgS.1.2⟩ =
        _root_.SpecialLinearGroup.toGeneralLinearGroup
          ((Matrix.SpecialLinearGroup.toLin_equiv b) (lastColHom last c)) := by
      apply blockGL_ext
      intro v hv
      rw [blockApply_blockRestrict]
      exact hΨa c ⟨v, hv⟩
    rw [hres]
    change LinearMap.det ((((Matrix.SpecialLinearGroup.toLin_equiv b) (lastColHom last c) :
      _root_.SpecialLinearGroup (AdjoinRoot (a : K[X])) W) :
        W ≃ₗ[AdjoinRoot (a : K[X])] W) : Module.End (AdjoinRoot (a : K[X])) W) = 1
    rw [← LinearEquiv.coe_det]
    exact congrArg Units.val ((Matrix.SpecialLinearGroup.toLin_equiv b) (lastColHom last c)).2
  ·
    intro y
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨c, hc⟩ := y.2
    rw [pow_one, Subgroup.coe_pow, ← hc, ← map_pow, lastColHom_pow_three, map_one]
    rfl
  ·
    rw [← Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv,
      ← Nat.card_congr (Multiplicative.toAdd : Multiplicative _ ≃ _)]
    refine nine_le_card_lastColVecs last rfl (Or.inr ⟨hm, ?_⟩)
    have h1 : Nat.card K ≤ Nat.card (AdjoinRoot (a : K[X])) :=
      Nat.card_le_card_of_injective _ (algebraMap K (AdjoinRoot (a : K[X]))).injective
    rw [hK.card, pow_mul'] at h1
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (ℓ ^ f) ^ 2 := Nat.pow_le_pow_left hq 2
      _ ≤ _ := h1
  ·
    rintro _ ⟨c, rfl⟩ hcent
    obtain ⟨r, hr⟩ := hfacts.scalar (Ψ c) (hΨS c).1 fun _ g hg => hcent g hg
    have hsc : ((lastColHom last c : Matrix.SpecialLinearGroup _ _) :
        Matrix (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
          (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X]))) =
        Matrix.scalar _ r := by
      apply (Matrix.toLin b b).injective
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      rw [← hΨa c w, hr w, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, map_smul,
        Matrix.toLin_one, LinearMap.smul_apply, LinearMap.id_apply]
    rw [eq_one_of_lastColHom_eq_scalar last c r hsc, map_one]
  ·
    rintro _ ⟨c, rfl⟩
    set N : W →ₗ[AdjoinRoot (a : K[X])] W := Matrix.toLin b b
      (Matrix.vecMulVec ((Multiplicative.toAdd c : lastColVecs last) :
        Fin _ → AdjoinRoot (a : K[X])) (Pi.single last 1)) with hNdef
    have hNN : ∀ w : W, N (N w) = 0 := by
      intro w
      have e1 : N.comp N = 0 := by
        rw [hNdef, ← Matrix.toLin_mul, vecMulVec_single_mul last (Multiplicative.toAdd c).2,
          map_zero]
      exact LinearMap.congr_fun e1 w
    refine sq_sub_one_eq_zero_of_paired H a hne (hΨS c) N hNN fun w => ?_
    rw [hΨa, coe_lastColHom, map_add, Matrix.toLin_one, LinearMap.add_apply, LinearMap.id_apply,
      Submodule.coe_add]

end Paired

end CFSG.LocalAnalysis.GLTheoremA.S2019
