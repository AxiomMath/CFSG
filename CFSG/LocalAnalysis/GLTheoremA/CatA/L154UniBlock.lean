module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.HardMathSupport.Dickson.Bal207.SemilinCoord
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open Polynomial Module CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open scoped Classical

section Ext

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {x : LinearMap.GeneralLinearGroup K V}

@[expose] noncomputable def l154BlockExt (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (a : primaryFactors (x : Module.End K V)) :
    blockGL (x : Module.End K V) (a : K[X]) →* LinearMap.GeneralLinearGroup K V :=
  (gl_centralizer x).subtype.comp (((glCentralizerEquivPi hsq).symm).toMonoidHom.comp
    (MonoidHom.mulSingle (fun b : primaryFactors (x : Module.End K V) =>
      blockGL (x : Module.End K V) (b : K[X])) a))

theorem l154BlockExt_apply_self (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (a : primaryFactors (x : Module.End K V)) (γ : blockGL (x : Module.End K V) (a : K[X])) (v : V)
    (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])) :
    ((l154BlockExt hsq a γ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
      blockApply γ v hv := by
  have h := blockApply_glCentralizerEquivPi hsq
    ((glCentralizerEquivPi hsq).symm (Pi.mulSingle a γ)) a v hv
  rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same] at h
  exact h.symm

theorem l154BlockExt_apply_ne (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (a : primaryFactors (x : Module.End K V)) (γ : blockGL (x : Module.End K V) (a : K[X]))
    (b : primaryFactors (x : Module.End K V)) (hb : b ≠ a) (v : V)
    (hv : v ∈ primaryComponent (x : Module.End K V) (b : K[X])) :
    ((l154BlockExt hsq a γ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
  have h := blockApply_glCentralizerEquivPi hsq
    ((glCentralizerEquivPi hsq).symm (Pi.mulSingle a γ)) b v hv
  rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_of_ne hb] at h
  exact h.symm.trans (blockApply_one v hv)

theorem l154BlockExt_mem_centralizer (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (a : primaryFactors (x : Module.End K V)) (γ : blockGL (x : Module.End K V) (a : K[X])) :
    l154BlockExt hsq a γ ∈ gl_centralizer x :=
  ((glCentralizerEquivPi hsq).symm (Pi.mulSingle a γ)).2

theorem l154BlockExt_injective (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (a : primaryFactors (x : Module.End K V)) : Function.Injective (l154BlockExt hsq a) := by
  intro γ γ' h
  apply blockGL_ext
  intro v hv
  rw [← l154BlockExt_apply_self hsq a γ v hv, ← l154BlockExt_apply_self hsq a γ' v hv, h]

theorem l154BlockExt_eq (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (a : primaryFactors (x : Module.End K V)) {g : LinearMap.GeneralLinearGroup K V}
    (γ : blockGL (x : Module.End K V) (a : K[X]))
    (hoff : ∀ b ∈ primaryFactors (x : Module.End K V), b ≠ (a : K[X]) →
      ∀ v ∈ primaryComponent (x : Module.End K V) b, (g : Module.End K V) v = v)
    (hγ : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      blockApply γ v hv = (g : Module.End K V) v) : l154BlockExt hsq a γ = g := by
  refine Units.ext (ext_primaryComponent hsq fun b hb v hv => ?_)
  by_cases hba : b = (a : K[X])
  · subst hba
    exact (l154BlockExt_apply_self hsq a γ v hv).trans (hγ v hv)
  · have hne : (⟨b, hb⟩ : primaryFactors (x : Module.End K V)) ≠ a := fun h => hba (congrArg Subtype.val h)
    exact (l154BlockExt_apply_ne hsq a γ ⟨b, hb⟩ hne v hv).trans (hoff b hb hba v hv).symm

end Ext

section Models

open CFSG.HardMathSupport.Dickson.Bal207.FirstClaim CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ComponentClassification.Burgoyne.U

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type*} [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem specialBlock_eq_map_l154BlockExt (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (a : primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar (a : K[X]) = a)
    {hE : UnitaryFieldData ℓ (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X]))}
    {Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
      primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])] AdjoinRoot (a : K[X])}
    {m : ℕ} (e : Module.Basis (Fin m) (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])))
    (he : ∀ i j, Hf (e i) (e j) = if i = j then 1 else 0)
    (φ : supportedUnitary B x {(a : K[X])} ≃* sesqUnitaryGroup Hf)
    (hφ : ∀ (g : supportedUnitary B x {(a : K[X])}) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
        blockApply (φ g : blockGL (x : Module.End K V) (a : K[X])) v hv =
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) :
    specialBlock B x (a : K[X]) =
      (StatedSU m (ℓ ^ (f * (a : K[X]).natDegree)) (AdjoinRoot (a : K[X]))).map
        ((l154BlockExt hsq a).comp
          (Matrix.GeneralLinearGroup.toLin' e).toMonoidHom) := by
  classical
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  have hsupp : orbitFactor B x (a : K[X]) = supportedUnitary B x {(a : K[X])} := by
    unfold orbitFactor
    rw [hself, Set.pair_eq_singleton]
  let T := Matrix.GeneralLinearGroup.toLin' e
  have hone : ∀ i j, Hf (e i) (e j) = ((1 : GL (Fin m) (AdjoinRoot (a : K[X]))) :
      Matrix (Fin m) (Fin m) (AdjoinRoot (a : K[X]))) i j := by
    intro i j
    rw [he, Units.val_one, Matrix.one_apply]
  have hSUeq : StatedSU m (ℓ ^ (f * (a : K[X]).natDegree)) (AdjoinRoot (a : K[X])) =
      gramSU hE ((1 : GL (Fin m) (AdjoinRoot (a : K[X]))) :
        Matrix (Fin m) (Fin m) (AdjoinRoot (a : K[X]))) := statedSU_eq_gramSU hE
  ext g
  constructor
  · intro hg
    obtain ⟨hgo, hgc, hdet⟩ := mem_specialBlock.mp hg
    have hgs : g ∈ supportedUnitary B x {(a : K[X])} := by rw [← hsupp]; exact hgo
    have hτg : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
        blockApply (φ ⟨g, hgs⟩ : blockGL (x : Module.End K V) (a : K[X])) v hv =
          (g : Module.End K V) v := fun v hv => hφ ⟨g, hgs⟩ v hv
    have hTP : T (T.symm (φ ⟨g, hgs⟩ : blockGL (x : Module.End K V) (a : K[X]))) =
        (φ ⟨g, hgs⟩ : blockGL (x : Module.End K V) (a : K[X])) := MulEquiv.apply_symm_apply _ _
    refine ⟨T.symm (φ ⟨g, hgs⟩ : blockGL (x : Module.End K V) (a : K[X])), ?_, ?_⟩
    · rw [SetLike.mem_coe, hSUeq, mem_gramSU]
      refine ⟨?_, ?_⟩
      · exact (toLin'_mem_sesqUnitaryGroup_iff e hE hone _).1 (by rw [hTP]; exact (φ ⟨g, hgs⟩).2)
      · have h1 : ((T.symm (φ ⟨g, hgs⟩ : blockGL (x : Module.End K V) (a : K[X])) :
            GL (Fin m) (AdjoinRoot (a : K[X]))) : Matrix (Fin m) (Fin m) (AdjoinRoot (a : K[X]))).det =
            LinearMap.det ((T (T.symm (φ ⟨g, hgs⟩ : blockGL (x : Module.End K V) (a : K[X]))) :
              LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X]))
                (primaryComponent (x : Module.End K V) (a : K[X]))) :
              Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) :=
          (CFSG.RankThree.CentralLift.det_toLin'_basis e _).symm
        rw [h1, hTP]
        have h2 : blockRestrict x (a : K[X]) ⟨g, hgc⟩ =
            (φ ⟨g, hgs⟩ : blockGL (x : Module.End K V) (a : K[X])) :=
          blockGL_ext fun v hv => by rw [blockApply_blockRestrict, hτg v hv]
        have h3 := congrArg Units.val hdet
        change LinearMap.det ((blockRestrict x (a : K[X]) ⟨g, hgc⟩ : blockGL (x : Module.End K V)
          (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))) = 1 at h3
        rwa [h2] at h3
    · show l154BlockExt hsq a (T (T.symm (φ ⟨g, hgs⟩ : blockGL (x : Module.End K V) (a : K[X])))) = g
      rw [hTP]
      refine l154BlockExt_eq hsq a _ (fun b hb hba v hv => ?_) hτg
      exact hgs.2 b hb (fun h => hba (Set.mem_singleton_iff.1 h)) v hv
  · rintro ⟨P, hP, rfl⟩
    rw [SetLike.mem_coe, hSUeq, mem_gramSU] at hP
    have hPu : T P ∈ sesqUnitaryGroup Hf := (toLin'_mem_sesqUnitaryGroup_iff e hE hone P).2 hP.1
    have hg₀φ : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
        blockApply (T P : blockGL (x : Module.End K V) (a : K[X])) v hv =
          ((φ.symm ⟨T P, hPu⟩ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v := by
      intro v hv
      have := hφ (φ.symm ⟨T P, hPu⟩) v hv
      rw [MulEquiv.apply_symm_apply] at this
      exact this
    have hιg : (l154BlockExt hsq a).comp T.toMonoidHom P =
        ((φ.symm ⟨T P, hPu⟩ : supportedUnitary B x {(a : K[X])}) : LinearMap.GeneralLinearGroup K V) :=
      l154BlockExt_eq hsq a _ (fun b hb hba v hv =>
        (φ.symm ⟨T P, hPu⟩).2.2 b hb (fun h => hba (Set.mem_singleton_iff.1 h)) v hv) hg₀φ
    rw [hιg]
    have hg₀c : ((φ.symm ⟨T P, hPu⟩ : supportedUnitary B x {(a : K[X])}) :
        LinearMap.GeneralLinearGroup K V) ∈ gl_centralizer x := (φ.symm ⟨T P, hPu⟩).2.1.2
    refine mem_specialBlock.2 ⟨by rw [hsupp]; exact (φ.symm ⟨T P, hPu⟩).2, hg₀c, ?_⟩
    apply Units.ext
    change LinearMap.det ((blockRestrict x (a : K[X]) ⟨_, hg₀c⟩ : blockGL (x : Module.End K V)
      (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X]))) = 1
    have h2 : blockRestrict x (a : K[X]) ⟨_, hg₀c⟩ = (T P : blockGL (x : Module.End K V) (a : K[X])) :=
      blockGL_ext fun v hv => by rw [blockApply_blockRestrict, hg₀φ v hv]
    rw [h2]
    change LinearMap.det ((T P : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X]))
      (primaryComponent (x : Module.End K V) (a : K[X]))) :
        Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) = 1
    rw [CFSG.RankThree.CentralLift.det_toLin'_basis e P]
    exact hP.2

theorem l154_selfDual_model_aux (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (a : primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar (a : K[X]) = a)
    {hE : UnitaryFieldData ℓ (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X]))}
    {Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
      primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])] AdjoinRoot (a : K[X])}
    {m : ℕ} (e : Module.Basis (Fin m) (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])))
    (he : ∀ i j, Hf (e i) (e j) = if i = j then 1 else 0)
    (φ : supportedUnitary B x {(a : K[X])} ≃* sesqUnitaryGroup Hf)
    (hφ : ∀ (g : supportedUnitary B x {(a : K[X])}) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
        blockApply (φ g : blockGL (x : Module.End K V) (a : K[X])) v hv =
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) :
    ∃ ι : GL (Fin m) (AdjoinRoot (a : K[X])) →* LinearMap.GeneralLinearGroup K V,
      Function.Injective ι ∧
      specialBlock B x (a : K[X]) =
        (StatedSU m (ℓ ^ (f * (a : K[X]).natDegree)) (AdjoinRoot (a : K[X]))).map ι ∧
      ∀ (P : GL (Fin m) (AdjoinRoot (a : K[X]))) (z : K),
        ((ι P : LinearMap.GeneralLinearGroup K V) : Module.End K V) = z • (1 : Module.End K V) →
          (P : Matrix (Fin m) (Fin m) (AdjoinRoot (a : K[X]))) =
            algebraMap K (AdjoinRoot (a : K[X])) z • (1 : Matrix (Fin m) (Fin m) (AdjoinRoot (a : K[X]))) := by
  classical
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  let T := Matrix.GeneralLinearGroup.toLin' e
  have hιapp : ∀ (P : GL (Fin m) (AdjoinRoot (a : K[X]))) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      (((l154BlockExt hsq a).comp T.toMonoidHom P : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
        ((((T P : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) ⟨v, hv⟩ :
            primaryComponent (x : Module.End K V) (a : K[X])) : V) :=
    fun P v hv => l154BlockExt_apply_self hsq a (T P) v hv
  refine ⟨(l154BlockExt hsq a).comp T.toMonoidHom,
    (l154BlockExt_injective hsq a).comp T.injective,
    specialBlock_eq_map_l154BlockExt hsq a hself e he φ hφ, ?_⟩
  · intro P z hz
    have h1 : ∀ w : primaryComponent (x : Module.End K V) (a : K[X]),
        ((Matrix.GeneralLinearGroup.toLin' e P : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) w =
            algebraMap K (AdjoinRoot (a : K[X])) z • w := by
      intro w
      apply Subtype.ext
      have h2 := congrArg (fun S : Module.End K V => S (w : V)) hz
      simp only [LinearMap.smul_apply, Module.End.one_apply] at h2
      rw [coe_algebraMap_smul_primaryComponent, ← h2]
      exact (hιapp P (w : V) w.2).symm
    ext i j
    have h3 : e.equivFun (((Matrix.GeneralLinearGroup.toLin' e P : LinearMap.GeneralLinearGroup
        (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) :
        Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) (e j)) i =
        e.equivFun (algebraMap K (AdjoinRoot (a : K[X])) z • e j) i :=
      congrArg (fun u => e.equivFun u i) (h1 (e j))
    rw [CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply, map_smul] at h3
    have h4 : (P : Matrix (Fin m) (Fin m) (AdjoinRoot (a : K[X]))) i j =
        algebraMap K (AdjoinRoot (a : K[X])) z * e.equivFun (e j) i := by
      rw [← smul_eq_mul, ← Pi.smul_apply, ← h3]
      simp [Matrix.mulVec, dotProduct, Module.Basis.equivFun_self, Pi.single_apply]
    rw [h4]
    by_cases hij : i = j
    · subst hij
      simp [Module.Basis.equivFun_self, Matrix.one_apply, Matrix.smul_apply]
    · simp [Module.Basis.equivFun_self, Matrix.one_apply, Matrix.smul_apply, hij, Ne.symm hij]

theorem l154_selfDual_model (H : UnitaryPrimaryData hK.bar B x) (a : primaryFactors (x : Module.End K V))
    (hself : dualPoly hK.bar (a : K[X]) = a) :
    ∃ (hE : UnitaryFieldData ℓ (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X])))
      (ι : GL (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X])) →*
        LinearMap.GeneralLinearGroup K V),
      Function.Injective ι ∧
      specialBlock B x (a : K[X]) =
        (StatedSU (primaryMultiplicity (x : Module.End K V) (a : K[X])) (ℓ ^ (f * (a : K[X]).natDegree))
          (AdjoinRoot (a : K[X]))).map ι ∧
      ∀ (P : GL (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X])))
        (z : K), ((ι P : LinearMap.GeneralLinearGroup K V) : Module.End K V) = z • (1 : Module.End K V) →
          (P : Matrix (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
            (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X]))) =
              algebraMap K (AdjoinRoot (a : K[X])) z • (1 : Matrix _ _ (AdjoinRoot (a : K[X]))) := by
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  obtain ⟨hE, hbarE, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, hφ, -⟩ :=
    (selfDualPrimaryBlock H a hself).unitaryForm
  exact ⟨hE, l154_selfDual_model_aux H.squarefree a hself e he φ hφ⟩

theorem l154_paired_model (H : UnitaryPrimaryData hK.bar B x) (a : primaryFactors (x : Module.End K V))
    (hne : (a : K[X]) ≠ dualPoly hK.bar (a : K[X])) :
    ∃ ι : GL (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X])) →*
        LinearMap.GeneralLinearGroup K V,
      Function.Injective ι ∧
      specialBlock B x (a : K[X]) =
        (StatedSL (primaryMultiplicity (x : Module.End K V) (a : K[X])) (AdjoinRoot (a : K[X]))).map ι ∧
      ∀ (P : GL (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X])))
        (z : K), ((ι P : LinearMap.GeneralLinearGroup K V) : Module.End K V) = z • (1 : Module.End K V) →
          (P : Matrix (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
            (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X]))) =
              algebraMap K (AdjoinRoot (a : K[X])) z • (1 : Matrix _ _ (AdjoinRoot (a : K[X]))) := by
  classical
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  let bW : Module.Basis (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
      (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])) :=
    Module.finBasisOfFinrankEq _ _ rfl
  let T := Matrix.GeneralLinearGroup.toLin' bW
  let Φ := pairedFactorEquiv H a.2 hne
  let ι : GL (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X])) →*
      LinearMap.GeneralLinearGroup K V :=
    (supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])}).subtype.comp
      (Φ.symm.toMonoidHom.comp T.toMonoidHom)
  have hιapp : ∀ (P : GL (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
      (AdjoinRoot (a : K[X]))) (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      ((ι P : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
        blockApply (T P : blockGL (x : Module.End K V) (a : K[X])) v hv := by
    intro P v hv
    have := blockApply_pairedFactorEquiv H a.2 hne (Φ.symm (T P)) v hv
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨ι, (Subtype.val_injective).comp (Φ.symm.injective.comp T.injective), ?_, ?_⟩
  · ext g
    constructor
    · intro hg
      obtain ⟨hgo, hgc, hdet⟩ := mem_specialBlock.mp hg
      have hγ : blockRestrict x (a : K[X]) ⟨g, hgc⟩ = Φ ⟨g, hgo⟩ :=
        blockGL_ext fun v hv => by
          rw [blockApply_blockRestrict]
          exact (blockApply_pairedFactorEquiv H a.2 hne ⟨g, hgo⟩ v hv).symm
      refine ⟨T.symm (Φ ⟨g, hgo⟩), ?_, ?_⟩
      · rw [SetLike.mem_coe, CFSG.Open.StatedAPI.mem_statedSL_iff]
        rw [← CFSG.RankThree.CentralLift.det_toLin'_basis bW, show Matrix.GeneralLinearGroup.toLin' bW
          (T.symm (Φ ⟨g, hgo⟩)) = Φ ⟨g, hgo⟩ from MulEquiv.apply_symm_apply _ _]
        have h3 := congrArg Units.val hdet
        change LinearMap.det ((blockRestrict x (a : K[X]) ⟨g, hgc⟩ : blockGL (x : Module.End K V)
          (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))) = 1 at h3
        rwa [hγ] at h3
      · show ((Φ.symm (T (T.symm (Φ ⟨g, hgo⟩))) : supportedUnitary B x {(a : K[X]),
          dualPoly hK.bar (a : K[X])}) : LinearMap.GeneralLinearGroup K V) = g
        rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
    · rintro ⟨P, hP, rfl⟩
      rw [SetLike.mem_coe, CFSG.Open.StatedAPI.mem_statedSL_iff] at hP
      have hc : ((Φ.symm (T P) : supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])}) :
          LinearMap.GeneralLinearGroup K V) ∈ gl_centralizer x := (Φ.symm (T P)).2.1.2
      refine mem_specialBlock.2 ⟨(Φ.symm (T P)).2, hc, ?_⟩
      apply Units.ext
      change LinearMap.det ((blockRestrict x (a : K[X]) ⟨_, hc⟩ : blockGL (x : Module.End K V)
        (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) = 1
      have h2 : blockRestrict x (a : K[X]) ⟨_, hc⟩ = (T P : blockGL (x : Module.End K V) (a : K[X])) :=
        blockGL_ext fun v hv => by
          rw [blockApply_blockRestrict]
          exact hιapp P v hv
      rw [h2]
      change LinearMap.det ((T P : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X]))) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) = 1
      rw [CFSG.RankThree.CentralLift.det_toLin'_basis bW P]
      exact hP
  · intro P z hz
    have h1 : ∀ w : primaryComponent (x : Module.End K V) (a : K[X]),
        ((Matrix.GeneralLinearGroup.toLin' bW P : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) w =
            algebraMap K (AdjoinRoot (a : K[X])) z • w := by
      intro w
      apply Subtype.ext
      have h2 := congrArg (fun S : Module.End K V => S (w : V)) hz
      simp only [LinearMap.smul_apply, Module.End.one_apply] at h2
      rw [coe_algebraMap_smul_primaryComponent, ← h2]
      exact (hιapp P (w : V) w.2).symm
    ext i j
    have h3 : bW.equivFun (((Matrix.GeneralLinearGroup.toLin' bW P : LinearMap.GeneralLinearGroup
        (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) :
        Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) (bW j)) i =
        bW.equivFun (algebraMap K (AdjoinRoot (a : K[X])) z • bW j) i :=
      congrArg (fun u => bW.equivFun u i) (h1 (bW j))
    rw [CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply, map_smul] at h3
    have h4 : (P : Matrix (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
        (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X]))) i j =
        algebraMap K (AdjoinRoot (a : K[X])) z * bW.equivFun (bW j) i := by
      rw [← smul_eq_mul, ← Pi.smul_apply, ← h3]
      simp [Matrix.mulVec, dotProduct, Module.Basis.equivFun_self, Pi.single_apply]
    rw [h4]
    by_cases hij : i = j
    · subst hij
      simp [Module.Basis.equivFun_self, Matrix.one_apply, Matrix.smul_apply]
    · simp [Module.Basis.equivFun_self, Matrix.one_apply, Matrix.smul_apply, hij, Ne.symm hij]

end Models

end CFSG.LocalAnalysis.GLTheoremA.K155X
