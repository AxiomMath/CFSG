module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniLine

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial Module CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.ComponentClassification.Burgoyne.U CFSG.HardMathSupport.Dickson.Bal207.FirstClaim
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.GLTheoremA.K155X

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {x : LinearMap.GeneralLinearGroup K V}

theorem l154BlockExt_conj (hsq : Squarefree (minpoly K (x : Module.End K V)))
    (a : primaryFactors (x : Module.End K V)) (γ : blockGL (x : Module.End K V) (a : K[X]))
    {ξ : LinearMap.GeneralLinearGroup K V} (hξ : ξ ∈ gl_centralizer x) :
    l154BlockExt hsq a (blockRestrict x (a : K[X]) ⟨ξ, hξ⟩ * γ *
        (blockRestrict x (a : K[X]) ⟨ξ, hξ⟩)⁻¹) =
      ξ * l154BlockExt hsq a γ * ξ⁻¹ := by
  refine l154BlockExt_eq hsq a _ (fun b hb hba v hv => ?_) (fun v hv => ?_)
  ·
    have hb' : (⟨b, hb⟩ : primaryFactors (x : Module.End K V)) ≠ a :=
      fun h => hba (congrArg Subtype.val h)
    have hξinv : ((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈
        primaryComponent (x : Module.End K V) b :=
      apply_mem_primaryComponent (mem_gl_centralizer.mp (Subgroup.inv_mem _ hξ)) hv
    have hL : ((l154BlockExt hsq a γ : LinearMap.GeneralLinearGroup K V) :
        Module.End K V) (((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) =
        ((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v :=
      l154BlockExt_apply_ne hsq a γ ⟨b, hb⟩ hb' _ hξinv
    change (((ξ : LinearMap.GeneralLinearGroup K V) : Module.End K V) *
      ((l154BlockExt hsq a γ : LinearMap.GeneralLinearGroup K V) : Module.End K V) *
      ((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)) v = v
    rw [Module.End.mul_apply, Module.End.mul_apply, hL]
    have hξξ : ((ξ : Module.End K V) * ((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) :
        Module.End K V)) v = v := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Module.End.one_apply]
    exact hξξ
  ·
    have hLmem : l154BlockExt hsq a γ ∈ gl_centralizer x := l154BlockExt_mem_centralizer hsq a γ
    have hconjmem : ξ * l154BlockExt hsq a γ * ξ⁻¹ ∈ gl_centralizer x :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hξ hLmem) (Subgroup.inv_mem _ hξ)
    have hblkL : blockRestrict x (a : K[X]) ⟨l154BlockExt hsq a γ, hLmem⟩ = γ := by
      apply blockGL_ext
      intro v hv
      rw [blockApply_blockRestrict]
      exact l154BlockExt_apply_self hsq a γ v hv
    have hsub : (⟨ξ * l154BlockExt hsq a γ * ξ⁻¹, hconjmem⟩ : gl_centralizer x) =
        ⟨ξ, hξ⟩ * ⟨l154BlockExt hsq a γ, hLmem⟩ * (⟨ξ, hξ⟩ : gl_centralizer x)⁻¹ :=
      Subtype.ext rfl
    have hblk : blockRestrict x (a : K[X]) ⟨ξ * l154BlockExt hsq a γ * ξ⁻¹, hconjmem⟩ =
        blockRestrict x (a : K[X]) ⟨ξ, hξ⟩ * γ *
          (blockRestrict x (a : K[X]) ⟨ξ, hξ⟩)⁻¹ := by
      rw [hsub, map_mul, map_mul, map_inv, hblkL]
    rw [← hblk, blockApply_blockRestrict]


section SelfDualModel

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem l154_blockRestrict_mem_sesqUnitaryGroup (a : primaryFactors (x : Module.End K V))
    {hE : UnitaryFieldData ℓ (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X]))}
    {Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
      primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
        AdjoinRoot (a : K[X])}
    (htrace : ∀ (v w : primaryComponent (x : Module.End K V) (a : K[X]))
      (b : AdjoinRoot (a : K[X])),
      Algebra.trace K (AdjoinRoot (a : K[X])) (b * Hf v w) =
        B (v : V) ((b • w : primaryComponent (x : Module.End K V) (a : K[X])) : V))
    {ξ : LinearMap.GeneralLinearGroup K V} (hξ : ξ ∈ unitaryCentralizer B x) :
    blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩ ∈ sesqUnitaryGroup Hf := by
  classical
  haveI : Finite K := hK.finite
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  rw [mem_sesqUnitaryGroup]
  intro v w
  apply eq_of_trace_eq
  intro b
  set β := blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩ with hβdef
  let βE : Module.End (AdjoinRoot (a : K[X]))
      (primaryComponent (x : Module.End K V) (a : K[X])) := β
  have hβvV : ((βE v : primaryComponent (x : Module.End K V) (a : K[X])) : V) =
      ((ξ : Module.End K V) (v : V)) :=
    blockApply_blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩ (v : V) v.2
  have hβbw : ((b • (βE w) : primaryComponent (x : Module.End K V) (a : K[X])) : V) =
      ((ξ : Module.End K V) ((b • w : primaryComponent (x : Module.End K V) (a : K[X])) : V)) := by
    have hsmul : (b • (βE w) : primaryComponent (x : Module.End K V) (a : K[X])) = βE (b • w) := by
      change (b • (βE w) : primaryComponent (x : Module.End K V) (a : K[X])) =
        βE (b • w)
      rw [map_smul]
    rw [hsmul]
    exact (blockApply_blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩
      (((b • w : primaryComponent (x : Module.End K V) (a : K[X])) : V))
      (Submodule.coe_mem _)).symm
  rw [mul_comm (Hf (βE v) (βE w)) b]
  rw [mul_comm (Hf v w) b]
  rw [htrace (βE v) (βE w) b, htrace v w b]
  rw [hβvV, hβbw]
  exact (mem_unitaryCentralizer.mp hξ).1 _ _




theorem l154_selfDual_model_block (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar (a : K[X]) = a)
    {m : ℕ} (hm : m = primaryMultiplicity (x : Module.End K V) (a : K[X])) :
    ∃ (hE : UnitaryFieldData ℓ (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X])))
      (Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
        primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
          AdjoinRoot (a : K[X]))
      (e : Module.Basis (Fin m) (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X])))
      (ι : GL (Fin m) (AdjoinRoot (a : K[X])) →*
        LinearMap.GeneralLinearGroup K V),
      Hf.IsSymm ∧ Hf.SeparatingLeft ∧
      (∀ i j, Hf (e i) (e j) = if i = j then 1 else 0) ∧
      Function.Injective ι ∧
      specialBlock B x (a : K[X]) =
        (StatedSU m (ℓ ^ (f * (a : K[X]).natDegree)) (AdjoinRoot (a : K[X]))).map ι ∧
      (∀ (P : GL (Fin m) (AdjoinRoot (a : K[X]))) (z : K),
        ((ι P : LinearMap.GeneralLinearGroup K V) : Module.End K V) = z • 1 →
          (P : Matrix (Fin m) (Fin m) (AdjoinRoot (a : K[X]))) =
            algebraMap K (AdjoinRoot (a : K[X])) z • 1) ∧
      (∀ (ξ : LinearMap.GeneralLinearGroup K V) (hξ : ξ ∈ unitaryCentralizer B x)
        (P : GL (Fin m) (AdjoinRoot (a : K[X]))),
        ι ((Matrix.GeneralLinearGroup.toLin' e).symm (blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩) *
            P * ((Matrix.GeneralLinearGroup.toLin' e).symm
              (blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩))⁻¹) =
          ξ * ι P * ξ⁻¹) ∧
      (∀ (ξ : LinearMap.GeneralLinearGroup K V) (hξ : ξ ∈ unitaryCentralizer B x),
        (Matrix.GeneralLinearGroup.toLin' e).symm (blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩) ∈
          primeFormUnitary hE ((1 : GL (Fin m) (AdjoinRoot (a : K[X]))) :
            Matrix (Fin m) (Fin m) (AdjoinRoot (a : K[X])))) := by
  classical
  subst hm
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  obtain ⟨hE, hbarE, -, Hf, hHf, hHfl, htrace, ⟨e, he⟩, φ, hφ, hdet⟩ :=
    (selfDualPrimaryBlock H a hself).unitaryForm
  let T := Matrix.GeneralLinearGroup.toLin' e
  let ι : GL (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
      (AdjoinRoot (a : K[X])) →* LinearMap.GeneralLinearGroup K V :=
    (l154BlockExt H.squarefree a).comp T.toMonoidHom
  have hιapp : ∀ (P : GL (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
      (AdjoinRoot (a : K[X]))) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      (((ι P : LinearMap.GeneralLinearGroup K V)) : Module.End K V) v =
        ((((T P : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) :
          Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) ⟨v, hv⟩ :
            primaryComponent (x : Module.End K V) (a : K[X])) : V) :=
    fun P v hv => l154BlockExt_apply_self H.squarefree a (T P) v hv
  refine ⟨hE, Hf, e, ι, hHf, hHfl, he, (l154BlockExt_injective H.squarefree a).comp T.injective,
    ?_, ?_, ?_, ?_⟩
  · exact specialBlock_eq_map_l154BlockExt H.squarefree a hself e he φ hφ
  · intro P z hz
    have h1 : ∀ w : primaryComponent (x : Module.End K V) (a : K[X]),
        ((Matrix.GeneralLinearGroup.toLin' e P : LinearMap.GeneralLinearGroup
          (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) :
          Module.End (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))) w =
            algebraMap K (AdjoinRoot (a : K[X])) z • w := by
      intro w
      apply Subtype.ext
      have h2 := congrArg (fun S : Module.End K V => S (w : V)) hz
      simp only [LinearMap.smul_apply, Module.End.one_apply] at h2
      rw [coe_algebraMap_smul_primaryComponent, ← h2]
      exact (hιapp P (w : V) w.2).symm
    ext i j
    have h3 : e.equivFun (((Matrix.GeneralLinearGroup.toLin' e P :
        LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X]))) :
        Module.End (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) (e j)) i =
        e.equivFun (algebraMap K (AdjoinRoot (a : K[X])) z • e j) i :=
      congrArg (fun u => e.equivFun u i) (h1 (e j))
    rw [CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply, map_smul] at h3
    have h4 : (P : Matrix (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
        (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X]))) i j =
        algebraMap K (AdjoinRoot (a : K[X])) z * e.equivFun (e j) i := by
      rw [← smul_eq_mul, ← Pi.smul_apply, ← h3]
      simp [Matrix.mulVec, dotProduct, Module.Basis.equivFun_self, Pi.single_apply]
    rw [h4]
    by_cases hij : i = j
    · subst hij
      simp [Module.Basis.equivFun_self, Matrix.one_apply, Matrix.smul_apply]
    · simp [Module.Basis.equivFun_self, Matrix.one_apply, Matrix.smul_apply, hij, Ne.symm hij]
  · intro ξ hξ
    refine fun P => ?_
    show l154BlockExt H.squarefree a (T ((Matrix.GeneralLinearGroup.toLin' e).symm
      (blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩) * P *
      ((Matrix.GeneralLinearGroup.toLin' e).symm (blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩))⁻¹)) =
      ξ * l154BlockExt H.squarefree a (T P) * ξ⁻¹
    have hT : T ((Matrix.GeneralLinearGroup.toLin' e).symm
        (blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩) * P *
        ((Matrix.GeneralLinearGroup.toLin' e).symm (blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩))⁻¹) =
        blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩ * T P *
          (blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩)⁻¹ := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [hT]
    exact l154BlockExt_conj H.squarefree a (T P) hξ.2
  · intro ξ hξ
    have hβ : blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩ ∈ sesqUnitaryGroup Hf :=
      l154_blockRestrict_mem_sesqUnitaryGroup a htrace hξ
    have hβ' : Matrix.GeneralLinearGroup.toLin' e
        ((Matrix.GeneralLinearGroup.toLin' e).symm (blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩)) ∈
        sesqUnitaryGroup Hf := by
      rw [MulEquiv.apply_symm_apply]
      exact hβ
    exact (toLin'_mem_sesqUnitaryGroup_iff (h := hE) (n := primaryMultiplicity (x : Module.End K V) (a : K[X])) (b := e) (H := Hf) he _).1 hβ' 



section PairedModel

theorem l154_paired_model_block (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V))
    (hne : (a : K[X]) ≠ dualPoly hK.bar (a : K[X]))
    {m : ℕ} (hm : m = primaryMultiplicity (x : Module.End K V) (a : K[X])) :
    ∃ (e : Module.Basis (Fin m) (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X])))
      (ι : GL (Fin m) (AdjoinRoot (a : K[X])) →*
        LinearMap.GeneralLinearGroup K V),
      Function.Injective ι ∧
      specialBlock B x (a : K[X]) =
        (StatedSL m (AdjoinRoot (a : K[X]))).map ι ∧
      (∀ (P : GL (Fin m) (AdjoinRoot (a : K[X]))) (z : K),
        ((ι P : LinearMap.GeneralLinearGroup K V) : Module.End K V) = z • 1 →
          (P : Matrix (Fin m) (Fin m) (AdjoinRoot (a : K[X]))) =
            algebraMap K (AdjoinRoot (a : K[X])) z • 1) ∧
      (∀ (ξ : LinearMap.GeneralLinearGroup K V) (hξ : ξ ∈ unitaryCentralizer B x)
        (P : GL (Fin m) (AdjoinRoot (a : K[X]))),
        ι ((Matrix.GeneralLinearGroup.toLin' e).symm (blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩) *
            P * ((Matrix.GeneralLinearGroup.toLin' e).symm
              (blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩))⁻¹) =
          ξ * ι P * ξ⁻¹) := by
  classical
  subst hm
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  let e : Module.Basis (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
      (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])) :=
    Module.finBasisOfFinrankEq _ _ rfl
  let T := Matrix.GeneralLinearGroup.toLin' e
  let Φ := pairedFactorEquiv H a.2 hne
  let ι : GL (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
      (AdjoinRoot (a : K[X])) →* LinearMap.GeneralLinearGroup K V :=
    (supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])}).subtype.comp
      (Φ.symm.toMonoidHom.comp T.toMonoidHom)
  have hιapp : ∀ (P : GL (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
      (AdjoinRoot (a : K[X]))) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      ((ι P : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
        blockApply (T P : blockGL (x : Module.End K V) (a : K[X])) v hv := by
    intro P v hv
    have := blockApply_pairedFactorEquiv H a.2 hne (Φ.symm (T P)) v hv
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨e, ι, (Subtype.val_injective).comp (Φ.symm.injective.comp T.injective), ?_, ?_, ?_⟩
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
        rw [← CFSG.RankThree.CentralLift.det_toLin'_basis e, show Matrix.GeneralLinearGroup.toLin' e
          (T.symm (Φ ⟨g, hgo⟩)) = Φ ⟨g, hgo⟩ from MulEquiv.apply_symm_apply _ _]
        have h3 := congrArg Units.val hdet
        change LinearMap.det ((blockRestrict x (a : K[X]) ⟨g, hgc⟩ : blockGL
          (x : Module.End K V) (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))) = 1 at h3
        rwa [hγ] at h3
      · show ((Φ.symm (T (T.symm (Φ ⟨g, hgo⟩))) :
          supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])}) :
          LinearMap.GeneralLinearGroup K V) = g
        rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
    · rintro ⟨P, hP, rfl⟩
      rw [SetLike.mem_coe, CFSG.Open.StatedAPI.mem_statedSL_iff] at hP
      have hc : ((Φ.symm (T P) : supportedUnitary B x {(a : K[X]),
          dualPoly hK.bar (a : K[X])}) : LinearMap.GeneralLinearGroup K V) ∈ gl_centralizer x :=
        (Φ.symm (T P)).2.1.2
      refine mem_specialBlock.2 ⟨(Φ.symm (T P)).2, hc, ?_⟩
      apply Units.ext
      change LinearMap.det ((blockRestrict x (a : K[X]) ⟨_, hc⟩ : blockGL
        (x : Module.End K V) (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) = 1
      have h2 : blockRestrict x (a : K[X]) ⟨_, hc⟩ =
          (T P : blockGL (x : Module.End K V) (a : K[X])) :=
        blockGL_ext fun v hv => by
          rw [blockApply_blockRestrict]
          exact hιapp P v hv
      rw [h2]
      change LinearMap.det ((T P : LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X]))) :
          Module.End (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))) = 1
      rw [CFSG.RankThree.CentralLift.det_toLin'_basis e P]
      exact hP
  · intro P z hz
    have h1 : ∀ w : primaryComponent (x : Module.End K V) (a : K[X]),
        ((Matrix.GeneralLinearGroup.toLin' e P : LinearMap.GeneralLinearGroup
          (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) :
          Module.End (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))) w =
            algebraMap K (AdjoinRoot (a : K[X])) z • w := by
      intro w
      apply Subtype.ext
      have h2 := congrArg (fun S : Module.End K V => S (w : V)) hz
      simp only [LinearMap.smul_apply, Module.End.one_apply] at h2
      rw [coe_algebraMap_smul_primaryComponent, ← h2]
      exact (hιapp P (w : V) w.2).symm
    ext i j
    have h3 : e.equivFun (((Matrix.GeneralLinearGroup.toLin' e P :
        LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X]))) :
        Module.End (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) (e j)) i =
        e.equivFun (algebraMap K (AdjoinRoot (a : K[X])) z • e j) i :=
      congrArg (fun u => e.equivFun u i) (h1 (e j))
    rw [CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply, map_smul] at h3
    have h4 : (P : Matrix (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
        (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X]))) (AdjoinRoot (a : K[X]))) i j =
        algebraMap K (AdjoinRoot (a : K[X])) z * e.equivFun (e j) i := by
      rw [← smul_eq_mul, ← Pi.smul_apply, ← h3]
      simp [Matrix.mulVec, dotProduct, Module.Basis.equivFun_self, Pi.single_apply]
    rw [h4]
    by_cases hij : i = j
    · subst hij
      simp [Module.Basis.equivFun_self, Matrix.one_apply, Matrix.smul_apply]
    · simp [Module.Basis.equivFun_self, Matrix.one_apply, Matrix.smul_apply, hij, Ne.symm hij]
  · intro ξ hξ P
    set β := blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩ with hβdef
    set B₁ := (Matrix.GeneralLinearGroup.toLin' e).symm β with hB₁def
    have hTB : T B₁ = β := by rw [hB₁def, MulEquiv.apply_symm_apply]
    set uP : supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])} := Φ.symm (T P) with huP
    have hιP : ((uP : supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])}) :
        LinearMap.GeneralLinearGroup K V) = ι P := rfl
    have hconj : ξ * ((ι P : LinearMap.GeneralLinearGroup K V)) * ξ⁻¹ ∈
        supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])} :=
      conj_mem_supportedUnitary hξ uP.2
    have hβapp : ∀ (w : V) (hw : w ∈ primaryComponent (x : Module.End K V) (a : K[X])),
        blockApply β w hw = ((ξ : LinearMap.GeneralLinearGroup K V) : Module.End K V) w := by
      intro w hw
      rw [hβdef]
      exact blockApply_blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩ w hw
    have hβinv : ∀ (w : V) (hw : w ∈ primaryComponent (x : Module.End K V) (a : K[X])),
        blockApply β⁻¹ w hw =
          ((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) w := by
      intro w hw
      rw [hβdef]
      conv_lhs => rw [← map_inv]
      exact blockApply_blockRestrict x (a : K[X]) ⟨ξ⁻¹, Subgroup.inv_mem _ hξ.2⟩ w hw
    have hΦconj : Φ ⟨ξ * ((ι P : LinearMap.GeneralLinearGroup K V)) * ξ⁻¹, hconj⟩ =
        β * T P * β⁻¹ := by
      apply blockGL_ext
      intro v hv
      have hξinv : ((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈
          primaryComponent (x : Module.End K V) (a : K[X]) :=
        apply_mem_primaryComponent (mem_gl_centralizer.mp (Subgroup.inv_mem _ hξ.2)) hv
      have hιmem : ((ι P : LinearMap.GeneralLinearGroup K V) : Module.End K V)
          (((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) ∈
          primaryComponent (x : Module.End K V) (a : K[X]) := by
        rw [hιapp P _ hξinv]
        exact blockApply_mem (T P) _ hξinv
      have hξmem : ((ξ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
          (((ι P : LinearMap.GeneralLinearGroup K V) : Module.End K V)
            (((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)) ∈
          primaryComponent (x : Module.End K V) (a : K[X]) :=
        apply_mem_primaryComponent (mem_gl_centralizer.mp hξ.2) hιmem
      have hpow : ∀ (Y : LinearMap.GeneralLinearGroup K V),
          ((Y : Module.End K V) : V →ₗ[K] V) = (Y : V →ₗ[K] V) := fun Y => rfl
      rw [blockApply_pairedFactorEquiv H a.2 hne]
      change ((ξ * ((ι P : LinearMap.GeneralLinearGroup K V)) * ξ⁻¹ :
          LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
        ((β : Module.End (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))) *
          (T P : Module.End (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))) *
          ((β⁻¹ : blockGL (x : Module.End K V) (a : K[X])) :
            Module.End (AdjoinRoot (a : K[X]))
              (primaryComponent (x : Module.End K V) (a : K[X]))))
          ⟨v, hv⟩
      rw [Module.End.mul_apply, Module.End.mul_apply]
      rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
      have e1 : (↑(β⁻¹ : blockGL (x : Module.End K V) (a : K[X])) :
            Module.End (AdjoinRoot (a : K[X]))
              (primaryComponent (x : Module.End K V) (a : K[X]))) ⟨v, hv⟩ =
          ⟨((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v, hξinv⟩ :=
        Subtype.ext (hβinv v hv)
      have e2 : ((T P : blockGL (x : Module.End K V) (a : K[X])) :
            Module.End (AdjoinRoot (a : K[X]))
              (primaryComponent (x : Module.End K V) (a : K[X]))) ⟨
          ((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v, hξinv⟩ =
          ⟨((ι P : LinearMap.GeneralLinearGroup K V) : Module.End K V)
            (((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v), hιmem⟩ :=
        Subtype.ext (hιapp P _ hξinv).symm
      have e3 : ((β : blockGL (x : Module.End K V) (a : K[X])) :
            Module.End (AdjoinRoot (a : K[X]))
              (primaryComponent (x : Module.End K V) (a : K[X]))) ⟨
          ((ι P : LinearMap.GeneralLinearGroup K V) : Module.End K V)
            (((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v), hιmem⟩ =
          ⟨((ξ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
            (((ι P : LinearMap.GeneralLinearGroup K V) : Module.End K V)
              (((ξ⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)), hξmem⟩ :=
        Subtype.ext (hβapp _ hιmem)
      rw [e1, e2, e3]
    set Q := B₁ * P * B₁⁻¹ with hQ
    have hTQ : T Q = β * T P * β⁻¹ := by
      rw [hQ, map_mul, map_mul, map_inv, hTB]
    have hQB : Q = (Matrix.GeneralLinearGroup.toLin' e).symm
        (blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩) * P *
        ((Matrix.GeneralLinearGroup.toLin' e).symm
          (blockRestrict x (a : K[X]) ⟨ξ, hξ.2⟩))⁻¹ := by
      rw [hQ, hB₁def, hβdef]
    have hleft : Φ (Φ.symm (T Q)) = β * T P * β⁻¹ := by
      rw [MulEquiv.apply_symm_apply, hTQ]
    have heq : Φ.symm (T Q) = ⟨ξ * ((ι P : LinearMap.GeneralLinearGroup K V)) * ξ⁻¹,
        hconj⟩ := Φ.injective (hleft.trans hΦconj.symm)
    have hfin : ((ι Q : LinearMap.GeneralLinearGroup K V)) = ξ * ι P * ξ⁻¹ := by
      have hcoe := congrArg (fun t : supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])} =>
        ((t : supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])}) :
          LinearMap.GeneralLinearGroup K V)) heq
      exact hcoe
    rw [hQB]
    exact hfin

end PairedModel

end SelfDualModel

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
