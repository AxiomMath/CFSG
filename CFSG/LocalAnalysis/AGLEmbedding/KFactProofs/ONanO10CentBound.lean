module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO10CentUnitary
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusPerfOrth
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusPerfFrame

public section

namespace CFSG.AGLEmbedding.O10Cent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module CFSG.AGLEmbedding.OmegaMinusCent
  CFSG.AGLEmbedding.OmegaMinusPerf CFSG.LocalAnalysis.ComponentInitial CFSG.LinearAlgebra

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Retract

variable {R A W : Type*} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]

@[expose] def retractHom (ι : A →ₗ[R] W) (π : W →ₗ[R] A) (hπι : ∀ a, π (ι a) = a)
    (Z : Subgroup (W ≃ₗ[R] W)) (hZ : ∀ g ∈ Z, ∀ a, ι (π (g (ι a))) = g (ι a)) :
    Z →* Module.End R A where
  toFun g := π ∘ₗ (g : W ≃ₗ[R] W).toLinearMap ∘ₗ ι
  map_one' := by
    ext a
    simp [hπι]
  map_mul' g h := by
    ext a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.End.mul_apply]
    rw [hZ h h.2 a]
    rfl

end Retract

section Centralizer

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {x : V ≃ₗ[ZMod 2] V}

@[expose] def isoCent (Q : QuadraticForm (ZMod 2) V) (x : V ≃ₗ[ZMod 2] V) :
    Subgroup (V ≃ₗ[ZMod 2] V) :=
  TauCeti.QuadraticMap.orthogonalGroup Q ⊓ Subgroup.centralizer {x}

theorem mem_isoCent {g : V ≃ₗ[ZMod 2] V} :
    g ∈ isoCent Q x ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ ∀ v, g (x v) = x (g v) := by
  rw [isoCent, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun _ => ⟨fun h v => ?_, fun h => ?_⟩
  · exact congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) h
  · ext v
    exact h v

theorem apply_mem_fixSpace {g : V ≃ₗ[ZMod 2] V} (hg : ∀ v, g (x v) = x (g v)) {v : V}
    (hv : v ∈ fixSpace x) : g v ∈ fixSpace x := by
  rw [mem_fixSpace] at hv ⊢
  rw [← hg, hv]

theorem apply_mem_moveSpace_of_comm {g : V ≃ₗ[ZMod 2] V} (hg : ∀ v, g (x v) = x (g v)) {m : V}
    (hm : m ∈ moveSpace x) : g m ∈ moveSpace x := by
  rw [mem_moveSpace] at hm ⊢
  have := congrArg g hm
  rw [map_add, map_add, hg, hg, map_zero] at this
  exact this

end Centralizer

section RestrC

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {x : V ≃ₗ[ZMod 2] V}

theorem subtype_fixProj_apply (hx3 : ∀ v, x (x (x v)) = v) {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ v, g (x v) = x (g v)) (a : ↥(fixSpace x)) :
    (fixSpace x).subtype (fixProj hx3 (g ((fixSpace x).subtype a))) =
      g ((fixSpace x).subtype a) := by
  have h := LinearMap.congr_fun (fixProj_comp_subtype hx3)
    (⟨g ((fixSpace x).subtype a), apply_mem_fixSpace hg a.2⟩ : ↥(fixSpace x))
  exact congrArg Subtype.val h

@[expose] noncomputable def endC (hx3 : ∀ v, x (x (x v)) = v) :
    isoCent Q x →* Module.End (ZMod 2) ↥(fixSpace x) :=
  retractHom (fixSpace x).subtype (fixProj hx3)
    (fun a => LinearMap.congr_fun (fixProj_comp_subtype hx3) a) (isoCent Q x)
    (fun _ hg a => subtype_fixProj_apply hx3 (mem_isoCent.1 hg).2 a)

@[expose] noncomputable def restrC (hx3 : ∀ v, x (x (x v)) = v) :
    isoCent Q x →* (↥(fixSpace x) ≃ₗ[ZMod 2] ↥(fixSpace x)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥(fixSpace x)).toMonoidHom.comp
    (endC hx3).toHomUnits

theorem restrC_apply (hx3 : ∀ v, x (x (x v)) = v) (g : isoCent Q x) (a : ↥(fixSpace x)) :
    ((restrC hx3 g a : ↥(fixSpace x)) : V) = (g : V ≃ₗ[ZMod 2] V) a := by
  exact subtype_fixProj_apply hx3 (mem_isoCent.1 g.2).2 a

theorem restrC_mem (hx3 : ∀ v, x (x (x v)) = v) (g : isoCent Q x) :
    restrC hx3 g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSpace x)) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro a
  change Q ((restrC hx3 g a : ↥(fixSpace x)) : V) = Q (a : V)
  rw [restrC_apply]
  exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (mem_isoCent.1 g.2).1) _

end RestrC

section Omega

theorem smul_eq_re_im {k : ℕ} (c : OmegaField) (z : Fin k → OmegaField) :
    c • z = omegaRe c • z + omegaIm c • (omega • z) := by
  conv_lhs => rw [eq_re_im c]
  rw [add_smul, mul_smul, algebraMap_smul, algebraMap_smul]

@[expose] noncomputable def toOmegaLinear {k : ℕ}
    (T : (Fin k → OmegaField) →ₗ[ZMod 2] (Fin k → OmegaField))
    (hT : ∀ z, T (omega • z) = omega • T z) :
    (Fin k → OmegaField) →ₗ[OmegaField] (Fin k → OmegaField) where
  toFun := T
  map_add' := T.map_add
  map_smul' c z := by
    simp only [RingHom.id_apply]
    rw [smul_eq_re_im c z, smul_eq_re_im c (T z), map_add, map_smul, map_smul, hT]

theorem toOmegaLinear_apply {k : ℕ} (T : (Fin k → OmegaField) →ₗ[ZMod 2] (Fin k → OmegaField))
    (hT : ∀ z, T (omega • z) = omega • T z) (z : Fin k → OmegaField) :
    toOmegaLinear T hT z = T z :=
  rfl

end Omega

section FrameRestr

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {x : V ≃ₗ[ZMod 2] V} {k : ℕ} {F : Frame Q x k}

structure Spans (F : Frame Q x k) : Prop where
  psi_mem : ∀ z, F.psi z ∈ moveSpace x
  psi_coord : ∀ m ∈ moveSpace x, F.psi (F.coord m) = m

theorem Spans.of_dim [FiniteDimensional (ZMod 2) V] (hx3 : ∀ v, x (x (x v)) = v)
    (F : Frame Q x k) (hFa : ∀ i, (F.P i).a ∈ moveSpace x)
    (hdim : finrank (ZMod 2) (fixSpace x) + 2 * k = finrank (ZMod 2) V) : Spans F := by
  have hmem : ∀ z, F.psi z ∈ moveSpace x := fun z => by
    rw [F.psi_apply]
    refine Submodule.sum_mem _ fun i _ => Submodule.add_mem _
      (Submodule.smul_mem _ _ (hFa i)) (Submodule.smul_mem _ _ ?_)
    rw [F.b_eq]
    exact apply_mem_moveSpace hx3 (hFa i)
  have hinj : Function.Injective F.psi := fun a b h => by
    have := congrArg F.coord h
    rwa [F.coord_psi, F.coord_psi] at this
  have hrange : LinearMap.range F.psi = moveSpace x := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨z, rfl⟩
      exact hmem z
    · have h1 := Submodule.finrank_add_eq_of_isCompl (isCompl_fix_move hx3 (x := x))
      have : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
      rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]
      simp only [finrank_omegaField, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]
      omega
  refine ⟨hmem, fun m hm => ?_⟩
  rw [← hrange] at hm
  obtain ⟨z, rfl⟩ := hm
  rw [F.coord_psi]

theorem coord_psi_comm (F : Frame Q x k) (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {g : V ≃ₗ[ZMod 2] V} (hg : ∀ v, g (x v) = x (g v)) (z : Fin k → OmegaField) :
    F.coord (g (F.psi (omega • z))) = omega • F.coord (g (F.psi z)) := by
  rw [← F.x_psi, hg, F.coord_x hx]

@[expose] noncomputable def endT (hF : Spans F) :
    isoCent Q x →* Module.End (ZMod 2) (Fin k → OmegaField) :=
  retractHom F.psi F.coord F.coord_psi (isoCent Q x) fun _ hg z =>
    hF.psi_coord _ (apply_mem_moveSpace_of_comm (mem_isoCent.1 hg).2 (hF.psi_mem z))

theorem endT_apply (hF : Spans F) (g : isoCent Q x) (z : Fin k → OmegaField) :
    endT hF g z = F.coord ((g : V ≃ₗ[ZMod 2] V) (F.psi z)) :=
  rfl

@[expose] noncomputable def endW (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hF : Spans F) : isoCent Q x →* Module.End OmegaField (Fin k → OmegaField) where
  toFun g := toOmegaLinear (endT hF g) fun z => by
    rw [endT_apply, endT_apply]
    exact coord_psi_comm F hx (mem_isoCent.1 g.2).2 z
  map_one' := LinearMap.ext fun z => by
    rw [toOmegaLinear_apply, map_one]
    rfl
  map_mul' g h := LinearMap.ext fun z => by
    rw [Module.End.mul_apply, toOmegaLinear_apply, toOmegaLinear_apply, toOmegaLinear_apply,
      map_mul]
    rfl

end FrameRestr

section Unitary

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {x : V ≃ₗ[ZMod 2] V} {k : ℕ} {F : Frame Q x k}

theorem endW_norm (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hF : Spans F)
    (g : isoCent Q x) (z : Fin k → OmegaField) :
    stdHerm k (endW hx hF g z) (endW hx hF g z) = stdHerm k z z := by
  rw [stdHerm_self, stdHerm_self]
  have h1 := F.algebraMap_map_psi (F.coord ((g : V ≃ₗ[ZMod 2] V) (F.psi z)))
  have h2 := F.algebraMap_map_psi z
  have hm : (g : V ≃ₗ[ZMod 2] V) (F.psi z) ∈ moveSpace x :=
    apply_mem_moveSpace_of_comm (mem_isoCent.1 g.2).2 (hF.psi_mem z)
  rw [hF.psi_coord _ hm, (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (mem_isoCent.1 g.2).1),
    h2] at h1
  exact h1.symm

@[expose] noncomputable def restrM (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hF : Spans F) : isoCent Q x →* sesqUnitaryGroup (stdHerm k) :=
  (endW hx hF).toHomUnits.codRestrict (sesqUnitaryGroup (stdHerm k)) fun g => by
    rw [mem_sesqUnitaryGroup]
    intro u v
    exact stdHerm_eq_of_norm (endW hx hF g) (endW_norm hx hF g) u v

end Unitary

section Embedding

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {x : V ≃ₗ[ZMod 2] V} {k : ℕ} {F : Frame Q x k}

@[expose] noncomputable def restrAll (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx3 : ∀ v, x (x (x v)) = v) (hF : Spans F) :
    isoCent Q x →* TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSpace x)) ×
      sesqUnitaryGroup (stdHerm k) :=
  ((restrC hx3).codRestrict _ (restrC_mem hx3)).prod (restrM hx hF)

theorem restrAll_injective (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx3 : ∀ v, x (x (x v)) = v) (hF : Spans F) : Function.Injective (restrAll hx hx3 hF) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := Prod.ext_iff.1 hg
  have hC : ∀ c ∈ fixSpace x, (g : V ≃ₗ[ZMod 2] V) c = c := fun c hc => by
    have h1 : restrC hx3 g = 1 := congrArg Subtype.val h.1
    have h2 := congrArg (fun e : ↥(fixSpace x) ≃ₗ[ZMod 2] ↥(fixSpace x) =>
      ((e ⟨c, hc⟩ : ↥(fixSpace x)) : V)) h1
    rw [restrC_apply] at h2
    exact h2
  have hM : ∀ z, F.coord ((g : V ≃ₗ[ZMod 2] V) (F.psi z)) = z := fun z => by
    have h1 : (restrM hx hF g : LinearMap.GeneralLinearGroup OmegaField (Fin k → OmegaField)) =
        1 := congrArg Subtype.val h.2
    have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup OmegaField (Fin k → OmegaField) =>
      (u : (Fin k → OmegaField) →ₗ[OmegaField] (Fin k → OmegaField)) z) h1
    exact h2
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨c, hc, m, hm, rfl⟩ := exists_fix_move hx3 v
  have hgm : (g : V ≃ₗ[ZMod 2] V) m = m := by
    have hmem : (g : V ≃ₗ[ZMod 2] V) (F.psi (F.coord m)) ∈ moveSpace x :=
      apply_mem_moveSpace_of_comm (mem_isoCent.1 g.2).2 (hF.psi_mem _)
    have h3 := hF.psi_coord _ hmem
    rw [hM, hF.psi_coord m hm] at h3
    exact h3.symm
  rw [map_add, hC c hc, hgm]
  rfl

theorem card_isoCent_dvd (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx3 : ∀ v, x (x (x v)) = v) {F : Frame Q x 3} (hF : Spans F) {n : ℕ}
    (hC : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSpace x))) = n) :
    Nat.card (isoCent Q x) ∣ n * 648 := by
  have h := Subgroup.card_dvd_of_injective _ (restrAll_injective hx hx3 hF)
  rwa [Nat.card_prod, hC, card_unitary_three] at h

end Embedding

end CFSG.AGLEmbedding.O10Cent
