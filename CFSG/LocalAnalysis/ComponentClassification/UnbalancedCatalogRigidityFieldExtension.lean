module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataFaithful
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalRealization

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs
  mem_unitMultiplierPairs_iff)

variable {K : Type} [Field K] {d : ℕ}

theorem map_mem_commutator {G H : Type*} [Group G] [Group H] (f : G →* H) {g : G}
    (hg : g ∈ commutator G) : f g ∈ commutator H := by
  have h : (commutator G).map f ≤ commutator H := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact h ⟨g, hg, rfl⟩

theorem mem_commutator_subtype_iff {G : Type*} [Group G] {H : Subgroup G} {g : H} :
    g ∈ commutator H ↔ (g : G) ∈ ⁅H, H⁆ := by
  have h : H.subtype g ∈ (commutator H).map H.subtype ↔ g ∈ commutator H :=
    Subgroup.mem_map_iff_mem H.subtype_injective
  rw [Subgroup.map_subtype_commutator] at h
  exact h.symm

@[expose] def pairSemilinearMap (g : coordinateSemilinearGroup d K) :
    (Fin d → K) →ₛₗ[(g.right : K →+* K)] (Fin d → K) where
  toFun := coordinateSemilinearMap g
  map_add' := map_add _
  map_smul' a v := coordinateSemilinearMap_smul g a v

theorem pairSemilinearMap_apply (g : coordinateSemilinearGroup d K) (v : Fin d → K) :
    pairSemilinearMap g v = coordinateSemilinearMap g v := rfl

theorem pair_eq_of_eq_on_span {g h : coordinateSemilinearGroup d K} (hgh : g.right = h.right)
    {s : Set (Fin d → K)} (hs : Submodule.span K s = ⊤)
    (heq : ∀ x ∈ s, coordinateSemilinearMap g x = coordinateSemilinearMap h x) : g = h := by
  have hmap : coordinateSemilinearMap g = coordinateSemilinearMap h := by
    apply AddEquiv.ext
    intro x
    have hx : x ∈ Submodule.span K s := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact heq x hx
    | zero => rw [map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul a x _ hx => rw [coordinateSemilinearMap_smul, coordinateSemilinearMap_smul, hx, hgh]
  exact SemidirectProduct.ext (coordinateSemilinearMap_matrix_eq g h hgh hmap) hgh

variable {Q : QuadraticForm K (Fin d → K)}

theorem pairSemilinearMap_quad {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    (v : Fin d → K) : Q (pairSemilinearMap S.val v) = S.val.right (Q v) :=
  (mem_unitMultiplierPairs_iff Q S).mp hS v

abbrev pairFix (S : similarityPairs Q) : Submodule (descentField S.val.right) (Fin d → K) :=
  fixSpace (pairSemilinearMap S.val)

abbrev pairDescentForm {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q) :
    QuadraticForm (descentField S.val.right) (pairFix S) :=
  descentForm (pairSemilinearMap_quad hS)

abbrev pairDescentDerived {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q) :
    Subgroup (pairFix S ≃ₗ[descentField S.val.right] pairFix S) :=
  ⁅TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS),
    TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)⁆

abbrev pairCentralizer (S : similarityPairs Q) : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  TauCeti.QuadraticMap.orthogonalGroup Q ⊓ semilinCentralizer (pairSemilinearMap S.val)

theorem semilinear_commute_of_mul_comm {R S : similarityPairs Q} (h : R * S = S * R)
    (v : Fin d → K) :
    coordinateSemilinearMap R.val (coordinateSemilinearMap S.val v) =
      coordinateSemilinearMap S.val (coordinateSemilinearMap R.val v) := by
  have h1 := congrArg (fun y : similarityPairs Q => coordinateSemilinearMap y.val v) h
  simpa only [Subgroup.coe_mul, coordinateSemilinearMap_mul] using h1

section Extension

variable {S : similarityPairs Q} {hS : S ∈ unitMultiplierPairs Q}
  (e : ↥(pairCentralizer S) ≃* ↥(TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)))

@[expose] def extHom :
    ↥(TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) →* GL (Fin d) K :=
  matrixLinearIso.symm.toMonoidHom.comp ((pairCentralizer S).subtype.comp e.symm.toMonoidHom)

theorem matrixLinearIso_extHom (g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) :
    matrixLinearIso (extHom e g) = (e.symm g : (Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  matrixLinearIso.apply_symm_apply _

theorem extHom_mulVec_eq (g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS))
    (x : Fin d → K) :
    ((extHom e g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ x =
      (e.symm g : (Fin d → K) ≃ₗ[K] (Fin d → K)) x := by
  rw [← matrixLinearIso_extHom]
  rfl

theorem extHom_injective : Function.Injective (extHom e) :=
  matrixLinearIso.symm.injective.comp (Subtype.val_injective.comp e.symm.injective)

theorem extHom_mem (g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) :
    extHom e g ∈ matrixIsometries Q := by
  change matrixLinearIso (extHom e g) ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  rw [matrixLinearIso_extHom]
  exact (e.symm g).2.1

theorem extHom_commute (g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS))
    (v : Fin d → K) :
    ((extHom e g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ coordinateSemilinearMap S.val v =
      coordinateSemilinearMap S.val
        (((extHom e g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) := by
  rw [extHom_mulVec_eq, extHom_mulVec_eq]
  exact (e.symm g).2.2 v

@[expose] def extIsometry :
    ↥(TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) →* matrixIsometries Q :=
  (extHom e).codRestrict _ (extHom_mem e)

theorem extIsometry_val (g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) :
    (extIsometry e g : GL (Fin d) K) = extHom e g := rfl

theorem extIsometry_injective : Function.Injective (extIsometry e) := fun _ _ hgh =>
  extHom_injective e (congrArg Subtype.val hgh)

theorem extHom_mulVec
    (he : ∀ g w, (((e g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) w : pairFix S) :
      Fin d → K) = (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) w)
    (g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) (w : pairFix S) :
    ((extHom e g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (w : Fin d → K) =
      (((g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) w : pairFix S) : Fin d → K) := by
  rw [extHom_mulVec_eq, ← he (e.symm g) w, MulEquiv.apply_symm_apply]

theorem extHom_unique
    (he : ∀ g w, (((e g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) w : pairFix S) :
      Fin d → K) = (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) w)
    (hspan : Submodule.span K (pairFix S : Set (Fin d → K)) = ⊤)
    (g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) (A : GL (Fin d) K)
    (hA : ∀ w : pairFix S, (A : Matrix (Fin d) (Fin d) K) *ᵥ (w : Fin d → K) =
      (((g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) w : pairFix S) : Fin d → K)) :
    A = extHom e g := by
  apply matrixLinearIso.injective
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on hspan fun w hw => ?_
  change (A : Matrix (Fin d) (Fin d) K) *ᵥ w =
    ((extHom e g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w
  rw [hA ⟨w, hw⟩, extHom_mulVec e he g ⟨w, hw⟩]

theorem extHom_mem_matrixDerived {g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)}
    (hg : (g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) ∈ pairDescentDerived hS) :
    extHom e g ∈ matrixDerived Q := by
  have h1 := map_mem_commutator (extIsometry e) (mem_commutator_subtype_iff.mpr hg)
  rw [mem_commutator_subtype_iff] at h1
  exact h1

theorem inclusion_extIsometry_commute
    (g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) :
    matrixIsometryInclusion Q (extIsometry e g) * S =
      S * matrixIsometryInclusion Q (extIsometry e g) := by
  apply Subtype.ext
  apply pair_eq_of_eq_on_span (s := Set.univ) (by
    change (SemidirectProduct.inl (extHom e g) * S.val).right =
      (S.val * SemidirectProduct.inl (extHom e g)).right
    simp) (Submodule.span_univ)
  intro x _
  change coordinateSemilinearMap (SemidirectProduct.inl (extHom e g) * S.val) x =
    coordinateSemilinearMap (S.val * SemidirectProduct.inl (extHom e g)) x
  rw [coordinateSemilinearMap_mul, coordinateSemilinearMap_mul, coordinateSemilinearMap_inl,
    coordinateSemilinearMap_inl, matrixLinearEquiv_apply, matrixLinearEquiv_apply]
  exact extHom_commute e g x

end Extension

end CFSG.ComponentClassification.UnbalancedCatalog
