module

public import CFSG.LieType.Chevalley.Monomial
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.Blueprint.ChevalleyWeyl
public import CFSG.LieType.BorelTits.WeightedMatrix
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.BorelTits

variable (τ : Tag) (K : Type) [Field K]

@[expose] def labelWt : Label τ → (Fin τ.rank → ℤ)
  | .inl _ => 0
  | .inr α => α.1

@[expose] noncomputable def weylElement (i : Fin τ.rank) : adjointGroup τ K :=
  ⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩

@[expose] noncomputable def torusElement (i : Fin τ.rank) (t : Kˣ) : adjointGroup τ K :=
  ⟨torusElt τ K i t, torusElt_mem_adjointGroup i t⟩

@[expose] noncomputable def monomialGroup : Subgroup (adjointGroup τ K) :=
  Subgroup.closure (Set.range (weylElement τ K) ∪
    Set.range fun x : Fin τ.rank × Kˣ => torusElement τ K x.1 x.2)

variable {τ K}

theorem hVec_eq_single (i : Fin τ.rank) : hVec τ K i = Finsupp.single (Sum.inl i) 1 := rfl

theorem rootVec_eq_single {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    rootVec τ K α = Finsupp.single (Sum.inr ⟨α, hα⟩) 1 := by
  simp [rootVec, hα]

theorem isMonomial_weylElement (i : Fin τ.rank) :
    IsMonomial (Finsupp.basisSingleOne) (labelWt τ) (glRep (adjointGroup τ K))
      (weylElement τ K i) (simple τ i) := by
  classical
  intro a c hac
  simp only [Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply,
    glRep_apply] at hac
  rcases c with k | ⟨α, hα⟩
  ·
    have h := weylElt_hVec (R := K) i k 1
    rw [hVec_eq_single, hVec_eq_single] at h
    change ((weylElt τ K i 1 : Module.End K (RootModule τ K)) (Finsupp.single (.inl k) 1)) a ≠ 0
      at hac
    rw [h] at hac
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] at hac
    have ha : a = .inl k ∨ a = .inl i := by
      by_contra! hne
      simp [Ne.symm hne.1, Ne.symm hne.2] at hac
    rcases ha with rfl | rfl <;> simp [labelWt]
  ·
    have h := weylElt_rootVec (R := K) i 1 hα
    rw [rootVec_eq_single hα, rootVec_eq_single (isRoot_reflect_iff i |>.mpr hα)] at h
    change ((weylElt τ K i 1 : Module.End K (RootModule τ K))
      (Finsupp.single (.inr ⟨α, hα⟩) 1)) a ≠ 0 at hac
    rw [h, Finsupp.smul_apply, Finsupp.single_apply] at hac
    split_ifs at hac with ha
    · subst ha
      simp [labelWt, simple_smul]
    · simp at hac

theorem isMonomial_torusElement (i : Fin τ.rank) (t : Kˣ) :
    IsMonomial (Finsupp.basisSingleOne) (labelWt τ) (glRep (adjointGroup τ K))
      (torusElement τ K i t) (1 : WeylGroup τ) := by
  classical
  intro a c hac
  simp only [Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply,
    glRep_apply] at hac
  rw [one_smul]
  rcases c with k | ⟨α, hα⟩
  · have h := torusElt_hVec (R := K) i k t
    rw [hVec_eq_single] at h
    change ((torusElt τ K i t : Module.End K (RootModule τ K)) (Finsupp.single (.inl k) 1)) a ≠ 0
      at hac
    rw [h, Finsupp.single_apply] at hac
    split_ifs at hac with ha
    · rw [← ha]
    · simp at hac
  · have h := torusElt_rootVec (R := K) i t hα
    rw [rootVec_eq_single hα] at h
    change ((torusElt τ K i t : Module.End K (RootModule τ K))
      (Finsupp.single (.inr ⟨α, hα⟩) 1)) a ≠ 0 at hac
    rw [h, Finsupp.smul_apply, Finsupp.single_apply] at hac
    split_ifs at hac with ha
    · rw [← ha]
    · simp at hac

theorem weylGroup_faithful_labelWt :
    ∀ w w' : WeylGroup τ, (∀ j, w • labelWt τ j = w' • labelWt τ j) → w = w' :=
  fun _ _ h => ext_single fun i => h (.inr ⟨Pi.single i 1, isRoot_single τ i⟩)

instance instFiniteModGL [Finite K] : Finite (ModGL τ K) := by
  have := Fintype.ofFinite (Label τ)
  have : Finite (RootModule τ K) :=
    Finite.of_equiv (Label τ → K) Finsupp.equivFunOnFinite.symm
  have : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  infer_instance

theorem isMonomialSubgroup_monomialGroup [Finite K] :
    IsMonomialSubgroup (WeylGroup τ) Finsupp.basisSingleOne (labelWt τ)
      (glRep (adjointGroup τ K)) (monomialGroup τ K) := by
  refine isMonomialSubgroup_closure ?_
  rintro x (⟨i, rfl⟩ | ⟨⟨i, t⟩, rfl⟩)
  · exact ⟨_, isMonomial_weylElement i⟩
  · exact ⟨1, isMonomial_torusElement i t⟩

variable (τ K) in
@[expose] noncomputable def weylHom [Finite K] : monomialGroup τ K →* WeylGroup τ :=
  monomialHom Finsupp.basisSingleOne (labelWt τ) (glRep (adjointGroup τ K))
    weylGroup_faithful_labelWt (monomialGroup τ K) isMonomialSubgroup_monomialGroup

theorem weylElement_mem_monomialGroup (i : Fin τ.rank) :
    weylElement τ K i ∈ monomialGroup τ K :=
  Subgroup.subset_closure (.inl ⟨i, rfl⟩)

theorem torusElement_mem_monomialGroup (i : Fin τ.rank) (t : Kˣ) :
    torusElement τ K i t ∈ monomialGroup τ K :=
  Subgroup.subset_closure (.inr ⟨(i, t), rfl⟩)

theorem isMonomial_weylHom [Finite K] (m : monomialGroup τ K) :
    IsMonomial Finsupp.basisSingleOne (labelWt τ) (glRep (adjointGroup τ K)) (m : adjointGroup τ K)
      (weylHom τ K m) :=
  isMonomial_monomialHom weylGroup_faithful_labelWt isMonomialSubgroup_monomialGroup m

theorem weylHom_weylElement [Finite K] (i : Fin τ.rank) :
    weylHom τ K ⟨weylElement τ K i, weylElement_mem_monomialGroup i⟩ = simple τ i :=
  monomialHom_eq weylGroup_faithful_labelWt isMonomialSubgroup_monomialGroup
    (isMonomial_weylElement i)

theorem weylHom_torusElement [Finite K] (i : Fin τ.rank) (t : Kˣ) :
    weylHom τ K ⟨torusElement τ K i t, torusElement_mem_monomialGroup i t⟩ = 1 :=
  monomialHom_eq weylGroup_faithful_labelWt isMonomialSubgroup_monomialGroup
    (isMonomial_torusElement i t)

end CFSG.LieType.Chevalley
