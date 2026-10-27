module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Assembly.InCatalog
public import CFSG.Open.PGLModelDefs
public import CFSG.Foundations.FullStandardCore

public section

namespace CFSG.Assembly

namespace ComponentType

@[expose] def IsTwoPComponent {X : Type*} [Group X] (L : Subgroup X) : Prop :=
  ∃ K : Subgroup (X ⧸ oddCore X), IsComponentOf K ⊤ ∧ IsSubnormal L ⊤ ∧
    L.map (QuotientGroup.mk' (oddCore X)) = K ∧
    ∀ J : Subgroup X, J < L → IsSubnormal J ⊤ → J.map (QuotientGroup.mk' (oddCore X)) ≠ K

@[expose] def LocalBProperty (G : Type*) [Group G] : Prop :=
  ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
    ∀ L : Subgroup (Subgroup.normalizer (S : Set G)), IsTwoPComponent L → IsComponentOf L ⊤

@[expose] def IsStandardSubgroup {G : Type*} [Group G] (L : Subgroup G) : Prop :=
  full_standard% FullStandardCore (IsQuasisimple L)
    (fun H g => H.map (MulAut.conj g).toMonoidHom) L

theorem isStandardSubgroup_eq_fullStandardCore {G : Type*} [Group G] (L : Subgroup G) :
    IsStandardSubgroup L =
      FullStandardCore (IsQuasisimple L) (fun H g => H.map (MulAut.conj g).toMonoidHom) L :=
  rfl

inductive ClassicalTag where
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus

@[expose] def ClassicalTag.Admissible : ClassicalTag → ℕ → ℕ → ℕ → Prop
  | .PSL, n, p, f => p.Prime ∧ 1 ≤ f ∧ 2 ≤ n ∧ ¬ (n = 2 ∧ (p ^ f = 2 ∨ p ^ f = 3))
  | .PSU, n, p, f => p.Prime ∧ 1 ≤ f ∧ 3 ≤ n ∧ ¬ (n = 3 ∧ p ^ f = 2)
  | .PSp, n, p, f => p.Prime ∧ 1 ≤ f ∧ 2 ≤ n ∧ ¬ (n = 2 ∧ p ^ f = 2)
  | .POmegaOdd, n, p, f => p.Prime ∧ 1 ≤ f ∧ 3 ≤ n ∧ p ≠ 2
  | .POmegaPlus, n, p, f => p.Prime ∧ 1 ≤ f ∧ 4 ≤ n
  | .POmegaMinus, n, p, f => p.Prime ∧ 1 ≤ f ∧ 4 ≤ n

section Models

variable (n p f : ℕ) [Fact p.Prime]

@[expose] noncomputable def pslModel : Subgroup (Matrix.ProjGenLinGroup (Fin n) (GaloisField p f)) :=
  PGLModel.projSL n (GaloisField p f)

@[expose] noncomputable def psuModel :
    Subgroup (Matrix.ProjGenLinGroup (Fin n) (GaloisField p (2 * f))) :=
  PGLModel.projSU n p f

abbrev symplecticForm (K : Type*) [Field K] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  PGLModel.sympForm n K

@[expose] noncomputable def pspModel :
    Subgroup (Matrix.ProjGenLinGroup (Fin n ⊕ Fin n) (GaloisField p f)) :=
  PGLModel.projSp n (GaloisField p f)

end Models

export CFSG.PGLModel (orthogonalGroup omegaModel)

@[expose] def quadOdd (n : ℕ) (K : Type*) [Field K] (v : (Fin n ⊕ Fin n) ⊕ Unit → K) : K :=
  ∑ i, v (.inl (.inl i)) * v (.inl (.inr i)) + v (.inr ()) ^ 2

@[expose] def quadPlus (n : ℕ) (K : Type*) [Field K] (v : Fin n ⊕ Fin n → K) : K :=
  ∑ i, v (.inl i) * v (.inr i)

@[expose] def quadMinus (n : ℕ) {K : Type*} [Field K] (b c : K)
    (v : (Fin (n - 1) ⊕ Fin (n - 1)) ⊕ Fin 2 → K) : K :=
  ∑ i, v (.inl (.inl i)) * v (.inl (.inr i)) + v (.inr 0) ^ 2 + b * v (.inr 0) * v (.inr 1) +
    c * v (.inr 1) ^ 2

@[expose] def ClassicalModel (X : Type) [Group X] (t : ClassicalTag) (n p f : ℕ) [Fact p.Prime] : Prop :=
  t.Admissible n p f ∧
    match t with
    | .PSL => Nonempty (X ≃* pslModel n p f)
    | .PSU => Nonempty (X ≃* psuModel n p f)
    | .PSp => Nonempty (X ≃* pspModel n p f)
    | .POmegaOdd => Nonempty (X ≃* omegaModel (quadOdd n (GaloisField p f)))
    | .POmegaPlus => Nonempty (X ≃* omegaModel (quadPlus n (GaloisField p f)))
    | .POmegaMinus => ∃ b c : GaloisField p f, (∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (X ≃* omegaModel (quadMinus n b c))

@[expose] def IsExceptionalIndex : TauCeti.LieTypeIndex → Prop
  | .E6 _ | .E7 _ | .E8 _ | .F4 _ | .G2 _ | .twistedE6 _ | .trialityD4 _ | .reeG2 _ => True
  | _ => False

@[expose] def OddLieType (X : Type) [Group X] : Prop :=
  (∃ (t : ClassicalTag) (n p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ ClassicalModel X t n p f) ∨
    ∃ d : TauCeti.ValidLieTypeIndex, IsExceptionalIndex d.1 ∧ d.1.characteristic ≠ 2 ∧
      Nonempty (X ≃* d.Group)

@[expose] def M11 : Subgroup (Equiv.Perm (Fin 11)) :=
  CFSG.Blueprint.NativeSporadic.M11

end ComponentType
end CFSG.Assembly
