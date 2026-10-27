module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Ident

open scoped Matrix

theorem perfect_hom_one {G H : Type*} [Group G] [CommGroup H] [Group.IsPerfect G] (f : G →* H)
    (g : G) : f g = 1 := by
  have h1 : commutator G ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    simp [commutatorElement_def]
  have h2 : g ∈ commutator G := Group.IsPerfect.mem_commutator
  exact h1 h2

section Rep

variable {E : Type} [Field E] {A : Type} [AddCommGroup A] [Module E A] {G : Type} [Group G]

@[expose] def repLin (ρ : G →* AddMonoid.End A)
    (hlin : ∀ (g : G) (c : E) (a : A), ρ g (c • a) = c • ρ g a) : G →* Module.End E A where
  toFun g :=
    { toFun := ρ g
      map_add' := map_add _
      map_smul' := fun c a => hlin g c a }
  map_one' := by ext a; simp
  map_mul' g h := by ext a; simp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def repMat (ρ : G →* AddMonoid.End A)
    (hlin : ∀ (g : G) (c : E) (a : A), ρ g (c • a) = c • ρ g a) (b : Module.Basis ι E A) :
    G →* Matrix ι ι E :=
  (LinearMap.toMatrixAlgEquiv b : (Module.End E A) →* Matrix ι ι E).comp (repLin ρ hlin)

theorem repMat_mulVec (ρ : G →* AddMonoid.End A)
    (hlin : ∀ (g : G) (c : E) (a : A), ρ g (c • a) = c • ρ g a) (b : Module.Basis ι E A)
    (g : G) (a : A) : repMat ρ hlin b g *ᵥ b.repr a = b.repr (ρ g a) :=
  LinearMap.toMatrix_mulVec_repr b b (repLin ρ hlin g) a

theorem det_repMat [Group.IsPerfect G] (ρ : G →* AddMonoid.End A)
    (hlin : ∀ (g : G) (c : E) (a : A), ρ g (c • a) = c • ρ g a) (b : Module.Basis ι E A)
    (g : G) : (repMat ρ hlin b g).det = 1 := by
  have h := perfect_hom_one ((Matrix.detMonoidHom.comp (repMat ρ hlin b)).toHomUnits) g
  have h2 := congrArg (fun u : Eˣ => (u : E)) h
  simpa using h2

theorem eq_of_repMat_eq_one (ρ : G →* AddMonoid.End A)
    (hlin : ∀ (g : G) (c : E) (a : A), ρ g (c • a) = c • ρ g a) (b : Module.Basis ι E A)
    (g : G) (h : repMat ρ hlin b g = 1) (a : A) : ρ g a = a := by
  apply b.repr.injective
  ext i
  have := congrFun (repMat_mulVec ρ hlin b g a) i
  rw [h, Matrix.one_mulVec] at this
  exact this.symm

theorem finrank_ne_one [Finite A] [Group.IsPerfect G] (ρ : G →* AddMonoid.End A)
    (hlin : ∀ (g : G) (c : E) (a : A), ρ g (c • a) = c • ρ g a)
    (hnt : ∃ (g : G) (a : A), ρ g a ≠ a) : Module.finrank E A ≠ 1 := by
  intro hd
  let b : Module.Basis (Fin 1) E A := Module.finBasisOfFinrankEq E A hd
  obtain ⟨g, a, ha⟩ := hnt
  apply ha
  refine eq_of_repMat_eq_one ρ hlin b g ?_ a
  have h1 := det_repMat ρ hlin b g
  rw [Matrix.det_unique] at h1
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi
  subst hj
  simpa using h1

end Rep

section Final

variable {E : Type} [Field E] {A : Type} [AddCommGroup A] [Module E A] [Finite A]
  {G : Type} [Group G]

theorem exists_natSection {F : Type} [Field F] [Finite F] (ι : E ≃+* F)
    (ρ : G →* AddMonoid.End A)
    (hlin : ∀ (g : G) (c : E) (a : A), ρ g (c • a) = c • ρ g a)
    (hd : Module.finrank E A = 2) [Group.IsPerfect G] [IsSimpleGroup G]
    (hnt : ∃ (g : G) (a : A), ρ g a ≠ a)
    (hcard : Nat.card G = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F)) :
    ∃ (θ : G ≃* Matrix.SpecialLinearGroup (Fin 2) F) (β : A ≃+ (Fin 2 → F)),
      ∀ (g : G) (a : A), β (ρ g a) = (θ g : Matrix (Fin 2) (Fin 2) F) *ᵥ β a := by
  let b : Module.Basis (Fin 2) E A := Module.finBasisOfFinrankEq E A hd
  let R : G →* Matrix (Fin 2) (Fin 2) E := repMat ρ hlin b
  have hdet : ∀ g, (R g).det = 1 := fun g => det_repMat ρ hlin b g
  let RS : G →* Matrix.SpecialLinearGroup (Fin 2) E :=
    { toFun := fun g => ⟨R g, hdet g⟩
      map_one' := Subtype.ext (map_one R)
      map_mul' := fun g h => Subtype.ext (map_mul R g h) }
  have hRS : Function.Injective RS := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hker : RS.ker = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal RS.ker with h | h
      · exact h
      · exfalso
        obtain ⟨g₀, a₀, ha₀⟩ := hnt
        have h1 : g₀ ∈ RS.ker := by rw [h]; trivial
        apply ha₀
        have h2 : RS g₀ = 1 := MonoidHom.mem_ker.mp h1
        have h3 : R g₀ = 1 := congrArg
          (fun s : Matrix.SpecialLinearGroup (Fin 2) E => (s : Matrix (Fin 2) (Fin 2) E)) h2
        exact eq_of_repMat_eq_one ρ hlin b g₀ h3 a₀
    have : g ∈ RS.ker := hg
    rw [hker] at this
    exact Subgroup.mem_bot.mp this
  let θ' : G →* Matrix.SpecialLinearGroup (Fin 2) F :=
    (Matrix.SpecialLinearGroup.map ι.toRingHom).comp RS
  have hθ' : Function.Injective θ' := by
    intro g h hgh
    apply hRS
    apply Subtype.ext
    have := congrArg (fun s : Matrix.SpecialLinearGroup (Fin 2) F => (s : Matrix (Fin 2) (Fin 2) F))
      hgh
    simp only [θ', MonoidHom.comp_apply, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply] at this
    exact Matrix.map_injective ι.injective this
  have hbij : Function.Bijective θ' := (Nat.bijective_iff_injective_and_card θ').2 ⟨hθ', hcard⟩
  refine ⟨MulEquiv.ofBijective θ' hbij,
    b.equivFun.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => ι.toAddEquiv), ?_⟩
  intro g a
  ext i
  have h1 := congrFun (repMat_mulVec ρ hlin b g a) i
  have h2 := RingHom.map_mulVec ι.toRingHom (R g) (b.repr a) i
  show ι (b.repr (ρ g a) i) = (((R g).map ι) *ᵥ (fun j => ι (b.repr a j))) i
  rw [← h1]
  exact h2

end Final

end CFSG.CGT.PushingUpLit.CGT6.Diag.Ident
