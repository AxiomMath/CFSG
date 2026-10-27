module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Tactic.Abel

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Ident

section MAct

variable {E : Type} [Field E] {A : Type} [AddCommGroup A] [Module E A]

@[expose] def mAct (M : Matrix (Fin 2) (Fin 2) E) (x : A × A) : A × A :=
  (M 0 0 • x.1 + M 0 1 • x.2, M 1 0 • x.1 + M 1 1 • x.2)

theorem mAct_mul (M N : Matrix (Fin 2) (Fin 2) E) (x : A × A) :
    mAct (M * N) x = mAct M (mAct N x) := by
  simp only [mAct, Matrix.mul_apply, Fin.sum_univ_two, add_smul, smul_add, mul_smul, Prod.mk.injEq]
  constructor <;> abel

theorem mAct_one (x : A × A) : mAct (1 : Matrix (Fin 2) (Fin 2) E) x = x := by
  simp [mAct]

theorem mAct_inj [Nontrivial A] {M N : Matrix (Fin 2) (Fin 2) E}
    (h : ∀ x : A × A, mAct M x = mAct N x) : M = N := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  have key : ∀ c d : E, c • a = d • a → c = d := fun c d hcd => by
    by_contra hne
    apply ha
    have h1 : (c - d) • a = 0 := by rw [sub_smul, hcd, sub_self]
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact absurd (sub_eq_zero.mp h2) hne
    · exact h2
  have h1 := h (a, 0)
  have h2 := h (0, a)
  simp only [mAct, smul_zero, add_zero, zero_add, Prod.mk.injEq] at h1 h2
  ext i j
  fin_cases i <;> fin_cases j
  · exact key _ _ h1.1
  · exact key _ _ h2.1
  · exact key _ _ h1.2
  · exact key _ _ h2.2

variable {G : Type} [Group G]

theorem exists_mAct (ρ : G →* AddMonoid.End A)
    (hscal : ∀ φ : A →+ A, (∀ g a, φ (ρ g a) = ρ g (φ a)) → ∃ c : E, ∀ a, φ a = c • a)
    (φ : A × A →+ A × A)
    (hφ : ∀ (g : G) (x : A × A), φ (ρ g x.1, ρ g x.2) = (ρ g (φ x).1, ρ g (φ x).2)) :
    ∃ M : Matrix (Fin 2) (Fin 2) E, ∀ x, φ x = mAct M x := by
  have key : ∀ (p : A × A →+ A) (_ : ∀ (g : G) (x : A × A), p (ρ g x.1, ρ g x.2) = ρ g (p x))
      (q : A →+ A × A) (_ : ∀ (g : G) (a : A), q (ρ g a) = (ρ g (q a).1, ρ g (q a).2)),
      ∃ c : E, ∀ a, p (q a) = c • a := by
    intro p hp q hq
    refine hscal (p.comp q) (fun g a => ?_)
    show p (q (ρ g a)) = ρ g (p (q a))
    rw [hq g a]
    exact hp g (q a)
  have hinl : ∀ (g : G) (a : A), (AddMonoidHom.inl A A) (ρ g a) =
      (ρ g ((AddMonoidHom.inl A A) a).1, ρ g ((AddMonoidHom.inl A A) a).2) := by
    intro g a; simp
  have hinr : ∀ (g : G) (a : A), (AddMonoidHom.inr A A) (ρ g a) =
      (ρ g ((AddMonoidHom.inr A A) a).1, ρ g ((AddMonoidHom.inr A A) a).2) := by
    intro g a; simp
  have hfst : ∀ (g : G) (x : A × A), (AddMonoidHom.fst A A) (φ (ρ g x.1, ρ g x.2)) =
      ρ g ((AddMonoidHom.fst A A) (φ x)) := by
    intro g x; simp [hφ g x]
  have hsnd : ∀ (g : G) (x : A × A), (AddMonoidHom.snd A A) (φ (ρ g x.1, ρ g x.2)) =
      ρ g ((AddMonoidHom.snd A A) (φ x)) := by
    intro g x; simp [hφ g x]
  obtain ⟨α, hα⟩ := key ((AddMonoidHom.fst A A).comp φ) hfst (AddMonoidHom.inl A A) hinl
  obtain ⟨γ, hγ⟩ := key ((AddMonoidHom.snd A A).comp φ) hsnd (AddMonoidHom.inl A A) hinl
  obtain ⟨β, hβ⟩ := key ((AddMonoidHom.fst A A).comp φ) hfst (AddMonoidHom.inr A A) hinr
  obtain ⟨δ, hδ⟩ := key ((AddMonoidHom.snd A A).comp φ) hsnd (AddMonoidHom.inr A A) hinr
  refine ⟨!![α, β; γ, δ], fun x => ?_⟩
  have h1 := hα x.1
  have h2 := hγ x.1
  have h3 := hβ x.2
  have h4 := hδ x.2
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply,
    AddMonoidHom.coe_fst, AddMonoidHom.coe_snd] at h1 h2 h3 h4
  have hx : φ x = φ (x.1, 0) + φ (0, x.2) := by
    rw [← map_add]
    congr 1
    simp
  rw [hx]
  ext
  · simp [mAct, h1, h3]
  · simp [mAct, h2, h4]

end MAct

section Embed

variable {E : Type} [Field E] {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module E A]
  {G G' : Type} [Group G] [Group G']

theorem exists_embed_matrix [Nontrivial A]
    (ρ : G →* AddMonoid.End A) (ρB : G →* AddMonoid.End B) (σ : G' →* AddMonoid.End B)
    (Φ : A × A ≃+ B)
    (hΦ : ∀ (g : G) (x y : A), Φ (ρ g x, ρ g y) = ρB g (Φ (x, y)))
    (hcomm : ∀ (g : G) (g' : G') (b : B), σ g' (ρB g b) = ρB g (σ g' b))
    (hscal : ∀ φ : A →+ A, (∀ g a, φ (ρ g a) = ρ g (φ a)) → ∃ c : E, ∀ a, φ a = c • a)
    (hfaith : ∀ g' : G', (∀ b, σ g' b = b) → g' = 1) :
    ∃ f : G' →* Matrix (Fin 2) (Fin 2) E, Function.Injective f := by
  let Tf : G' → A × A → A × A := fun g' x => Φ.symm (σ g' (Φ x))
  have hTadd : ∀ g' x y, Tf g' (x + y) = Tf g' x + Tf g' y := fun g' x y => by
    simp [Tf, map_add]
  let T : G' → (A × A →+ A × A) := fun g' => AddMonoidHom.mk' (Tf g') (hTadd g')
  have hT_apply : ∀ g' x, T g' x = Φ.symm (σ g' (Φ x)) := fun _ _ => rfl
  have hTmul : ∀ g' h' x, T (g' * h') x = T g' (T h' x) := by
    intro g' h' x
    rw [hT_apply, hT_apply, hT_apply, map_mul, AddEquiv.apply_symm_apply]
    rfl
  have hT1 : ∀ x, T 1 x = x := by
    intro x
    rw [hT_apply, map_one]
    exact Φ.symm_apply_apply x
  have hρB : ∀ (g : G) (z : B), Φ.symm (ρB g z) =
      (ρ g (Φ.symm z).1, ρ g (Φ.symm z).2) := by
    intro g z
    rw [AddEquiv.symm_apply_eq, hΦ g, Prod.mk.eta, AddEquiv.apply_symm_apply]
  have hTρ : ∀ (g' : G') (g : G) (x : A × A),
      T g' (ρ g x.1, ρ g x.2) = (ρ g (T g' x).1, ρ g (T g' x).2) := by
    intro g' g x
    rw [hT_apply, hΦ g x.1 x.2, Prod.mk.eta, hcomm, hρB, hT_apply]
  choose M hM using fun g' => exists_mAct ρ hscal (T g') (fun g x => hTρ g' g x)
  have hM1 : M 1 = 1 := by
    refine mAct_inj (A := A) ?_
    intro x
    rw [← hM, hT1, mAct_one]
  refine ⟨{ toFun := M, map_one' := hM1, map_mul' := fun g h => ?_ }, ?_⟩
  · refine mAct_inj (A := A) ?_
    intro x
    rw [← hM, hTmul, hM, hM, mAct_mul]
  · rw [injective_iff_map_eq_one]
    intro g' hg'
    apply hfaith
    intro b
    have h1 : M g' = 1 := hg'
    have h2 := hM g' (Φ.symm b)
    rw [h1, mAct_one, hT_apply, AddEquiv.apply_symm_apply] at h2
    have := congrArg Φ h2
    rwa [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at this

end Embed

end CFSG.CGT.PushingUpLit.CGT6.Diag.Ident
