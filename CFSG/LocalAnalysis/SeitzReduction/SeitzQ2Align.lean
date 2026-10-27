module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

public section

namespace CFSG.SeitzReduction.SeitzQ2

section Prod

variable {A : Type*} [Group A]

theorem eq_one_of_forall_mul_comm_of_center_eq_bot (hZ : Subgroup.center A = ⊥) :
    ∀ a : A, (∀ b : A, a * b = b * a) → a = 1 := fun a ha => by
  have h : a ∈ Subgroup.center A := Subgroup.mem_center_iff.2 fun b => (ha b).symm
  rw [hZ] at h
  exact h

theorem apply_one_left_of_fix_diag (θ : MulAut (A × A)) (hdiag : ∀ a : A, θ (a, a) = (a, a))
    (b : A) : θ (1, b) = (b, b) * θ (b⁻¹, 1) := by
  have h : ((1 : A), b) = (b, b) * (b⁻¹, 1) := by ext <;> simp
  rw [h, map_mul, hdiag]

theorem eq_one_of_fix_diag_of_snd (hZ : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1)
    (θ : MulAut (A × A)) (hdiag : ∀ a : A, θ (a, a) = (a, a)) (h : ∀ a, (θ (a, 1)).2 = 1) :
    θ = 1 := by
  set φ : A →* A := (MonoidHom.fst A A).comp (θ.toMonoidHom.comp (MonoidHom.inl A A)) with hφ
  have hφa : ∀ a, φ a = (θ (a, 1)).1 := fun a => rfl
  have hθa : ∀ a, θ (a, 1) = (φ a, 1) := fun a => Prod.ext (hφa a).symm (h a)
  have hθb : ∀ b, θ (1, b) = (b * φ b⁻¹, b) := by
    intro b
    rw [apply_one_left_of_fix_diag θ hdiag, hθa]
    ext <;> simp
  have hsurj : ∀ c, ∃ a, φ a = c := by
    intro c
    obtain ⟨⟨a, b⟩, hab⟩ := θ.surjective (c, 1)
    have hsplit : ((a, b) : A × A) = (a, 1) * (1, b) := by ext <;> simp
    rw [hsplit, map_mul, hθa, hθb] at hab
    have hb : b = 1 := by simpa using congrArg Prod.snd hab
    subst hb
    exact ⟨a, by simpa using congrArg Prod.fst hab⟩
  have hcen : ∀ b, b * φ b⁻¹ = 1 := by
    intro b
    refine hZ _ fun c => ?_
    obtain ⟨a, rfl⟩ := hsurj c
    have hc : ((a, 1) : A × A) * (1, b) = (1, b) * (a, 1) := by ext <;> simp
    have h1 := congrArg Prod.fst (congrArg θ hc)
    rw [map_mul, map_mul, hθa, hθb] at h1
    simpa using h1.symm
  have hφid : ∀ b, φ b = b := by
    intro b
    have h1 := hcen b⁻¹
    rw [inv_inv] at h1
    calc φ b = b⁻¹⁻¹ * (b⁻¹ * φ b) := by group
      _ = b := by rw [h1, mul_one, inv_inv]
  refine MulEquiv.ext fun x => ?_
  obtain ⟨a, b⟩ := x
  have hsplit : ((a, b) : A × A) = (a, 1) * (1, b) := by ext <;> simp
  rw [MulAut.one_apply, hsplit, map_mul, hθa, hθb, hφid, hφid]
  ext <;> simp

theorem eq_one_or_eq_prodComm_of_fix_diag
    (hZ : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1) (θ : MulAut (A × A))
    (hdiag : ∀ a : A, θ (a, a) = (a, a))
    (hfac : (∀ a, (θ (a, 1)).2 = 1) ∨ (∀ a, (θ (a, 1)).1 = 1)) :
    θ = 1 ∨ θ = MulEquiv.prodComm := by
  rcases hfac with h | h
  · exact Or.inl (eq_one_of_fix_diag_of_snd hZ θ hdiag h)
  · right
    have h1 : (MulEquiv.prodComm : MulAut (A × A)) * θ = 1 := by
      refine eq_one_of_fix_diag_of_snd hZ _ (fun a => ?_) (fun a => ?_)
      · rw [MulAut.mul_apply, hdiag]
        rfl
      · rw [MulAut.mul_apply]
        exact h a
    have h2 : θ = (MulEquiv.prodComm : MulAut (A × A))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact MulEquiv.ext fun x => rfl

theorem fac_of_fix_diag_of_isSimpleGroup [IsSimpleGroup A]
    (hZ : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1) (θ : MulAut (A × A))
    (hdiag : ∀ a : A, θ (a, a) = (a, a)) :
    (∀ a, (θ (a, 1)).2 = 1) ∨ (∀ a, (θ (a, 1)).1 = 1) := by
  set α : A →* A := (MonoidHom.fst A A).comp (θ.toMonoidHom.comp (MonoidHom.inl A A)) with hα
  set β : A →* A := (MonoidHom.snd A A).comp (θ.toMonoidHom.comp (MonoidHom.inl A A)) with hβ
  have hθa : ∀ a, θ (a, 1) = (α a, β a) := fun a => rfl
  have hθb : ∀ b, θ (1, b) = (b * α b⁻¹, b * β b⁻¹) := by
    intro b
    rw [apply_one_left_of_fix_diag θ hdiag, hθa]
    rfl
  have hconj : ∀ (x : A × A) (a : A), θ (x * (a, 1) * x⁻¹) = θ x * θ (a, 1) * (θ x)⁻¹ := by
    intro x a
    rw [map_mul, map_mul, map_inv]
  have hx1 : ∀ (x : A × A) (a : A), x * (a, 1) * x⁻¹ = (x.1 * a * x.1⁻¹, 1) := by
    intro x a
    ext <;> simp
  have hnα : α.range.Normal := by
    refine ⟨fun y hy c => ?_⟩
    obtain ⟨a, rfl⟩ := hy
    set x := θ.symm (c, 1) with hx
    have h1 := congrArg Prod.fst (hconj x a)
    simp only [hx1, hx, MulEquiv.apply_symm_apply, hθa, Prod.fst_mul, Prod.fst_inv] at h1
    exact ⟨_, h1⟩
  have hnβ : β.range.Normal := by
    refine ⟨fun y hy c => ?_⟩
    obtain ⟨a, rfl⟩ := hy
    set x := θ.symm (1, c) with hx
    have h1 := congrArg Prod.snd (hconj x a)
    simp only [hx1, hx, MulEquiv.apply_symm_apply, hθa, Prod.snd_mul, Prod.snd_inv] at h1
    exact ⟨_, h1⟩
  have hcomm : ∀ a b, θ (a, 1) * θ (1, b) = θ (1, b) * θ (a, 1) := by
    intro a b
    rw [← map_mul, ← map_mul]
    congr 1
    ext <;> simp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal α.range with hα0 | hα1
  · right
    intro a
    have : α a ∈ α.range := ⟨a, rfl⟩
    rw [hα0] at this
    exact this
  · left
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal β.range with hβ0 | hβ1
    · intro a
      have : β a ∈ β.range := ⟨a, rfl⟩
      rw [hβ0] at this
      exact this
    · exfalso
      have hαid : ∀ b, b * α b⁻¹ = 1 := by
        intro b
        refine hZ _ fun c => ?_
        obtain ⟨a, rfl⟩ : c ∈ α.range := hα1 ▸ Subgroup.mem_top c
        have h1 := congrArg Prod.fst (hcomm a b)
        rw [hθa, hθb] at h1
        simpa using h1.symm
      have hβid : ∀ b, b * β b⁻¹ = 1 := by
        intro b
        refine hZ _ fun c => ?_
        obtain ⟨a, rfl⟩ : c ∈ β.range := hβ1 ▸ Subgroup.mem_top c
        have h1 := congrArg Prod.snd (hcomm a b)
        rw [hθa, hθb] at h1
        simpa using h1.symm
      obtain ⟨b, hb⟩ := exists_ne (1 : A)
      have h1 : θ (b, 1) = θ (b, b) := by
        rw [hθa, hdiag]
        have e1 := hαid b⁻¹
        have e2 := hβid b⁻¹
        rw [inv_inv] at e1 e2
        ext
        · exact (eq_of_inv_mul_eq_one e1).symm
        · exact (eq_of_inv_mul_eq_one e2).symm
      have h2 := congrArg Prod.snd (θ.injective h1)
      exact hb h2.symm

theorem eq_one_or_eq_prodComm_of_fix_diag_of_isSimpleGroup [IsSimpleGroup A]
    (hZ : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1) (θ : MulAut (A × A))
    (hdiag : ∀ a : A, θ (a, a) = (a, a)) : θ = 1 ∨ θ = MulEquiv.prodComm :=
  eq_one_or_eq_prodComm_of_fix_diag hZ θ hdiag (fac_of_fix_diag_of_isSimpleGroup hZ θ hdiag)

theorem eq_or_eq_comp_prodComm_of_range_eq [IsSimpleGroup A]
    (hZ : ∀ a : A, (∀ b : A, a * b = b * a) → a = 1) {G : Type*} [Group G]
    {Ψ₁ Ψ₂ : A × A →* G} (h₁ : Function.Injective Ψ₁) (h₂ : Function.Injective Ψ₂)
    (hr : Ψ₂.range = Ψ₁.range) (hd : ∀ a, Ψ₂ (a, a) = Ψ₁ (a, a)) :
    Ψ₂ = Ψ₁ ∨ Ψ₂ = Ψ₁.comp (MulEquiv.prodComm : A × A ≃* A × A).toMonoidHom := by
  set θ : MulAut (A × A) := (MonoidHom.ofInjective h₂).trans
    ((MulEquiv.subgroupCongr hr).trans (MonoidHom.ofInjective h₁).symm) with hθ
  have hΨθ : ∀ x, Ψ₁ (θ x) = Ψ₂ x := by
    intro x
    rw [hθ, MulEquiv.trans_apply, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm]
    rfl
  have hdiag : ∀ a : A, θ (a, a) = (a, a) := fun a => h₁ (by rw [hΨθ, hd])
  rcases eq_one_or_eq_prodComm_of_fix_diag_of_isSimpleGroup hZ θ hdiag with h | h
  · left
    ext x
    rw [← hΨθ, h, MulAut.one_apply]
  · right
    ext x
    rw [← hΨθ, h]
    rfl

end Prod

section Closure

variable {ι : Type*}

inductive TriangleClosure (S : ι → ι → Prop) (T : ι → ι → ι → Prop) : ι → ι → Prop
  | base {a b : ι} : S a b → TriangleClosure S T a b
  | symm {a b : ι} : TriangleClosure S T a b → TriangleClosure S T b a
  | tri {a b c : ι} : T a b c → TriangleClosure S T a b → TriangleClosure S T b c →
      TriangleClosure S T a c

variable {A : Type*} [Group A]

theorem eq_mul_inv_of_triangleClosure {S : ι → ι → Prop} {T : ι → ι → ι → Prop}
    {τ : ι → ι → A} {σ : ι → A} (hS : ∀ a b, S a b → τ a b = σ a * (σ b)⁻¹)
    (hsymm : ∀ a b, TriangleClosure S T a b → τ b a = (τ a b)⁻¹)
    (hT : ∀ a b c, T a b c → TriangleClosure S T a b → TriangleClosure S T b c →
      τ a c = τ a b * τ b c) {a b : ι}
    (h : TriangleClosure S T a b) : τ a b = σ a * (σ b)⁻¹ := by
  induction h with
  | base h => exact hS _ _ h
  | symm h ih => rw [hsymm _ _ h, ih]; group
  | tri ht h₁ h₂ ih₁ ih₂ => rw [hT _ _ _ ht h₁ h₂, ih₁, ih₂]; group

@[expose] def TreeEdge (p : ι → ι) (d : ι → ℕ) (a b : ι) : Prop :=
  p a = b ∧ d b < d a

noncomputable def treePotential (τ : ι → ι → A) (p : ι → ι) (d : ι → ℕ) : ι → A :=
  (measure d).wf.fix fun a rec => if h : d (p a) < d a then τ a (p a) * rec (p a) h else 1

theorem treePotential_of_lt (τ : ι → ι → A) {p : ι → ι} {d : ι → ℕ} {a : ι}
    (h : d (p a) < d a) : treePotential τ p d a = τ a (p a) * treePotential τ p d (p a) := by
  rw [treePotential, WellFounded.fix_eq, dite_eq_left h]

theorem eq_mul_inv_treePotential (τ : ι → ι → A) {p : ι → ι} {d : ι → ℕ} {a b : ι}
    (h : TreeEdge p d a b) :
    τ a b = treePotential τ p d a * (treePotential τ p d b)⁻¹ := by
  obtain ⟨rfl, h⟩ := h
  rw [treePotential_of_lt τ h]
  group

theorem eq_mul_inv_treePotential_of_triangleClosure (τ : ι → ι → A) {p : ι → ι}
    {d : ι → ℕ} {T : ι → ι → ι → Prop}
    (hsymm : ∀ a b, TriangleClosure (TreeEdge p d) T a b → τ b a = (τ a b)⁻¹)
    (hT : ∀ a b c, T a b c → TriangleClosure (TreeEdge p d) T a b →
      TriangleClosure (TreeEdge p d) T b c → τ a c = τ a b * τ b c) {a b : ι}
    (h : TriangleClosure (TreeEdge p d) T a b) :
    τ a b = treePotential τ p d a * (treePotential τ p d b)⁻¹ :=
  eq_mul_inv_of_triangleClosure (S := TreeEdge p d) (σ := treePotential τ p d)
    (fun _ _ he => eq_mul_inv_treePotential τ he) hsymm hT h

end Closure

end CFSG.SeitzReduction.SeitzQ2
