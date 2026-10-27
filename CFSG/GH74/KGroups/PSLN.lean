module

public import CFSG.Blueprint.Catalog
public import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.GH74.KGroups.PSLN

open Matrix

variable {F : Type*} [Field F] {ι : Type*} {N : ℕ}

@[expose] noncomputable def ptEquivOf (vec : Fin N → (ι → F)) (hne : ∀ i, vec i ≠ 0)
    (hinj : ∀ i j (c : F), c • vec j = vec i → i = j)
    (hsurj : ∀ v : ι → F, v ≠ 0 → ∃ i, ∃ c : F, c • v = vec i) :
    Fin N ≃ Projectivization F (ι → F) :=
  Equiv.ofBijective (fun i => Projectivization.mk F (vec i) (hne i)) (by
    constructor
    · intro i j hij
      rw [Projectivization.mk_eq_mk_iff'] at hij
      obtain ⟨c, hc⟩ := hij
      exact hinj i j c hc
    · intro p
      induction p using Projectivization.ind with
      | _ v hv =>
        obtain ⟨i, c, hc⟩ := hsurj v hv
        refine ⟨i, ?_⟩
        rw [Projectivization.mk_eq_mk_iff']
        exact ⟨c, hc⟩)

theorem ptEquivOf_apply (vec : Fin N → (ι → F)) (hne : ∀ i, vec i ≠ 0)
    (hinj : ∀ i j (c : F), c • vec j = vec i → i = j)
    (hsurj : ∀ v : ι → F, v ≠ 0 → ∃ i, ∃ c : F, c • v = vec i) (i : Fin N) :
    ptEquivOf vec hne hinj hsurj i = Projectivization.mk F (vec i) (hne i) := rfl

variable [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def permHom (E : Fin N ≃ Projectivization F (ι → F)) :
    Matrix.ProjectiveSpecialLinearGroup ι F →* Equiv.Perm (Fin N) where
  toFun g := E.trans ((MulAction.toPerm g).trans E.symm)
  map_one' := by
    ext i
    simp
  map_mul' g h := by
    ext i
    simp [mul_smul]

theorem permHom_apply (E : Fin N ≃ Projectivization F (ι → F))
    (g : Matrix.ProjectiveSpecialLinearGroup ι F) (i : Fin N) :
    E (permHom E g i) = g • E i := by
  simp [permHom]

theorem permHom_injective (E : Fin N ≃ Projectivization F (ι → F)) :
    Function.Injective (permHom E : Matrix.ProjectiveSpecialLinearGroup ι F →* _) := by
  intro g h hgh
  have : MulAction.toPerm g =
      (MulAction.toPerm h : Equiv.Perm (Projectivization F (ι → F))) := by
    ext x
    have := congrArg (fun σ : Equiv.Perm (Fin N) => E (σ (E.symm x))) hgh
    simpa [permHom_apply] using this
  exact MulAction.toPerm_injective this

theorem permHom_mk_eq (E : Fin N ≃ Projectivization F (ι → F))
    (A : Matrix.SpecialLinearGroup ι F) (p : Equiv.Perm (Fin N))
    (h : ∀ i, E (p i) = A • E i) :
    permHom E (A : Matrix.ProjectiveSpecialLinearGroup ι F) = p := by
  refine Equiv.ext fun i => ?_
  apply E.injective
  rw [permHom_apply, h]
  rfl

theorem psl_equiv_closure [Finite F] (E : Fin N ≃ Projectivization F (ι → F))
    (a b : Matrix.SpecialLinearGroup ι F) (pa pb : Equiv.Perm (Fin N))
    (ha : ∀ i, E (pa i) = a • E i) (hb : ∀ i, E (pb i) = b • E i)
    (P : Subgroup (Equiv.Perm (Fin N))) (hP : P = Subgroup.closure {pa, pb})
    (hcard : Nat.card P = Nat.card (Matrix.ProjectiveSpecialLinearGroup ι F)) :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup ι F ≃* P) := by
  have hinj := permHom_injective E (F := F) (ι := ι)
  have hrange : P = (permHom E : Matrix.ProjectiveSpecialLinearGroup ι F →* _).range := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [hP, Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨_, permHom_mk_eq E a _ ha⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨_, permHom_mk_eq E b _ hb⟩
    · rw [hcard, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)⟩

theorem pointwise_of_exists (vec : Fin N → (ι → F)) (hne : ∀ i, vec i ≠ 0)
    (hinj : ∀ i j (c : F), c • vec j = vec i → i = j)
    (hsurj : ∀ v : ι → F, v ≠ 0 → ∃ i, ∃ c : F, c • v = vec i)
    (A : Matrix.SpecialLinearGroup ι F) (p : Equiv.Perm (Fin N))
    (h : ∀ i, ∃ c : F, c • ((A : Matrix ι ι F) *ᵥ vec i) = vec (p i)) :
    ∀ i, ptEquivOf vec hne hinj hsurj (p i) = A • ptEquivOf vec hne hinj hsurj i := by
  intro i
  rw [ptEquivOf_apply, ptEquivOf_apply, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff']
  exact h i

theorem card_psl_of_center_bot (h : Subgroup.center (Matrix.SpecialLinearGroup ι F) = ⊥) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup ι F) =
      Nat.card (Matrix.SpecialLinearGroup ι F) := by
  have e : Matrix.ProjectiveSpecialLinearGroup ι F ≃* Matrix.SpecialLinearGroup ι F :=
    (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot
  exact Nat.card_congr e.toEquiv

section Model

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem stated_of_lieModel_psl {K : Type} [Group K] {n p f : ℕ} (h : LieModel K .PSL n p f) :
    StatedClassicalModel K .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem psl_equiv_of_stated {K : Type} [Group K] {F : Type} [Field F] [Finite F] (n p f : ℕ)
    [Fact p.Prime] (hf : 0 < f) (hF : Nat.card F = p ^ f)
    (h : StatedClassicalModel K .PSL n p f) :
    Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) F) := by
  obtain ⟨-, F', hF1, hF2, hF', ⟨e⟩⟩ := h
  have e1 := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F' n p f hf hF'
  have e2 := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField F p f hf hF).symm (Fin n)
  exact ⟨e.trans (e1.trans e2)⟩

theorem psl_equiv_of_lieModel {K : Type} [Group K] {F : Type} [Field F] [Finite F] (n p f : ℕ)
    [Fact p.Prime] (hf : 0 < f) (hF : Nat.card F = p ^ f) (h : LieModel K .PSL n p f) :
    Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) F) :=
  psl_equiv_of_stated n p f hf hF (stated_of_lieModel_psl h)

end Model

end CFSG.GH74.KGroups.PSLN
