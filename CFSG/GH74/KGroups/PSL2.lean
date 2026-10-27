module

public import CFSG.Blueprint.Catalog
public import CFSG.Adapters.LinearFieldTransport

public section

namespace CFSG.GH74.KGroups.PSL2

open Matrix

variable {F : Type*} [Field F] {q : ℕ}

@[expose] def vecP (e : Fin q → F) (i : Fin (q + 1)) : Fin 2 → F :=
  if h : i.val < q then ![1, e ⟨i, h⟩] else ![0, 1]

theorem vecP_ne_zero (e : Fin q → F) (i : Fin (q + 1)) : vecP e i ≠ 0 := by
  unfold vecP
  split_ifs
  · intro h
    have := congrFun h 0
    simp at this
  · intro h
    have := congrFun h 1
    simp at this

@[expose] def pt (e : Fin q → F) (i : Fin (q + 1)) : Projectivization F (Fin 2 → F) :=
  Projectivization.mk F (vecP e i) (vecP_ne_zero e i)

theorem pt_injective (e : Fin q → F) (he : Function.Injective e) : Function.Injective (pt e) := by
  intro i j hij
  unfold pt at hij
  rw [Projectivization.mk_eq_mk_iff'] at hij
  obtain ⟨a, ha⟩ := hij
  unfold vecP at ha
  by_cases hi : i.val < q <;> by_cases hj : j.val < q <;>
    simp only [hi, hj, dite_true, dite_false] at ha
  · have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    simp at h0 h1
    subst h0
    have h2 : (⟨i, hi⟩ : Fin q) = ⟨j, hj⟩ := he (by simpa using h1.symm)
    have h3 : i.val = j.val := by simpa using congrArg Fin.val h2
    exact Fin.ext h3
  · have h0 := congrFun ha 0
    simp at h0
  · have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    simp at h0 h1
    subst h0
    simp at h1
  · exact Fin.ext (by omega)

theorem pt_surjective (e : Fin q → F) (he : Function.Surjective e) : Function.Surjective (pt e) := by
  intro p
  induction p using Projectivization.ind with
  | _ v hv =>
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext i
        fin_cases i <;> simp [h0, h1]
      refine ⟨Fin.last _, ?_⟩
      unfold pt
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨(v 1)⁻¹, ?_⟩
      simp only [vecP, Fin.val_last, lt_irrefl, dite_false]
      ext i
      fin_cases i <;> simp [h0, h1]
    · obtain ⟨k, hk⟩ := he (v 1 / v 0)
      refine ⟨⟨k.val, by omega⟩, ?_⟩
      unfold pt
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨(v 0)⁻¹, ?_⟩
      simp only [vecP, k.2, dite_true]
      ext i
      fin_cases i
      · simp [h0]
      · simp [hk]; field_simp

@[expose] noncomputable def ptEquiv (e : Fin q → F) (he : Function.Bijective e) :
    Fin (q + 1) ≃ Projectivization F (Fin 2 → F) :=
  Equiv.ofBijective (pt e) ⟨pt_injective e he.1, pt_surjective e he.2⟩

theorem ptEquiv_apply (e : Fin q → F) (he : Function.Bijective e) (i : Fin (q + 1)) :
    ptEquiv e he i = pt e i := rfl

variable {N : ℕ}

@[expose] noncomputable def permHom (E : Fin N ≃ Projectivization F (Fin 2 → F)) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F →* Equiv.Perm (Fin N) where
  toFun g := E.trans ((MulAction.toPerm g).trans E.symm)
  map_one' := by
    ext i
    simp
  map_mul' g h := by
    ext i
    simp [mul_smul]

theorem permHom_apply (E : Fin N ≃ Projectivization F (Fin 2 → F))
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (i : Fin N) :
    E (permHom E g i) = g • E i := by
  simp [permHom]

theorem permHom_injective (E : Fin N ≃ Projectivization F (Fin 2 → F)) :
    Function.Injective (permHom E : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F →* _) := by
  intro g h hgh
  have : MulAction.toPerm g =
      (MulAction.toPerm h : Equiv.Perm (Projectivization F (Fin 2 → F))) := by
    ext x
    have := congrArg (fun σ : Equiv.Perm (Fin N) => E (σ (E.symm x))) hgh
    simpa [permHom_apply] using this
  exact MulAction.toPerm_injective this

theorem permHom_mk_eq (E : Fin N ≃ Projectivization F (Fin 2 → F))
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (p : Equiv.Perm (Fin N))
    (h : ∀ i, E (p i) = A • E i) :
    permHom E (A : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = p := by
  refine Equiv.ext fun i => ?_
  apply E.injective
  rw [permHom_apply, h]
  rfl

theorem psl2_equiv_closure [Finite F] (E : Fin N ≃ Projectivization F (Fin 2 → F))
    (a b : Matrix.SpecialLinearGroup (Fin 2) F) (pa pb : Equiv.Perm (Fin N))
    (ha : ∀ i, E (pa i) = a • E i) (hb : ∀ i, E (pb i) = b • E i)
    (P : Subgroup (Equiv.Perm (Fin N))) (hP : P = Subgroup.closure {pa, pb})
    (hcard : Nat.card P = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* P) := by
  have hinj := permHom_injective E (F := F)
  have hrange : P = (permHom E : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F →* _).range := by
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

theorem pointwise_of_exists (e : Fin q → F) (he : Function.Bijective e)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (p : Equiv.Perm (Fin (q + 1)))
    (h : ∀ i, ∃ c : F, c • ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ vecP e i) = vecP e (p i)) :
    ∀ i, ptEquiv e he (p i) = A • ptEquiv e he i := by
  intro i
  rw [ptEquiv_apply, ptEquiv_apply]
  unfold pt
  rw [Projectivization.smul_mk]
  rw [Projectivization.mk_eq_mk_iff']
  exact h i

section Model

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem stated_of_lieModel_psl {K : Type} [Group K] {n p f : ℕ} (h : LieModel K .PSL n p f) :
    StatedClassicalModel K .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem psl2_equiv_of_stated {K : Type} [Group K] {F : Type} [Field F] [Finite F] (p f : ℕ)
    [Fact p.Prime] (hf : 0 < f) (hF : Nat.card F = p ^ f)
    (h : StatedClassicalModel K .PSL 2 p f) :
    Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  obtain ⟨-, F', hF1, hF2, hF', ⟨e⟩⟩ := h
  have e1 := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F' 2 p f hf hF'
  have e2 := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField F p f hf hF).symm (Fin 2)
  exact ⟨e.trans (e1.trans e2)⟩

theorem psl2_equiv_of_lieModel {K : Type} [Group K] {F : Type} [Field F] [Finite F] (p f : ℕ)
    [Fact p.Prime] (hf : 0 < f) (hF : Nat.card F = p ^ f) (h : LieModel K .PSL 2 p f) :
    Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
  psl2_equiv_of_stated p f hf hF (stated_of_lieModel_psl h)

end Model

end CFSG.GH74.KGroups.PSL2
