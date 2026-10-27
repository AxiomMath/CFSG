module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7C2b

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

abbrev V4 : Type := Fin 2 × Fin 2 × Fin 2 × Fin 2

@[expose] def addV (v w : V4) : V4 :=
  (v.1 + w.1, v.2.1 + w.2.1, v.2.2.1 + w.2.2.1, v.2.2.2 + w.2.2.2)

@[expose] def smulV (a : Fin 2) (v : V4) : V4 := if a = 0 then (0, 0, 0, 0) else v

@[expose] def vecE : Fin 4 → V4 := ![(1, 0, 0, 0), (1, 0, 1, 0), (0, 0, 0, 1), (0, 1, 0, 1)]

@[expose] def Mσ (σ : Perm (Fin 4)) (v : V4) : V4 :=
  addV (addV (addV (smulV v.1 (vecE (σ 0))) (smulV v.2.1 (addV (vecE (σ 2)) (vecE (σ 3)))))
    (smulV v.2.2.1 (addV (vecE (σ 0)) (vecE (σ 1))))) (smulV v.2.2.2 (vecE (σ 2)))

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Case2

variable (C : S.Case2)

@[expose] noncomputable def wordV (v : V4) : X := C.word v.1 v.2.1 v.2.2.1 v.2.2.2

theorem wordV_mem (v : V4) : C.wordV v ∈ S.E C.yb := C.word_mem _ _ _ _

theorem wordV_add (v w : V4) : C.wordV (addV v w) = C.wordV v * C.wordV w :=
  (C.word_mul _ _ _ _ _ _ _ _).symm

theorem wordV_smul (a : Fin 2) (v : V4) : C.wordV (smulV a v) = C.wordV v ^ (a : ℕ) := by
  fin_cases a
  · simp [smulV, wordV, word]
  · simp [smulV]

theorem wordV_injective {v w : V4} (h : C.wordV v = C.wordV w) : v = w := by
  obtain ⟨h1, h2, h3, h4⟩ := C.word_injective h
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

theorem exists_wordV {g : X} (hg : g ∈ S.E C.yb) : ∃ v : V4, g = C.wordV v := by
  obtain ⟨a, b, c, d, rfl⟩ := C.exists_word hg
  exact ⟨(a, b, c, d), rfl⟩

@[expose] noncomputable def e (i : Fin 4) : X := C.wordV (vecE i)

theorem e_zero : C.e 0 = S.t := by simp [e, wordV, word, vecE]

theorem e_one : C.e 1 = S.t * C.f := by simp [e, wordV, word, vecE]

theorem e_two : C.e 2 = C.u := by simp [e, wordV, word, vecE]

theorem e_three : C.e 3 = S.z * C.u := by simp [e, wordV, word, vecE]

theorem e_injective : Function.Injective C.e := by
  intro i j h
  have := C.wordV_injective h
  clear h
  revert this
  revert i j
  decide

theorem e_mem (i : Fin 4) : C.e i ∈ S.E C.yb := C.wordV_mem _

theorem conjTo_e (i : Fin 4) : ConjTo S.t (C.e i) := by
  rw [C.omega_big _ (C.e_mem i)]
  fin_cases i
  · exact Or.inl C.e_zero
  · exact Or.inr (Or.inl C.e_one)
  · exact Or.inr (Or.inr (Or.inl C.e_two))
  · exact Or.inr (Or.inr (Or.inr C.e_three))

theorem exists_index {n : X} (hn : n ∈ normalizer (S.E C.yb : Set X)) (i : Fin 4) :
    ∃ j, n * C.e i * n⁻¹ = C.e j := by
  have hE : n * C.e i * n⁻¹ ∈ S.E C.yb := (mem_normalizer_iff.mp hn _).mp (C.e_mem i)
  have hc : ConjTo S.t (n * C.e i * n⁻¹) := (conjTo_conj_iff S.t _ n).mpr (C.conjTo_e i)
  rcases (C.omega_big _ hE).mp hc with h | h | h | h
  · exact ⟨0, h.trans C.e_zero.symm⟩
  · exact ⟨1, h.trans C.e_one.symm⟩
  · exact ⟨2, h.trans C.e_two.symm⟩
  · exact ⟨3, h.trans C.e_three.symm⟩

noncomputable def σn (n : normalizer (S.E C.yb : Set X)) : Perm (Fin 4) :=
  Equiv.ofBijective (fun i => Classical.choose (C.exists_index n.2 i)) (by
    have hinj : Function.Injective fun i => Classical.choose (C.exists_index n.2 i) := by
      intro i j h
      have hi := Classical.choose_spec (C.exists_index n.2 i)
      have hj := Classical.choose_spec (C.exists_index n.2 j)
      simp only at h
      rw [h] at hi
      have := hi.trans hj.symm
      exact C.e_injective (by simpa using this)
    exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩)

theorem σn_spec (n : normalizer (S.E C.yb : Set X)) (i : Fin 4) :
    (n : X) * C.e i * (n : X)⁻¹ = C.e (C.σn n i) :=
  Classical.choose_spec (C.exists_index n.2 i)

theorem σn_unique (n : normalizer (S.E C.yb : Set X)) {τ : Perm (Fin 4)}
    (hτ : ∀ i, (n : X) * C.e i * (n : X)⁻¹ = C.e (τ i)) : C.σn n = τ := by
  ext i
  exact congrArg Fin.val (C.e_injective ((C.σn_spec n i).symm.trans (hτ i)))

noncomputable def π : normalizer (S.E C.yb : Set X) →* Perm (Fin 4) where
  toFun := C.σn
  map_one' := C.σn_unique 1 fun i => by simp
  map_mul' := fun n m => C.σn_unique (n * m) fun i => by
    rw [Perm.mul_apply, ← C.σn_spec n, ← C.σn_spec m]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

theorem π_spec (n : normalizer (S.E C.yb : Set X)) (i : Fin 4) :
    (n : X) * C.e i * (n : X)⁻¹ = C.e (C.π n i) :=
  C.σn_spec n i

theorem π_eq (n : normalizer (S.E C.yb : Set X)) {τ : Perm (Fin 4)}
    (hτ : ∀ i, (n : X) * C.e i * (n : X)⁻¹ = C.e (τ i)) : C.π n = τ :=
  C.σn_unique n hτ

theorem z_eq : S.z = C.e 2 * C.e 3 := by
  rw [C.e_two, C.e_three, ← mul_assoc, C.comm C.u_mem C.z_mem_E, mul_assoc, ← pow_two, C.u_sq,
    mul_one]

theorem f_eq : C.f = C.e 0 * C.e 1 := by
  rw [C.e_zero, C.e_one, ← mul_assoc, ← pow_two, S.t_sq, one_mul]

theorem conj_wordV (n : normalizer (S.E C.yb : Set X)) (v : V4) :
    (n : X) * C.wordV v * (n : X)⁻¹ = C.wordV (Mσ (C.π n) v) := by
  have hconj : ∀ g : X, (n : X) * g * (n : X)⁻¹ = MulAut.conj (n : X) g := fun g => rfl
  have ht : MulAut.conj (n : X) S.t = C.wordV (vecE (C.π n 0)) := by
    rw [← hconj, ← C.e_zero, C.π_spec]
    rfl
  have hz : MulAut.conj (n : X) S.z =
      C.wordV (addV (vecE (C.π n 2)) (vecE (C.π n 3))) := by
    rw [C.wordV_add, C.z_eq, map_mul, ← hconj, ← hconj, C.π_spec, C.π_spec]
    rfl
  have hf : MulAut.conj (n : X) C.f =
      C.wordV (addV (vecE (C.π n 0)) (vecE (C.π n 1))) := by
    rw [C.wordV_add, C.f_eq, map_mul, ← hconj, ← hconj, C.π_spec, C.π_spec]
    rfl
  have hu : MulAut.conj (n : X) C.u = C.wordV (vecE (C.π n 2)) := by
    rw [← hconj, ← C.e_two, C.π_spec]
    rfl
  rw [hconj, Mσ, C.wordV_add, C.wordV_add, C.wordV_add, C.wordV_smul, C.wordV_smul,
    C.wordV_smul, C.wordV_smul, ← ht, ← hz, ← hf, ← hu, ← map_pow, ← map_pow, ← map_pow,
    ← map_pow, ← map_mul, ← map_mul, ← map_mul]
  rfl

theorem conj_wordV_eq_iff (n : normalizer (S.E C.yb : Set X)) (v : V4) :
    (n : X) * C.wordV v * (n : X)⁻¹ = C.wordV v ↔ Mσ (C.π n) v = v := by
  rw [C.conj_wordV]
  exact ⟨C.wordV_injective, fun h => by rw [h]⟩

theorem π_eq_one_iff (n : normalizer (S.E C.yb : Set X)) :
    C.π n = 1 ↔ ∀ g ∈ S.E C.yb, (n : X) * g * (n : X)⁻¹ = g := by
  constructor
  · intro h g hg
    obtain ⟨v, rfl⟩ := C.exists_wordV hg
    rw [C.conj_wordV_eq_iff, h]
    clear hg
    revert v
    decide
  · intro h
    exact C.π_eq n fun i => by rw [h _ (C.e_mem i)]; rfl

end Case2

end A7Base

end CFSG.ComponentClassification.HSFLit
