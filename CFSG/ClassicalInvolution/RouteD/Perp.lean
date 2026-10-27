module

public import CFSG.ClassicalInvolution.RouteD.Leaf
public import CFSG.ClassicalInvolution.RouteD.Root
public import CFSG.LieType.Universal.Spin.Roots.TypeB
public import CFSG.LieType.Universal.Spin.Roots.TypeD

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti CFSG.LieType.RootSystem

@[expose] def PerpWitnessM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (ℓ b : Fin n) : Prop :=
  ∃ r : Fin n → ℤ, RRoot A r ∧ (∑ j, A ℓ j * r j) = 0 ∧ r b ≠ 0

section B

open CFSG.LieType.Universal.Spin

theorem perpWitness_B (n : ℕ) {ℓ b : Fin n} (hℓ : ℓ.val = 0) (hb : b.val = 1) :
    PerpWitnessM (cartanB n) ℓ b := by
  obtain ⟨l, hl⟩ := ℓ
  obtain ⟨bv, hbv⟩ := b
  simp only at hℓ hb
  subst hℓ hb
  have h0n : 0 < n := hl
  have h1n : 1 < n := hbv
  set e : Fin n → ℤ := Pi.single ⟨0, h0n⟩ 1 + Pi.single ⟨1, h1n⟩ 1 with he
  have hroot := ofStdB_mem_rootsB n (e := e)
    (Or.inl ⟨⟨0, h0n⟩, ⟨1, h1n⟩, 1, 1, by simp [Fin.ext_iff], Or.inl rfl, Or.inl rfl, he⟩)
  refine ⟨ofStdB n e, RRoot.of_mem_roots (isFiniteType_cartanB n) hroot, ?_, ?_⟩
  · rw [← coroot_apply, coroot_cartanB_of_lt n (by show 0 + 1 < n; omega), toStdB_ofStdB]
    simp [he, Fin.ext_iff]
  · have hx0 : ofStdB n e ⟨0, h0n⟩ = 1 := by
      have := congrFun (toStdB_ofStdB n e) ⟨0, h0n⟩
      simp only [toStdB] at this
      simpa [he, Fin.ext_iff] using this
    have hx1 : ofStdB n e ⟨1, h1n⟩ - ofStdB n e ⟨0, h0n⟩ = 1 := by
      have := congrFun (toStdB_ofStdB n e) ⟨1, h1n⟩
      simp only [toStdB] at this
      simpa [he, Fin.ext_iff] using this
    omega

theorem stdCartan_eq_cartanB (n : ℕ) : stdCartan (.B n) = cartanB n :=
  (stdCartan_B_eq n).trans (cartanB_eq_transpose n).symm

end B

section D

open CFSG.LieType.Universal.Spin

theorem perpWitness_D (n : ℕ) (hn : 4 ≤ n) {ℓ b : Fin n}
    (h : (ℓ.val = 0 ∧ b.val = 1) ∨ ((ℓ.val + 2 = n ∨ ℓ.val + 1 = n) ∧ b.val + 3 = n)) :
    PerpWitnessM (cartanD n) ℓ b := by
  have h0n : 0 < n := by omega
  have h1n : 1 < n := by omega
  obtain ⟨γ, hγ, hx⟩ := exists_mem_rootsD_toStdD_eq n (i := ⟨0, h0n⟩) (j := ⟨1, h1n⟩) (s := 1)
    (t := 1) (by simp [Fin.ext_iff]) (Or.inl rfl) (Or.inl rfl)
  have hγ' : ∀ k : ℕ, ∀ hk : k + 3 ≤ n, γ ⟨k, by omega⟩ = if k = 0 then 1 else 2 := by
    intro k
    induction k with
    | zero =>
      intro hk
      have := congrFun hx ⟨0, h0n⟩
      have h2 : ¬ (2 = n) := by omega
      simp [toStdD, Fin.ext_iff, h2] at this
      simpa using this
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have := congrFun hx ⟨k + 1, by omega⟩
      have h3 : ¬ (k + 1 + 2 = n) := by omega
      simp [toStdD, Fin.ext_iff, Pi.single_apply, h3] at this
      by_cases hk0 : k = 0
      · subst hk0
        simp at ih' ⊢
        simp at this
        omega
      · simp [hk0] at ih' ⊢
        simp [hk0] at this
        omega
  refine ⟨γ, RRoot.of_mem_roots (isFiniteType_cartanD n) hγ, ?_, ?_⟩
  · rw [← coroot_apply]
    by_cases hl1 : ℓ.val + 1 < n
    · rw [coroot_cartanD_of_lt n hl1, hx]
      simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> first | omega | contradiction
    · rw [coroot_cartanD_of_not_lt n hl1, hx]
      simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
  · have hb1 : b.val ≠ 0 := by omega
    have := hγ' b.val (by omega)
    simp only [Fin.eta, hb1, ite_false] at this
    rw [this]
    norm_num

theorem stdCartan_eq_cartanD (n : ℕ) : stdCartan (.D n) = cartanD n :=
  (stdCartan_D_eq n).trans ((CartanMatrix.D_transpose n).trans (cartanD_eq n).symm)

end D


section Exceptional

@[expose] def refl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (v : Fin n → ℤ) :
    Fin n → ℤ :=
  fun k => if k = i then v k - ∑ j, A i j * v j else v k

theorem reflection_eq_refl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (v : Fin n → ℤ) :
    reflection A i v = refl A i v := by
  funext k
  rw [reflection_apply]
  by_cases hk : k = i
  · subst hk; simp [refl, sub_eq_add_neg]
  · simp [refl, hk]

@[expose] def chainVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) (l : List (Fin n)) :
    Fin n → ℤ :=
  l.foldl (fun v i => refl A i v) (Pi.single j 1)

theorem rroot_chainVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) (l : List (Fin n)) :
    RRoot A (chainVec A j l) := by
  suffices ∀ (l : List (Fin n)) (v : Fin n → ℤ), RRoot A v →
      RRoot A (l.foldl (fun v i => refl A i v) v) from this l _ (RRoot.simple j)
  intro l
  induction l with
  | nil => intro v hv; exact hv
  | cons i l ih =>
    intro v hv
    exact ih _ (by show RRoot A (refl A i v); rw [← reflection_eq_refl]; exact hv.reflect i)

theorem perpWitness_E6_0 : PerpWitnessM (CartanMatrix.E 6).transpose 0 2 :=
  ⟨chainVec _ 0 [2, 3, 1, 4, 3, 2], rroot_chainVec _ _ _, by decide, by decide⟩

theorem perpWitness_E6_1 : PerpWitnessM (CartanMatrix.E 6).transpose 1 3 :=
  ⟨chainVec _ 1 [3, 2, 4, 3], rroot_chainVec _ _ _, by decide, by decide⟩

theorem perpWitness_E6_5 : PerpWitnessM (CartanMatrix.E 6).transpose 5 4 :=
  ⟨chainVec _ 1 [3, 2, 4, 3, 5, 4], rroot_chainVec _ _ _, by decide, by decide⟩

theorem perpWitness_E7_0 : PerpWitnessM (CartanMatrix.E 7).transpose 0 2 :=
  ⟨chainVec _ 0 [2, 3, 1, 4, 3, 2], rroot_chainVec _ _ _, by decide, by decide⟩

theorem perpWitness_E7_1 : PerpWitnessM (CartanMatrix.E 7).transpose 1 3 :=
  ⟨chainVec _ 1 [3, 2, 4, 3], rroot_chainVec _ _ _, by decide, by decide⟩

theorem perpWitness_E7_6 : PerpWitnessM (CartanMatrix.E 7).transpose 6 5 :=
  ⟨chainVec _ 1 [3, 2, 4, 3, 5, 4, 6, 5], rroot_chainVec _ _ _, by decide, by decide⟩

theorem perpWitness_E8_0 : PerpWitnessM (CartanMatrix.E 8).transpose 0 2 :=
  ⟨chainVec _ 0 [2, 3, 1, 4, 3, 2], rroot_chainVec _ _ _, by decide, by decide⟩

theorem perpWitness_E8_1 : PerpWitnessM (CartanMatrix.E 8).transpose 1 3 :=
  ⟨chainVec _ 1 [3, 2, 4, 3], rroot_chainVec _ _ _, by decide, by decide⟩

theorem perpWitness_E8_7 : PerpWitnessM (CartanMatrix.E 8).transpose 7 6 :=
  ⟨chainVec _ 1 [3, 2, 4, 3, 5, 4, 6, 5, 7, 6], rroot_chainVec _ _ _, by decide, by decide⟩

theorem perpWitness_F4_0 : PerpWitnessM CartanMatrix.F₄.transpose 0 1 :=
  ⟨chainVec _ 0 [1, 2, 1], rroot_chainVec _ _ _, by decide, by decide⟩

end Exceptional

theorem perpWitness_of_leafCase {t : DynkinType} (ht : t.Valid) (hA : ∀ n, t ≠ .A n)
    {ℓ b : Fin t.rank} (h : LeafCase t ℓ b) : PerpWitnessM (stdCartan t) ℓ b := by
  cases t with
  | A n => exact absurd rfl (hA n)
  | B n =>
    obtain ⟨-, h1, h2⟩ := h
    have := perpWitness_B n (ℓ := ℓ) (b := b) h1 h2
    rw [← stdCartan_eq_cartanB] at this
    exact this
  | C n => exact h.elim
  | D n =>
    have hn : 4 ≤ n := DynkinType.valid_D.mp ht
    have := perpWitness_D n hn (ℓ := ℓ) (b := b) h
    rw [← stdCartan_eq_cartanD] at this
    exact this
  | E6 =>
    rw [stdCartan_E6_eq]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [show ℓ = (0 : Fin 6) from Fin.ext h1, show b = (2 : Fin 6) from Fin.ext h2]
      exact perpWitness_E6_0
    · rw [show ℓ = (1 : Fin 6) from Fin.ext h1, show b = (3 : Fin 6) from Fin.ext h2]
      exact perpWitness_E6_1
    · rw [show ℓ = (5 : Fin 6) from Fin.ext h1, show b = (4 : Fin 6) from Fin.ext h2]
      exact perpWitness_E6_5
  | E7 =>
    rw [stdCartan_E7_eq]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [show ℓ = (0 : Fin 7) from Fin.ext h1, show b = (2 : Fin 7) from Fin.ext h2]
      exact perpWitness_E7_0
    · rw [show ℓ = (1 : Fin 7) from Fin.ext h1, show b = (3 : Fin 7) from Fin.ext h2]
      exact perpWitness_E7_1
    · rw [show ℓ = (6 : Fin 7) from Fin.ext h1, show b = (5 : Fin 7) from Fin.ext h2]
      exact perpWitness_E7_6
  | E8 =>
    rw [stdCartan_E8_eq]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [show ℓ = (0 : Fin 8) from Fin.ext h1, show b = (2 : Fin 8) from Fin.ext h2]
      exact perpWitness_E8_0
    · rw [show ℓ = (1 : Fin 8) from Fin.ext h1, show b = (3 : Fin 8) from Fin.ext h2]
      exact perpWitness_E8_1
    · rw [show ℓ = (7 : Fin 8) from Fin.ext h1, show b = (6 : Fin 8) from Fin.ext h2]
      exact perpWitness_E8_7
  | F4 =>
    rw [stdCartan_F4_eq]
    obtain ⟨h1, h2⟩ := h
    rw [show ℓ = (0 : Fin 4) from Fin.ext h1, show b = (1 : Fin 4) from Fin.ext h2]
    exact perpWitness_F4_0
  | G2 => exact h.elim

end CFSG.ClassicalInvolution.RouteD
