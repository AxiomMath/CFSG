module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Weights
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Family

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CoxeterSystem
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

section Lin

variable {τ : Tag}

theorem mExp_combF (i : Fin τ.rank) (a b : ℤ) (x y : Fin τ.rank → ℤ) :
    mExp τ i (a • x - b • y) = a * mExp τ i x - b * mExp τ i y := by
  unfold mExp
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem mExp_subF (i : Fin τ.rank) (x y : Fin τ.rank → ℤ) :
    mExp τ i (x - y) = mExp τ i x - mExp τ i y := by
  have := mExp_combF i 1 1 x y
  simpa using this

theorem mExp_singleF (i s : Fin τ.rank) :
    mExp τ i (Pi.single s (1 : ℤ)) = τ.cartan i s := by
  unfold mExp
  simp [Pi.single_apply]

theorem reflect_combF (i : Fin τ.rank) (a b : ℤ) (x y : Fin τ.rank → ℤ) :
    reflect τ i (a • x - b • y) = a • reflect τ i x - b • reflect τ i y := by
  have hs : ∑ j, τ.cartan i j * (a • x - b • y) j =
      a * ∑ j, τ.cartan i j * x j - b * ∑ j, τ.cartan i j * y j := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold reflect
  rw [hs]
  ext c
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem weyl_smul_combF
    (w : WeylGroup τ) (a b : ℤ) (x y : Fin τ.rank → ℤ) :
    w • (a • x - b • y) = a • (w • x) - b • (w • y) := by
  obtain ⟨l, -, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  simp only [wordProd_smul']
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, reflect_combF]

theorem reflect_dvdF (i : Fin τ.rank) (d : ℤ) (x : Fin τ.rank → ℤ) (h : ∀ c, d ∣ x c) :
    ∀ c, d ∣ reflect τ i x c := by
  intro c
  unfold reflect
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact dvd_sub (h c) (dvd_mul_of_dvd_left
    (Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (h j) _) _)

theorem weyl_dvdF
    (w : WeylGroup τ) (d : ℤ) (x : Fin τ.rank → ℤ) (h : ∀ c, d ∣ x c) :
    ∀ c, d ∣ (w • x) c := by
  obtain ⟨l, -, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  simp only [wordProd_smul']
  induction l with
  | nil => exact h
  | cons i l ih => rw [List.foldr_cons]; exact reflect_dvdF i d _ ih

end Lin

theorem mExp_f4Omega : ∀ i s : Fin Tag.F4.rank, mExp .F4 i (f4Omega s) = if i = s then 1 else 0 := by
  decide +kernel

theorem dvd_of_dvd_mExpF (m : ℤ) (δ : Fin Tag.F4.rank → ℤ) (h : ∀ c, m ∣ mExp .F4 c δ) :
    ∀ l, m ∣ δ l := by
  intro l
  have h1 : δ l = ∑ c, f4Omega c l * mExp .F4 c δ := by
    unfold mExp
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ c, f4Omega c l * (Tag.F4.cartan c j * δ j) = (if l = j then 1 else 0) * δ j := by
      intro j
      rw [← f4Omega_mul_cartan l j, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    simp only [this]
    simp
  rw [h1]
  exact Finset.dvd_sum fun c _ => dvd_mul_of_dvd_right (h c) _

@[expose] def lamF (a : Fin Tag.F4.rank → ℕ) : Fin Tag.F4.rank → ℤ :=
  fun l => ∑ c, (a c : ℤ) * f4Omega c l

theorem mExp_lamF (a : Fin Tag.F4.rank → ℕ) (i : Fin Tag.F4.rank) : mExp .F4 i (lamF a) = a i := by
  unfold mExp lamF
  have : ∀ j, Tag.F4.cartan i j * ∑ c, (a c : ℤ) * f4Omega c j =
      ∑ c, (a c : ℤ) * (Tag.F4.cartan i j * f4Omega c j) := by
    intro j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  simp only [this]
  rw [Finset.sum_comm]
  have h2 : ∀ c, ∑ j, (a c : ℤ) * (Tag.F4.cartan i j * f4Omega c j) = (a c : ℤ) * (if i = c then 1 else 0) := by
    intro c
    rw [← Finset.mul_sum]
    congr 1
    have := mExp_f4Omega i c
    unfold mExp at this
    exact this
  simp only [h2]
  simp

theorem lamF_dvd (a : Fin Tag.F4.rank → ℕ) (d : ℕ) (hd : ∀ c, d ∣ a c) :
    ∀ l, (d : ℤ) ∣ lamF a l := by
  intro l
  unfold lamF
  exact Finset.dvd_sum fun c _ => dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 (hd c)) _

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
