module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Weights
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8AdjOps

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CoxeterSystem

section Lin

variable {τ : Tag}

theorem reflect_comb (i : Fin τ.rank) (a b : ℤ) (x y : Fin τ.rank → ℤ) :
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

theorem weyl_smul_comb
    (w : WeylGroup τ) (a b : ℤ) (x y : Fin τ.rank → ℤ) :
    w • (a • x - b • y) = a • (w • x) - b • (w • y) := by
  obtain ⟨l, -, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  simp only [wordProd_smul']
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, reflect_comb]

theorem reflect_dvd (i : Fin τ.rank) (d : ℤ) (x : Fin τ.rank → ℤ) (h : ∀ c, d ∣ x c) :
    ∀ c, d ∣ reflect τ i x c := by
  intro c
  unfold reflect
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact dvd_sub (h c) (dvd_mul_of_dvd_left
    (Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (h j) _) _)

theorem weyl_dvd
    (w : WeylGroup τ) (d : ℤ) (x : Fin τ.rank → ℤ) (h : ∀ c, d ∣ x c) :
    ∀ c, d ∣ (w • x) c := by
  obtain ⟨l, -, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  simp only [wordProd_smul']
  induction l with
  | nil => exact h
  | cons i l ih => rw [List.foldr_cons]; exact reflect_dvd i d _ ih

theorem weyl_dvd_iff
    (w : WeylGroup τ) (d : ℤ) (x : Fin τ.rank → ℤ) : (∀ c, d ∣ (w • x) c) ↔ ∀ c, d ∣ x c := by
  refine ⟨fun h => ?_, weyl_dvd w d x⟩
  have := weyl_dvd w⁻¹ d _ h
  simpa using this

end Lin

theorem dvd_of_dvd_mExp (m : ℤ) (δ : Fin Tag.E8.rank → ℤ) (h : ∀ c, m ∣ mExp .E8 c δ) :
    ∀ l, m ∣ δ l := by
  intro l
  have h1 : δ l = ∑ c, e8Omega c l * mExp .E8 c δ := by
    unfold mExp
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ c, e8Omega c l * (Tag.E8.cartan c j * δ j) = (if l = j then 1 else 0) * δ j := by
      intro j
      rw [← omega_mul_cartan l j, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    simp only [this]
    simp
  rw [h1]
  exact Finset.dvd_sum fun c _ => dvd_mul_of_dvd_right (h c) _

theorem odd_coprime_two_pow {g : ℕ} (hg : Odd g) (b : ℕ) : IsCoprime (g : ℤ) ((2 : ℤ) ^ b) := by
  refine IsCoprime.pow_right ?_
  obtain ⟨k, rfl⟩ := hg
  exact ⟨1, -(k : ℤ), by push_cast; ring⟩

theorem R1_sep (m a b : ℕ) (hm : Odd m) (hh : 3 ≤ Nat.gcd a m) (hnd : ¬ m ∣ a)
    (β : Fin 240 → Fin Tag.E8.rank → ℤ) (X : Fin 240 → Fin 56 → Fin Tag.E8.rank → ℤ)
    (hβ : ∀ i i', i ≠ i' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ c, (d : ℤ) ∣ (β i - β i') c)
    (hX : ∀ i j j', j ≠ j' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ c, (d : ℤ) ∣ (X i j - X i j') c)
    (i i' : Fin 240) (j j' : Fin 56)
    (h : ∀ c, (m : ℤ) ∣ ((a : ℤ) • X i j - ((2 : ℤ) ^ b) • β i -
      ((a : ℤ) • X i' j' - ((2 : ℤ) ^ b) • β i')) c) : i = i' ∧ j = j' := by
  set g := Nat.gcd a m with hgdef
  have hgpos : 0 < g := by omega
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a m
  obtain ⟨d, hd⟩ := Nat.gcd_dvd_right a m
  have hgm : g ∣ m := Nat.gcd_dvd_right a m
  have hgodd : Odd g := Odd.of_dvd_nat hm hgm
  have hii : i = i' := by
    by_contra hne
    apply hβ i i' hne g hh
    intro c
    have h1 : (g : ℤ) ∣ (2 : ℤ) ^ b * (β i - β i') c := by
      have h2 : (g : ℤ) ∣ (a : ℤ) * (X i j - X i' j') c :=
        dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left a m)) _
      have h3 := dvd_trans (Int.natCast_dvd_natCast.2 hgm) (h c)
      have h4 : ((a : ℤ) • X i j - ((2 : ℤ) ^ b) • β i -
          ((a : ℤ) • X i' j' - ((2 : ℤ) ^ b) • β i')) c =
          (a : ℤ) * (X i j - X i' j') c - (2 : ℤ) ^ b * (β i - β i') c := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [h4] at h3
      have := dvd_sub h2 h3
      rwa [sub_sub_cancel] at this
    exact (odd_coprime_two_pow hgodd b).dvd_of_dvd_mul_left h1
  subst hii
  refine ⟨rfl, ?_⟩
  by_contra hjj
  have hdodd : Odd d := Odd.of_dvd_nat hm ⟨g, by rw [hd]; ring⟩
  have hd3 : 3 ≤ d := by
    rcases hdodd with ⟨k, hk⟩
    by_contra hlt
    have : d = 1 := by omega
    apply hnd
    rw [this, mul_one] at hd
    rw [hd]
    exact Nat.gcd_dvd_left a m
  apply hX i j j' hjj d hd3
  intro c
  have h1 := h c
  have h4 : ((a : ℤ) • X i j - ((2 : ℤ) ^ b) • β i -
      ((a : ℤ) • X i j' - ((2 : ℤ) ^ b) • β i)) c = (a : ℤ) * (X i j - X i j') c := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h4] at h1
  have hcop : IsCoprime (a' : ℤ) (d : ℤ) := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := m) hgpos
    rw [show a / Nat.gcd a m = a' by rw [← hgdef, ha']; exact Nat.mul_div_cancel_left a' hgpos,
      show m / Nat.gcd a m = d by rw [← hgdef, hd]; exact Nat.mul_div_cancel_left d hgpos] at this
    exact Nat.isCoprime_iff_coprime.2 this
  have h5 : (g : ℤ) * d ∣ g * a' * (X i j - X i j') c := by
    have e1 : (m : ℤ) = g * d := by rw [hd]; push_cast; ring
    have e2 : (a : ℤ) = g * a' := by rw [ha']; push_cast; ring
    rwa [e1, e2] at h1
  have h6 : (d : ℤ) ∣ a' * (X i j - X i j') c := by
    rw [mul_assoc] at h5
    exact (mul_dvd_mul_iff_left (by exact_mod_cast hgpos.ne')).1 h5
  exact hcop.symm.dvd_of_dvd_mul_left h6

theorem R2_sep (m b : ℕ) (hm : Odd m) (h3 : 3 ≤ m)
    (β : Fin 240 → Fin Tag.E8.rank → ℤ) (X : Fin 240 → Fin 56 → Fin Tag.E8.rank → ℤ)
    (hβ : ∀ i i', i ≠ i' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ c, (d : ℤ) ∣ (β i - β i') c)
    (i i' : Fin 240) (j j' : Fin 56)
    (h : ∀ c, (m : ℤ) ∣ (((m : ℤ)) • X i j - ((2 : ℤ) ^ b) • β i -
      (((m : ℤ)) • X i' j' - ((2 : ℤ) ^ b) • β i')) c) : i = i' := by
  by_contra hne
  apply hβ i i' hne m h3
  intro c
  have h1 := h c
  have h4 : (((m : ℤ)) • X i j - ((2 : ℤ) ^ b) • β i -
      (((m : ℤ)) • X i' j' - ((2 : ℤ) ^ b) • β i')) c =
      (m : ℤ) * (X i j - X i' j') c - (2 : ℤ) ^ b * (β i - β i') c := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h4] at h1
  have h2 : (m : ℤ) ∣ (2 : ℤ) ^ b * (β i - β i') c := by
    have := dvd_sub (dvd_mul_right (m : ℤ) ((X i j - X i' j') c)) h1
    rwa [sub_sub_cancel] at this
  exact (odd_coprime_two_pow hm b).dvd_of_dvd_mul_left h2

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

