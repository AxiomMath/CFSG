module

public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.Coprime
public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.E7Families
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8CaseI
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesWeyl

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

theorem two_pow_ge_133 {t : ℕ} (h : 12 ≤ t) : 133 * t + 1 ≤ 2 ^ t := by
  have := two_pow_ge_of_ge_twelve h
  omega

theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (((2 ^ n - 1 : ℕ) : ℤ)) :=
  (Int.odd_coe_nat _).2 (Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩)
    odd_one)

theorem dvd_two_mul_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) :
    ((2 ^ n - 1 : ℕ) : ℤ) ∣ ((2 : ℕ) : ℤ) * ((2 ^ (n - 1) : ℕ) : ℤ) - 1 := by
  have h4 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hpow : 2 * 2 ^ (n - 1) = 2 ^ n := by rw [← pow_succ']; congr 1; omega
  refine ⟨1, ?_⟩
  have : (2 : ℤ) * 2 ^ (n - 1) = 2 ^ n := by exact_mod_cast hpow
  push_cast [h4]
  linarith

section Nodes


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]
  [Module.Finite k V]

theorem node7_bound {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .E7 K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup .E7 K → k} {J : Finset (Fin Tag.E7.rank)}
    (ht : IsChevType .E7 K 2 CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7 ρ y χ J)
    (hJ : ∀ j, j ≠ n7 → j ∈ J) (hs : n7 ∉ J) :
    (∃ b < n, ∀ z : Kˣ, χ (dC .E7 K n7 z) = (algebraMap K k (z : K)) ^ (2 ^ b)) ∨
      168 ≤ Module.finrank k V := by
  obtain ⟨w, hβ⟩ := exists_betaFamily7
  obtain ⟨u, hu, hXu⟩ := exists_copyFamily7
  obtain ⟨w₀, u₀, hσ, hu₀, hfc⟩ := exists_unitFamily7
  have h := node_bound hn hK hρ ht hJ hs (θ := e7Theta7) (c := 2) (c' := 2 ^ (n - 1))
    (by intro i; rw [mExp_e7Theta7]; push_cast; rfl) (dvd_two_mul_two_pow_sub_one hn)
    (fun δ hδ => e7_dvd_of_dvd_mExp _ (odd_two_pow_sub_one hn) δ hδ) w hβ u hu hXu w₀ sigma7 hσ u₀
    hu₀ (fun hn3 => hfc n hn3)
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa using h)

theorem node1_bound {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .E7 K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup .E7 K → k} {J : Finset (Fin Tag.E7.rank)}
    (ht : IsChevType .E7 K 2 CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7 ρ y χ J)
    (hJ : ∀ j, j ≠ n1 → j ∈ J) (hs : n1 ∉ J) :
    (∃ b < n, ∀ z : Kˣ, χ (dC .E7 K n1 z) = (algebraMap K k (z : K)) ^ (2 ^ b)) ∨
      256 ≤ Module.finrank k V := by
  obtain ⟨w, hβ⟩ := exists_betaFamily1
  obtain ⟨u, hu, hXu⟩ := exists_copyFamily1
  obtain ⟨w₀, u₀, hσ, hu₀, hfc⟩ := exists_unitFamily1
  have h := node_bound hn hK hρ ht hJ hs (θ := e7Theta1) (c := 1) (c' := 1)
    (by intro i; rw [mExp_e7Theta1]; push_cast; rfl) (by simp)
    (fun δ hδ => e7_dvd_of_dvd_mExp _ (odd_two_pow_sub_one hn) δ hδ) w hβ u hu hXu w₀ sigma1 hσ u₀
    hu₀ (fun hn3 => by simpa using hfc n hn3)
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa using h)

theorem node7_bound_two {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .E7 K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup .E7 K → k} {J : Finset (Fin Tag.E7.rank)}
    (ht : IsChevType .E7 K 2 CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7 ρ y χ J)
    (hJ : ∀ j, j ≠ n7 → j ∈ J) (hs : n7 ∉ J) {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ z : Kˣ, χ (dC .E7 K n7 z) ^ (2 ^ g) = χ (dC .E7 K n7 z)) (ht2 : 2 ≤ n / g) :
    133 * (n / g) + 1 ≤ Module.finrank k V := by
  rcases Nat.lt_or_ge (n / g) 12 with h11 | h12
  · obtain ⟨w, hβ⟩ := exists_betaFamily7
    obtain ⟨u, hu, hXu⟩ := exists_copyFamily7
    have := tensor_bound hn hK hρ ht hJ hs hg hgn hper ht2 (θ := e7Theta7) (c := 2)
      (c' := 2 ^ (n - 1)) (by intro i; rw [mExp_e7Theta7]; push_cast; rfl)
      (dvd_two_mul_two_pow_sub_one hn)
      (fun δ hδ => e7_dvd_of_dvd_mExp _ (odd_two_pow_sub_one hn) δ hδ) w hβ u hu hXu
    omega
  · have := two_pow_le_finrank_of_periodic hn hK hρ ht hs hg hgn hper
    have := two_pow_ge_133 h12
    omega

theorem node1_bound_two {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .E7 K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup .E7 K → k} {J : Finset (Fin Tag.E7.rank)}
    (ht : IsChevType .E7 K 2 CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7 ρ y χ J)
    (hJ : ∀ j, j ≠ n1 → j ∈ J) (hs : n1 ∉ J) {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ z : Kˣ, χ (dC .E7 K n1 z) ^ (2 ^ g) = χ (dC .E7 K n1 z)) (ht2 : 2 ≤ n / g) :
    133 * (n / g) + 1 ≤ Module.finrank k V := by
  rcases Nat.lt_or_ge (n / g) 12 with h11 | h12
  · obtain ⟨w, hβ⟩ := exists_betaFamily1
    obtain ⟨u, hu, hXu⟩ := exists_copyFamily1
    have := tensor_bound hn hK hρ ht hJ hs hg hgn hper ht2 (θ := e7Theta1) (c := 1) (c' := 1)
      (by intro i; rw [mExp_e7Theta1]; push_cast; rfl) (by simp)
      (fun δ hδ => e7_dvd_of_dvd_mExp _ (odd_two_pow_sub_one hn) δ hδ) w hβ u hu hXu
    omega
  · have := two_pow_le_finrank_of_periodic hn hK hρ ht hs hg hgn hper
    have := two_pow_ge_133 h12
    omega

end Nodes

end CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis
