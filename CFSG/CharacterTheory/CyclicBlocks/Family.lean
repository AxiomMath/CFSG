module

public import CFSG.CharacterTheory.CyclicBlocks.Sections
public import CFSG.CharacterTheory.CyclicBlocks.Gram
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeInversionFamily

public section

open scoped BigOperators Classical

namespace CFSG.CyclicBlocks

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.Semidihedral.Principal

section RootSums

theorem sum_cyclicRoot_pair_eq_neg_one_of_odd {n : ℕ} (hn : n % 2 = 1) {j : ℤ}
    (hj : ¬ (n : ℤ) ∣ j) :
    ∑ i ∈ Finset.Icc 1 ((n - 1) / 2),
      (cyclicRoot n ^ ((i : ℤ) * j) + cyclicRoot n ^ (-((i : ℤ) * j))) = -1 := by
  have hnpos : 0 < n := by omega
  set r := (n - 1) / 2 with hr
  have hr2 : 2 * r + 1 = n := by omega
  set f : ℕ → ℂ := fun k => cyclicRoot n ^ (j * (k : ℤ)) with hf
  have htotal : ∑ k ∈ Finset.range n, f k = 0 := by
    rw [hf, sum_range_cyclicRoot_zpow hnpos j]
    simp [hj]
  have hsplit : ∑ k ∈ Finset.range n, f k = f 0 + ∑ k ∈ Finset.Ico 1 n, f k := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive f (Nat.zero_le 1) (by omega : 1 ≤ n)]
    simp
  have hsplit2 : ∑ k ∈ Finset.Ico 1 n, f k =
      ∑ k ∈ Finset.Ico 1 (r + 1), f k + ∑ k ∈ Finset.Ico (r + 1) n, f k :=
    (Finset.sum_Ico_consecutive f (by omega) (by omega)).symm
  have hrefl : ∑ k ∈ Finset.Ico (r + 1) n, f k = ∑ i ∈ Finset.Ico 1 (r + 1), f (n - i) := by
    apply Finset.sum_nbij' (fun k => n - k) (fun i => n - i)
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      congr 1
      omega
  have hf0 : f 0 = 1 := by simp [hf]
  have hterm : ∀ i ∈ Finset.Icc 1 r,
      cyclicRoot n ^ ((i : ℤ) * j) + cyclicRoot n ^ (-((i : ℤ) * j)) = f i + f (n - i) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    simp only [hf]
    congr 1
    · rw [mul_comm]
    · apply cyclicRoot_zpow_congr
      have hcast : ((n - i : ℕ) : ℤ) = (n : ℤ) - i := by
        rw [Nat.cast_sub (by omega : i ≤ n)]
      rw [hcast]
      exact Int.modEq_iff_dvd.mpr ⟨j, by ring⟩
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.Ico_add_one_right_eq_Icc,
    ← hrefl]
  have h := htotal
  rw [hsplit, hsplit2, hf0] at h
  linear_combination h

theorem sum_cyclicRoot_pair_sq_of_odd {n : ℕ} (hn : n % 2 = 1) {j : ℤ} (hj : ¬ (n : ℤ) ∣ j) :
    ∑ i ∈ Finset.Icc 1 ((n - 1) / 2),
      (cyclicRoot n ^ ((i : ℤ) * j) + cyclicRoot n ^ (-((i : ℤ) * j))) ^ 2 = n - 2 := by
  have h2j : ¬ (n : ℤ) ∣ 2 * j := by
    rintro ⟨c, hc⟩
    apply hj
    have hm : (n + 1) / 2 * 2 = n + 1 := by omega
    have hm' : ((((n + 1) / 2 : ℕ) : ℤ)) * 2 = n + 1 := by exact_mod_cast hm
    refine ⟨(((n + 1) / 2 : ℕ) : ℤ) * c - j, ?_⟩
    linear_combination ((((n + 1) / 2 : ℕ) : ℤ)) * hc - j * hm'
  have hne : cyclicRoot n ≠ 0 := cyclicRoot_ne_zero n
  have hsq : ∀ i : ℕ, (cyclicRoot n ^ ((i : ℤ) * j) + cyclicRoot n ^ (-((i : ℤ) * j))) ^ 2 =
      2 + (cyclicRoot n ^ ((i : ℤ) * (2 * j)) + cyclicRoot n ^ (-((i : ℤ) * (2 * j)))) := by
    intro i
    have h1 : cyclicRoot n ^ ((i : ℤ) * j) * cyclicRoot n ^ (-((i : ℤ) * j)) = 1 := by
      rw [← zpow_add₀ hne, add_neg_cancel, zpow_zero]
    have h2 : cyclicRoot n ^ ((i : ℤ) * (2 * j)) =
        cyclicRoot n ^ ((i : ℤ) * j) * cyclicRoot n ^ ((i : ℤ) * j) := by
      rw [← zpow_add₀ hne]
      ring_nf
    have h3 : cyclicRoot n ^ (-((i : ℤ) * (2 * j))) =
        cyclicRoot n ^ (-((i : ℤ) * j)) * cyclicRoot n ^ (-((i : ℤ) * j)) := by
      rw [← zpow_add₀ hne]
      ring_nf
    rw [h2, h3]
    linear_combination 2 * h1
  simp_rw [hsq]
  rw [Finset.sum_add_distrib, sum_cyclicRoot_pair_eq_neg_one_of_odd hn h2j, Finset.sum_const,
    Nat.card_Icc]
  have hr : (n - 1) / 2 + 1 - 1 = (n - 1) / 2 := by omega
  rw [hr, nsmul_eq_mul]
  have hr2 : (n - 1) / 2 * 2 + 1 = n := by omega
  have hcast := congrArg (Nat.cast : ℕ → ℂ) hr2
  push_cast at hcast
  linear_combination hcast

end RootSums

variable {G : Type*} [Group G] [Fintype G]

section Projections

variable (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
  [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]

theorem cyclic_inversionProjection_zpow (hp2 : p ≠ 2) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow p G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) {ℓ : ℕ} (hP : Nat.card P = ℓ)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2) (i k : ℤ) :
    principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal) u (inversionTwist u ℓ i) (u ^ k) =
      2 - cyclicRoot ℓ ^ (i * k) - cyclicRoot ℓ ^ (-(i * k)) := by
  have hpp : p.Prime := Fact.out
  have hu : orderOf u = ℓ := by rw [← Nat.card_zpowers, ← hPu]; exact hP
  have hue := orderOf_dvd_of_sylow_eq_zpowers P hPu
  by_cases hk : (ℓ : ℤ) ∣ k
  · have h1 : u ^ k = 1 := by rw [← orderOf_dvd_iff_zpow_eq_one, hu]; exact hk
    have hz1 : cyclicRoot ℓ ^ (i * k) = 1 := by
      rw [cyclicRoot_zpow_congr (y := 0) (Int.modEq_zero_iff_dvd.mpr (hk.mul_left i)),
        zpow_zero]
    have hz2 : cyclicRoot ℓ ^ (-(i * k)) = 1 := by
      rw [cyclicRoot_zpow_congr (y := 0)
        (Int.modEq_zero_iff_dvd.mpr ((hk.mul_left i).neg_right)), zpow_zero]
    rw [h1, hz1, hz2, principalCyclicProjection_eq_zero_of_coprime basis ideal p principal hue _
      (inversionTwist_one hu i) (by rw [orderOf_one]; exact hpp.not_dvd_one)]
    norm_num
  · have hz : (⟨u ^ k, Subgroup.zpow_mem_zpowers u k⟩ : Subgroup.zpowers u) ≠ 1 := by
      intro h
      apply hk
      rw [← hu]
      exact orderOf_dvd_iff_zpow_eq_one.mpr (congrArg Subtype.val h)
    have h := principalCyclicProjection_section basis ideal p hp2 principal hprincipal P hPu
      hindex (inversionTwist u ℓ i) _ hz (y := 1) (Commute.one_right _)
      (by rw [orderOf_one]; exact hpp.not_dvd_one)
    have hinv : (⟨u ^ k, Subgroup.zpow_mem_zpowers u k⟩ : Subgroup.zpowers u)⁻¹ =
        ⟨u ^ (-k), Subgroup.zpow_mem_zpowers u (-k)⟩ := Subtype.ext (zpow_neg u k).symm
    rw [mul_one, hinv] at h
    rw [h, inversionTwist_zpow hu, inversionTwist_zpow hu, mul_neg]
    ring

theorem cyclic_cyclicMultiplicity_inversionProjection (hp2 : p ≠ 2) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow p G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) {ℓ : ℕ} (hP : Nat.card P = ℓ)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2) (i m : ℤ) :
    cyclicMultiplicity (principalCyclicProjection basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) u
        (inversionTwist u ℓ i)) u ℓ m =
      2 * (if (ℓ : ℤ) ∣ m then 1 else 0) - (if (ℓ : ℤ) ∣ i - m then 1 else 0) -
        (if (ℓ : ℤ) ∣ i + m then 1 else 0) := by
  have hℓpos : 0 < ℓ := by
    rw [← hP]
    exact Nat.card_pos
  have hne : cyclicRoot ℓ ≠ 0 := cyclicRoot_ne_zero ℓ
  have hℓ0 : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓpos.ne'
  unfold cyclicMultiplicity
  have hval : ∀ v : ℕ, principalCyclicProjection basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) u
        (inversionTwist u ℓ i) (u ^ v) * cyclicRoot ℓ ^ (-(m * v)) =
      2 * cyclicRoot ℓ ^ (-m * v) - cyclicRoot ℓ ^ ((i - m) * v) -
        cyclicRoot ℓ ^ ((-i - m) * v) := by
    intro v
    rw [← zpow_natCast u v, cyclic_inversionProjection_zpow basis ideal p hp2 principal hprincipal
      P u hPu hP hindex i v]
    have e1 : cyclicRoot ℓ ^ (i * (v : ℤ)) * cyclicRoot ℓ ^ (-(m * v)) =
        cyclicRoot ℓ ^ ((i - m) * v) := by
      rw [← zpow_add₀ hne]
      congr 1
      ring
    have e2 : cyclicRoot ℓ ^ (-(i * (v : ℤ))) * cyclicRoot ℓ ^ (-(m * v)) =
        cyclicRoot ℓ ^ ((-i - m) * v) := by
      rw [← zpow_add₀ hne]
      congr 1
      ring
    have e3 : cyclicRoot ℓ ^ (-(m * (v : ℤ))) = cyclicRoot ℓ ^ (-m * v) := by
      congr 1
      ring
    rw [sub_mul, sub_mul, e1, e2, e3]
  rw [Finset.sum_congr rfl fun v _ => hval v, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_range_cyclicRoot_zpow hℓpos, sum_range_cyclicRoot_zpow hℓpos,
    sum_range_cyclicRoot_zpow hℓpos]
  have hneg : ∀ x : ℤ, (ℓ : ℤ) ∣ -x ↔ (ℓ : ℤ) ∣ x := fun x => dvd_neg
  have hsub : ∀ x y : ℤ, (ℓ : ℤ) ∣ -x - y ↔ (ℓ : ℤ) ∣ x + y := fun x y => by
    rw [show -x - y = -(x + y) by ring, dvd_neg]
  simp only [hneg, hsub]
  split_ifs <;> field_simp <;> ring

end Projections

section Family

variable (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
  [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]

theorem cyclic_inversion_family_decomposition (hp2 : p ≠ 2) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow p G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) {ℓ : ℕ} (hP : Nat.card P = ℓ)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2) :
    ∃ (a : basis.index) (b : Finset.Icc 1 ((ℓ - 1) / 2) → basis.index) (δ : ℤ),
      a ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      a ≠ principal ∧ Function.Injective b ∧
      (∀ k, b k ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
        b k ≠ principal ∧ b k ≠ a) ∧
      (δ = 1 ∨ δ = -1) ∧
      (∀ k, (Module.finrank ℂ (basis.representation (b k)).vector : ℤ) =
        Module.finrank ℂ (basis.representation a).vector + δ) ∧
      0 < (Module.finrank ℂ (basis.representation a).vector : ℤ) + δ ∧
      ∀ (k : Finset.Icc 1 ((ℓ - 1) / 2)) (g : G),
        principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
          principal) u (inversionTwist u ℓ (k : ℕ)) g =
          1 + δ * (basis.representation a).character g -
            δ * (basis.representation (b k)).character g := by
  classical
  have hpp : p.Prime := Fact.out
  obtain ⟨hu, hodd, h3⟩ := card_sylow_odd_three_le hp2 P hPu hindex
  rw [hP] at hu hodd h3
  have hue := orderOf_dvd_of_sylow_eq_zpowers P hPu
  have hℓpos : 0 < ℓ := by omega
  have hupow : u ^ ℓ = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  set r := (ℓ - 1) / 2 with hr
  have hr1 : 1 ≤ r := by omega
  have hrl : 2 * r < ℓ := by omega
  have hprinB : principal ∈ B := coefficientBlock_self_mem _ _ _
  choose m hm using fun (x : basis.index) (k : ℤ) =>
    cyclicMultiplicity_natural (basis.representation x) u hℓpos hupow k
  have hc : ∀ (x : basis.index) (i : ℤ),
      characterPairing (fun y : Subgroup.zpowers u => (basis.representation x).character y)
        (inversionTwist u ℓ i) = (((m x 0 : ℤ) - m x i : ℤ) : ℂ) := by
    intro x i
    rw [characterPairing_inversionTwist _ hu, hm, hm]
    push_cast
    ring
  have hTsum : ∀ (i : ℤ) (g : G), principalCyclicProjection basis B u (inversionTwist u ℓ i) g =
      ∑ x ∈ B, (((m x 0 : ℤ) - m x i : ℤ) : ℂ) * (basis.representation x).character g := by
    intro i g
    unfold principalCyclicProjection
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hc]
  have hgram : ∀ i i' : ℤ, ¬ (ℓ : ℤ) ∣ i → ¬ (ℓ : ℤ) ∣ i' →
      ((∑ x ∈ B, ((m x 0 : ℤ) - m x i) * ((m x 0 : ℤ) - m x i') : ℤ) : ℂ) =
        2 + (if (ℓ : ℤ) ∣ i - i' then 1 else 0) + (if (ℓ : ℤ) ∣ i + i' then 1 else 0) := by
    intro i i' hi hi'
    have h1 := characterPairing_sum_left B (fun x => (((m x 0 : ℤ) - m x i : ℤ) : ℂ))
      (fun x (y : Subgroup.zpowers u) => (basis.representation x).character y)
      (inversionTwist u ℓ i')
    have h2 : (fun y : Subgroup.zpowers u => ∑ x ∈ B, (((m x 0 : ℤ) - m x i : ℤ) : ℂ) *
        (basis.representation x).character y) =
        fun y : Subgroup.zpowers u => principalCyclicProjection basis B u
          (inversionTwist u ℓ i) y := by
      funext y
      rw [hTsum]
    rw [h2, characterPairing_inversionTwist _ hu,
      cyclic_cyclicMultiplicity_inversionProjection basis ideal p hp2 principal hprincipal P u hPu
        hP hindex i 0,
      cyclic_cyclicMultiplicity_inversionProjection basis ideal p hp2 principal hprincipal P u hPu
        hP hindex i i'] at h1
    simp_rw [hc] at h1
    push_cast at h1 ⊢
    simp only [sub_zero, add_zero, dvd_zero, hi, hi', ↓reduceIte, mul_one, mul_zero] at h1
    linear_combination -h1
  have hIcard : 1 ≤ Fintype.card (Finset.Icc 1 r) := by
    rw [Fintype.card_coe, Nat.card_Icc]
    omega
  have hkmem : ∀ k : Finset.Icc 1 r, 1 ≤ (k : ℕ) ∧ (k : ℕ) ≤ r := fun k => Finset.mem_Icc.mp k.2
  have hidx : ∀ k : Finset.Icc 1 r, ¬ (ℓ : ℤ) ∣ ((k : ℕ) : ℤ) := by
    intro k hdvd
    have hk := hkmem k
    have h' := Int.le_of_dvd (by exact_mod_cast (by omega : 0 < (k : ℕ))) hdvd
    omega
  let v : Finset.Icc 1 r → basis.index → ℤ := fun k x =>
    if x ∈ B then (m x 0 : ℤ) - m x ((k : ℕ) : ℤ) else 0
  let d : basis.index → ℤ := fun x => Module.finrank ℂ (basis.representation x).vector
  have hd : ∀ x, 0 < d x := fun x => by
    show (0 : ℤ) < (Module.finrank ℂ (basis.representation x).vector : ℤ)
    exact_mod_cast (label_character_one basis x).2
  have hdo : d principal = 1 := by
    have h := (label_character_one basis principal).1
    rw [hprincipal, Pi.one_apply] at h
    have h' : (Module.finrank ℂ (basis.representation principal).vector : ℂ) = 1 := h.symm
    show (Module.finrank ℂ (basis.representation principal).vector : ℤ) = 1
    exact_mod_cast h'
  have hmprin : ∀ j : ℤ, (m principal j : ℂ) = if (ℓ : ℤ) ∣ j then 1 else 0 := by
    intro j
    have h := hm principal j
    rw [hprincipal, cyclicMultiplicity_one_character hℓpos] at h
    exact h.symm
  have hvo : ∀ k, v k principal = 1 := by
    intro k
    have h0 := hmprin 0
    have hk := hmprin ((k : ℕ) : ℤ)
    simp only [dvd_zero, ↓reduceIte, hidx k] at h0 hk
    have h0' : m principal 0 = 1 := by exact_mod_cast h0
    have hk' : m principal ((k : ℕ) : ℤ) = 0 := by exact_mod_cast hk
    simp only [v, hprinB, ↓reduceIte, h0', hk']
    norm_num
  have hsumB : ∀ F : basis.index → ℤ, ∑ x, (if x ∈ B then F x else 0) = ∑ x ∈ B, F x := by
    intro F
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hnorm : ∀ k, ∑ x, v k x ^ 2 = 3 := by
    intro k
    have h := hgram _ _ (hidx k) (hidx k)
    have hk := hkmem k
    have h2k : ¬ (ℓ : ℤ) ∣ ((k : ℕ) : ℤ) + ((k : ℕ) : ℤ) := by
      intro hdvd
      have h' := Int.le_of_dvd (by omega) hdvd
      omega
    simp only [sub_self, dvd_zero, ↓reduceIte, h2k, add_zero] at h
    have h' : ((∑ x ∈ B, ((m x 0 : ℤ) - m x ((k : ℕ) : ℤ)) * ((m x 0 : ℤ) - m x ((k : ℕ) : ℤ)) :
        ℤ) : ℂ) = ((3 : ℤ) : ℂ) := by
      rw [h]
      norm_num
    have h'' := Int.cast_injective h'
    rw [← h'', ← hsumB]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [v]
    split_ifs <;> ring
  have hdeg : ∀ k, ∑ x, d x * v k x = 0 := by
    intro k
    have hT1 := principalCyclicProjection_eq_zero_of_coprime basis ideal p principal hue
      (inversionTwist u ℓ ((k : ℕ) : ℤ)) (inversionTwist_one hu _) (g := 1)
      (by rw [orderOf_one]; exact hpp.not_dvd_one)
    rw [hTsum] at hT1
    have h' : ((∑ x ∈ B, (Module.finrank ℂ (basis.representation x).vector : ℤ) *
        ((m x 0 : ℤ) - m x ((k : ℕ) : ℤ)) : ℤ) : ℂ) = ((0 : ℤ) : ℂ) := by
      push_cast
      rw [← hT1]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [(label_character_one basis x).1]
      push_cast
      ring
    have h'' := Int.cast_injective h'
    rw [← h'', ← hsumB]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [v, d]
    split_ifs <;> ring
  have hgram' : ∀ k k', k ≠ k' → ∑ x, v k x * v k' x = 2 := by
    intro k k' hkk
    have h := hgram _ _ (hidx k) (hidx k')
    have hk := hkmem k
    have hk' := hkmem k'
    have hsub : ¬ (ℓ : ℤ) ∣ ((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ) := by
      intro hdvd
      have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by omega)
      exact hkk (Subtype.ext (by omega))
    have hadd : ¬ (ℓ : ℤ) ∣ ((k : ℕ) : ℤ) + ((k' : ℕ) : ℤ) := by
      intro hdvd
      have h' := Int.le_of_dvd (by omega) hdvd
      omega
    simp only [hsub, hadd, ↓reduceIte, add_zero] at h
    have h' : ((∑ x ∈ B, ((m x 0 : ℤ) - m x ((k : ℕ) : ℤ)) * ((m x 0 : ℤ) - m x ((k' : ℕ) : ℤ)) :
        ℤ) : ℂ) = ((2 : ℤ) : ℂ) := by
      rw [h]
      norm_num
    have h'' := Int.cast_injective h'
    rw [← h'', ← hsumB]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [v]
    split_ifs <;> ring
  obtain ⟨a, hao, b, hbinj, hbne, δ, hδ, hv⟩ :=
    integral_norm_three_degree_zero_gram_family_of_pos hIcard principal d hd hdo v hvo hnorm hdeg
      hgram'
  have hvB : ∀ k x, v k x ≠ 0 → x ∈ B := by
    intro k x hx
    by_contra hxB
    exact hx (by simp only [v, hxB, ↓reduceIte])
  have hk₀ : (1 : ℕ) ∈ Finset.Icc 1 r := Finset.mem_Icc.mpr ⟨le_refl 1, hr1⟩
  have haB : a ∈ B := hvB ⟨1, hk₀⟩ a (((hv ⟨1, hk₀⟩).2.2.2 a).mpr (Or.inr (Or.inl rfl)))
  have hbB : ∀ k, b k ∈ B := fun k => hvB k (b k) (((hv k).2.2.2 (b k)).mpr (Or.inr (Or.inr rfl)))
  refine ⟨a, b, δ, haB, hao, hbinj, fun k => ⟨hbB k, (hbne k).1, (hbne k).2⟩, hδ,
    fun k => (hv k).2.1, (hv ⟨1, hk₀⟩).2.2.1, fun k g => ?_⟩
  rw [hTsum]
  have hext : ∑ x ∈ B, (((m x 0 : ℤ) - m x ((k : ℕ) : ℤ) : ℤ) : ℂ) *
      (basis.representation x).character g =
      ∑ x, (v k x : ℂ) * (basis.representation x).character g := by
    rw [← Finset.sum_subset (Finset.subset_univ B)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      simp only [v, hx, ↓reduceIte]
    · intro x _ hx
      simp only [v, hx, ↓reduceIte]
      push_cast
      ring
  rw [hext, (hv k).1]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  push_cast
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hprincipal, Pi.one_apply]

end Family

section Values

variable (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
  [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]

theorem cyclic_inversion_values_at_powers (hp2 : p ≠ 2) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow p G) (u : G)
    (hPu : (P : Subgroup G) = Subgroup.zpowers u) {ℓ : ℕ} (hP : Nat.card P = ℓ)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    (a : basis.index) (b : Finset.Icc 1 ((ℓ - 1) / 2) → basis.index) (δ : ℤ)
    (haB : a ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hao : a ≠ principal) (hbinj : Function.Injective b)
    (hb : ∀ k, b k ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      b k ≠ principal ∧ b k ≠ a) (hδ : δ = 1 ∨ δ = -1)
    (hT : ∀ (k : Finset.Icc 1 ((ℓ - 1) / 2)) (g : G),
      principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
        principal) u (inversionTwist u ℓ (k : ℕ)) g =
        1 + δ * (basis.representation a).character g -
          δ * (basis.representation (b k)).character g)
    {j : ℤ} (hj : ¬ (ℓ : ℤ) ∣ j) :
    (basis.representation a).character (u ^ j) = δ ∧
    (∀ k : Finset.Icc 1 ((ℓ - 1) / 2), (basis.representation (b k)).character (u ^ j) =
      δ * (cyclicRoot ℓ ^ (((k : ℕ) : ℤ) * j) + cyclicRoot ℓ ^ (-(((k : ℕ) : ℤ) * j)))) ∧
    ∀ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      θ ≠ principal → θ ≠ a → (∀ k, θ ≠ b k) →
        (basis.representation θ).character (u ^ j) = 0 := by
  classical
  obtain ⟨hu, hodd, -⟩ := card_sylow_odd_three_le hp2 P hPu hindex
  rw [hP] at hu hodd
  have hδsq : (δ : ℂ) * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hδnorm : Complex.normSq (δ : ℂ) = 1 := by rcases hδ with rfl | rfl <;> simp
  have hprinB : principal ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal :=
    coefficientBlock_self_mem _ _ _
  let α : Finset.Icc 1 ((ℓ - 1) / 2) → ℂ := fun k =>
    cyclicRoot ℓ ^ (((k : ℕ) : ℤ) * j) + cyclicRoot ℓ ^ (-(((k : ℕ) : ℤ) * j))
  have hαreal : ∀ k, (α k).im = 0 := by
    intro k
    have hconj : starRingEnd ℂ (α k) = α k := by
      simp only [α, map_add, map_zpow₀, cyclicRoot_conj, inv_zpow', neg_neg]
      ring
    exact Complex.conj_eq_iff_im.mp hconj
  have hαsum : ∑ k, α k = -1 := by
    rw [Finset.sum_coe_sort (Finset.Icc 1 ((ℓ - 1) / 2))
      (fun i : ℕ => cyclicRoot ℓ ^ ((i : ℤ) * j) + cyclicRoot ℓ ^ (-((i : ℤ) * j)))]
    exact sum_cyclicRoot_pair_eq_neg_one_of_odd hodd hj
  have hαsq : ∑ k, α k ^ 2 = ℓ - 2 := by
    rw [Finset.sum_coe_sort (Finset.Icc 1 ((ℓ - 1) / 2))
      (fun i : ℕ => (cyclicRoot ℓ ^ ((i : ℤ) * j) + cyclicRoot ℓ ^ (-((i : ℤ) * j))) ^ 2)]
    exact sum_cyclicRoot_pair_sq_of_odd hodd hj
  have hαsumR : ∑ k, (α k).re = -1 := by
    rw [← Complex.re_sum, hαsum]
    simp
  have hαsqR : ∑ k, (α k).re ^ 2 = (ℓ : ℝ) - 2 := by
    have h : ∀ k, (α k ^ 2).re = (α k).re ^ 2 := fun k => by
      rw [sq, Complex.mul_re, hαreal k]
      ring
    rw [← Finset.sum_congr rfl fun k _ => h k, ← Complex.re_sum, hαsq]
    simp
  have hTj : ∀ k, 1 + δ * (basis.representation a).character (u ^ j) -
      δ * (basis.representation (b k)).character (u ^ j) = 2 - α k := by
    intro k
    rw [← hT k, cyclic_inversionProjection_zpow basis ideal p hp2 principal hprincipal P u hPu hP
      hindex]
    simp only [α]
    ring
  set A := (basis.representation a).character (u ^ j) with hA
  have hBk : ∀ k, (basis.representation (b k)).character (u ^ j) =
      δ * ((δ * A - 1) + α k) := by
    intro k
    linear_combination (-(δ : ℂ)) * hTj k - (basis.representation (b k)).character (u ^ j) * hδsq
  have hAβ : A = δ * ((δ * A - 1) + 1) := by linear_combination (-A) * hδsq
  have hne : u ^ j ≠ 1 := fun h => hj (by rwa [← orderOf_dvd_iff_zpow_eq_one, hu] at h)
  have hcol := principal_column_norm basis ideal p hp2 principal hprincipal P hPu hindex
    (Subgroup.zpow_mem_zpowers u j) hne
  rw [hP] at hcol
  have hcolR : ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      Complex.normSq ((basis.representation θ).character (u ^ j)) = ℓ := by
    have h : ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ((Complex.normSq ((basis.representation θ).character (u ^ j)) : ℝ) : ℂ) = (ℓ : ℂ) := by
      rw [← hcol]
      refine Finset.sum_congr rfl fun θ _ => ?_
      rw [Complex.mul_conj]
    exact_mod_cast h
  let S : Finset basis.index := insert principal (insert a (Finset.univ.image b))
  have hSB : S ⊆ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | rfl | ⟨k, rfl⟩
    · exact hprinB
    · exact haB
    · exact (hb k).1
  have hpa : principal ∉ insert a (Finset.univ.image b) := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
      not_exists]
    exact ⟨fun h => hao h.symm, fun k hk => (hb k).2.1 hk⟩
  have ha : a ∉ Finset.univ.image b := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun k hk => (hb k).2.2 hk
  have hnormsq : ∀ w : ℂ, w.im = 0 → Complex.normSq ((δ * A - 1) + w) =
      Complex.normSq (δ * A - 1) + w.re ^ 2 + 2 * (δ * A - 1).re * w.re := by
    intro w hw
    have hw2 : Complex.normSq w = w.re ^ 2 := by
      rw [Complex.normSq_apply, hw]
      ring
    rw [Complex.normSq_add, hw2, Complex.mul_re, Complex.conj_re, Complex.conj_im, hw]
    ring
  have hsumS : ∑ θ ∈ S, Complex.normSq ((basis.representation θ).character (u ^ j)) =
      ℓ + ((((ℓ - 1) / 2 : ℕ) : ℝ) + 1) * Complex.normSq (δ * A - 1) := by
    rw [Finset.sum_insert hpa, Finset.sum_insert ha,
      Finset.sum_image (fun x _ y _ h => hbinj h)]
    rw [hprincipal, Pi.one_apply, Complex.normSq_one]
    have h1 : Complex.normSq A = Complex.normSq (δ * A - 1) + 1 + 2 * (δ * A - 1).re := by
      conv_lhs => rw [hAβ]
      rw [Complex.normSq_mul, hδnorm, one_mul, hnormsq 1 Complex.one_im, Complex.one_re]
      ring
    have h2 : ∀ k, Complex.normSq ((basis.representation (b k)).character (u ^ j)) =
        Complex.normSq (δ * A - 1) + (α k).re ^ 2 + 2 * (δ * A - 1).re * (α k).re := by
      intro k
      rw [hBk k, Complex.normSq_mul, hδnorm, one_mul, hnormsq (α k) (hαreal k)]
    rw [h1, Finset.sum_congr rfl fun k _ => h2 k, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, ← Finset.mul_sum, hαsumR, hαsqR, Finset.card_univ, Fintype.card_coe,
      Nat.card_Icc, nsmul_eq_mul]
    have hr : (ℓ - 1) / 2 + 1 - 1 = (ℓ - 1) / 2 := by omega
    rw [hr]
    ring
  have hsplit := Finset.sum_sdiff hSB (f := fun θ =>
    Complex.normSq ((basis.representation θ).character (u ^ j)))
  rw [hsumS, hcolR] at hsplit
  have hrest_nonneg : 0 ≤ ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal \ S, Complex.normSq ((basis.representation θ).character (u ^ j)) :=
    Finset.sum_nonneg fun θ _ => Complex.normSq_nonneg _
  have hβ0 : Complex.normSq (δ * A - 1) = 0 := by
    have hnn := Complex.normSq_nonneg (δ * A - 1)
    have hrpos : (0 : ℝ) < (((ℓ - 1) / 2 : ℕ) : ℝ) + 1 := by positivity
    nlinarith
  have hrest : ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal \ S,
      Complex.normSq ((basis.representation θ).character (u ^ j)) = 0 := by
    rw [hβ0, mul_zero, add_zero] at hsplit
    linarith
  have hβ : δ * A - 1 = 0 := Complex.normSq_eq_zero.mp hβ0
  refine ⟨?_, fun k => ?_, fun θ hθ hθo hθa hθb => ?_⟩
  · rw [hAβ, hβ, zero_add, mul_one]
  · rw [hBk k, hβ, zero_add]
  · have hθS : θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal \ S := by
      refine Finset.mem_sdiff.mpr ⟨hθ, ?_⟩
      simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
        not_exists]
      exact ⟨hθo, hθa, fun k hk => hθb k hk.symm⟩
    have h := (Finset.sum_eq_zero_iff_of_nonneg fun θ _ => Complex.normSq_nonneg
      ((basis.representation θ).character (u ^ j))).mp hrest θ hθS
    exact Complex.normSq_eq_zero.mp h

end Values

end CFSG.CyclicBlocks
