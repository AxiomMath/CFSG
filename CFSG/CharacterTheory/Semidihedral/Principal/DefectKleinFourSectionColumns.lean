module

public import CFSG.CharacterTheory.Semidihedral.Principal.BrauerFiberSectionInduction
public import CFSG.CharacterTheory.Semidihedral.Principal.ThreeNormFourColumns
public import CFSG.CharacterTheory.Semidihedral.Principal.DefectFourOddSectionMatrix
public import CFSG.CharacterTheory.Semidihedral.Principal.DefectPrimaryVanishing

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

namespace KleinFourColumns

@[expose] def signOf (b : Bool) : ℤ := if b then 1 else -1

@[expose] def signDot (x y : Fin 4 → Bool) : ℤ :=
  signOf (x 0) * signOf (y 0) + signOf (x 1) * signOf (y 1) + signOf (x 2) * signOf (y 2) +
    signOf (x 3) * signOf (y 3)

@[expose] def kleinSignMatrix : Fin 4 → Fin 3 → ℤ :=
  ![![1, 1, 1], ![-1, -1, 1], ![-1, 1, -1], ![1, -1, -1]]

theorem sign_rows_orthogonal : ∀ x y z : Fin 4 → Bool, signDot x y = 0 → signDot x z = 0 →
    signDot y z = 0 → ∀ i k : Fin 4,
      signOf (x i) * signOf (x k) + signOf (y i) * signOf (y k) + signOf (z i) * signOf (z k) +
        (signOf (x i) * signOf (y i) * signOf (z i)) *
          (signOf (x k) * signOf (y k) * signOf (z k)) = if i = k then 4 else 0 := by
  decide

theorem sign_rows_standard_pos : ∀ x y z : Fin 4 → Bool, signDot x y = 0 → signDot x z = 0 →
    signDot y z = 0 → (∀ k : Fin 4, signOf (x k) * signOf (y k) * signOf (z k) = 1) →
    ∀ i : Fin 4, ∃ k : Fin 4, signOf (x k) = kleinSignMatrix i 0 ∧
      signOf (y k) = kleinSignMatrix i 1 ∧ signOf (z k) = kleinSignMatrix i 2 := by
  decide

theorem sign_rows_standard_neg : ∀ x y z : Fin 4 → Bool, signDot x y = 0 → signDot x z = 0 →
    signDot y z = 0 → (∀ k : Fin 4, signOf (x k) * signOf (y k) * signOf (z k) = -1) →
    ∀ i : Fin 4, ∃ k : Fin 4, signOf (x k) = -kleinSignMatrix i 0 ∧
      signOf (y k) = -kleinSignMatrix i 1 ∧ signOf (z k) = -kleinSignMatrix i 2 := by
  decide

theorem kleinSignMatrix_rows_injective :
    ∀ i i' : Fin 4, (∀ j, kleinSignMatrix i j = kleinSignMatrix i' j) → i = i' := by
  decide

theorem sign_structure (U : Fin 4 → Fin 3 → ℤ) (hU : ∀ i j, U i j = 1 ∨ U i j = -1)
    (horth : ∀ j j', j ≠ j' → ∑ i, U i j * U i j' = 0) (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i)
    (hdot : ∀ j, ∑ i, (U i j : ℝ) * d i = 0) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∃ σ : Fin 4 ≃ Fin 4,
      (∀ i j, U (σ i) j = ε * kleinSignMatrix i j) ∧ ∀ i, d (σ i) = d (σ 0) := by
  let col : Fin 3 → Fin 4 → Bool := fun j i => decide (U i j = 1)
  have hcol : ∀ i j, signOf (col j i) = U i j := by
    intro i j
    rcases hU i j with h | h <;> simp [col, signOf, h]
  have hdot4 : ∀ j j', j ≠ j' → signDot (col j) (col j') = 0 := by
    intro j j' hjj'
    have h := horth j j' hjj'
    simp only [Fin.sum_univ_four] at h
    simp only [signDot, hcol]
    linarith
  have hrows := sign_rows_orthogonal (col 0) (col 1) (col 2) (hdot4 0 1 (by decide))
    (hdot4 0 2 (by decide)) (hdot4 1 2 (by decide))
  simp only [hcol] at hrows
  set w : Fin 4 → ℤ := fun i => U i 0 * U i 1 * U i 2 with hw
  have hwpm : ∀ i, w i = 1 ∨ w i = -1 := by
    intro i
    rcases hU i 0 with h0 | h0 <;> rcases hU i 1 with h1 | h1 <;> rcases hU i 2 with h2 | h2 <;>
      simp [hw, h0, h1, h2]
  set S : ℝ := ∑ i, (w i : ℝ) * d i with hS
  have hdk : ∀ k, 4 * d k = (w k : ℝ) * S := by
    intro k
    have h : ∀ i, (U i 0 * U k 0 + U i 1 * U k 1 + U i 2 * U k 2 + w i * w k : ℝ) =
        if i = k then 4 else 0 := by
      intro i
      have := hrows i k
      split_ifs at this ⊢ with hik
      · exact_mod_cast this
      · exact_mod_cast this
    have hsum : ∑ i, d i * (U i 0 * U k 0 + U i 1 * U k 1 + U i 2 * U k 2 + w i * w k : ℝ) =
        4 * d k := by
      simp only [h, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    rw [← hsum]
    have e0 := hdot 0
    have e1 := hdot 1
    have e2 := hdot 2
    simp only [Fin.sum_univ_four] at e0 e1 e2 ⊢
    rw [hS, Fin.sum_univ_four]
    linear_combination (U k 0 : ℝ) * e0 + (U k 1 : ℝ) * e1 + (U k 2 : ℝ) * e2
  have hwconst : ∀ k, w k = w 0 := by
    intro k
    rcases hwpm k with hk | hk <;> rcases hwpm 0 with h0 | h0
    · rw [hk, h0]
    · exfalso
      have a := hdk k
      have b := hdk 0
      rw [hk] at a
      rw [h0] at b
      push_cast at a b
      linarith [hd k, hd 0]
    · exfalso
      have a := hdk k
      have b := hdk 0
      rw [hk] at a
      rw [h0] at b
      push_cast at a b
      linarith [hd k, hd 0]
    · rw [hk, h0]
  have hdconst : ∀ k, d k = d 0 := by
    intro k
    have a := hdk k
    have b := hdk 0
    rw [hwconst k] at a
    linarith
  have hfind : ∀ i, ∃ k, ∀ j, U k j = w 0 * kleinSignMatrix i j := by
    intro i
    rcases hwpm 0 with h0 | h0
    · have hprod : ∀ k : Fin 4, signOf (col 0 k) * signOf (col 1 k) * signOf (col 2 k) = 1 := by
        intro k
        simp only [hcol]
        have := hwconst k
        rw [h0] at this
        exact this
      obtain ⟨k, hk0, hk1, hk2⟩ := sign_rows_standard_pos (col 0) (col 1) (col 2)
        (hdot4 0 1 (by decide)) (hdot4 0 2 (by decide)) (hdot4 1 2 (by decide)) hprod i
      refine ⟨k, fun j => ?_⟩
      rw [h0, one_mul]
      fin_cases j
      · rw [← hcol]; exact hk0
      · rw [← hcol]; exact hk1
      · rw [← hcol]; exact hk2
    · have hprod : ∀ k : Fin 4, signOf (col 0 k) * signOf (col 1 k) * signOf (col 2 k) = -1 := by
        intro k
        simp only [hcol]
        have := hwconst k
        rw [h0] at this
        exact this
      obtain ⟨k, hk0, hk1, hk2⟩ := sign_rows_standard_neg (col 0) (col 1) (col 2)
        (hdot4 0 1 (by decide)) (hdot4 0 2 (by decide)) (hdot4 1 2 (by decide)) hprod i
      refine ⟨k, fun j => ?_⟩
      rw [h0, neg_one_mul]
      fin_cases j
      · rw [← hcol]; exact hk0
      · rw [← hcol]; exact hk1
      · rw [← hcol]; exact hk2
  choose τ hτ using hfind
  have hτinj : Function.Injective τ := by
    intro i i' h
    apply kleinSignMatrix_rows_injective
    intro j
    have a := hτ i j
    have b := hτ i' j
    rw [h, b] at a
    rcases hwpm 0 with h0 | h0
    · rw [h0] at a
      linarith
    · rw [h0] at a
      linarith
  have hτbij : Function.Bijective τ := Finite.injective_iff_bijective.mp hτinj
  refine ⟨w 0, hwpm 0, Equiv.ofBijective τ hτbij, fun i j => hτ i j, fun i => ?_⟩
  simp only [Equiv.ofBijective_apply]
  rw [hdconst (τ i), hdconst (τ 0)]

theorem norm_four_column_entries {ι : Type*} (s : Finset ι) (u : ι → ℤ) (d : ι → ℝ)
    (hd : ∀ i ∈ s, 0 < d i) (hnorm : ∑ i ∈ s, u i ^ 2 = 4)
    (hdot : ∑ i ∈ s, (u i : ℝ) * d i = 0) :
    (∀ i ∈ s, u i = -1 ∨ u i = 0 ∨ u i = 1) ∧ (s.filter fun i => u i ≠ 0).card = 4 := by
  have hentry : ∀ i ∈ s, u i = -1 ∨ u i = 0 ∨ u i = 1 := by
    intro i hi
    have hle : u i ^ 2 ≤ 4 := by
      rw [← hnorm]
      exact Finset.single_le_sum (f := fun i => u i ^ 2) (fun i _ => sq_nonneg _) hi
    have hne2 : u i ^ 2 ≠ 4 := by
      intro h4
      have hrest : ∀ i' ∈ s.erase i, u i' = 0 := by
        have hsum := Finset.add_sum_erase s (fun i => u i ^ 2) hi
        rw [hnorm, h4] at hsum
        have hzero : ∑ i' ∈ s.erase i, u i' ^ 2 = 0 := by linarith
        intro i' hi'
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (u i))).mp hzero i' hi'
        exact pow_eq_zero_iff two_ne_zero |>.mp this
      have hsum := hdot
      rw [← Finset.add_sum_erase s _ hi,
        Finset.sum_eq_zero (fun i' hi' => by rw [hrest i' hi', Int.cast_zero, zero_mul]),
        add_zero] at hsum
      have hU0 : (u i : ℝ) ≠ 0 := by
        intro h0
        have : u i = 0 := by exact_mod_cast h0
        rw [this] at h4
        norm_num at h4
      exact mul_ne_zero hU0 (hd i hi).ne' hsum
    have hb : -2 ≤ u i ∧ u i ≤ 2 := by
      constructor <;> nlinarith [sq_nonneg (u i - 2), sq_nonneg (u i + 2)]
    have h2 : u i ≠ 2 := fun h => hne2 (by rw [h]; norm_num)
    have hm2 : u i ≠ -2 := fun h => hne2 (by rw [h]; norm_num)
    omega
  refine ⟨hentry, ?_⟩
  have hsq : ∀ i ∈ s, u i ^ 2 = if u i ≠ 0 then 1 else 0 := by
    intro i hi
    rcases hentry i hi with h | h | h <;> simp [h]
  rw [Finset.sum_congr rfl hsq, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    mul_one] at hnorm
  exact_mod_cast hnorm

theorem trace_idempotent_nat {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (P : Module.End ℂ V) (hP : IsIdempotentElem P) : ∃ m : ℕ, LinearMap.trace ℂ V P = m :=
  ⟨Module.finrank ℂ (LinearMap.range P), (LinearMap.IsIdempotentElem.isProj_range P hP).trace⟩

theorem half_one_add_idempotent {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (hT : T * T = 1) (c : ℂ) (hc : c * c = 1) :
    IsIdempotentElem ((2 : ℂ)⁻¹ • (1 + c • T)) := by
  change (2 : ℂ)⁻¹ • (1 + c • T) * ((2 : ℂ)⁻¹ • (1 + c • T)) = (2 : ℂ)⁻¹ • (1 + c • T)
  have hsq : (1 + c • T) * (1 + c • T) = (2 : ℂ) • (1 + c • T) := by
    have e : (1 + c • T) * (1 + c • T) = 1 + (2 : ℂ) • (c • T) + (c * c) • (T * T) := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
      module
    rw [e, hc, hT, one_smul]
    module
  rw [smul_mul_smul_comm, hsq, smul_smul]
  congr 1
  norm_num

theorem involution_character_split {G : Type*} [Group G] (data : FiniteComplexRepresentation G)
    (v : G) (hv : v ^ 2 = 1) :
    ∃ m n : ℕ, data.character v = (m : ℂ) - n ∧ (Module.finrank ℂ data.vector : ℂ) = m + n := by
  have hT : data.representation v * data.representation v = 1 := by
    rw [← map_mul, ← pow_two, hv, map_one]
  obtain ⟨m, hm⟩ := trace_idempotent_nat _
    (half_one_add_idempotent (data.representation v) hT 1 (by norm_num))
  obtain ⟨n, hn⟩ := trace_idempotent_nat _
    (half_one_add_idempotent (data.representation v) hT (-1) (by norm_num))
  rw [map_smul, map_add, LinearMap.trace_one, map_smul, one_smul, smul_eq_mul] at hm
  rw [map_smul, map_add, LinearMap.trace_one, map_smul, smul_eq_mul, smul_eq_mul] at hn
  have hchar : data.character v = LinearMap.trace ℂ data.vector (data.representation v) := rfl
  refine ⟨m, n, ?_, ?_⟩
  · rw [hchar, ← hm, ← hn]
    ring
  · rw [← hm, ← hn]
    ring

theorem kleinFour_character_congruence {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (a b : G) (hab : a * b = b * a) (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (s : ℂ) (has : data.character a = s) (hbs : data.character b = s)
    (habs : data.character (a * b) = s) :
    ∃ n : ℕ, (Module.finrank ℂ data.vector : ℂ) - s = 4 * n := by
  have hTa : data.representation a * data.representation a = 1 := by
    rw [← map_mul, ← pow_two, ha, map_one]
  have hTb : data.representation b * data.representation b = 1 := by
    rw [← map_mul, ← pow_two, hb, map_one]
  have hPa := half_one_add_idempotent (data.representation a) hTa 1 (by norm_num)
  have hPb := half_one_add_idempotent (data.representation b) hTb (-1) (by norm_num)
  have hc : Commute (data.representation a) (data.representation b) := by
    change data.representation a * data.representation b =
      data.representation b * data.representation a
    rw [← map_mul, ← map_mul, hab]
  have hcomm₀ : Commute (1 + (1 : ℂ) • data.representation a)
      (1 + (-1 : ℂ) • data.representation b) := by
    apply Commute.add_left
    · exact Commute.one_left _
    · apply Commute.add_right (Commute.one_right _)
      exact (hc.smul_left (1 : ℂ)).smul_right (-1 : ℂ)
  have hcomm : Commute ((2 : ℂ)⁻¹ • (1 + (1 : ℂ) • data.representation a))
      ((2 : ℂ)⁻¹ • (1 + (-1 : ℂ) • data.representation b)) :=
    (hcomm₀.smul_left (2 : ℂ)⁻¹).smul_right (2 : ℂ)⁻¹
  obtain ⟨n, hn⟩ := trace_idempotent_nat _ (IsIdempotentElem.mul_of_commute hcomm hPa hPb)
  refine ⟨n, ?_⟩
  rw [← hn]
  have hprod : ((2 : ℂ)⁻¹ • (1 + (1 : ℂ) • data.representation a)) *
      ((2 : ℂ)⁻¹ • (1 + (-1 : ℂ) • data.representation b)) =
      (4 : ℂ)⁻¹ • (1 + data.representation a - data.representation b -
        data.representation (a * b)) := by
    rw [map_mul, smul_mul_smul_comm]
    simp only [one_smul, neg_one_smul, add_mul, mul_add, one_mul, mul_one, mul_neg]
    rw [show (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ = (4 : ℂ)⁻¹ by norm_num]
    congr 1
    abel
  rw [hprod, map_smul, map_sub, map_sub, map_add, LinearMap.trace_one, smul_eq_mul]
  have hca : LinearMap.trace ℂ data.vector (data.representation a) = s := has
  have hcb : LinearMap.trace ℂ data.vector (data.representation b) = s := hbs
  have hcab : LinearMap.trace ℂ data.vector (data.representation (a * b)) = s := habs
  rw [hca, hcb, hcab]
  ring

theorem even_primeSectionUnion {G : Type*} [Group G] :
    primeSectionUnion 2 {x : G | Even (orderOf x)} := by
  intro u₁ u₂ v₁ v₂ e₁ e₂ hu₁ hu₂ hv₁ hv₂ hc₁ hc₂ hconj
  have h := DefectFourOdd.odd_primeSectionUnion u₁ u₂ v₁ v₂ e₁ e₂ hu₁ hu₂ hv₁ hv₂ hc₁ hc₂ hconj
  simp only [Set.mem_ofPred_eq] at h ⊢
  rw [← Nat.not_odd_iff_even, ← Nat.not_odd_iff_even, h]

theorem even_orderOf_of_mem_involutionLocalSection {G : Type*} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) (q : Subgroup.centralizer (Subgroup.zpowers t : Set G))
    (hq : q ∈ involutionLocalSection t) : Even (orderOf (q : G)) := by
  obtain ⟨y, rfl, hy⟩ := hq
  have hcomm : Commute t (y : G) :=
    Subtype.ext_iff.mp (BrauerFiberSection.commute_centralizerSelf t y)
  have hcop : Nat.Coprime (orderOf t) (orderOf (y : G)) := by
    rw [ht, Subgroup.orderOf_coe]
    exact Nat.coprime_two_left.mpr hy
  rw [Subgroup.coe_mul, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, ht]
  exact even_two_mul _

theorem even_orderOf_of_mem_involutionSectionUnion {G : Type*} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) (x : G) (hx : x ∈ involutionSectionUnion t) : Even (orderOf x) := by
  obtain ⟨g, q, hq, rfl⟩ := hx
  have h := (MulAut.conj g).orderOf_eq (q : G)
  rw [MulAut.conj_apply] at h
  rw [h]
  exact even_orderOf_of_mem_involutionLocalSection ht q hq

theorem mem_involutionSectionUnion_of_even {G : Type*} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) (hinv : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (x : G) (heven : Even (orderOf x)) (hnot : ¬ 4 ∣ orderOf x) :
    x ∈ involutionSectionUnion t := by
  obtain ⟨u, v, e, -, -, huv, hprod, hu, hv⟩ := finite_prime_primary_factorization x 2
    Nat.prime_two
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hu
  have hcop : Nat.Coprime (orderOf u) (orderOf v) := by
    rw [hk]
    exact Nat.Coprime.pow_left k hv
  have hord : orderOf x = orderOf u * orderOf v := by
    rw [← hprod]
    exact huv.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  have hvodd : Odd (orderOf v) := Nat.coprime_two_left.mp hv
  have hu2 : orderOf u = 2 := by
    rw [hk]
    rcases k with _ | _ | k
    · exfalso
      rw [hord, hk, pow_zero, one_mul] at heven
      exact (Nat.not_even_iff_odd.mpr hvodd) heven
    · rfl
    · exfalso
      apply hnot
      rw [hord, hk]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega : 2 ≤ k + 2)) _
  obtain ⟨g, hg⟩ := isConj_iff.mp (hinv u t hu2 ht)
  have hy : g * v * g⁻¹ ∈ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hg]
    have huv' : Commute (g * u * g⁻¹) (g * v * g⁻¹) := by
      have := huv.map (MulAut.conj g).toMonoidHom
      simpa [MulAut.conj_apply] using this
    exact (huv'.zpow_left n).eq
  have hyodd : Odd (orderOf (⟨g * v * g⁻¹, hy⟩ :
      Subgroup.centralizer (Subgroup.zpowers t : Set G))) := by
    rw [← Subgroup.orderOf_coe]
    have h := (MulAut.conj g).orderOf_eq v
    rw [MulAut.conj_apply] at h
    simp only
    rw [h]
    exact hvodd
  refine ⟨g⁻¹, ⟨t, element_mem_centralizer_zpowers t⟩ * ⟨g * v * g⁻¹, hy⟩,
    ⟨_, rfl, hyodd⟩, ?_⟩
  rw [Subgroup.coe_mul]
  change x = g⁻¹ * (t * (g * v * g⁻¹)) * g⁻¹⁻¹
  rw [← hg, ← hprod]
  group

theorem pairing_finset_sum_left {H ι : Type*} [Group H] [Fintype H] (s : Finset ι)
    (c : ι → ℂ) (F : ι → H → ℂ) (g : H → ℂ) :
    characterPairing (fun x => ∑ i ∈ s, c i * F i x) g =
      ∑ i ∈ s, c i * characterPairing (F i) g := by
  unfold characterPairing
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  ring

theorem pairing_basis {H : Type*} [Group H] [Fintype H] (basis : FiniteIrreducibleCharacterBasis H)
    (χ ψ : basis.index) :
    characterPairing (basis.representation χ).character (basis.representation ψ).character =
      if χ = ψ then 1 else 0 := by
  rw [characterPairing_irreducible _ _ (basis.irreducible χ) (basis.irreducible ψ)]
  by_cases h : χ = ψ
  · subst h
    simp
  · rw [ite_eq_right (fun hc => h (basis.distinct hc)), ite_eq_right h]

end KleinFourColumns

open KleinFourColumns BrauerFiberSection

theorem defect_klein_four_section_columns_four_character_family {G : Type} [Group G]
    [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (hinv : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (t : G) (ht : orderOf t = 2) (hgroup : IsPGroup 2 (Subgroup.zpowers t))
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers t : Set G)))
    (label : basis.index) (D : Subgroup G) (hDK : IsKleinFour D)
    (hD : coefficientBlockDefect basis ideal 2 label D)
    (b : Fin 3 → Finset localBasis.index) (hb : Function.Injective b)
    (hfiber : brauerFiberBlocks basis ideal 2 t hgroup localBasis label = Finset.univ.image b)
    (α : Fin 3 → Subgroup.centralizer (Subgroup.zpowers t : Set G) → ℂ)
    (hαint : ∀ j, α j ∈ coefficientVirtualLattice localBasis (b j))
    (_hαsupp : ∀ j x, x ∉ involutionLocalSection t → α j x = 0)
    (hαnorm : ∀ j, BlocksInnerProduct (α j) (α j) = 4)
    (hαspan : ∀ j, coefficientCharacterSpace localBasis (b j) ⊓
      sectionSupported (involutionLocalSection t) = Submodule.span ℂ {α j})
    (f : Fin 3 → ℕ) (hf : ∀ j, 0 < f j)
    (hαt : ∀ j, α j ⟨t, element_mem_centralizer_zpowers t⟩ = 4 * f j) :
    ∃ (Φ : Fin 4 → basis.index) (ε : ℤ) (h : ℕ),
      Function.Injective Φ ∧
      coefficientBlock basis (localizedComplexIntegerRing ideal) label = Finset.univ.image Φ ∧
      (ε = 1 ∨ ε = -1) ∧ 0 < h ∧
      (∀ i, Module.finrank ℂ (basis.representation (Φ i)).vector = h) ∧
      inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G)) (α 0) =
        (ε : ℂ) • ((basis.representation (Φ 0)).character -
          (basis.representation (Φ 1)).character - (basis.representation (Φ 2)).character +
            (basis.representation (Φ 3)).character) ∧
      inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G)) (α 1) =
        (ε : ℂ) • ((basis.representation (Φ 0)).character -
          (basis.representation (Φ 1)).character + (basis.representation (Φ 2)).character -
            (basis.representation (Φ 3)).character) ∧
      inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G)) (α 2) =
        (ε : ℂ) • ((basis.representation (Φ 0)).character +
          (basis.representation (Φ 1)).character - (basis.representation (Φ 2)).character -
            (basis.representation (Φ 3)).character) ∧
      (∀ x : G, Odd (orderOf x) → ∀ i i',
        (basis.representation (Φ i)).character x = (basis.representation (Φ i')).character x) ∧
      (∀ x : G, 4 ∣ orderOf x → ∀ i, (basis.representation (Φ i)).character x = 0) ∧
      (∀ x ∈ involutionLocalSection t,
        (basis.representation (Φ 0)).character x = ε * (α 0 x + α 1 x + α 2 x) / 4 ∧
        (basis.representation (Φ 1)).character x = ε * (-α 0 x - α 1 x + α 2 x) / 4 ∧
        (basis.representation (Φ 2)).character x = ε * (-α 0 x + α 1 x - α 2 x) / 4 ∧
        (basis.representation (Φ 3)).character x = ε * (α 0 x - α 1 x - α 2 x) / 4) ∧
      (∀ v : G, orderOf v = 2 →
        (basis.representation (Φ 0)).character v = ε * ((f 0 : ℂ) + f 1 + f 2) ∧
        (basis.representation (Φ 1)).character v = ε * (-(f 0 : ℂ) - f 1 + f 2) ∧
        (basis.representation (Φ 2)).character v = ε * (-(f 0 : ℂ) + f 1 - f 2) ∧
        (basis.representation (Φ 3)).character v = ε * ((f 0 : ℂ) - f 1 - f 2)) ∧
      f 0 + f 1 + f 2 ≤ h ∧ (h : ℤ) ≡ ε * (f 0 + f 1 + f 2) [ZMOD 4] ∧
      (IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) → f 0 + f 1 + f 2 < h) := by
  obtain ⟨-, horth, e, he, hesymm, hiso⟩ :=
    brauer_fiber_involution_section_induction_decomposition basis ideal t ht hgroup localBasis
      label
  have hbT : ∀ j, b j ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label := fun j => by
    rw [hfiber]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have hαV : ∀ j, α j ∈ coefficientCharacterSpace localBasis (b j) ⊓
      sectionSupported (involutionLocalSection t) := fun j => by
    rw [hαspan j]
    exact Submodule.mem_span_singleton_self _
  have hαM : ∀ j, α j ∈ (⨆ b' ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
      coefficientCharacterSpace localBasis b' ⊓ sectionSupported (involutionLocalSection t)) :=
    fun j => Submodule.mem_iSup_of_mem (b j) (Submodule.mem_iSup_of_mem (hbT j) (hαV j))
  have hMspan : ∀ F ∈ (⨆ b' ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
      coefficientCharacterSpace localBasis b' ⊓ sectionSupported (involutionLocalSection t)),
      ∃ c : Fin 3 → ℂ, ∑ j, c j • α j = F := by
    intro F hF
    have hle : (⨆ b' ∈ brauerFiberBlocks basis ideal 2 t hgroup localBasis label,
        coefficientCharacterSpace localBasis b' ⊓ sectionSupported (involutionLocalSection t)) ≤
        Submodule.span ℂ (Set.range α) := by
      refine iSup₂_le fun b' hb' => ?_
      rw [hfiber] at hb'
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb'
      rw [hαspan j]
      exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self j))
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hle hF)
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Fin 3 → G → ℂ,
      ∀ j, Θ j = inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G)) (α j) :=
    ⟨_, fun _ => rfl⟩
  have hΘe : ∀ j, (e ⟨α j, hαM j⟩ : G → ℂ) = Θ j := fun j => by rw [he, hΘ]
  have hΘW : ∀ j, Θ j ∈ coefficientCharacterSpace basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
        sectionSupported (involutionSectionUnion t) := fun j => by
    rw [← hΘe]
    exact (e _).2
  have hΘQ : ∀ j, ∀ x ∈ involutionLocalSection t, Θ j x = α j x := by
    intro j x hx
    have h := congrFun (congrArg Subtype.val (e.symm_apply_apply ⟨α j, hαM j⟩)) x
    rw [hesymm, hΘe] at h
    unfold characterFunctionMask at h
    rwa [ite_eq_left hx] at h
  have hΘvirt : ∀ j, Θ j ∈ virtualCharacters G := fun j => by
    rw [hΘ]
    exact inducedFunction_mem_virtualCharacters _
      (coefficientVirtualLattice_le_virtual localBasis (b j) (hαint j))
  have hΘodd : ∀ j (x : G), Odd (orderOf x) → Θ j x = 0 := by
    intro j x hx
    apply (Submodule.mem_inf.mp (hΘW j)).2 x
    intro hmem
    exact (Nat.not_even_iff_odd.mpr hx) (even_orderOf_of_mem_involutionSectionUnion ht x hmem)
  have hΘvchar : ∀ j, Θ j ∈ BlocksVChar G := fun j => by
    rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup]
    exact hΘvirt j
  have hgram : ∀ i j, characterPairing (Θ i) (Θ j) = if i = j then 4 else 0 := by
    intro i j
    rw [← blocksInnerProduct_eq_characterPairing _ (hΘvchar j), ← hΘe i, ← hΘe j, hiso]
    split_ifs with hij
    · subst hij
      exact hαnorm i
    · exact horth (b i) (hbT i) (b j) (hbT j) (hb.ne hij) (α i) (hαV i) (α j) (hαV j)
  have hint : ∀ (χ : basis.index) (j : Fin 3),
      ∃ n : ℤ, characterPairing (Θ j) (basis.representation χ).character = n :=
    fun χ j => characterPairing_virtual_integer _ _ (hΘvirt j) (character_mem_virtualCharacters _)
  choose u hu using hint
  have hΘexp : ∀ j, Θ j = fun x => ∑ χ ∈ coefficientBlock basis
      (localizedComplexIntegerRing ideal) label,
        (u χ j : ℂ) * (basis.representation χ).character x := by
    intro j
    have h := characterSubsetProjection_identity basis _ (Θ j) (Submodule.mem_inf.mp (hΘW j)).1
    rw [← h]
    funext x
    rw [BrauerSecondMain.characterSubsetProjection_apply_sum]
    exact Finset.sum_congr rfl fun χ _ => by rw [hu χ j]
  have hUU : ∀ i j, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      u χ i * u χ j = if i = j then 4 else 0 := by
    intro i j
    have h := hgram i j
    rw [hΘexp i, pairing_finset_sum_left] at h
    have h' : ((∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        u χ i * u χ j : ℤ) : ℂ) = ((if i = j then 4 else 0 : ℤ) : ℂ) := by
      push_cast
      rw [← h]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [characterPairing_comm, hu χ j]
    exact_mod_cast h'
  have hUd : ∀ j, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      (u χ j : ℝ) * (Module.finrank ℂ (basis.representation χ).vector : ℝ) = 0 := by
    intro j
    have h := congrFun (hΘexp j) 1
    rw [hΘodd j 1 (by rw [orderOf_one]; exact odd_one)] at h
    have h' : ((∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        u χ j * (Module.finrank ℂ (basis.representation χ).vector : ℤ) : ℤ) : ℂ) = 0 := by
      push_cast
      rw [h]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [FiniteComplexRepresentation.character, Representation.char_one]
    have h'' : ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        u χ j * (Module.finrank ℂ (basis.representation χ).vector : ℤ) = 0 := by
      exact_mod_cast h'
    exact_mod_cast h''
  have hexp2 : ∀ x ∈ D, x ≠ 1 → orderOf x = 2 := by
    intro x hx hx1
    have h2 : (⟨x, hx⟩ : D) ^ 2 = 1 := by
      have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : D)
      rwa [hDK.exponent_two] at this
    have h2' : x ^ 2 = 1 := by
      have := congrArg Subtype.val h2
      simpa using this
    exact orderOf_eq_prime h2' hx1
  have hvanish : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      ∀ x : G, 4 ∣ orderOf x → (basis.representation χ).character x = 0 := fun χ hχ x hx =>
    block_characters_vanish_of_defect_exponent_prime basis ideal 2 label D hD hexp2 x
      (by norm_num; exact hx) χ hχ
  have hevenExp : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      characterFunctionMask {x : G | Even (orderOf x)} (basis.representation χ).character =
        fun x => ∑ j, ((u χ j : ℂ) / 4) * Θ j x := by
    intro χ hχ
    have hFW : characterFunctionMask {x : G | Even (orderOf x)}
        (basis.representation χ).character ∈ coefficientCharacterSpace basis
          (coefficientBlock basis (localizedComplexIntegerRing ideal) label) ⊓
            sectionSupported (involutionSectionUnion t) := by
      refine Submodule.mem_inf.mpr ⟨coefficientBlock_section_mask_mem basis ideal 2 label _
        even_primeSectionUnion _ (Submodule.subset_span ⟨χ, hχ, rfl⟩), ?_⟩
      intro x hx
      unfold characterFunctionMask
      split_ifs with heven
      · by_cases h4 : 4 ∣ orderOf x
        · exact hvanish χ hχ x h4
        · exact absurd (mem_involutionSectionUnion_of_even ht hinv x heven h4) hx
      · rfl
    obtain ⟨c, hc⟩ := hMspan _ (e.symm ⟨_, hFW⟩).2
    have hF : characterFunctionMask {x : G | Even (orderOf x)} (basis.representation χ).character =
        fun x => ∑ j, c j * Θ j x := by
      have h1 : inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G))
          (e.symm ⟨_, hFW⟩ : Subgroup.centralizer (Subgroup.zpowers t : Set G) → ℂ) =
            characterFunctionMask {x : G | Even (orderOf x)}
              (basis.representation χ).character := by
        have h0 := congrArg Subtype.val (e.apply_symm_apply ⟨_, hFW⟩)
        rw [he] at h0
        exact h0
      rw [← h1, ← hc]
      funext x
      have hlin := congrFun (map_sum (inducedFunctionComplexLinearMap
        (Subgroup.centralizer (Subgroup.zpowers t : Set G))) (fun j => c j • α j) Finset.univ) x
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hlin
      change inducedFunction _ (∑ j, c j • α j) x = _
      rw [show inducedFunction (Subgroup.centralizer (Subgroup.zpowers t : Set G))
        (∑ j, c j • α j) x = (inducedFunctionComplexLinearMap
          (Subgroup.centralizer (Subgroup.zpowers t : Set G)) (∑ j, c j • α j)) x from rfl, hlin]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hΘ j]
      rfl
    have hcoef : ∀ k, c k = (u χ k : ℂ) / 4 := by
      intro k
      have h : characterPairing (characterFunctionMask {x : G | Even (orderOf x)}
          (basis.representation χ).character) (Θ k) =
          characterPairing (fun x => ∑ j, c j * Θ j x) (Θ k) := by rw [hF]
      rw [characterPairing_expansion_left] at h
      simp only [hgram, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
      have hl : characterPairing (characterFunctionMask {x : G | Even (orderOf x)}
          (basis.representation χ).character) (Θ k) = u χ k := by
        rw [← hu χ k, characterPairing_comm]
        unfold characterPairing characterFunctionMask
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Set.mem_ofPred_eq]
        split_ifs with hx
        · rfl
        · rw [hΘodd k x (by rw [← orderOf_inv]; exact Nat.not_even_iff_odd.mp hx), zero_mul,
            zero_mul]
      rw [hl] at h
      linear_combination -h / 4
    rw [hF]
    funext x
    exact Finset.sum_congr rfl fun j _ => by rw [hcoef j]
  have hA : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      ∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        oddSectionMatrix basis χ ψ =
          ((4 * (if χ = ψ then 1 else 0) - ∑ j, u χ j * u ψ j : ℤ) : ℂ) := by
    intro χ hχ ψ _
    rw [DefectFourOdd.oddSectionMatrix_eq_pairing]
    have hsplit : characterFunctionMask {x : G | Odd (orderOf x)}
        (basis.representation χ).character =
        fun x => (basis.representation χ).character x -
          characterFunctionMask {x : G | Even (orderOf x)}
            (basis.representation χ).character x := by
      funext x
      unfold characterFunctionMask
      simp only [Set.mem_ofPred_eq]
      by_cases hx : Odd (orderOf x)
      · rw [ite_eq_left hx, ite_eq_right (Nat.not_even_iff_odd.mpr hx), sub_zero]
      · rw [ite_eq_right hx, ite_eq_left (Nat.not_odd_iff_even.mp hx), sub_self]
    rw [hsplit, hevenExp χ hχ]
    have hsub : characterPairing (fun x => (basis.representation χ).character x -
        ∑ j, (u χ j : ℂ) / 4 * Θ j x) (basis.representation ψ).character =
        characterPairing (basis.representation χ).character (basis.representation ψ).character -
          ∑ j, (u χ j : ℂ) / 4 * characterPairing (Θ j) (basis.representation ψ).character := by
      rw [← characterPairing_expansion_left]
      unfold characterPairing
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [sub_mul, Finset.sum_mul]
    rw [hsub, pairing_basis]
    simp only [hu]
    push_cast
    rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) label with hB
  have hlabel : label ∈ B := coefficientBlock_self_mem basis _ label
  have hdpos : ∀ χ : basis.index,
      (0 : ℝ) < (Module.finrank ℂ (basis.representation χ).vector : ℝ) := fun χ => by
    have h := irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    have h' : Module.finrank ℂ (basis.representation χ).vector ≠ 0 := by exact_mod_cast h
    exact_mod_cast Nat.pos_of_ne_zero h'
  have hodd : ∃ χ ∈ B, ∃ ψ ∈ B, Odd (∑ j, u χ j * u ψ j) := by
    let eB := B.equivFin
    have h3 := three_norm_four_integral_columns_odd_gram_entry _
      (Finset.card_pos.mpr ⟨label, hlabel⟩) (Matrix.of fun i j => u (eB.symm i) j) ?_
      (fun i => (Module.finrank ℂ (basis.representation (eB.symm i)).vector : ℝ))
      (fun i => hdpos _) ?_
    · obtain ⟨⟨i, i', hii'⟩, -⟩ := h3
      refine ⟨eB.symm i, (eB.symm i).2, eB.symm i', (eB.symm i').2, ?_⟩
      simpa [Matrix.mul_apply, Matrix.transpose_apply] using hii'
    · ext j j'
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul]
      rw [Equiv.sum_comp eB.symm (fun x : B => u x j * u x j'),
        Finset.sum_coe_sort B (fun χ => u χ j * u χ j'), hUU j j']
      split_ifs <;> simp
    · funext j
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.transpose_apply,
        Matrix.of_apply, Pi.zero_apply]
      rw [Equiv.sum_comp eB.symm (fun x : B => (u x j : ℝ) *
        (Module.finrank ℂ (basis.representation x).vector : ℝ)),
        Finset.sum_coe_sort B (fun χ => (u χ j : ℝ) *
          (Module.finrank ℂ (basis.representation χ).vector : ℝ))]
      exact hUd j
  obtain ⟨χ₀, hχ₀, ψ₀, hψ₀, hodd0⟩ := hodd
  have hBle : B.card ≤ 4 :=
    (defect_order_four_odd_section_matrix_bounds_block basis ideal label D hD
      hDK.card_four).2 (fun χ hχ ψ hψ => ⟨_, hA χ hχ ψ hψ⟩)
      ⟨χ₀, hχ₀, ψ₀, hψ₀, _, Even.sub_odd ⟨2 * (if χ₀ = ψ₀ then 1 else 0), by ring⟩ hodd0,
        hA χ₀ hχ₀ ψ₀ hψ₀⟩
  have hcol := fun j => norm_four_column_entries B (fun χ => u χ j)
    (fun χ => (Module.finrank ℂ (basis.representation χ).vector : ℝ)) (fun χ _ => hdpos χ)
    (by
      have h := hUU j j
      rw [ite_eq_left rfl] at h
      simpa [sq] using h) (hUd j)
  have hBge : 4 ≤ B.card := by
    rw [← (hcol 0).2]
    exact Finset.card_filter_le _ _
  have hB4 : B.card = 4 := le_antisymm hBle hBge
  have hpm : ∀ χ ∈ B, ∀ j, u χ j = 1 ∨ u χ j = -1 := by
    intro χ hχ j
    have hfilter : B.filter (fun χ => u χ j ≠ 0) = B :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [(hcol j).2, hB4])
    have hne : u χ j ≠ 0 := by
      have : χ ∈ B.filter (fun χ => u χ j ≠ 0) := by rw [hfilter]; exact hχ
      exact (Finset.mem_filter.mp this).2
    rcases (hcol j).1 χ hχ with h | h | h
    · exact Or.inr h
    · exact absurd h hne
    · exact Or.inl h
  let eB4 : Fin 4 ≃ B := (B.equivFinOfCardEq hB4).symm
  have hreindex : ∀ g : basis.index → ℝ, ∑ i : Fin 4, g (eB4 i) = ∑ χ ∈ B, g χ := fun g => by
    rw [Equiv.sum_comp eB4 (fun x : B => g x), Finset.sum_coe_sort B g]
  have hreindexZ : ∀ g : basis.index → ℤ, ∑ i : Fin 4, g (eB4 i) = ∑ χ ∈ B, g χ := fun g => by
    rw [Equiv.sum_comp eB4 (fun x : B => g x), Finset.sum_coe_sort B g]
  obtain ⟨ε, hε, σ, hσU, hσd⟩ := sign_structure (fun i j => u (eB4 i) j)
    (fun i j => hpm _ (eB4 i).2 j)
    (fun j j' hjj' => by
      rw [hreindexZ (fun χ => u χ j * u χ j'), hUU j j', ite_eq_right hjj'])
    (fun i => (Module.finrank ℂ (basis.representation (eB4 i)).vector : ℝ)) (fun i => hdpos _)
    (fun j => by rw [hreindex (fun χ => (u χ j : ℝ) *
      (Module.finrank ℂ (basis.representation χ).vector : ℝ))]; exact hUd j)
  set Φ : Fin 4 → basis.index := fun i => (eB4 (σ i) : basis.index) with hΦ
  have hΦmem : ∀ i, Φ i ∈ B := fun i => (eB4 (σ i)).2
  have hΦinj : Function.Injective Φ := by
    intro i i' h
    exact σ.injective (eB4.injective (Subtype.ext h))
  have hΦimage : B = Finset.univ.image Φ := by
    apply Finset.eq_of_subset_of_card_le
    · intro χ hχ
      rw [Finset.mem_image]
      obtain ⟨i, hi⟩ := eB4.surjective ⟨χ, hχ⟩
      refine ⟨σ.symm i, Finset.mem_univ _, ?_⟩
      simp only [hΦ, Equiv.apply_symm_apply, hi]
    · rw [Finset.card_image_of_injective _ hΦinj, Finset.card_univ, Fintype.card_fin, hB4]
  have hΦu : ∀ i j, u (Φ i) j = ε * kleinSignMatrix i j := hσU
  have hsumΦ : ∀ g : basis.index → ℂ, ∑ χ ∈ B, g χ = ∑ i, g (Φ i) := fun g => by
    rw [hΦimage, Finset.sum_image (fun i _ i' _ h => hΦinj h)]
  have hΘΦ : ∀ j x, Θ j x = ∑ i, ((ε * kleinSignMatrix i j : ℤ) : ℂ) *
      (basis.representation (Φ i)).character x := by
    intro j x
    rw [hΘexp j]
    beta_reduce
    rw [hsumΦ (fun χ => (u χ j : ℂ) * (basis.representation χ).character x)]
    simp only [hΦu]
  have hε0 : (ε : ℂ) ≠ 0 := by
    rcases hε with h | h <;> simp [h]
  have hoddeq : ∀ x : G, Odd (orderOf x) → ∀ i,
      (basis.representation (Φ i)).character x = (basis.representation (Φ 0)).character x := by
    intro x hx i
    have e0 := hΘΦ 0 x
    have e1 := hΘΦ 1 x
    have e2 := hΘΦ 2 x
    rw [hΘodd 0 x hx] at e0
    rw [hΘodd 1 x hx] at e1
    rw [hΘodd 2 x hx] at e2
    simp only [Fin.sum_univ_four, kleinSignMatrix] at e0 e1 e2
    norm_num at e0 e1 e2
    have h1 : (ε : ℂ) * (2 * ((basis.representation (Φ 1)).character x -
        (basis.representation (Φ 0)).character x)) = 0 := by linear_combination e0 + e1
    have h2 : (ε : ℂ) * (2 * ((basis.representation (Φ 2)).character x -
        (basis.representation (Φ 0)).character x)) = 0 := by linear_combination e0 + e2
    have h3 : (ε : ℂ) * (2 * ((basis.representation (Φ 3)).character x -
        (basis.representation (Φ 0)).character x)) = 0 := by linear_combination e1 + e2
    have hsol : ∀ y : ℂ, (ε : ℂ) * (2 * y) = 0 → y = 0 := fun y hy => by
      rcases mul_eq_zero.mp hy with h | h
      · exact absurd h hε0
      · rcases mul_eq_zero.mp h with h' | h'
        · norm_num at h'
        · exact h'
    fin_cases i
    · rfl
    · exact sub_eq_zero.mp (hsol _ h1)
    · exact sub_eq_zero.mp (hsol _ h2)
    · exact sub_eq_zero.mp (hsol _ h3)
  have hQval : ∀ i, ∀ x ∈ involutionLocalSection t, (basis.representation (Φ i)).character x =
      ∑ j, ((ε * kleinSignMatrix i j : ℤ) : ℂ) / 4 * α j x := by
    intro i x hx
    have h := congrFun (hevenExp (Φ i) (hΦmem i)) x
    unfold characterFunctionMask at h
    rw [ite_eq_left (show (x : G) ∈ {x : G | Even (orderOf x)} from
      even_orderOf_of_mem_involutionLocalSection ht x hx)] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΦu i j, hΘQ j x hx]
  have htQ : (⟨t, element_mem_centralizer_zpowers t⟩ :
      Subgroup.centralizer (Subgroup.zpowers t : Set G)) ∈ involutionLocalSection t :=
    ⟨1, (mul_one _).symm, by rw [orderOf_one]; exact odd_one⟩
  have htval : ∀ i, (basis.representation (Φ i)).character t =
      ∑ j, ((ε * kleinSignMatrix i j : ℤ) : ℂ) * f j := by
    intro i
    have h := hQval i _ htQ
    simp only [hαt] at h
    change (basis.representation (Φ i)).character t = _ at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hinvval : ∀ i (v : G), orderOf v = 2 →
      (basis.representation (Φ i)).character v = (basis.representation (Φ i)).character t := by
    intro i v hv
    obtain ⟨g, rfl⟩ := isConj_iff.mp (hinv t v ht hv)
    exact Representation.char_conj _ _ _
  have hΦdeg : ∀ i, Module.finrank ℂ (basis.representation (Φ i)).vector =
      Module.finrank ℂ (basis.representation (Φ 0)).vector := by
    intro i
    have h := hσd i
    exact_mod_cast h
  have hs : (basis.representation (Φ 0)).character t = (ε : ℂ) * ((f 0 : ℂ) + f 1 + f 2) := by
    rw [htval 0]
    simp [Fin.sum_univ_three, kleinSignMatrix]
    ring
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  obtain ⟨m, n, hmn, hdeg⟩ := involution_character_split (basis.representation (Φ 0)) t ht2
  have hhmn : Module.finrank ℂ (basis.representation (Φ 0)).vector = m + n := by
    exact_mod_cast hdeg
  have hsmn : ε * ((f 0 : ℤ) + f 1 + f 2) = (m : ℤ) - n := by
    have h : ((ε * ((f 0 : ℤ) + f 1 + f 2) : ℤ) : ℂ) = (((m : ℤ) - n : ℤ) : ℂ) := by
      push_cast
      rw [← hs, hmn]
    exact_mod_cast h
  have hbound : f 0 + f 1 + f 2 ≤ Module.finrank ℂ (basis.representation (Φ 0)).vector := by
    rw [hhmn]
    rcases hε with h1 | h1 <;> rw [h1] at hsmn <;> omega
  have hcardD : Fintype.card D = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hDK.card_four
  obtain ⟨a, haS⟩ : ((Finset.univ : Finset D).erase 1).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      hcardD]
    norm_num
  obtain ⟨a', haS'⟩ : (((Finset.univ : Finset D).erase 1).erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem haS,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardD]
    norm_num
  have ha1 : a ≠ 1 := Finset.ne_of_mem_erase haS
  have ha'1 : a' ≠ 1 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase haS')
  have ha'a : a' ≠ a := Finset.ne_of_mem_erase haS'
  have hsqD : ∀ x : D, x ^ 2 = 1 := fun x => by
    have := Monoid.pow_exponent_eq_one x
    rwa [hDK.exponent_two] at this
  have hinvD : ∀ x : D, x⁻¹ = x := fun x => by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hsqD x]
  have hcommD : a * a' = a' * a := by
    rw [← hinvD (a * a'), mul_inv_rev, hinvD a, hinvD a']
  have haa' : a * a' ≠ 1 := by
    intro h
    apply ha'a
    have := eq_inv_of_mul_eq_one_right h
    rwa [hinvD] at this
  have hordD : ∀ x : D, x ≠ 1 → orderOf (x : G) = 2 := by
    intro x hx
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hsqD x) hx
  have hcong : ∃ k : ℕ, (Module.finrank ℂ (basis.representation (Φ 0)).vector : ℂ) -
      (ε : ℂ) * ((f 0 : ℂ) + f 1 + f 2) = 4 * k := by
    apply kleinFour_character_congruence (basis.representation (Φ 0)) (a : G) (a' : G)
      (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcommD])
      (by rw [← Subgroup.coe_pow, hsqD a, Subgroup.coe_one])
      (by rw [← Subgroup.coe_pow, hsqD a', Subgroup.coe_one])
    · rw [hinvval 0 _ (hordD a ha1), hs]
    · rw [hinvval 0 _ (hordD a' ha'1), hs]
    · rw [← Subgroup.coe_mul, hinvval 0 _ (hordD _ haa'), hs]
  obtain ⟨k, hk⟩ := hcong
  have hkZ : (Module.finrank ℂ (basis.representation (Φ 0)).vector : ℤ) -
      ε * ((f 0 : ℤ) + f 1 + f 2) = 4 * k := by
    have h : (((Module.finrank ℂ (basis.representation (Φ 0)).vector : ℤ) -
        ε * ((f 0 : ℤ) + f 1 + f 2) : ℤ) : ℂ) = ((4 * k : ℤ) : ℂ) := by
      push_cast
      exact hk
    exact_mod_cast h
  have hsimple : IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      f 0 + f 1 + f 2 < Module.finrank ℂ (basis.representation (Φ 0)).vector := by
    intro hsimp hnonab
    rcases lt_or_eq_of_le hbound with hlt | heq
    · exact hlt
    exfalso
    have hs3 : 3 ≤ f 0 + f 1 + f 2 := by
      have := hf 0
      have := hf 1
      have := hf 2
      omega
    have htriv : ¬ ∀ g, (basis.representation (Φ 0)).representation g = 1 := by
      intro hall
      have hchar : ∀ g, (basis.representation (Φ 0)).character g =
          (Module.finrank ℂ (basis.representation (Φ 0)).vector : ℂ) := fun g => by
        rw [FiniteComplexRepresentation.character, Representation.character, hall g,
          LinearMap.trace_one]
      have hpair := pairing_basis basis (Φ 0) (Φ 0)
      rw [ite_eq_left rfl] at hpair
      unfold characterPairing at hpair
      simp only [hchar] at hpair
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
        ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul] at hpair
      have hh : (Module.finrank ℂ (basis.representation (Φ 0)).vector : ℝ) ^ 2 = 1 := by
        have : ((Module.finrank ℂ (basis.representation (Φ 0)).vector : ℂ)) ^ 2 = 1 := by
          rw [sq]; exact hpair
        exact_mod_cast this
      have hge : (3 : ℝ) ≤ (Module.finrank ℂ (basis.representation (Φ 0)).vector : ℝ) := by
        exact_mod_cast heq ▸ hs3
      nlinarith
    rcases hε with hε1 | hε1
    ·
      apply representation_involution_character_ne_degree_of_simple
        (basis.representation (Φ 0)).representation (by push Not at htriv; exact htriv) t ht
      change (basis.representation (Φ 0)).character t = (basis.representation (Φ 0)).character 1
      rw [hs, hε1, FiniteComplexRepresentation.character, Representation.char_one, ← heq]
      push_cast
      ring
    ·
      have hneg : -(basis.representation (Φ 0)).representation t = 1 := by
        apply involutive_linearMap_eq_one_of_trace_eq_finrank
        · rw [neg_mul_neg, ← map_mul, ← pow_two, ht2, map_one]
        · rw [map_neg]
          change -(basis.representation (Φ 0)).character t = _
          rw [hs, hε1, ← heq]
          push_cast
          ring
      have hρt : (basis.representation (Φ 0)).representation t = -1 := by
        rw [← neg_neg ((basis.representation (Φ 0)).representation t), hneg]
      have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
      have hker : ∀ g : G, t * g * t⁻¹ * g⁻¹ ∈ (basis.representation (Φ 0)).representation.ker :=
        fun g => by
          rw [MonoidHom.mem_ker, htinv, map_mul, map_mul, map_mul, hρt]
          rw [show (-1 : Module.End ℂ (basis.representation (Φ 0)).vector) *
              (basis.representation (Φ 0)).representation g * (-1) *
                (basis.representation (Φ 0)).representation g⁻¹ =
              (basis.representation (Φ 0)).representation g *
                (basis.representation (Φ 0)).representation g⁻¹ by noncomm_ring,
            ← map_mul, mul_inv_cancel, map_one]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (basis.representation (Φ 0)).representation.ker with hbot | htop
      · obtain ⟨x, y, hxy⟩ := hnonab
        have hcent : ∀ g : G, t * g = g * t := fun g => by
          have h := hker g
          rw [hbot, Subgroup.mem_bot] at h
          calc t * g = t * g * t⁻¹ * g⁻¹ * (g * t) := by group
            _ = g * t := by rw [h, one_mul]
        have htcenter : t ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => (hcent g).symm
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
        · rw [hc, Subgroup.mem_bot] at htcenter
          rw [htcenter, orderOf_one] at ht
          norm_num at ht
        · apply hxy
          have hx : x ∈ Subgroup.center G := by rw [hc]; trivial
          exact (Subgroup.mem_center_iff.mp hx y).symm
      · apply htriv
        intro g
        have h : g ∈ (basis.representation (Φ 0)).representation.ker := by rw [htop]; trivial
        exact h
  refine ⟨Φ, ε, Module.finrank ℂ (basis.representation (Φ 0)).vector, hΦinj, hΦimage, hε,
    Nat.pos_of_ne_zero fun h0 => ?_, hΦdeg, ?_, ?_, ?_,
    fun x hx i i' => (hoddeq x hx i).trans (hoddeq x hx i').symm,
    fun x hx i => hvanish (Φ i) (hΦmem i) x hx, ?_, ?_, hbound,
    Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨k, hkZ⟩), hsimple⟩
  · have := hdpos (Φ 0)
    rw [h0, Nat.cast_zero] at this
    exact lt_irrefl _ this
  · funext x
    rw [← hΘ 0, hΘΦ 0 x]
    simp [Fin.sum_univ_four, kleinSignMatrix]
    ring
  · funext x
    rw [← hΘ 1, hΘΦ 1 x]
    simp [Fin.sum_univ_four, kleinSignMatrix]
    ring
  · funext x
    rw [← hΘ 2, hΘΦ 2 x]
    simp [Fin.sum_univ_four, kleinSignMatrix]
    ring
  · intro x hx
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hQval _ x hx] <;> simp [Fin.sum_univ_three, kleinSignMatrix] <;>
      ring
  · intro v hv
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hinvval _ v hv, htval] <;>
      simp [Fin.sum_univ_three, kleinSignMatrix] <;> ring

end CFSG.Semidihedral.Principal
