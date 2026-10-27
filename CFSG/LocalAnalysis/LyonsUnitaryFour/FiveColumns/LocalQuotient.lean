module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.OneBlock
public import CFSG.LocalAnalysis.LyonsUnitaryFour.CentralFourOddCore

public section

open scoped BigOperators Classical Pointwise

namespace CFSG.LyonsUnitaryFour

variable {L : Type} [Group L]

structure UnitaryFourByFive (S₀ : Subgroup L) (h : L) : Prop where
  normal : S₀.Normal
  two_group : IsPGroup 2 S₀
  card : Nat.card S₀ = 64
  card_center : Nat.card (Subgroup.center S₀) = 4
  commutator : ∀ x ∈ S₀, ∀ y ∈ S₀, x * y * x⁻¹ * y⁻¹ ∈ (Subgroup.center S₀).map S₀.subtype
  orderOf_h : orderOf h = 5
  sup : S₀ ⊔ Subgroup.zpowers h = ⊤
  inf : S₀ ⊓ Subgroup.zpowers h = ⊥
  fixes : ∀ x ∈ (Subgroup.center S₀).map S₀.subtype, h * x * h⁻¹ = x
  free : ∀ x ∈ S₀, h * x * h⁻¹ * x⁻¹ ∈ (Subgroup.center S₀).map S₀.subtype →
    x ∈ (Subgroup.center S₀).map S₀.subtype

namespace UnitaryFourByFive

variable {S₀ : Subgroup L} {h : L} (hL : UnitaryFourByFive S₀ h)
include hL

theorem pow_five : h ^ 5 = 1 := by
  rw [← hL.orderOf_h]
  exact pow_orderOf_eq_one h

theorem pow_mem_iff (j : ℕ) : h ^ j ∈ S₀ ↔ 5 ∣ j := by
  constructor
  · intro hj
    have hmem : h ^ j ∈ S₀ ⊓ Subgroup.zpowers h := ⟨hj, Subgroup.npow_mem_zpowers h j⟩
    rw [hL.inf, Subgroup.mem_bot] at hmem
    rw [← hL.orderOf_h]
    exact orderOf_dvd_of_pow_eq_one hmem
  · rintro ⟨k, rfl⟩
    rw [pow_mul, hL.pow_five, one_pow]
    exact S₀.one_mem

theorem pow_mod_five (j : ℕ) : h ^ j = h ^ (j % 5) := by
  conv_lhs => rw [← Nat.mod_add_div j 5, pow_add, pow_mul, hL.pow_five, one_pow, mul_one]

theorem exists_decomp (g : L) : ∃ s ∈ S₀, ∃ j : ℕ, j < 5 ∧ g = s * h ^ j := by
  have : S₀.Normal := hL.normal
  have hg : g ∈ ((S₀ ⊔ Subgroup.zpowers h : Subgroup L) : Set L) := by
    rw [hL.sup]
    exact Subgroup.mem_top g
  rw [Subgroup.normal_mul] at hg
  obtain ⟨s, hs, t, ht, rfl⟩ := hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  refine ⟨s, hs, (k % 5).toNat, ?_, ?_⟩
  · have := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 5)
    have := Int.emod_nonneg k (by norm_num : (5 : ℤ) ≠ 0)
    omega
  · congr 1
    have h5 : h ^ (5 : ℤ) = 1 := by rw [zpow_ofNat, hL.pow_five]
    rw [zpow_eq_zpow_emod k h5, ← zpow_natCast, Int.toNat_of_nonneg
      (Int.emod_nonneg k (by norm_num))]

theorem decomp_unique {s s' : L} (hs : s ∈ S₀) (hs' : s' ∈ S₀) {j j' : ℕ} (hj : j < 5)
    (hj' : j' < 5) (heq : s * h ^ j = s' * h ^ j') : s = s' ∧ j = j' := by
  wlog hle : j ≤ j' generalizing s s' j j'
  · obtain ⟨h1, h2⟩ := this hs' hs hj' hj heq.symm (by omega)
    exact ⟨h1.symm, h2.symm⟩
  have hmem : h ^ (j' - j) ∈ S₀ := by
    have hrel : h ^ (j' - j) = s'⁻¹ * s := by
      have hsplit : h ^ j' = h ^ j * h ^ (j' - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hle]
      rw [hsplit, ← mul_assoc] at heq
      have := congrArg (fun x => s'⁻¹ * x * (h ^ j)⁻¹) heq
      simp only [mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left] at this
      rw [← mul_assoc] at this
      exact (by
        have h3 : s'⁻¹ * s = h ^ j * h ^ (j' - j) * (h ^ j)⁻¹ := this
        rw [h3, show h ^ j * h ^ (j' - j) = h ^ (j' - j) * h ^ j by
          rw [← pow_add, ← pow_add, add_comm], mul_inv_cancel_right])
    rw [hrel]
    exact S₀.mul_mem (S₀.inv_mem hs') hs
  have hdvd := (hL.pow_mem_iff (j' - j)).mp hmem
  have hjj : j = j' := by omega
  subst hjj
  exact ⟨mul_right_cancel heq, rfl⟩

theorem center_le_center : (Subgroup.center S₀).map S₀.subtype ≤ Subgroup.center L := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨s, hs, j, -, rfl⟩ := hL.exists_decomp g
  have hxs := (mem_map_center_iff.mp hx).2 s hs
  have hxh : h * x = x * h := by
    have := hL.fixes x hx
    calc h * x = h * x * h⁻¹ * h := by group
      _ = x * h := by rw [this]
  have hxhj : h ^ j * x = x * h ^ j := ((Commute.pow_left hxh j).eq)
  calc s * h ^ j * x = s * (h ^ j * x) := mul_assoc _ _ _
    _ = s * (x * h ^ j) := by rw [hxhj]
    _ = (s * x) * h ^ j := (mul_assoc _ _ _).symm
    _ = x * (s * h ^ j) := by rw [hxs, mul_assoc]

theorem pow_fixes (j : ℕ) (x : L) (hx : x ∈ (Subgroup.center S₀).map S₀.subtype) :
    h ^ j * x * (h ^ j)⁻¹ = x := by
  have hc := Subgroup.mem_center_iff.mp (hL.center_le_center hx) (h ^ j)
  rw [hc, mul_inv_cancel_right]

theorem free_pow {j : ℕ} (hj : ¬ 5 ∣ j) {x : L} (hx : x ∈ S₀)
    (hfix : h ^ j * x * (h ^ j)⁻¹ * x⁻¹ ∈ (Subgroup.center S₀).map S₀.subtype) :
    x ∈ (Subgroup.center S₀).map S₀.subtype := by
  set Z₀ := (Subgroup.center S₀).map S₀.subtype with hZ₀
  set a := h ^ j with ha
  have hiter : ∀ k : ℕ, a ^ k * x * (a ^ k)⁻¹ * x⁻¹ ∈ Z₀ := by
    intro k
    induction k with
    | zero => simp [Z₀.one_mem]
    | succ k ih =>
      set w := a ^ k * x * (a ^ k)⁻¹ * x⁻¹ with hw
      have hwfix : a * w * a⁻¹ = w := hL.pow_fixes j w ih
      have hstep : a ^ (k + 1) * x * (a ^ (k + 1))⁻¹ * x⁻¹ =
          (a * w * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by
        rw [hw, pow_succ']
        group
      rw [hstep, hwfix]
      exact Z₀.mul_mem ih hfix
  obtain ⟨k, hk⟩ : ∃ k : ℕ, j * k % 5 = 1 := by
    have : j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact ⟨1, by omega⟩
    · exact ⟨3, by omega⟩
    · exact ⟨2, by omega⟩
    · exact ⟨4, by omega⟩
  have hak : a ^ k = h := by
    rw [ha, ← pow_mul, hL.pow_mod_five, hk, pow_one]
  have := hiter k
  rw [hak] at this
  exact hL.free x hx this

theorem centralizer_le [Finite L] (g : L) (hg : g ∈ Subgroup.centralizer (S₀ : Set L)) :
    g ∈ (Subgroup.center S₀).map S₀.subtype := by
  obtain ⟨s, hs, j, hj, rfl⟩ := hL.exists_decomp g
  have hcomm : ∀ x ∈ S₀, s * h ^ j * x = x * (s * h ^ j) := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp hg x hx).symm
  by_cases hj0 : j = 0
  · subst hj0
    rw [pow_zero, mul_one] at hcomm ⊢
    exact mem_map_center_iff.mpr ⟨hs, fun t ht => (hcomm t ht).symm⟩
  · exfalso
    have hnd : ¬ 5 ∣ j := fun hd => hj0 (Nat.eq_zero_of_dvd_of_lt hd hj)
    have hall : ∀ x ∈ S₀, x ∈ (Subgroup.center S₀).map S₀.subtype := by
      intro x hx
      apply hL.free_pow hnd hx
      have hconj : h ^ j * x * (h ^ j)⁻¹ = s⁻¹ * x * s := by
        have := hcomm x hx
        calc h ^ j * x * (h ^ j)⁻¹ = s⁻¹ * (s * h ^ j * x) * (h ^ j)⁻¹ := by group
          _ = s⁻¹ * (x * (s * h ^ j)) * (h ^ j)⁻¹ := by rw [this]
          _ = s⁻¹ * x * s := by group
      rw [hconj]
      have := hL.commutator s⁻¹ (S₀.inv_mem hs) x hx
      simpa only [inv_inv] using this
    have hle : S₀ ≤ (Subgroup.center S₀).map S₀.subtype := hall
    have hcard := Subgroup.card_le_of_le hle
    rw [hL.card, Subgroup.card_map_of_injective S₀.subtype_injective, hL.card_center] at hcard
    norm_num at hcard

theorem coefficientBlock_eq_univ [Fintype L]
    (basis : CFSG.TwoRankLowerBound.Helpers.FiniteIrreducibleCharacterBasis L)
    (ideal : Ideal CFSG.TwoRankLowerBound.Helpers.ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (CFSG.TwoRankLowerBound.Helpers.ComplexAlgebraicIntegers ⧸ ideal) 2]
    (label : basis.index) :
    CFSG.TwoRankLowerBound.Helpers.coefficientBlock basis
      (CFSG.TwoRankLowerBound.Helpers.localizedComplexIntegerRing ideal) label = Finset.univ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : S₀.Normal := hL.normal
  refine coefficientBlock_eq_univ_of_centralizer_central basis ideal 2 S₀ hL.two_group
    (fun c hc => ⟨hL.center_le_center (hL.centralizer_le c hc), ?_⟩) label
  have hcZ := hL.centralizer_le c hc
  have hcS : c ∈ S₀ := (mem_map_center_iff.mp hcZ).1
  obtain ⟨k, hk⟩ := hL.two_group ⟨c, hcS⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem card_eq : Nat.card L = 320 := by
  let f : S₀ × Fin 5 → L := fun p => (p.1 : L) * h ^ (p.2 : ℕ)
  have hinj : Function.Injective f := by
    rintro ⟨s, j⟩ ⟨s', j'⟩ heq
    obtain ⟨h1, h2⟩ := hL.decomp_unique s.2 s'.2 j.2 j'.2 heq
    exact Prod.ext (Subtype.ext h1) (Fin.ext h2)
  have hsurj : Function.Surjective f := by
    intro g
    obtain ⟨s, hs, j, hj, rfl⟩ := hL.exists_decomp g
    exact ⟨(⟨s, hs⟩, ⟨j, hj⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, hL.card,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_centralizer_mul_pow {z₀ : L} (hz₀ : z₀ ∈ (Subgroup.center S₀).map S₀.subtype)
    {j : ℕ} (hj : ¬ 5 ∣ j) : Nat.card (Subgroup.centralizer ({z₀ * h ^ j} : Set L)) = 20 := by
  set Z₀ := (Subgroup.center S₀).map S₀.subtype with hZ₀
  have hZ₀S : ∀ x ∈ Z₀, x ∈ S₀ := fun x hx => (mem_map_center_iff.mp hx).1
  let f : Z₀ × Fin 5 → Subgroup.centralizer ({z₀ * h ^ j} : Set L) := fun p =>
    ⟨(p.1 : L) * h ^ (p.2 : ℕ), by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hp := Subgroup.mem_center_iff.mp (hL.center_le_center p.1.2)
      have hz := Subgroup.mem_center_iff.mp (hL.center_le_center hz₀)
      have hhh : h ^ (p.2 : ℕ) * h ^ j = h ^ j * h ^ (p.2 : ℕ) := by
        rw [← pow_add, ← pow_add, add_comm]
      calc (p.1 : L) * h ^ (p.2 : ℕ) * (z₀ * h ^ j)
          = (p.1 : L) * (h ^ (p.2 : ℕ) * z₀) * h ^ j := by simp only [mul_assoc]
        _ = (p.1 : L) * (z₀ * h ^ (p.2 : ℕ)) * h ^ j := by rw [hz]
        _ = ((p.1 : L) * z₀) * (h ^ (p.2 : ℕ) * h ^ j) := by simp only [mul_assoc]
        _ = (z₀ * (p.1 : L)) * (h ^ j * h ^ (p.2 : ℕ)) := by rw [hz, hhh]
        _ = z₀ * ((p.1 : L) * h ^ j) * h ^ (p.2 : ℕ) := by simp only [mul_assoc]
        _ = z₀ * (h ^ j * (p.1 : L)) * h ^ (p.2 : ℕ) := by rw [← hp]
        _ = z₀ * h ^ j * ((p.1 : L) * h ^ (p.2 : ℕ)) := by simp only [mul_assoc]⟩
  have hinj : Function.Injective f := by
    rintro ⟨s, k⟩ ⟨s', k'⟩ heq
    have heq' := congrArg Subtype.val heq
    obtain ⟨h1, h2⟩ := hL.decomp_unique (hZ₀S s s.2) (hZ₀S s' s'.2) k.2 k'.2 heq'
    exact Prod.ext (Subtype.ext h1) (Fin.ext h2)
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨s, hs, k, hk, rfl⟩ := hL.exists_decomp g
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have hz := Subgroup.mem_center_iff.mp (hL.center_le_center hz₀)
    have hsh : s * h ^ j = h ^ j * s := by
      have hhh : h ^ k * h ^ j = h ^ j * h ^ k := by rw [← pow_add, ← pow_add, add_comm]
      have h1 : z₀ * (s * h ^ j * h ^ k) = z₀ * (h ^ j * s * h ^ k) := by
        calc z₀ * (s * h ^ j * h ^ k) = z₀ * (s * (h ^ k * h ^ j)) := by
              rw [hhh]; simp only [mul_assoc]
          _ = (s * h ^ k) * z₀ * h ^ j := by
              rw [← hz (s * (h ^ k * h ^ j)), mul_assoc (s * h ^ k) z₀ (h ^ j), ← hz (h ^ j)]
              simp only [mul_assoc]
          _ = s * h ^ k * (z₀ * h ^ j) := by simp only [mul_assoc]
          _ = z₀ * h ^ j * (s * h ^ k) := hg
          _ = z₀ * (h ^ j * s * h ^ k) := by simp only [mul_assoc]
      have h2 := mul_left_cancel h1
      exact mul_right_cancel h2
    have hsZ : s ∈ Z₀ := by
      apply hL.free_pow hj hs
      have : h ^ j * s * (h ^ j)⁻¹ * s⁻¹ = 1 := by
        rw [← hsh]; group
      rw [this]
      exact Z₀.one_mem
    exact ⟨(⟨s, hsZ⟩, ⟨k, hk⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod,
    hZ₀, Subgroup.card_map_of_injective S₀.subtype_injective, hL.card_center,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem not_isConj {z₀ z₁ : L} (hz₀ : z₀ ∈ (Subgroup.center S₀).map S₀.subtype)
    (hz₁ : z₁ ∈ (Subgroup.center S₀).map S₀.subtype) {j l : ℕ} (hj : j < 5) (hl : l < 5)
    (hjl : j ≠ l) : ¬ IsConj (z₀ * h ^ j) (z₁ * h ^ l) := by
  have : S₀.Normal := hL.normal
  rintro hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  obtain ⟨s, hs, k, -, rfl⟩ := hL.exists_decomp g
  have hz := Subgroup.mem_center_iff.mp (hL.center_le_center hz₀)
  have hz₀S : z₀ ∈ S₀ := (mem_map_center_iff.mp hz₀).1
  have hz₁S : z₁ ∈ S₀ := (mem_map_center_iff.mp hz₁).1
  have hhh : h ^ k * h ^ j = h ^ j * h ^ k := by rw [← pow_add, ← pow_add, add_comm]
  have hform : s * h ^ k * (z₀ * h ^ j) * (s * h ^ k)⁻¹ =
      (z₀ * s * (h ^ j * s⁻¹ * (h ^ j)⁻¹)) * h ^ j := by
    have e1 : s * h ^ k * (z₀ * h ^ j) = z₀ * (s * (h ^ k * h ^ j)) := by
      calc s * h ^ k * (z₀ * h ^ j) = (s * h ^ k * z₀) * h ^ j := by simp only [mul_assoc]
        _ = (z₀ * (s * h ^ k)) * h ^ j := by rw [← hz]
        _ = z₀ * (s * (h ^ k * h ^ j)) := by simp only [mul_assoc]
    rw [e1, hhh, mul_inv_rev]
    simp only [mul_assoc, mul_inv_cancel_left, mul_one, inv_mul_cancel]
  have hmem : z₀ * s * (h ^ j * s⁻¹ * (h ^ j)⁻¹) ∈ S₀ :=
    S₀.mul_mem (S₀.mul_mem hz₀S hs) (hL.normal.conj_mem _ (S₀.inv_mem hs) (h ^ j))
  rw [hform] at hg
  exact hjl (hL.decomp_unique hmem hz₁S hj hl hg).2

end UnitaryFourByFive

end CFSG.LyonsUnitaryFour
