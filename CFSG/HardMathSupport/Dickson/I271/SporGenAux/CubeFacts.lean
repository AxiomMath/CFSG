module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PairConj

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem cube_facts [Finite G] {p : ℕ} [hp : Fact p.Prime] {x y c : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hc : c = x * y * x ^ (p - 1) * y ^ (p - 1))
    (hcx : c * x = x * c) (hcy : c * y = y * c)
    (hinj : ∀ i j k i' j' k' : ℕ, i < p → j < p → k < p → i' < p → j' < p → k' < p →
      x ^ i * y ^ j * c ^ k = x ^ i' * y ^ j' * c ^ k' → i = i' ∧ j = j' ∧ k = k')
    (hfac : (Nat.card G).factorization p = 3)
    (hconj : ∀ i j k : ℕ, i < p → j < p → k < p → i + j + k ≠ 0 →
      ∃ m : G, m * (x ^ i * y ^ j * c ^ k) = c * m) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 3 ∧
      Nat.card (Subgroup.closure ({x, y} : Set G)) =
        p ^ (Nat.card (⊤ : Subgroup G)).factorization p ∧
      c ≠ 1 ∧ c ^ p = 1 ∧ c ∈ Subgroup.closure ({x, y} : Set G) ∧
      (∀ q ∈ Subgroup.closure ({x, y} : Set G), q ^ p = 1) ∧
      ∀ s : G, orderOf s = p → ∃ m : G, m * s * m⁻¹ = c := by
  have hp0 : 0 < p := hp.out.pos
  have hxy : ⁅x, y⁆ = c := by rw [hc, commutatorElement_eq_of_pow hp0 hx hy]
  have hzx : Commute ⁅x, y⁆ x := by rw [hxy]; exact hcx
  have hzy : Commute ⁅x, y⁆ y := by rw [hxy]; exact hcy
  have hQ : Nat.card (Subgroup.closure ({x, y} : Set G)) = p ^ 3 := by
    refine CFSG.SectionRank.LocalWitness.card_closure_eq_cube hp0 hx hy hzx hzy ?_
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
    simp only [hxy] at h
    obtain ⟨h1, h2, h3⟩ := hinj i j k i' j' k' i.2 j.2 k.2 i'.2 j'.2 k'.2 h
    exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))
  have hQfull : Nat.card (Subgroup.closure ({x, y} : Set G)) =
      p ^ (Nat.card (⊤ : Subgroup G)).factorization p := by
    rw [hQ, Subgroup.card_top, hfac]
  have hcp : c ^ p = 1 := by
    rw [← hxy, CFSG.SectionRank.LocalWitness.commutator_pow_eq hzx, hx,
      commutatorElement_one_left]
  have hc1 : c ≠ 1 := by
    intro h1
    have := hinj 0 0 1 0 0 0 hp0 hp0 hp.out.one_lt hp0 hp0 hp0 (by simp [h1])
    exact absurd this.2.2 (by norm_num)
  have hxQ : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hcQ : c ∈ Subgroup.closure ({x, y} : Set G) := by
    rw [hc]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxQ hyQ)
      (Subgroup.pow_mem _ hxQ _)) (Subgroup.pow_mem _ hyQ _)
  have hconjpow : ∀ (m q : G), m * q = c * m → q ^ p = 1 := by
    intro m q hm
    have hq : q = m⁻¹ * c * (m⁻¹)⁻¹ := by
      rw [inv_inv, mul_assoc, ← hm]; group
    rw [hq, conj_pow, hcp]
    group
  refine ⟨hQ, hQfull, hc1, hcp, hcQ, fun q hq => ?_, fun s hs => ?_⟩
  · obtain ⟨i, j, k, hi, hj, hk, hw⟩ :=
      CFSG.SectionRank.LocalWitness.mem_closure_normalForm hp0 hx hy hzx hzy hq
    rw [hxy] at hw
    by_cases h0 : i + j + k = 0
    · have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      have hk0 : k = 0 := by omega
      rw [hw, hi0, hj0, hk0]
      simp
    · obtain ⟨m, hm⟩ := hconj i j k hi hj hk h0
      rw [← hw] at hm
      exact hconjpow m q hm
  · obtain ⟨g, -, hgQ⟩ := Co3T.exists_conj_mem_of_full le_top hQfull (Subgroup.mem_top s) hs
    obtain ⟨i, j, k, hi, hj, hk, hw⟩ :=
      CFSG.SectionRank.LocalWitness.mem_closure_normalForm hp0 hx hy hzx hzy hgQ
    rw [hxy] at hw
    have hwo : orderOf (g⁻¹ * s * g) = p := by rw [orderOf_inv_mul_mul, hs]
    have hijk : i + j + k ≠ 0 := by
      intro h0
      have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      have hk0 : k = 0 := by omega
      rw [hi0, hj0, hk0, pow_zero, pow_zero, pow_zero, mul_one, mul_one] at hw
      rw [hw, orderOf_one] at hwo
      exact hp.out.one_lt.ne hwo
    obtain ⟨m, hm⟩ := hconj i j k hi hj hk hijk
    refine ⟨m * g⁻¹, ?_⟩
    rw [← hw] at hm
    calc (m * g⁻¹) * s * (m * g⁻¹)⁻¹ = (m * (g⁻¹ * s * g)) * m⁻¹ := by group
      _ = c := by rw [hm]; group

theorem conj_mem_closure_pair {x y h : G} (hx : h * x * h⁻¹ ∈ Subgroup.closure ({x, y} : Set G))
    (hy : h * y * h⁻¹ ∈ Subgroup.closure ({x, y} : Set G)) :
    ∀ q ∈ Subgroup.closure ({x, y} : Set G), h * q * h⁻¹ ∈ Subgroup.closure ({x, y} : Set G) := by
  intro q hq
  induction hq using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  | one => simp
  | mul a b _ _ ha hb =>
    have : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem list_prod_conj_mem {Q : Subgroup G} {l : List G}
    (hl : ∀ h ∈ l, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) : ∀ q ∈ Q, l.prod * q * l.prod⁻¹ ∈ Q := by
  induction l with
  | nil => intro q hq; simpa using hq
  | cons h l ih =>
    intro q hq
    have h1 := ih (fun h' hh' => hl h' (List.mem_cons_of_mem _ hh')) q hq
    have h2 := hl h List.mem_cons_self _ h1
    have : (h :: l).prod * q * (h :: l).prod⁻¹ = h * (l.prod * q * l.prod⁻¹) * h⁻¹ := by
      rw [List.prod_cons]; group
    rw [this]
    exact h2

end CFSG.HardMathSupport.Dickson.I271
