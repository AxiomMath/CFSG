module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5CentInv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem coord_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd (1 : ZMod 2) := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]

private theorem sigma_ne_one : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide

private theorem sigma_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by decide

private def swapW : A5WrTwo := ⟨1, Multiplicative.ofAdd (1 : ZMod 2)⟩

private theorem swapW_right : swapW.right = Multiplicative.ofAdd (1 : ZMod 2) := rfl

private theorem baseEmb_right (p q : alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb (p, q)).right = 1 := by
  have hmem : A5WrTwo.baseEmb (p, q) ∈
      (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)).ker := by
    rw [← A5WrTwo.commutator_eq_ker, ← A5WrTwo.range_baseEmb]
    exact MonoidHom.mem_range.mpr ⟨(p, q), rfl⟩
  exact hmem

private theorem swapW_sq : swapW * swapW = 1 := by
  apply RegularWreathProduct.ext
  · funext i
    simp [swapW, RegularWreathProduct.mul_def, sigma_mul_self]
  · simp [swapW, RegularWreathProduct.mul_def, sigma_mul_self]

private theorem swapW_mul_baseEmb_mul_inv (x y : alternatingGroup (Fin 5)) :
    swapW * A5WrTwo.baseEmb (x, y) * swapW⁻¹ = A5WrTwo.baseEmb (y, x) :=
  A5WrTwo.swap_mul_baseEmb_mul_inv x y

private theorem not_mem_commutator_of_right_eq_sigma {g : A5WrTwo}
    (hg : g.right = Multiplicative.ofAdd (1 : ZMod 2)) : g ∉ commutator A5WrTwo := by
  intro h
  rw [A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker] at h
  have h1 : g.right = 1 := h
  rw [hg] at h1
  exact sigma_ne_one h1

private theorem baseEmb_mul_swapW_mul_baseEmb_mul_swapW
    (x y x' y' : alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb (x, y) * swapW) * (A5WrTwo.baseEmb (x', y') * swapW)
      = A5WrTwo.baseEmb (x * y', y * x') := by
  calc (A5WrTwo.baseEmb (x, y) * swapW) * (A5WrTwo.baseEmb (x', y') * swapW)
      = A5WrTwo.baseEmb (x, y) * (swapW * A5WrTwo.baseEmb (x', y') * swapW⁻¹) *
          (swapW * swapW) := by group
    _ = A5WrTwo.baseEmb (x, y) * A5WrTwo.baseEmb (y', x') * 1 := by
          rw [swapW_mul_baseEmb_mul_inv, swapW_sq]
    _ = A5WrTwo.baseEmb (x * y', y * x') := by
          rw [mul_one, ← A5WrTwo.baseEmb.map_mul, Prod.mk_mul_mk]

private theorem baseEmb_mul_swapW_sq (x y : alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb (x, y) * swapW) ^ 2 = A5WrTwo.baseEmb (x * y, y * x) := by
  rw [pow_two, baseEmb_mul_swapW_mul_baseEmb_mul_swapW]

private theorem baseEmb_pair_pow (a b : alternatingGroup (Fin 5)) (n : ℕ) :
    (A5WrTwo.baseEmb (a, b)) ^ n = A5WrTwo.baseEmb (a ^ n, b ^ n) := by
  rw [← A5WrTwo.baseEmb.map_pow,
    show (a, b) ^ n = (a ^ n, b ^ n) from
      Prod.ext (map_pow (MonoidHom.fst _ _) (a, b) n)
        (map_pow (MonoidHom.snd _ _) (a, b) n)]

private theorem a5_exists_cube_eq_one :
    ∃ c : alternatingGroup (Fin 5), c ^ 3 = 1 ∧ c ≠ 1 := by
  decide +kernel

private theorem a5_exists_conj_mul_cube :
    ∀ x y : alternatingGroup (Fin 5), x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 → y ≠ 1 →
      ∃ k : alternatingGroup (Fin 5),
        (x * (k * y * k⁻¹)) ^ 3 = 1 ∧ x * (k * y * k⁻¹) ≠ 1 := by
  decide +kernel

private theorem natCard_A5WrTwo : Nat.card A5WrTwo = 7200 := by
  have hD : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hQ : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod]
  rw [RegularWreathProduct.card, hD, hQ]
  norm_num

private theorem exists_outer_of_outer {u : A5WrTwo} (hu2 : u ^ 2 = 1)
    (hu : u ∉ commutator A5WrTwo) :
    ∃ v : A5WrTwo, v ^ 2 = 1 ∧ v ∉ commutator A5WrTwo ∧
      ∀ k : ℕ, orderOf (u * v) ≠ 2 ^ k := by
  have hu_right_ne : u.right ≠ 1 := by
    intro h1
    exact hu (by rw [A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker]; exact h1)
  have hu_right : u.right = Multiplicative.ofAdd (1 : ZMod 2) := by
    rcases coord_cases u.right with h | h
    · exact absurd h hu_right_ne
    · exact h
  obtain ⟨⟨p, q⟩, hpq_eq⟩ : ∃ pq : alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      A5WrTwo.baseEmb pq = u * swapW⁻¹ := by
    refine MonoidHom.mem_range.mp ?_
    rw [A5WrTwo.range_baseEmb, A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker]
    change (u * swapW⁻¹).right = 1
    rw [RegularWreathProduct.mul_right, RegularWreathProduct.inv_right, hu_right, swapW_right,
      mul_inv_cancel]
  have hu_eq : u = A5WrTwo.baseEmb (p, q) * swapW := by
    rw [hpq_eq]
    group
  have hsq : A5WrTwo.baseEmb (p * q, q * p) = 1 := by
    have h := hu2
    rw [hu_eq, baseEmb_mul_swapW_sq] at h
    exact h
  have hpq : (p * q, q * p) = 1 :=
    A5WrTwo.baseEmb_injective (by rw [hsq]; exact (A5WrTwo.baseEmb.map_one).symm)
  have hqp : q * p = 1 := congrArg Prod.snd hpq
  obtain ⟨c, hc3, hc1⟩ := a5_exists_cube_eq_one
  let k : alternatingGroup (Fin 5) := c⁻¹ * p
  let v : A5WrTwo := A5WrTwo.baseEmb (k, k⁻¹) * swapW
  refine ⟨v, ?_, ?_, ?_⟩
  · show v ^ 2 = 1
    dsimp only [v]
    rw [baseEmb_mul_swapW_sq, mul_inv_cancel, inv_mul_cancel]
    exact A5WrTwo.baseEmb.map_one
  · apply not_mem_commutator_of_right_eq_sigma
    show v.right = Multiplicative.ofAdd (1 : ZMod 2)
    dsimp only [v]
    rw [RegularWreathProduct.mul_right, swapW_right, baseEmb_right, one_mul]
  · intro m hm
    have huv : u * v = A5WrTwo.baseEmb (c, q * k) := by
      dsimp only [v]
      rw [hu_eq, baseEmb_mul_swapW_mul_baseEmb_mul_swapW]
      rw [show p * k⁻¹ = c from by
        dsimp only [k]
        rw [mul_inv_rev, inv_inv]
        group]
    have hqk3 : (q * k) ^ 3 = 1 := by
      have hp_eq : p = q⁻¹ := eq_inv_of_mul_eq_one_right hqp
      have hqk : q * k = q * c⁻¹ * q⁻¹ := by
        dsimp only [k]
        rw [hp_eq]
        group
      rw [hqk]
      have hcinv3 : (c⁻¹) ^ 3 = 1 := by rw [inv_pow, hc3, inv_one]
      rw [conj_pow, hcinv3, mul_one, mul_inv_cancel]
    have huv3 : (u * v) ^ 3 = 1 := by
      rw [huv, baseEmb_pair_pow c (q * k) 3, hc3, hqk3]
      exact A5WrTwo.baseEmb.map_one
    have huv_ne : u * v ≠ 1 := by
      rw [huv]
      intro h
      have h' : (c, q * k) = 1 :=
        A5WrTwo.baseEmb_injective (by rw [h]; exact (A5WrTwo.baseEmb.map_one).symm)
      exact hc1 (congrArg Prod.fst h')
    have horder : orderOf (u * v) = 3 :=
      orderOf_eq_prime (p := 3) (hp := ⟨by norm_num⟩) huv3 huv_ne
    have hdvd : (3 : ℕ) ∣ orderOf (u * v) := by rw [horder]
    rw [hm] at hdvd
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at h32

private theorem exists_outer_of_inner_card32 {u : A5WrTwo} (hu2 : u ^ 2 = 1)
    (hin : u ∈ commutator A5WrTwo)
    (hcard : Nat.card ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) = 32) :
    ∃ v : A5WrTwo, v ^ 2 = 1 ∧ v ∉ commutator A5WrTwo ∧
      ∀ k : ℕ, orderOf (u * v) ≠ 2 ^ k := by
  have hu1 : u ≠ 1 := by
    intro h1
    have htop : Subgroup.centralizer ({(1 : A5WrTwo)} : Set A5WrTwo) = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      simp
    rw [h1, htop, Subgroup.card_top, natCard_A5WrTwo] at hcard
    norm_num at hcard
  rcases baseInvolution_cases hin hu2 hu1 with
    ⟨x, hx2, hx1, -, hc240⟩ | ⟨x, y, hx2, hy2, hx1, hy1, huy, _⟩
  · exfalso
    rw [hc240] at hcard
    norm_num at hcard
  · subst huy
    obtain ⟨k, hP3, hP1⟩ := a5_exists_conj_mul_cube x y hx2 hy2 hx1 hy1
    let P : alternatingGroup (Fin 5) := x * (k * y * k⁻¹)
    let v : A5WrTwo := A5WrTwo.baseEmb (k, k⁻¹) * swapW
    refine ⟨v, ?_, ?_, ?_⟩
    · show v ^ 2 = 1
      dsimp only [v]
      rw [baseEmb_mul_swapW_sq, mul_inv_cancel, inv_mul_cancel]
      exact A5WrTwo.baseEmb.map_one
    · apply not_mem_commutator_of_right_eq_sigma
      show v.right = Multiplicative.ofAdd (1 : ZMod 2)
      dsimp only [v]
      rw [RegularWreathProduct.mul_right, swapW_right, baseEmb_right, one_mul]
    · intro m hm
      have huv : A5WrTwo.baseEmb (x, y) * v
          = A5WrTwo.baseEmb (x * k, y * k⁻¹) * swapW := by
        dsimp only [v]
        rw [← mul_assoc, ← A5WrTwo.baseEmb.map_mul]
        rfl
      have huv2 : (A5WrTwo.baseEmb (x, y) * v) ^ 2
          = A5WrTwo.baseEmb (P, (x * k)⁻¹ * P * (x * k)) := by
        rw [huv, baseEmb_mul_swapW_sq]
        have h1 : x * k * (y * k⁻¹) = P := by
          dsimp only [P]; group
        have h2 : y * k⁻¹ * (x * k) = (x * k)⁻¹ * P * (x * k) := by
          dsimp only [P]; group
        rw [h1, h2]
      have hsq3 : ((A5WrTwo.baseEmb (x, y) * v) ^ 2) ^ 3 = 1 := by
        rw [huv2, baseEmb_pair_pow P ((x * k)⁻¹ * P * (x * k)) 3]
        have hconj : ((x * k)⁻¹ * P * (x * k)) ^ 3 = 1 := by
          have h := conj_pow (a := (x * k)⁻¹) (b := P) (i := 3)
          rw [inv_inv] at h
          rw [h, hP3, mul_one, inv_mul_cancel]
        rw [hP3, hconj]
        exact A5WrTwo.baseEmb.map_one
      have hsq_ne : (A5WrTwo.baseEmb (x, y) * v) ^ 2 ≠ 1 := by
        rw [huv2]
        intro h
        have h' : (P, (x * k)⁻¹ * P * (x * k)) = 1 :=
          A5WrTwo.baseEmb_injective (by rw [h]; exact (A5WrTwo.baseEmb.map_one).symm)
        exact hP1 (congrArg Prod.fst h')
      have horder : orderOf ((A5WrTwo.baseEmb (x, y) * v) ^ 2) = 3 :=
        orderOf_eq_prime (p := 3) (hp := ⟨by norm_num⟩) hsq3 hsq_ne
      have hdvd : (3 : ℕ) ∣ orderOf (A5WrTwo.baseEmb (x, y) * v) := by
        rw [← horder]
        exact orderOf_pow_dvd (n := 2)
      rw [hm] at hdvd
      have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      norm_num at h32

theorem exists_outer_involution_mul {u : A5WrTwo} (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
    (h : u ∉ commutator A5WrTwo ∨
      Nat.card ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) = 32) :
    ∃ v : A5WrTwo, v ^ 2 = 1 ∧ v ∉ commutator A5WrTwo ∧ ∀ k : ℕ, orderOf (u * v) ≠ 2 ^ k := by
  by_cases hin : u ∈ commutator A5WrTwo
  · exact exists_outer_of_inner_card32 hu2 hin (h.resolve_left (fun hout => hout hin))
  · exact exists_outer_of_outer hu2 hin

end CFSG.EvenSporadicStandard.HNRecog.Section3
