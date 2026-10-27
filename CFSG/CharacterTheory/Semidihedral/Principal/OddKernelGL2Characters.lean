module

public import CFSG.CharacterTheory.Semidihedral.Principal.GL2ThreeCharacterTable
public import CFSG.CharacterTheory.Semidihedral.Principal.SevenIrreducibles
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionInductionIsometry
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCentralTransferKernel

public section

namespace CFSG.Semidihedral.Principal

namespace GL2OddKernel

open CFSG.TwoRankLowerBound.Helpers GL2ThreeCharacters
open CFSG.Semidihedral.FourPointMatrices (normalUnit normalUnit_surjective)

@[expose] def rep (a p b : G23) : Fin 8 → G23 := ![1, -1, a ^ 2, p, -1 * p, b, a, a⁻¹]

@[expose] def charTable (ω : ℂ) : Fin 8 → Fin 8 → ℂ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, -1, -1, -1],
    ![2, 2, 2, -1, -1, 0, 0, 0], ![3, 3, -1, 0, 0, -1, 1, 1], ![3, 3, -1, 0, 0, 1, -1, -1],
    ![4, -4, 0, 1, -1, 0, 0, 0], ![2, -2, 0, -1, 1, 0, ω, -ω], ![2, -2, 0, -1, 1, 0, -ω, ω]]

theorem charTable_eq (ω : ℂ) (i j : Fin 8) :
    charTable ω i j = (tableA i j : ℂ) + (tableB i j : ℂ) * ω := by
  fin_cases i <;> fin_cases j <;> simp [charTable, tableA, tableB]

theorem exp_eq_xi : Complex.exp (2 * Real.pi * Complex.I / 8) = xi := by
  simp only [xi, cyclicRoot]
  norm_num

theorem rep_facts {a p b : G23} (ha : orderOf a = 8) (hp : orderOf p = 3) (hb : orderOf b = 2)
    (hbz : b ∉ Subgroup.center G23) :
    (∀ h : G23, ∃ k, IsConj (rep a p b k) h) ∧
    (∀ k l, IsConj (rep a p b k) (rep a p b l) → k = l) ∧
    (∀ k, Nat.card {h : G23 // IsConj (rep a p b k) h} = classSize k) := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G23)
  have h := GL2_three_ordinary_character_table_construction basis a p b ha hp hb hbz
  obtain ⟨-, hcover, hdisj, hsize, -⟩ := h
  exact ⟨hcover, hdisj, hsize⟩

theorem sum_rep {a p b : G23} (ha : orderOf a = 8) (hp : orderOf p = 3) (hb : orderOf b = 2)
    (hbz : b ∉ Subgroup.center G23) (f : G23 → ℂ) (hf : ∀ c g : G23, f (c * g * c⁻¹) = f g) :
    ∑ h : G23, f h = ∑ k : Fin 8, (classSize k : ℂ) * f (rep a p b k) := by
  classical
  obtain ⟨hcover, hdisj, hsize⟩ := rep_facts ha hp hb hbz
  choose cls hcls using hcover
  have hf' : ∀ h, f h = f (rep a p b (cls h)) := by
    intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp (hcls h)
    have e := hf c (rep a p b (cls h))
    rw [hc] at e
    exact e
  rw [Finset.sum_congr rfl fun h _ => hf' h,
    ← Finset.sum_fiberwise' Finset.univ cls (fun k => f (rep a p b k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (Finset.univ.filter fun h => cls h = k).card =
      Nat.card {h : G23 // IsConj (rep a p b k) h} := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun h =>
      ⟨fun hh => hh ▸ hcls h, fun hh => hdisj _ _ ((hcls h).trans hh.symm)⟩)
  have e' : ((Finset.univ.filter fun h => cls h = k).card : ℂ) = classSize k := by
    exact_mod_cast e.trans (hsize k)
  rw [Finset.sum_const, nsmul_eq_mul, e']

theorem blocksIrr_conj {X : Type} [Group X] {χ : X → ℂ} (hχ : χ ∈ CFSG.BlocksIrr X)
    (c g : X) : χ (c * g * c⁻¹) = χ g := by
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hχ
  exact Representation.char_conj ρ g c

@[expose] def bigPhi (φ : Fin 8 → G23 → ℂ) : Fin 5 → G23 → ℂ :=
  ![φ 0 + φ 2 - φ 4, φ 2 - φ 6, φ 6 - φ 7, φ 1 + φ 4 - φ 5, φ 1 + φ 2 - φ 3]

@[expose] def phiA : Fin 5 → Fin 8 → ℤ :=
  ![![0, 0, 4, 0, 0, 0, 2, 2], ![0, 4, 2, 0, -2, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 8, 0, 0, 2, 0, -2, -2], ![0, 0, 4, 0, 0, 0, -2, -2]]

@[expose] def phiB : Fin 5 → Fin 8 → ℤ :=
  ![0, ![0, 0, 0, 0, 0, 0, -1, 1], ![0, 0, 0, 0, 0, 0, 2, -2], 0, 0]

theorem bigPhi_rep {a p b : G23} {φ : Fin 8 → G23 → ℂ}
    (hφ : ∀ i j, φ i (rep a p b j) = (tableA i j : ℂ) + (tableB i j : ℂ) * omega8)
    (i : Fin 5) (k : Fin 8) :
    bigPhi φ i (rep a p b k) = (phiA i k : ℂ) + (phiB i k : ℂ) * omega8 := by
  fin_cases i <;> fin_cases k <;>
    simp [bigPhi, phiA, phiB, hφ, tableA, tableB] <;> ring

theorem omega8_conj : starRingEnd ℂ omega8 = -omega8 := by
  have hxi : starRingEnd ℂ xi = -xi ^ 3 := by
    rw [cyclicRoot_conj]
    have h : xi * xi ^ 7 = 1 := by rw [← pow_succ', xi_pow_eight]
    rw [inv_eq_of_mul_eq_one_right h, xi_pow_seven]
  have h9 : xi ^ 9 = xi := by rw [xi_pow_sub 9 (by norm_num)]; norm_num
  show starRingEnd ℂ (xi + xi ^ 3) = -(xi + xi ^ 3)
  rw [map_add, map_pow, hxi, show (-xi ^ 3) ^ 3 = -(xi ^ 9) by ring, h9]
  ring

theorem conj_int_add_mul_omega8 (A B : ℤ) :
    starRingEnd ℂ ((A : ℂ) + (B : ℂ) * omega8) = (A : ℂ) - (B : ℂ) * omega8 := by
  rw [map_add, map_mul, map_intCast, map_intCast, omega8_conj]
  ring

theorem sum_classSize_mul_conj_pair (A B A' B' : Fin 8 → ℤ) :
    ∑ k : Fin 8, (classSize k : ℂ) * (((A k : ℂ) + B k * omega8) *
      starRingEnd ℂ ((A' k : ℂ) + B' k * omega8)) =
      ((∑ k, (classSize k : ℤ) * (A k * A' k + 2 * B k * B' k) : ℤ) : ℂ) +
        ((∑ k, (classSize k : ℤ) * (B k * A' k - A k * B' k) : ℤ) : ℂ) * omega8 := by
  simp only [conj_int_add_mul_omega8]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination (-(classSize k : ℂ) * B k * B' k) * omega8_sq

@[expose] def gram : Fin 5 → Fin 5 → ℤ :=
  ![![3, 1, 0, -1, 1], ![1, 2, -1, 0, 1], ![0, -1, 2, 0, 0], ![-1, 0, 0, 3, 1],
    ![1, 1, 0, 1, 3]]

theorem gram_rational : ∀ i j : Fin 5,
    ∑ k, (classSize k : ℤ) * (phiA i k * phiA j k + 2 * phiB i k * phiB j k) = 48 * gram i j := by
  decide

theorem gram_omega : ∀ i j : Fin 5,
    ∑ k, (classSize k : ℤ) * (phiB i k * phiA j k - phiA i k * phiB j k) = 0 := by
  decide

theorem principal_rational : ∀ i : Fin 5,
    ∑ k, (classSize k : ℤ) * phiA i k = 48 * ![1, 0, 0, 0, 0] i := by
  decide

theorem principal_omega : ∀ i : Fin 5, ∑ k, (classSize k : ℤ) * phiB i k = 0 := by
  decide

theorem bigPhi_conj {φ : Fin 8 → G23 → ℂ} (hφirr : ∀ i, φ i ∈ CFSG.BlocksIrr G23) (i : Fin 5)
    (c g : G23) : bigPhi φ i (c * g * c⁻¹) = bigPhi φ i g := by
  fin_cases i <;> simp [bigPhi, blocksIrr_conj (hφirr _)]

theorem inner_bigPhi {a p b : G23} (ha : orderOf a = 8) (hp : orderOf p = 3) (hb : orderOf b = 2)
    (hbz : b ∉ Subgroup.center G23) {φ : Fin 8 → G23 → ℂ}
    (hφirr : ∀ i, φ i ∈ CFSG.BlocksIrr G23)
    (hφ : ∀ i j, φ i (rep a p b j) = (tableA i j : ℂ) + (tableB i j : ℂ) * omega8)
    (i j : Fin 5) : BlocksInnerProduct (bigPhi φ i) (bigPhi φ j) = gram i j := by
  unfold BlocksInnerProduct
  rw [sum_rep ha hp hb hbz (fun h => bigPhi φ i h * starRingEnd ℂ (bigPhi φ j h))
    (fun c g => by simp only [bigPhi_conj hφirr])]
  simp only [bigPhi_rep hφ]
  rw [sum_classSize_mul_conj_pair, gram_rational, gram_omega, card_G23]
  push_cast
  ring

theorem inner_bigPhi_one {a p b : G23} (ha : orderOf a = 8) (hp : orderOf p = 3)
    (hb : orderOf b = 2) (hbz : b ∉ Subgroup.center G23) {φ : Fin 8 → G23 → ℂ}
    (hφirr : ∀ i, φ i ∈ CFSG.BlocksIrr G23)
    (hφ : ∀ i j, φ i (rep a p b j) = (tableA i j : ℂ) + (tableB i j : ℂ) * omega8)
    (i : Fin 5) : BlocksInnerProduct (bigPhi φ i) 1 = (![1, 0, 0, 0, 0] i : ℤ) := by
  unfold BlocksInnerProduct
  rw [sum_rep ha hp hb hbz (fun h => bigPhi φ i h * starRingEnd ℂ ((1 : G23 → ℂ) h))
    (fun c g => by simp only [bigPhi_conj hφirr, Pi.one_apply])]
  simp only [bigPhi_rep hφ, Pi.one_apply, map_one, mul_one]
  have h := principal_rational i
  have h' := principal_omega i
  have hsum : ∑ k : Fin 8, (classSize k : ℂ) * ((phiA i k : ℂ) + (phiB i k : ℂ) * omega8) =
      ((∑ k, (classSize k : ℤ) * phiA i k : ℤ) : ℂ) +
        ((∑ k, (classSize k : ℤ) * phiB i k : ℤ) : ℂ) * omega8 := by
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsum, h, h', card_G23]
  push_cast
  ring

theorem bigPhi_rep_zero {a p b : G23} {φ : Fin 8 → G23 → ℂ}
    (hφ : ∀ i j, φ i (rep a p b j) = (tableA i j : ℂ) + (tableB i j : ℂ) * omega8)
    (i : Fin 5) (k : Fin 8) (hk : k = 0 ∨ k = 3 ∨ k = 5) : bigPhi φ i (rep a p b k) = 0 := by
  rw [bigPhi_rep hφ]
  rcases hk with rfl | rfl | rfl <;> fin_cases i <;> simp [phiA, phiB]

theorem bigPhi_one {a p b : G23} {φ : Fin 8 → G23 → ℂ}
    (hφ : ∀ i j, φ i (rep a p b j) = (tableA i j : ℂ) + (tableB i j : ℂ) * omega8)
    (i : Fin 5) : bigPhi φ i 1 = 0 :=
  bigPhi_rep_zero hφ i 0 (Or.inl rfl)

theorem span_relations (y : Fin 8 → ℂ)
    (h : ∀ i : Fin 5, ∑ k, ((phiA i k : ℂ) + (phiB i k : ℂ) * omega8) * y k = 0) :
    y 1 = 0 ∧ y 2 = 0 ∧ y 4 = 0 ∧ y 6 = 0 ∧ y 7 = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  simp [Fin.sum_univ_eight, phiA, phiB] at h0 h1 h2 h3 h4
  have hy2 : y 2 = 0 := by linear_combination (h0 + h4) / 8
  have hsum : y 6 + y 7 = 0 := by linear_combination (h0 - h4) / 4
  have hdiff : y 6 - y 7 = 0 := by
    linear_combination (-omega8 / 4) * h2 + ((y 6 - y 7) / 2) * omega8_sq
  have hy6 : y 6 = 0 := by linear_combination (hsum + hdiff) / 2
  have hy7 : y 7 = 0 := by linear_combination (hsum - hdiff) / 2
  have hy1 : y 1 = 0 := by
    linear_combination (h1 + h3 - 2 * hy2 + omega8 * hdiff + 2 * hsum) / 12
  have hy4 : y 4 = 0 := by linear_combination (h3 - 8 * hy1 + 2 * hsum) / 2
  exact ⟨hy1, hy2, hy4, hy6, hy7⟩

section Inflation

open scoped Classical

variable {G : Type} [Group G] [Fintype G] {t : G}
  (π : Subgroup.centralizer ({t} : Set G) →* G23) (hπ : Function.Surjective π)
include hπ

omit [Fintype G] in
theorem card_centralizer_eq : Nat.card (Subgroup.centralizer ({t} : Set G)) =
    Nat.card π.ker * Nat.card G23 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker, mul_comm,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]

theorem sum_fiber_eq (h : G23) (g : Subgroup.centralizer ({t} : Set G) → ℂ) :
    ∑ x ∈ Finset.univ.filter (fun x : Subgroup.centralizer ({t} : Set G) => π x = h), g x =
      ∑ n : π.ker, g (Function.surjInv hπ h * n) := by
  symm
  apply Finset.sum_nbij
    (fun n : π.ker => Function.surjInv hπ h * (n : Subgroup.centralizer ({t} : Set G)))
  · intro n _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [map_mul, Function.surjInv_eq hπ h, MonoidHom.mem_ker.mp n.2, mul_one]
  · intro n _ m _ hnm
    exact Subtype.ext (mul_left_cancel hnm)
  · intro x hx
    have hxh := (Finset.mem_filter.mp hx).2
    have hmem : (Function.surjInv hπ h)⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxh, Function.surjInv_eq hπ h, inv_mul_cancel]
    refine ⟨⟨_, hmem⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
    show Function.surjInv hπ h * ((Function.surjInv hπ h)⁻¹ * x) = x
    group
  · intro n _
    rfl

theorem card_fiber (h : G23) :
    ((Finset.univ.filter fun x : Subgroup.centralizer ({t} : Set G) => π x = h).card : ℂ) =
      Nat.card π.ker := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  have e := sum_fiber_eq π hπ h (fun _ => (1 : ℂ))
  simp only [Nat.cast_one] at e ⊢
  rw [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]

theorem sum_comp (F : G23 → ℂ) :
    ∑ x : Subgroup.centralizer ({t} : Set G), F (π x) =
      (Nat.card π.ker : ℂ) * ∑ h : G23, F h := by
  rw [← Finset.sum_fiberwise' Finset.univ π F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, card_fiber π hπ h, mul_comm]

theorem blocksInnerProduct_inflate (f g : G23 → ℂ) :
    BlocksInnerProduct (fun x : Subgroup.centralizer ({t} : Set G) => f (π x))
      (fun x => g (π x)) = BlocksInnerProduct f g := by
  unfold BlocksInnerProduct
  rw [sum_comp π hπ (fun h => f h * starRingEnd ℂ (g h)), card_centralizer_eq π hπ,
    Nat.cast_mul]
  have hN : (Nat.card π.ker : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  generalize (Nat.card π.ker : ℂ) = A at hN ⊢
  generalize (Nat.card G23 : ℂ) = B
  generalize ∑ h : G23, f h * starRingEnd ℂ (g h) = S
  field_simp

theorem sum_fiber (F : G23 → ℂ) (g : Subgroup.centralizer ({t} : Set G) → ℂ) :
    ∑ x : Subgroup.centralizer ({t} : Set G), F (π x) * g x =
      ∑ h : G23, F h * ∑ n : π.ker, g (Function.surjInv hπ h * n) := by
  rw [← Finset.sum_fiberwise Finset.univ π (fun x => F (π x) * g x)]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hfib : ∀ x ∈ Finset.univ.filter (fun x => π x = h), F (π x) * g x = F h * g x := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl hfib, ← Finset.mul_sum, sum_fiber_eq π hπ h g]

end Inflation

theorem fin8_cases (k : Fin 8) :
    (k = 0 ∨ k = 3 ∨ k = 5) ∨ (k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 7) := by
  revert k
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem pow_four_coord : ∀ i : Coord,
    GL2ThreeStructure.coordinateOrder i = 8 → normalUnit i ^ 4 = -1 := by
  decide

theorem pow_four_of_orderOf_eight {g : G23} (hg : orderOf g = 8) : g ^ 4 = -1 := by
  obtain ⟨i, rfl⟩ := normalUnit_surjective g
  rw [GL2ThreeStructure.normalUnit_order] at hg
  exact pow_four_coord i hg

theorem neg_one_mul_comm (x : G23) : x * -1 = -1 * x := by rw [mul_neg_one, neg_one_mul]

theorem orderOf_neg_one : orderOf (-1 : G23) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

theorem pow_half_eq_neg_one {h : G23} (hz : (-1 : G23) ∈ Subgroup.zpowers h) :
    2 ∣ orderOf h ∧ h ^ (orderOf h / 2) = -1 := by
  have h2 : 2 ∣ orderOf h := by
    have := orderOf_dvd_of_mem_zpowers hz
    rwa [orderOf_neg_one] at this
  refine ⟨h2, ?_⟩
  have hx : h ^ (orderOf h / 2) ∈ Subgroup.zpowers h := Subgroup.npow_mem_zpowers h _
  have hord : orderOf (h ^ (orderOf h / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos h).ne' h2
  have e := eq_of_orderOf_eq_two_of_isCyclic (G := Subgroup.zpowers h)
    (a := ⟨_, hx⟩) (b := ⟨-1, hz⟩) (by rw [Subgroup.orderOf_mk, hord])
    (by rw [Subgroup.orderOf_mk, orderOf_neg_one])
  exact congrArg Subtype.val e

theorem neg_one_mem_zpowers_conj {r h : G23} (hrh : IsConj r h)
    (hr : (-1 : G23) ∈ Subgroup.zpowers r) : (-1 : G23) ∈ Subgroup.zpowers h := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hrh
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hr
  refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
  rw [conj_zpow, hm, neg_one_mul_comm, mul_inv_cancel_right]

theorem neg_one_mem_zpowers_rep {a p b : G23} (ha : orderOf a = 8) (hp : orderOf p = 3)
    (k : Fin 8) (hk : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 7) :
    (-1 : G23) ∈ Subgroup.zpowers (rep a p b k) := by
  have ha4 := pow_four_of_orderOf_eight ha
  have hp3 : p ^ 3 = 1 := by
    have h := pow_orderOf_eq_one p
    rwa [hp] at h
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.mem_zpowers _
  · refine Subgroup.mem_zpowers_iff.mpr ⟨2, ?_⟩
    show (a ^ 2) ^ (2 : ℤ) = -1
    rw [zpow_ofNat, ← pow_mul, ha4]
  · refine Subgroup.mem_zpowers_iff.mpr ⟨3, ?_⟩
    show (-1 * p) ^ (3 : ℤ) = -1
    rw [zpow_ofNat, (Commute.neg_one_left p).mul_pow, hp3, mul_one]
    norm_num
  · exact Subgroup.mem_zpowers_iff.mpr ⟨4, by show a ^ (4 : ℤ) = -1; rw [zpow_ofNat, ha4]⟩
  · refine Subgroup.mem_zpowers_iff.mpr ⟨4, ?_⟩
    show a⁻¹ ^ (4 : ℤ) = -1
    rw [zpow_ofNat, inv_pow, ha4, inv_neg_one]

theorem neg_one_not_mem_zpowers_rep {a p b : G23} (hp : orderOf p = 3)
    (hb : orderOf b = 2) (hbz : b ∉ Subgroup.center G23)
    (k : Fin 8) (hk : k = 0 ∨ k = 3 ∨ k = 5) :
    (-1 : G23) ∉ Subgroup.zpowers (rep a p b k) := by
  intro hmem
  have hdvd := orderOf_dvd_of_mem_zpowers hmem
  rw [orderOf_neg_one] at hdvd
  rcases hk with rfl | rfl | rfl
  · have h1 : orderOf (rep a p b 0) = 1 := by
      show orderOf (1 : G23) = 1
      exact orderOf_one
    rw [h1] at hdvd
    exact absurd hdvd (by norm_num)
  · have h3 : orderOf (rep a p b 3) = 3 := hp
    rw [h3] at hdvd
    exact absurd hdvd (by norm_num)
  · have hb' : rep a p b 5 = b := rfl
    rw [hb'] at hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hmod : b ^ m = b ^ (m % 2) := by
      rw [← zpow_mod_orderOf b m, hb]
      rfl
    rcases Int.emod_two_eq_zero_or_one m with h0 | h1
    · rw [hmod, h0, zpow_zero] at hm
      exact absurd hm.symm (by
        intro h
        have := congrArg orderOf h
        rw [orderOf_neg_one, orderOf_one] at this
        exact absurd this (by norm_num))
    · rw [hmod, h1, zpow_one] at hm
      exact hbz (hm ▸ Subgroup.mem_center_iff.mpr fun x => neg_one_mul_comm x)

section Section

variable {G : Type} [Group G] {t : G}
  (π : Subgroup.centralizer ({t} : Set G) →* G23)

@[expose] def tC (t : G) : Subgroup.centralizer ({t} : Set G) :=
  ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem tC_comm (t : G) (x : Subgroup.centralizer ({t} : Set G)) : Commute x (tC t) :=
  Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2)

theorem mem_section_of_neg_one_mem (ht : orderOf t = 2)
    (hN : Odd (Nat.card π.ker)) (hπt : π (tC t) = -1)
    (c : Subgroup.centralizer ({t} : Set G)) (hz : (-1 : G23) ∈ Subgroup.zpowers (π c)) :
    (c : G) ∈ centralInvolutionSection t := by
  obtain ⟨h2', hhalf⟩ := pow_half_eq_neg_one hz
  have hdvd : orderOf (π c) ∣ orderOf c := orderOf_map_dvd π c
  have h2 : 2 ∣ orderOf c := h2'.trans hdvd
  have hker : c ^ orderOf (π c) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  have hodd_pow : Odd (orderOf (c ^ orderOf (π c))) :=
    hN.of_dvd_nat (π.ker.orderOf_dvd_natCard hker)
  have hord_pow : orderOf (c ^ orderOf (π c)) = orderOf c / orderOf (π c) := by
    rw [orderOf_pow' c (orderOf_pos _).ne', Nat.gcd_eq_right hdvd]
  rw [hord_pow] at hodd_pow
  obtain ⟨m, hm⟩ := hdvd
  have hm' : orderOf c / orderOf (π c) = m := by
    rw [hm, Nat.mul_div_cancel_left _ (orderOf_pos _)]
  rw [hm'] at hodd_pow
  obtain ⟨k, hk⟩ := h2'
  have hsplit : orderOf c / 2 = k * m := by
    rw [hm, hk, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  have hπu : π (c ^ (orderOf c / 2)) = -1 := by
    rw [map_pow, hsplit, pow_mul, show k = orderOf (π c) / 2 by omega, hhalf,
      hodd_pow.neg_one_pow]
  have hut : c ^ (orderOf c / 2) * (tC t)⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπu, hπt, inv_neg_one, mul_neg_one, neg_neg]
  have hu2 : (c ^ (orderOf c / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel h2, pow_orderOf_eq_one]
  have ht2 : (tC t) ^ 2 = 1 := Subtype.ext (by
    show t ^ 2 = 1
    rw [← ht, pow_orderOf_eq_one])
  have hcomm : Commute (c ^ (orderOf c / 2)) (tC t) := ((tC_comm t c).pow_left _)
  have hsq : (c ^ (orderOf c / 2) * (tC t)⁻¹) ^ 2 = 1 := by
    rw [(hcomm.inv_right).mul_pow, hu2, inv_pow, ht2, inv_one, one_mul]
  have hord1 : orderOf (c ^ (orderOf c / 2) * (tC t)⁻¹) = 1 := by
    have hd2 := orderOf_dvd_of_pow_eq_one hsq
    have hdN := π.ker.orderOf_dvd_natCard hut
    have hodd := hN.of_dvd_nat hdN
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have hu : c ^ (orderOf c / 2) = tC t := by
    have := orderOf_eq_one_iff.mp hord1
    exact mul_inv_eq_one.mp this
  refine ⟨c.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact even_iff_two_dvd.mpr h2
  · rw [Subgroup.orderOf_coe, ← Subgroup.coe_pow, hu]
    rfl

end Section

theorem ip_add_left {X : Type} [Group X] [Fintype X] (f g h : X → ℂ) :
    BlocksInnerProduct (f + g) h = BlocksInnerProduct f h + BlocksInnerProduct g h := by
  unfold BlocksInnerProduct
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem ip_sub_left {X : Type} [Group X] [Fintype X] (f g h : X → ℂ) :
    BlocksInnerProduct (f - g) h = BlocksInnerProduct f h - BlocksInnerProduct g h := by
  unfold BlocksInnerProduct
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem ip_smul_left {X : Type} [Group X] [Fintype X] (c : ℂ) (f h : X → ℂ) :
    BlocksInnerProduct (c • f) h = c * BlocksInnerProduct f h := by
  unfold BlocksInnerProduct
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem ip_irr_ne {X : Type} [Group X] [Fintype X] (χ ψ : CFSG.BlocksIrr X)
    (h : (χ : X → ℂ) ≠ ψ) : BlocksInnerProduct (χ : X → ℂ) (ψ : X → ℂ) = 0 := by
  rw [blocksInnerProduct_irreducible, ite_eq_right]
  intro e
  exact h (congrArg Subtype.val e)

theorem inflate_mem_blocksVChar {X Y : Type} [Group X] [Group Y] [Finite X] (π : X →* Y)
    {χ : Y → ℂ} (hχ : χ ∈ CFSG.BlocksIrr Y) : (fun x => χ (π x)) ∈ CFSG.BlocksVChar X := by
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hχ
  let data : FiniteComplexRepresentation X := { vector := V, representation := ρ.comp π }
  have hchar : data.character = fun x => ρ.character (π x) := rfl
  rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup, ← hchar]
  exact character_mem_virtualCharacters data

section KernelSum

open scoped Classical

variable {G : Type} [Group G] [Fintype G] {t : G}
  (π : Subgroup.centralizer ({t} : Set G) →* G23) (hπ : Function.Surjective π)

@[expose] noncomputable def kernelSum (ψ : G → ℂ) (h : G23) : ℂ :=
  ∑ n : π.ker, ψ (((Function.surjInv hπ h : Subgroup.centralizer ({t} : Set G)) : G) *
    ((n : Subgroup.centralizer ({t} : Set G)) : G))

theorem kernelSum_lift (ψ : G → ℂ) (y : Subgroup.centralizer ({t} : Set G)) :
    kernelSum π hπ ψ (π y) =
      ∑ n : π.ker, ψ ((y : G) * ((n : Subgroup.centralizer ({t} : Set G)) : G)) := by
  unfold kernelSum
  have hn₀ : y⁻¹ * Function.surjInv hπ (π y) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, Function.surjInv_eq hπ, inv_mul_cancel]
  have hy : Function.surjInv hπ (π y) = y * (⟨_, hn₀⟩ : π.ker) := by
    show Function.surjInv hπ (π y) = y * (y⁻¹ * Function.surjInv hπ (π y))
    group
  rw [hy]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨_, hn₀⟩ : π.ker)) _ _ fun n => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, mul_assoc]

theorem kernelSum_conj (ψ : G → ℂ) (hψ : ∀ c g : G, ψ (c * g * c⁻¹) = ψ g) (x h : G23) :
    kernelSum π hπ ψ (x * h * x⁻¹) = kernelSum π hπ ψ h := by
  obtain ⟨d, rfl⟩ := hπ x
  obtain ⟨y, rfl⟩ := hπ h
  rw [← map_inv, ← map_mul, ← map_mul, kernelSum_lift, kernelSum_lift]
  refine Fintype.sum_equiv (MulAut.conjNormal d⁻¹).toEquiv _ _ fun n => ?_
  have hn : (((MulAut.conjNormal d⁻¹).toEquiv n : π.ker) : Subgroup.centralizer ({t} : Set G)) =
      d⁻¹ * n * d := by
    rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conjNormal_apply, inv_inv]
  rw [hn]
  have e : ((d * y * d⁻¹ : Subgroup.centralizer ({t} : Set G)) : G) *
      ((n : Subgroup.centralizer ({t} : Set G)) : G) =
      (d : G) * ((y : G) * ((d⁻¹ * n * d : Subgroup.centralizer ({t} : Set G)) : G)) *
        (d : G)⁻¹ := by
    push_cast
    group
  rw [e, hψ]

end KernelSum

end GL2OddKernel

open GL2OddKernel GL2ThreeCharacters CFSG.TwoRankLowerBound.Helpers in
open scoped Classical in
theorem odd_kernel_GL2_centralizer_produces_actual_characters {G : Type} [Group G] [Fintype G]
    (t : G) (ht : orderOf t = 2)
    (π : Subgroup.centralizer ({t} : Set G) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hπ : Function.Surjective π) (hN : Odd (Nat.card π.ker))
    (hπt : π ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = -1)
    (a p b : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (ha : orderOf a = 8)
    (hp : orderOf p = 3) (hb : orderOf b = 2)
    (hbz : b ∉ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))
    (φ : Fin 8 → Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) → ℂ)
    (hφirr : ∀ i, φ i ∈ CFSG.BlocksIrr (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))
    (hφ : let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)
      let ω : ℂ := ξ + ξ ^ 3
      let rep : Fin 8 → Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
        ![1, -1, a ^ 2, p, -1 * p, b, a, a⁻¹]
      let table : Fin 8 → Fin 8 → ℂ := ![![1, 1, 1, 1, 1, 1, 1, 1],
        ![1, 1, 1, 1, 1, -1, -1, -1], ![2, 2, 2, -1, -1, 0, 0, 0], ![3, 3, -1, 0, 0, -1, 1, 1],
        ![3, 3, -1, 0, 0, 1, -1, -1], ![4, -4, 0, 1, -1, 0, 0, 0], ![2, -2, 0, -1, 1, 0, ω, -ω],
        ![2, -2, 0, -1, 1, 0, -ω, ω]]
      ∀ i j, φ i (rep j) = table i j) :
    let C := Subgroup.centralizer ({t} : Set G)
    let N := π.ker
    let Φ : Fin 5 → Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) → ℂ :=
      ![φ 0 + φ 2 - φ 4, φ 2 - φ 6, φ 6 - φ 7, φ 1 + φ 4 - φ 5, φ 1 + φ 2 - φ 3]
    let β : Fin 5 → G → ℂ := fun i => inducedFunction C (fun c => Φ i (π c))
    ∃ (χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : CFSG.BlocksIrr G) (ε ε₁ ε₂ ε₃ : ℤ),
      [χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇].Nodup ∧
      (χ₁ : G → ℂ) ≠ 1 ∧ (χ₂ : G → ℂ) ≠ 1 ∧ (χ₃ : G → ℂ) ≠ 1 ∧ (χ₄ : G → ℂ) ≠ 1 ∧
      (χ₅ : G → ℂ) ≠ 1 ∧ (χ₆ : G → ℂ) ≠ 1 ∧ (χ₇ : G → ℂ) ≠ 1 ∧
      (ε = 1 ∨ ε = -1) ∧ (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧ (ε₃ = 1 ∨ ε₃ = -1) ∧
      β 0 = 1 + (ε : ℂ) • ((χ₁ : G → ℂ) - χ₂) ∧
      β 1 = (ε : ℂ) • ((χ₁ : G → ℂ) - χ₃) ∧
      β 2 = (ε : ℂ) • ((χ₃ : G → ℂ) - χ₄) ∧
      β 3 = (ε : ℂ) • (χ₂ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₂ : ℂ) • (χ₆ : G → ℂ) ∧
      β 4 = (ε : ℂ) • (χ₁ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₃ : ℂ) • (χ₇ : G → ℂ) ∧
      (∀ i : Fin 5, ∀ g : G, Odd (orderOf g) → β i g = 0) ∧
      ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ (χ₁ : G → ℂ) → ψ ≠ (χ₂ : G → ℂ) →
        ψ ≠ (χ₃ : G → ℂ) → ψ ≠ (χ₄ : G → ℂ) → ψ ≠ (χ₅ : G → ℂ) → ψ ≠ (χ₆ : G → ℂ) →
        ψ ≠ (χ₇ : G → ℂ) →
        (∀ c : C, t ∈ Subgroup.zpowers (c : G) →
          ∑ n : N, ψ ((c : G) * ((n : C) : G)) = 0) ∧
        (N = ⊥ → (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) →
          ∀ g : G, Even (orderOf g) → ψ g = 0) := by
  intro C N Φ β
  have hφ' : ∀ i j, φ i (rep a p b j) = (tableA i j : ℂ) + (tableB i j : ℂ) * omega8 := by
    intro i j
    have h : φ i (rep a p b j) = charTable (Complex.exp (2 * Real.pi * Complex.I / 8) +
        Complex.exp (2 * Real.pi * Complex.I / 8) ^ 3) i j := hφ i j
    rw [h, charTable_eq, exp_eq_xi]
  have hΦ : Φ = bigPhi φ := rfl
  have hπt' : π (tC t) = -1 := hπt
  have hαclass : ∀ i, CFSG.BlocksIsClassFunction (fun c : C => bigPhi φ i (π c)) := by
    intro i g h
    simp only [map_mul, map_inv]
    exact bigPhi_conj hφirr i _ _
  have hαsupp : ∀ i, ∀ x : C, (x : G) ∉ centralInvolutionSection t →
      (fun c : C => bigPhi φ i (π c)) x = 0 := by
    intro i x hx
    obtain ⟨k, hk⟩ := (rep_facts ha hp hb hbz).1 (π x)
    have hval : bigPhi φ i (π x) = bigPhi φ i (rep a p b k) := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hk
      rw [← hc, bigPhi_conj hφirr]
    show bigPhi φ i (π x) = 0
    rw [hval]
    rcases fin8_cases k with hk' | hk''
    · exact bigPhi_rep_zero hφ' i k hk'
    · exfalso
      exact hx (mem_section_of_neg_one_mem π ht hN hπt' x
        (neg_one_mem_zpowers_conj hk (neg_one_mem_zpowers_rep ha hp k hk'')))
  have hαvirt : ∀ i, (fun c : C => bigPhi φ i (π c)) ∈ CFSG.BlocksVChar C := by
    have hinf := fun j => inflate_mem_blocksVChar π (hφirr j)
    intro i
    fin_cases i
    · exact (CFSG.BlocksVChar C).sub_mem ((CFSG.BlocksVChar C).add_mem (hinf 0) (hinf 2)) (hinf 4)
    · exact (CFSG.BlocksVChar C).sub_mem (hinf 2) (hinf 6)
    · exact (CFSG.BlocksVChar C).sub_mem (hinf 6) (hinf 7)
    · exact (CFSG.BlocksVChar C).sub_mem ((CFSG.BlocksVChar C).add_mem (hinf 1) (hinf 4)) (hinf 5)
    · exact (CFSG.BlocksVChar C).sub_mem ((CFSG.BlocksVChar C).add_mem (hinf 1) (hinf 2)) (hinf 3)
  obtain ⟨hiso1, hiso2, -⟩ := central_involution_section_induction_isometry t
  have hβ : ∀ i, β i = inducedFunction C (fun c : C => bigPhi φ i (π c)) := fun i => rfl
  have hβvirt : ∀ i, β i ∈ CFSG.BlocksVChar G := fun i => by
    rw [hβ]
    exact (hiso1 _ (hαclass i) (hαsupp i)).2.2.2 (hαvirt i)
  have hDeven : ∀ g : G, g ∈ (⋃ x : G, (fun y => x * y * x⁻¹) '' centralInvolutionSection t) →
      Even (orderOf g) := by
    intro g hg
    obtain ⟨x, y, hy, rfl⟩ := Set.mem_iUnion.mp hg
    have h := (MulAut.conj x).orderOf_eq y
    rw [MulAut.conj_apply] at h
    rw [h]
    exact hy.2.1
  have hβodd : ∀ i : Fin 5, ∀ g : G, Odd (orderOf g) → β i g = 0 := by
    intro i g hg
    rw [hβ]
    apply (hiso1 _ (hαclass i) (hαsupp i)).2.1
    intro hmem
    exact (Nat.not_even_iff_odd.mpr hg) (hDeven g hmem)
  have hβdeg : ∀ i, β i 1 = 0 := fun i => hβodd i 1 (by rw [orderOf_one]; exact odd_one)
  have hβprin : ∀ i, CFSG.BlocksInnerProduct (β i) 1 = (![1, 0, 0, 0, 0] i : ℤ) := by
    intro i
    rw [hβ, (hiso1 _ (hαclass i) (hαsupp i)).2.2.1,
      show (1 : C → ℂ) = fun c : C => (1 : G23 → ℂ) (π c) from rfl,
      blocksInnerProduct_inflate π hπ, inner_bigPhi_one ha hp hb hbz hφirr hφ']
  have hβgram : ∀ i j, CFSG.BlocksInnerProduct (β i) (β j) = gram i j := by
    intro i j
    rw [hβ, hβ, hiso2 _ _ (hαclass i) (hαsupp i) (hαclass j) (hαsupp j),
      blocksInnerProduct_inflate π hπ, inner_bigPhi ha hp hb hbz hφirr hφ']
  obtain ⟨χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, ε, ε₁, ε₂, ε₃, hnodup, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
      hε, hε₁, hε₂, hε₃, hb₁, hb₂, hb₃, hb₄, hb₅, -⟩ :=
    five_virtual_characters_produce_seven_irreducibles (hβvirt 0) (hβvirt 1) (hβvirt 2)
      (hβvirt 3) (hβvirt 4) (hβdeg 0) (hβdeg 1) (hβdeg 2) (hβdeg 3) (hβdeg 4)
      (by rw [hβprin]; norm_num) (by rw [hβprin]; norm_num) (by rw [hβprin]; norm_num)
      (by rw [hβprin]; norm_num) (by rw [hβprin]; norm_num)
      (by rw [hβgram]; norm_num [gram]) (by rw [hβgram]; norm_num [gram])
      (by rw [hβgram]; norm_num [gram]) (by rw [hβgram]; norm_num [gram])
      (by rw [hβgram]; norm_num [gram]) (by rw [hβgram]; norm_num [gram])
      (by rw [hβgram]; norm_num [gram]) (by rw [hβgram]; norm_num [gram])
      (by rw [hβgram]; norm_num [gram]) (by rw [hβgram]; norm_num [gram])
      (by rw [hβgram]; norm_num [gram]) (by rw [hβgram]; norm_num [gram])
      (by rw [hβgram]; norm_num [gram]) (by rw [hβgram]; norm_num [gram])
      (by rw [hβgram]; norm_num [gram])
  refine ⟨χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, ε, ε₁, ε₂, ε₃, hnodup, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
    hε, hε₁, hε₂, hε₃, hb₁, hb₂, hb₃, hb₄, hb₅, hβodd, ?_⟩
  intro ψ hψ hψ1 hψ₁ hψ₂ hψ₃ hψ₄ hψ₅ hψ₆ hψ₇
  have hψclass : CFSG.BlocksIsClassFunction ψ := fun g h => blocksIrr_conj hψ h g
  let ψI : CFSG.BlocksIrr G := ⟨ψ, hψ⟩
  have hip1 : CFSG.BlocksInnerProduct (1 : G → ℂ) ψ = 0 :=
    ip_irr_ne ⟨1, principal_mem_blocksIrr G⟩ ψI (Ne.symm hψ1)
  have hipχ : ∀ χ : CFSG.BlocksIrr G, (χ : G → ℂ) ≠ ψ →
      CFSG.BlocksInnerProduct (χ : G → ℂ) ψ = 0 := fun χ h => ip_irr_ne χ ψI h
  have horth0 : CFSG.BlocksInnerProduct (β 0) ψ = 0 := by
    rw [hb₁, ip_add_left, ip_smul_left, ip_sub_left, hip1, hipχ χ₁ (Ne.symm hψ₁),
      hipχ χ₂ (Ne.symm hψ₂)]
    ring
  have horth1 : CFSG.BlocksInnerProduct (β 1) ψ = 0 := by
    rw [hb₂, ip_smul_left, ip_sub_left, hipχ χ₁ (Ne.symm hψ₁), hipχ χ₃ (Ne.symm hψ₃)]
    ring
  have horth2 : CFSG.BlocksInnerProduct (β 2) ψ = 0 := by
    rw [hb₃, ip_smul_left, ip_sub_left, hipχ χ₃ (Ne.symm hψ₃), hipχ χ₄ (Ne.symm hψ₄)]
    ring
  have horth3 : CFSG.BlocksInnerProduct (β 3) ψ = 0 := by
    rw [hb₄, ip_add_left, ip_add_left, ip_smul_left, ip_smul_left, ip_smul_left,
      hipχ χ₂ (Ne.symm hψ₂), hipχ χ₅ (Ne.symm hψ₅), hipχ χ₆ (Ne.symm hψ₆)]
    ring
  have horth4 : CFSG.BlocksInnerProduct (β 4) ψ = 0 := by
    rw [hb₅, ip_add_left, ip_add_left, ip_smul_left, ip_smul_left, ip_smul_left,
      hipχ χ₁ (Ne.symm hψ₁), hipχ χ₅ (Ne.symm hψ₅), hipχ χ₇ (Ne.symm hψ₇)]
    ring
  have horth : ∀ i, CFSG.BlocksInnerProduct (β i) ψ = 0 := by
    intro i
    fin_cases i
    exacts [horth0, horth1, horth2, horth3, horth4]
  have hcard : (Nat.card C : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hF : ∀ i, ∑ h : G23, bigPhi φ i h * starRingEnd ℂ (kernelSum π hπ ψ h) = 0 := by
    intro i
    have e := horth i
    rw [hβ, blocksInnerProduct_inducedFunction_left C _ ψ hψclass] at e
    unfold CFSG.BlocksInnerProduct at e
    rw [sum_fiber π hπ (bigPhi φ i) (fun x => starRingEnd ℂ (ψ x))] at e
    have e' : ∑ h : G23, bigPhi φ i h *
        ∑ n : π.ker, starRingEnd ℂ (ψ ((Function.surjInv hπ h * n : C) : G)) = 0 := by
      rcases mul_eq_zero.mp e with h0 | h0
      · exact absurd (inv_eq_zero.mp h0) hcard
      · exact h0
    rw [← e']
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [kernelSum, map_sum]
    rfl
  have hFclass : ∀ i, ∀ x h : G23,
      (fun h => bigPhi φ i h * starRingEnd ℂ (kernelSum π hπ ψ h)) (x * h * x⁻¹) =
        (fun h => bigPhi φ i h * starRingEnd ℂ (kernelSum π hπ ψ h)) h := by
    intro i x h
    simp only [bigPhi_conj hφirr, kernelSum_conj π hπ ψ (fun c g => hψclass g c)]
  have hrel : ∀ i : Fin 5, ∑ k, ((phiA i k : ℂ) + (phiB i k : ℂ) * omega8) *
      ((classSize k : ℂ) * starRingEnd ℂ (kernelSum π hπ ψ (rep a p b k))) = 0 := by
    intro i
    have e := hF i
    rw [sum_rep ha hp hb hbz _ (hFclass i)] at e
    rw [← e]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [bigPhi_rep hφ']
    ring
  obtain ⟨hy1, hy2, hy4, hy6, hy7⟩ := span_relations _ hrel
  have hvanish : ∀ k : Fin 8, (k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 7) →
      kernelSum π hπ ψ (rep a p b k) = 0 := by
    intro k hk
    have hy : (classSize k : ℂ) * starRingEnd ℂ (kernelSum π hπ ψ (rep a p b k)) = 0 := by
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hsize : (classSize k : ℂ) ≠ 0 := by
      have : 0 < classSize k := by fin_cases k <;> decide
      exact_mod_cast this.ne'
    have hc := (mul_eq_zero.mp hy).resolve_left hsize
    simpa using congrArg (starRingEnd ℂ) hc
  have hsection : ∀ c : C, t ∈ Subgroup.zpowers (c : G) →
      ∑ n : N, ψ ((c : G) * ((n : C) : G)) = 0 := by
    intro c hc
    have hz : (-1 : G23) ∈ Subgroup.zpowers (π c) := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hc
      have htm : c ^ m = tC t := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm)
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
      rw [← map_zpow, htm, hπt']
    obtain ⟨k, hk⟩ := (rep_facts ha hp hb hbz).1 (π c)
    have hk' : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 7 := by
      rcases fin8_cases k with hk0 | hk1
      · exact absurd (neg_one_mem_zpowers_conj hk.symm hz)
          (neg_one_not_mem_zpowers_rep hp hb hbz k hk0)
      · exact hk1
    have hval : kernelSum π hπ ψ (π c) = kernelSum π hπ ψ (rep a p b k) := by
      obtain ⟨x, hx⟩ := isConj_iff.mp hk
      rw [← hx, kernelSum_conj π hπ ψ (fun c g => hψclass g c)]
    rw [← kernelSum_lift π hπ ψ c, hval, hvanish k hk']
  refine ⟨hsection, fun hbot hinv g hg => ?_⟩
  have h2 : 2 ∣ orderOf g := even_iff_two_dvd.mp hg
  have hu : orderOf (g ^ (orderOf g / 2)) = 2 := orderOf_pow_orderOf_div (orderOf_pos g).ne' h2
  obtain ⟨x, hx⟩ := isConj_iff.mp (hinv _ t hu ht)
  have hc0t : (x * g * x⁻¹) ^ (orderOf g / 2) = t := by rw [conj_pow, hx]
  have hc0C : x * g * x⁻¹ ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc0t]
    exact (Commute.self_pow (x * g * x⁻¹) (orderOf g / 2)).eq
  have hsum := hsection ⟨x * g * x⁻¹, hc0C⟩ (by
    rw [← hc0t]
    exact Subgroup.npow_mem_zpowers _ _)
  have hone : ∀ n : N, ((n : C) : G) = 1 := by
    intro n
    have hn : (n : C) = 1 := (Subgroup.eq_bot_iff_forall N).mp hbot n n.2
    rw [hn]
    rfl
  have hcardN : Fintype.card N = 1 := by
    rw [← Nat.card_eq_fintype_card, show N = ⊥ from hbot, Subgroup.card_bot]
  simp only [hone, mul_one, Finset.sum_const, Finset.card_univ, hcardN, one_smul] at hsum
  have hg' := hψclass (x * g * x⁻¹) x⁻¹
  rw [inv_inv, show x⁻¹ * (x * g * x⁻¹) * x = g by group, hsum] at hg'
  exact hg'

end CFSG.Semidihedral.Principal
