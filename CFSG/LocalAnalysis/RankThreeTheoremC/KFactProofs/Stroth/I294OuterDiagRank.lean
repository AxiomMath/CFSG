module

public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.RankThree.PartOne.KF.UnitaryModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThree.PartOne.KFU CFSG.Open.StatedAPI

section Torus

variable {K : Type} [Field K] {n : ℕ}

@[expose] def torus4Nat (a : Fin 4 → Kˣ) (j : ℕ) : Kˣ :=
  if j = 0 then a 0 else if j = 1 then a 1 * (a 0)⁻¹ else if j = 2 then a 2 * (a 1)⁻¹
  else if j = 3 then a 3 * (a 2)⁻¹ else if j = 4 then (a 3)⁻¹ else 1

@[expose] def torus4Fun (a : Fin 4 → Kˣ) (i : Fin n) : Kˣ := torus4Nat a i.val

theorem torus4Nat_mul (a b : Fin 4 → Kˣ) (j : ℕ) :
    torus4Nat (a * b) j = torus4Nat a j * torus4Nat b j := by
  simp only [torus4Nat, Pi.mul_apply]
  split_ifs <;> (try simp only [mul_inv, one_mul]) <;> (try ac_rfl)

theorem torus4Nat_mem {μ : Subgroup Kˣ} {x : Fin 4 → Kˣ} (hx : ∀ i, x i ∈ μ) (j : ℕ) :
    torus4Nat x j ∈ μ := by
  unfold torus4Nat
  split_ifs
  · exact hx 0
  · exact μ.mul_mem (hx 1) (μ.inv_mem (hx 0))
  · exact μ.mul_mem (hx 2) (μ.inv_mem (hx 1))
  · exact μ.mul_mem (hx 3) (μ.inv_mem (hx 2))
  · exact μ.inv_mem (hx 3)
  · exact μ.one_mem

theorem torus4Nat_one (j : ℕ) : torus4Nat (1 : Fin 4 → Kˣ) j = 1 := by
  simp only [torus4Nat, Pi.one_apply]
  split_ifs <;> simp

@[expose] def torus4 (n : ℕ) : (Fin 4 → Kˣ) →* (Fin n → Kˣ) where
  toFun a := torus4Fun a
  map_one' := funext fun i => torus4Nat_one i.val
  map_mul' a b := funext fun i => torus4Nat_mul a b i.val

theorem torus4_apply (a : Fin 4 → Kˣ) (i : Fin n) : torus4 n a i = torus4Nat a i.val := rfl

theorem torus4_prod (hn : 5 ≤ n) (a : Fin 4 → Kˣ) : ∏ i, torus4 n a i = 1 := by
  have h1 : ∏ i : Fin n, torus4 n a i = ∏ j ∈ Finset.range n, torus4Nat a j := by
    simp only [torus4_apply]
    exact Fin.prod_univ_eq_prod_range (fun j => torus4Nat a j) n
  have h2 : ∏ j ∈ Finset.range 5, torus4Nat a j = ∏ j ∈ Finset.range n, torus4Nat a j := by
    apply Finset.prod_subset (Finset.range_subset_range.2 hn)
    intro j hj hj5
    simp only [Finset.mem_range, not_lt] at hj hj5
    have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    have h2 : j ≠ 2 := by omega
    have h3 : j ≠ 3 := by omega
    have h4 : j ≠ 4 := by omega
    simp [torus4Nat, h0, h1, h2, h3, h4]
  have key : ∀ x y : Kˣ, x * (y * x⁻¹) = y := fun x y => by
    rw [mul_comm y, mul_inv_cancel_left]
  rw [h1, ← h2]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, torus4Nat]
  simp

theorem torus4_apply_five (hn : 6 ≤ n) (a : Fin 4 → Kˣ) :
    torus4 n a ⟨5, by omega⟩ = 1 := by
  simp [torus4_apply, torus4Nat]

theorem torus4_injective (hn : 5 ≤ n) : Function.Injective (torus4 (K := K) n) := by
  intro a b hab
  have e0 := congrFun hab ⟨0, by omega⟩
  have e1 := congrFun hab ⟨1, by omega⟩
  have e2 := congrFun hab ⟨2, by omega⟩
  have e3 := congrFun hab ⟨3, by omega⟩
  simp only [torus4_apply, torus4Nat] at e0 e1 e2 e3
  simp only [if_true, one_ne_zero, if_false, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] at e0 e1 e2 e3
  funext i
  fin_cases i
  · exact e0
  · simpa [e0] using e1
  · have h1 : a 1 = b 1 := by simpa [e0] using e1
    simpa [h1] using e2
  · have h1 : a 1 = b 1 := by simpa [e0] using e1
    have h2 : a 2 = b 2 := by simpa [h1] using e2
    simpa [h2] using e3

end Torus

section Rank

variable {K : Type} [Field K] [Finite K] {p n : ℕ}

theorem odTorus_four_le_pRank_statedProj (hp : p.Prime) (hn : 6 ≤ n) {ζ : Kˣ} (hζ : orderOf ζ = p)
    {H : Subgroup (GL (Fin n) K)}
    (hH : ∀ w : Fin n → Kˣ, (∀ i, w i ∈ Subgroup.zpowers ζ) → ∏ i, w i = 1 → diagU w ∈ H) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj H)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  let μ : Subgroup Kˣ := Subgroup.zpowers ζ
  have hμp : ∀ x : μ, x ^ p = 1 := by
    rintro ⟨x, k, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζp, one_zpow]
  have hμcard : Nat.card μ = p := by rw [Nat.card_zpowers, hζ]
  let ι : (Fin 4 → μ) →* (Fin 4 → Kˣ) := MonoidHom.compLeft μ.subtype (Fin 4)
  let φ : (Fin 4 → μ) →* GL (Fin n) K := (diagUHom (n := n) (K := K)).comp ((torus4 n).comp ι)
  have hφapp : ∀ a, φ a = diagU (torus4 n (fun i => (a i : Kˣ))) := fun a => rfl
  have hentry : ∀ (a : Fin 4 → μ) (i : Fin n), torus4 n (fun j => (a j : Kˣ)) i ∈ μ := by
    intro a i
    rw [torus4_apply]
    exact torus4Nat_mem (fun j => (a j).2) i.val
  refine CFSG.SectionRank.ClassicalOdd.le_pRank_statedProj (H := H) (A := Fin 4 → μ) hp.one_lt
    (fun a b => mul_comm a b) (fun a => funext fun i => hμp (a i)) ?_ φ ?_ ?_
    (v := Pi.single ⟨5, by omega⟩ 1) ?_ ?_
  · rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hμcard]
  ·
    intro a b hab
    have : (fun i => (a i : Kˣ)) = fun i => (b i : Kˣ) :=
      torus4_injective (by omega) (diagU_injective hab)
    funext i
    exact Subtype.ext (congrFun this i)
  · intro a
    rw [hφapp]
    exact hH _ (hentry a) (torus4_prod (by omega) _)
  · intro h
    have := congrFun h ⟨5, by omega⟩
    simp at this
  · intro a
    rw [hφapp, diagU_val, Matrix.diagonal_mulVec_single, torus4_apply_five (by omega)]
    simp

end Rank

section Models

variable {K : Type} [Field K] [Finite K] {p n : ℕ}

theorem odFour_le_pRank_psl (hp : p.Prime) (hn : 6 ≤ n) (hpK : p ∣ Nat.card K - 1) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n K))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine odTorus_four_le_pRank_statedProj hp hn hζ fun w _ hw => ?_
  refine mem_statedSL_of_det ?_
  rw [det_diagU, ← Units.coe_prod, hw, Units.val_one]

theorem odFour_le_pRank_psu {ℓ f : ℕ} (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f K)
    (hp : p.Prime) (hn : 6 ≤ n) (hpq : p ∣ ℓ ^ f + 1) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hU.card_eq_sq]
    have h1 : (ℓ ^ f) ^ 2 - 1 ^ 2 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := Nat.sq_sub_sq _ _
    rw [one_pow] at h1
    rw [h1]
    exact hpq.mul_right _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  refine odTorus_four_le_pRank_statedProj (H := StatedSU n (ℓ ^ f) K) hp hn hζ fun w hwμ hw => ?_
  refine torusSU_le_unitarySU hU hpq (mem_torusSU_iff.2 ⟨w, fun i => ?_, hw, rfl⟩)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hwμ i)
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζp, one_zpow]

end Models

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
