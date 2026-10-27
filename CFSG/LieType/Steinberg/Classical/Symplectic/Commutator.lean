module

public import CFSG.LieType.Steinberg.Classical.Symplectic.Basic

public noncomputable section

namespace CFSG.LieType.Steinberg.Sp

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.RootSystem TauCeti.GLSymplecticFin
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {n : ℕ} {F : Type} [Field F]

open _root_.Classical in
@[expose] def Exz (γ : Fin n → ℤ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ :=
  if h : ∃ r : RootSubgroupIndex n, stdVec r = toStd n γ then Ez h.choose else 0

variable (F) in
@[expose] def Ex (γ : Fin n → ℤ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  (Exz γ).map (Int.castRingHom F)

open _root_.Classical in
@[expose] def entryAt (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) (γ : Fin n → ℤ) : ℤ :=
  if h : ∃ r : RootSubgroupIndex n, stdVec r = toStd n γ then
    M (pos1 h.choose).1 (pos1 h.choose).2
  else 0

theorem Exz_eq {γ : Fin n → ℤ} {r : RootSubgroupIndex n} (hr : stdVec r = toStd n γ) :
    Exz γ = Ez r := by
  have h : ∃ r : RootSubgroupIndex n, stdVec r = toStd n γ := ⟨r, hr⟩
  rw [Exz, dite_eq_left h, stdVec_injective (h.choose_spec.trans hr.symm)]

theorem Exz_of_not {γ : Fin n → ℤ} (h : ¬∃ r : RootSubgroupIndex n, stdVec r = toStd n γ) :
    Exz γ = 0 := by
  rw [Exz, dite_eq_right h]

theorem entryAt_eq (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) {γ : Fin n → ℤ}
    {r : RootSubgroupIndex n} (hr : stdVec r = toStd n γ) :
    entryAt M γ = M (pos1 r).1 (pos1 r).2 := by
  have h : ∃ r : RootSubgroupIndex n, stdVec r = toStd n γ := ⟨r, hr⟩
  rw [entryAt, dite_eq_left h, stdVec_injective (h.choose_spec.trans hr.symm)]

theorem Ex_eq {γ : Fin n → ℤ} {r : RootSubgroupIndex n} (hr : stdVec r = toStd n γ) :
    Ex F γ = E F r := by
  rw [Ex, Exz_eq hr, E_eq_map]

theorem Ex_of_not {γ : Fin n → ℤ} (h : ¬∃ r : RootSubgroupIndex n, stdVec r = toStd n γ) :
    Ex F γ = 0 := by
  rw [Ex, Exz_of_not h]
  ext a b
  simp

theorem Ex_of_notMem {γ : Fin n → ℤ} (h : γ ∉ roots (isFiniteType_cartanC n) ∅) :
    Ex F γ = 0 :=
  Ex_of_not fun ⟨_, hr⟩ => h (mem_roots_of_stdVec hr)

theorem mat_x (γ : Fin n → ℤ) (c : F) : mat n F (x n F γ c) = 1 + c • Ex F γ := by
  by_cases h : ∃ r : RootSubgroupIndex n, stdVec r = toStd n γ
  · obtain ⟨r, hr⟩ := h
    rw [x_eq hr, Ex_eq hr, mat_elt]
  · rw [x_of_not h, Ex_of_not h, map_one, smul_zero, add_zero]

theorem hasDeg_Ex (γ : Fin n → ℤ) : HasDeg (toStd n γ) (Ex F γ) := by
  by_cases h : ∃ r : RootSubgroupIndex n, stdVec r = toStd n γ
  · obtain ⟨r, hr⟩ := h
    rw [Ex_eq hr, ← hr]
    exact hasDeg_E r
  · rw [Ex_of_not h]
    exact HasDeg.zero

theorem toStd_comb (α β : Fin n → ℤ) (i j : ℕ) :
    toStd n (i • α + j • β) = i • toStd n α + j • toStd n β := by
  rw [toStd_add', toStd_nsmul', toStd_nsmul']

theorem toStd_add_ne_zero {α β : Fin n → ℤ} (hαβ : α + β ≠ 0) :
    toStd n α + toStd n β ≠ 0 := by
  rw [← toStd_add', ← toStd_zero' (n := n)]
  exact fun h => hαβ (toStd_inj h)

theorem two_le_dot_add {r s : RootSubgroupIndex n} (hrs : stdVec r + stdVec s ≠ 0) :
    2 ≤ (stdVec r + stdVec s) ⬝ᵥ (stdVec r + stdVec s) := by
  have h0 : 0 < (stdVec r + stdVec s) ⬝ᵥ (stdVec r + stdVec s) :=
    lt_of_le_of_ne (dot_self_nonneg _) fun h => hrs (dotProduct_self_eq_zero.1 h.symm)
  have h := dot_add_self (stdVec r) (stdVec s)
  have ha := dot_stdVec r
  have hb := dot_stdVec s
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

@[expose] def commC (α β : Fin n → ℤ) (p : ℕ × ℕ) : ℤ :=
  if α + β = 0 then 1
  else if p = (1, 1) then entryAt (Exz α * Exz β - Exz β * Exz α) (α + β)
  else if p = (2, 1) then entryAt (-(Exz α * Exz β * Exz α)) (2 • α + β)
  else if p = (1, 2) then entryAt (Exz β * Exz α * Exz β) (α + 2 • β)
  else 1

theorem commC_eq_zero {α β : Fin n → ℤ} (hαβ : α + β = 0) (p : ℕ × ℕ) : commC α β p = 1 := by
  rw [commC, ite_eq_left hαβ]

theorem commC_one_one {α β : Fin n → ℤ} (hαβ : α + β ≠ 0) :
    commC α β (1, 1) = entryAt (Exz α * Exz β - Exz β * Exz α) (α + β) := by
  rw [commC, ite_eq_right hαβ, ite_eq_left rfl]

theorem commC_two_one {α β : Fin n → ℤ} (hαβ : α + β ≠ 0) :
    commC α β (2, 1) = entryAt (-(Exz α * Exz β * Exz α)) (2 • α + β) := by
  rw [commC, ite_eq_right hαβ, ite_eq_right (by decide), ite_eq_left rfl]

theorem commC_one_two {α β : Fin n → ℤ} (hαβ : α + β ≠ 0) :
    commC α β (1, 2) = entryAt (Exz β * Exz α * Exz β) (α + 2 • β) := by
  rw [commC, ite_eq_right hαβ, ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl]

private theorem map_apply_cast (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (a b : Fin n ⊕ Fin n) : M.map (Int.castRingHom F) a b = (M a b : F) := by
  simp

private theorem two_nsmul_add_ne_zero (r s : RootSubgroupIndex n) :
    2 • stdVec r + stdVec s ≠ 0 := by
  intro h
  have hs : stdVec s = -(2 • stdVec r) := eq_neg_of_add_eq_zero_right h
  have h1 := dot_stdVec s
  have h2 := dot_stdVec r
  rw [hs, neg_dotProduct, dotProduct_neg, neg_neg, smul_dotProduct, dotProduct_smul,
    smul_smul] at h1
  simp only [nsmul_eq_mul] at h1
  push_cast at h1
  omega

theorem Ex_lie {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0) :
    Ex F α * Ex F β - Ex F β * Ex F α = (commC α β (1, 1) : F) • Ex F (α + β) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hα
  obtain ⟨s, hs⟩ := exists_stdVec_of_mem_roots hβ
  have hsum : toStd n (α + β) = stdVec r + stdVec s := by rw [toStd_add', hr, hs]
  have hdeg : HasDeg (stdVec r + stdVec s) (E F r * E F s - E F s * E F r) :=
    ((hasDeg_E r).mul (hasDeg_E s)).sub (((hasDeg_E s).mul (hasDeg_E r)).congr (add_comm _ _))
  rw [Ex_eq hr, Ex_eq hs, commC_one_one hαβ, Exz_eq hr, Exz_eq hs]
  by_cases ht : ∃ t : RootSubgroupIndex n, stdVec t = toStd n (α + β)
  · obtain ⟨t, ht⟩ := ht
    rw [entryAt_eq _ ht, Ex_eq ht]
    have hM := eq_smul_E t ((isSp_E r).lie (isSp_E s)) (hdeg.congr (ht.trans hsum).symm)
    rw [hM]
    congr 1
    rw [E_eq_map, E_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.sub_apply,
      map_apply_cast, map_apply_cast, Matrix.sub_apply, Int.cast_sub]
  · rw [Ex_of_not ht, smul_zero]
    refine hdeg.eq_zero fun hpw => ht ?_
    obtain ⟨t, htv⟩ := exists_stdVec_of_isPosWt hpw
      (by rw [hr, hs]; exact toStd_add_ne_zero hαβ)
    exact ⟨t, htv.trans hsum.symm⟩

theorem Ex_triple {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0) :
    -(Ex F α * Ex F β * Ex F α) = (commC α β (2, 1) : F) • Ex F (2 • α + β) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hα
  obtain ⟨s, hs⟩ := exists_stdVec_of_mem_roots hβ
  have hsum : toStd n (2 • α + β) = 2 • stdVec r + stdVec s := by
    rw [toStd_add', toStd_nsmul', hr, hs]
  have hdeg : HasDeg (2 • stdVec r + stdVec s) (-(E F r * E F s * E F r)) :=
    (((hasDeg_E r).mul (hasDeg_E s)).mul (hasDeg_E r)).neg.congr (by rw [two_nsmul]; abel)
  rw [Ex_eq hr, Ex_eq hs, commC_two_one hαβ, Exz_eq hr, Exz_eq hs]
  by_cases ht : ∃ t : RootSubgroupIndex n, stdVec t = toStd n (2 • α + β)
  · obtain ⟨t, ht⟩ := ht
    rw [entryAt_eq _ ht, Ex_eq ht]
    have hM := eq_smul_E t ((isSp_E r).triple (isSp_E s)).neg (hdeg.congr (ht.trans hsum).symm)
    rw [hM]
    congr 1
    rw [E_eq_map, E_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.neg_apply,
      map_apply_cast, Matrix.neg_apply, Int.cast_neg]
  · rw [Ex_of_not ht, smul_zero]
    refine hdeg.eq_zero fun hpw => ht ?_
    obtain ⟨t, htv⟩ := exists_stdVec_of_isPosWt hpw (two_nsmul_add_ne_zero r s)
    exact ⟨t, htv.trans hsum.symm⟩

theorem Ex_triple' {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0) :
    Ex F β * Ex F α * Ex F β = (commC α β (1, 2) : F) • Ex F (α + 2 • β) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hα
  obtain ⟨s, hs⟩ := exists_stdVec_of_mem_roots hβ
  have hsum : toStd n (α + 2 • β) = 2 • stdVec s + stdVec r := by
    rw [toStd_add', toStd_nsmul', hr, hs, add_comm]
  have hdeg : HasDeg (2 • stdVec s + stdVec r) (E F s * E F r * E F s) :=
    (((hasDeg_E s).mul (hasDeg_E r)).mul (hasDeg_E s)).congr (by rw [two_nsmul]; abel)
  rw [Ex_eq hr, Ex_eq hs, commC_one_two hαβ, Exz_eq hr, Exz_eq hs]
  by_cases ht : ∃ t : RootSubgroupIndex n, stdVec t = toStd n (α + 2 • β)
  · obtain ⟨t, ht⟩ := ht
    rw [entryAt_eq _ ht, Ex_eq ht]
    have hM := eq_smul_E t ((isSp_E s).triple (isSp_E r)) (hdeg.congr (ht.trans hsum).symm)
    rw [hM]
    congr 1
    rw [E_eq_map, E_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, map_apply_cast]
  · rw [Ex_of_not ht, smul_zero]
    refine hdeg.eq_zero fun hpw => ht ?_
    obtain ⟨t, htv⟩ := exists_stdVec_of_isPosWt hpw (two_nsmul_add_ne_zero s r)
    exact ⟨t, htv.trans hsum.symm⟩

abbrev expS : Finset (ℕ × ℕ) := {(1, 1), (2, 1), (1, 2)}

theorem sum_expS {M : Type*} [AddCommMonoid M] (g : ℕ × ℕ → M) :
    ∑ p ∈ expS, g p = g (1, 1) + g (2, 1) + g (1, 2) := by
  rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide), add_assoc]

theorem mat_commutator {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0) (c d : F) :
    mat n F ⁅x n F α c, x n F β d⁆ =
      1 + ∑ p ∈ expS, ((commC α β p : F) * c ^ p.1 * d ^ p.2) • Ex F (p.1 • α + p.2 • β) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hα
  obtain ⟨s, hs⟩ := exists_stdVec_of_mem_roots hβ
  have hrs : stdVec r + stdVec s ≠ 0 := by
    rw [hr, hs]
    exact toStd_add_ne_zero hαβ
  have h2 := two_le_dot_add hrs
  set A := c • E F r with hA
  set B := d • E F s with hB
  have hAA : A * A = 0 := smul_E_mul_self r c
  have hBB : B * B = 0 := smul_E_mul_self s d
  have hAd : HasDeg (stdVec r) A := (hasDeg_E r).smul c
  have hBd : HasDeg (stdVec s) B := (hasDeg_E s).smul d
  have hABAB : A * B * A * B = 0 := by
    refine ((((hAd.mul hBd).mul hAd).mul hBd).congr
      (show _ = 2 • (stdVec r + stdVec s) by rw [two_nsmul]; abel)).eq_zero fun hpw => ?_
    have h4 := dot_le_four_of_isPosWt hpw
    rw [smul_dotProduct, dotProduct_smul, smul_smul] at h4
    simp only [nsmul_eq_mul] at h4
    push_cast at h4
    omega
  have hcomm : mat n F ⁅x n F α c, x n F β d⁆ = 1 + (A * B - B * A) + -(A * B * A) + B * A * B := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, x_eq hr, x_eq hs, mat_elt, mat_elt,
      mat_elt_inv, mat_elt_inv, ← hA, ← hB]
    have hexp : (1 + A) * (1 + B) * (1 - A) * (1 - B) =
        1 + (A * B - B * A) + -(A * B * A) + B * A * B + A * B * A * B - A * A - B * B -
          A * (B * B) + A * A * B := by noncomm_ring
    rw [hexp, hABAB, hAA, hBB]
    simp
  have e1 : A * B - B * A = (c * d) • (Ex F α * Ex F β - Ex F β * Ex F α) := by
    rw [Ex_eq hr, Ex_eq hs, hA, hB, smul_sub, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm d c]
  have e2 : -(A * B * A) = (c ^ 2 * d) • -(Ex F α * Ex F β * Ex F α) := by
    rw [Ex_eq hr, Ex_eq hs, hA, hB, smul_mul_smul_comm, smul_mul_smul_comm, smul_neg,
      show c * d * c = c ^ 2 * d by ring]
  have e3 : B * A * B = (c * d ^ 2) • (Ex F β * Ex F α * Ex F β) := by
    rw [Ex_eq hr, Ex_eq hs, hA, hB, smul_mul_smul_comm, smul_mul_smul_comm,
      show d * c * d = c * d ^ 2 by ring]
  rw [hcomm, e1, e2, e3, Ex_lie hα hβ hαβ, Ex_triple hα hβ hαβ, Ex_triple' hα hβ hαβ, sum_expS]
  simp only [one_smul, pow_one, smul_smul, add_assoc]
  ac_rfl

theorem list_prod_one_add {ι R : Type*} [Ring R] (N : ι → R) :
    ∀ L : List ι, L.Nodup → (∀ p ∈ L, ∀ q ∈ L, p ≠ q → N p * N q = 0) →
      (L.map fun p => 1 + N p).prod = 1 + (L.map N).sum
  | [], _, _ => by simp
  | p :: L, hL, h => by
    rw [List.nodup_cons] at hL
    have ih := list_prod_one_add N L hL.2 fun a ha b hb =>
      h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    have h0 : N p * (L.map N).sum = 0 := by
      rw [← List.sum_map_mul_left]
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
      exact h p List.mem_cons_self q (List.mem_cons_of_mem _ hq) fun e => hL.1 (e ▸ hq)
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, add_mul, one_mul,
      mul_add, mul_one, h0, add_zero]
    abel

theorem Ex_mul_Ex_eq_zero {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0) {p q : ℕ × ℕ}
    (hp : p ∈ expS) (hq : q ∈ expS) (hpq : p ≠ q) :
    Ex F (p.1 • α + p.2 • β) * Ex F (q.1 • α + q.2 • β) = 0 := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hα
  obtain ⟨s, hs⟩ := exists_stdVec_of_mem_roots hβ
  have hrs : stdVec r + stdVec s ≠ 0 := by
    rw [hr, hs]
    exact toStd_add_ne_zero hαβ
  have h2 := two_le_dot_add hrs
  have hab := dot_add_self (stdVec r) (stdVec s)
  have ha := dot_stdVec r
  have hb := dot_stdVec s
  have hdeg := (hasDeg_Ex (F := F) (p.1 • α + p.2 • β)).mul (hasDeg_Ex (q.1 • α + q.2 • β))
  rw [toStd_comb, toStd_comb, ← hr, ← hs,
    show p.1 • stdVec r + p.2 • stdVec s + (q.1 • stdVec r + q.2 • stdVec s) =
      (p.1 + q.1) • stdVec r + (p.2 + q.2) • stdVec s by rw [add_nsmul, add_nsmul]; abel] at hdeg
  refine hdeg.eq_zero fun hpw => ?_
  have h4 := dot_le_four_of_isPosWt hpw
  rw [dot_comb] at h4
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    first
    | exact hpq rfl
    | (push_cast at h4; rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega)

theorem mat_prod_list {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0) (L : List (ℕ × ℕ))
    (hL : L.Nodup) (hLS : ∀ p ∈ L, p ∈ expS)
    (hLe : ∀ p ∈ expS, p ∉ L → p.1 • α + p.2 • β ∉ roots (isFiniteType_cartanC n) ∅)
    (a : ℕ × ℕ → F) :
    mat n F (L.map fun p => x n F (p.1 • α + p.2 • β) (a p)).prod =
      1 + ∑ p ∈ expS, a p • Ex F (p.1 • α + p.2 • β) := by
  rw [map_list_prod, List.map_map]
  simp only [Function.comp_def, mat_x]
  rw [list_prod_one_add _ L hL fun p hp q hq hpq => by
    rw [smul_mul_smul_comm, Ex_mul_Ex_eq_zero hα hβ hαβ (hLS p hp) (hLS q hq) hpq, smul_zero]]
  congr 1
  rw [← List.sum_toFinset _ hL]
  refine Finset.sum_subset (fun p hp => hLS p (List.mem_toFinset.1 hp)) fun p hp hpL => ?_
  rw [Ex_of_notMem (hLe p hp fun h => hpL (List.mem_toFinset.2 h)), smul_zero]

theorem exp_arith {a b g i j : ℤ} (ha : a = 2 ∨ a = 4) (hb : b = 2 ∨ b = 4)
    (hg : 2 ≤ a + 2 * g + b) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (h : i * i * a + 2 * i * j * g + j * j * b ≤ 4) :
    (i = 1 ∧ j = 1) ∨ (i = 2 ∧ j = 1) ∨ (i = 1 ∧ j = 2) := by
  have hij : 0 ≤ i * j := by positivity
  have key : i * j * (2 - a - b) ≤ i * j * (2 * g) := mul_le_mul_of_nonneg_left (by linarith) hij
  have h' : i * i * a + i * j * (2 - a - b) + j * j * b ≤ 4 := by linarith
  have hb2 : i ≤ 2 ∧ j ≤ 2 := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> constructor <;>
      nlinarith [sq_nonneg (i - j), sq_nonneg (i - 2 * j), sq_nonneg (2 * i - j)]
  obtain ⟨hi2, hj2⟩ := hb2
  interval_cases i <;> interval_cases j <;> rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;> omega

theorem mem_expS_of_mem_expPairs {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0) {p : ℕ × ℕ}
    (hp : p ∈ expPairs (Φ n F) α β) : p ∈ expS := by
  obtain ⟨hp1, hp2, hpr⟩ := hp
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hα
  obtain ⟨s, hs⟩ := exists_stdVec_of_mem_roots hβ
  obtain ⟨t, ht⟩ := exists_stdVec_of_mem_roots hpr
  have hrs : stdVec r + stdVec s ≠ 0 := by
    rw [hr, hs]
    exact toStd_add_ne_zero hαβ
  have h2 := two_le_dot_add hrs
  rw [dot_add_self] at h2
  have htt := dot_stdVec t
  rw [ht, toStd_comb, ← hr, ← hs, dot_comb] at htt
  have key := exp_arith (dot_stdVec r) (dot_stdVec s) h2 (i := p.1) (j := p.2)
    (by exact_mod_cast hp1) (by exact_mod_cast hp2) (by rcases htt with h | h <;> omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
  omega

theorem mem_expPairs_iff {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) (hαβ : α + β ≠ 0) (p : ℕ × ℕ) :
    p ∈ expPairs (Φ n F) α β ↔
      p ∈ expS ∧ p.1 • α + p.2 • β ∈ roots (isFiniteType_cartanC n) ∅ := by
  refine ⟨fun hp => ⟨mem_expS_of_mem_expPairs hα hβ hαβ hp, hp.2.2⟩, fun ⟨hp, hr⟩ => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  refine ⟨?_, ?_, hr⟩ <;> rcases hp with rfl | rfl | rfl <;> norm_num

theorem notMem_roots_of_notMem_list (O : CommOrder (Φ n F)) {α β : Fin n → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC n) ∅) (hβ : β ∈ roots (isFiniteType_cartanC n) ∅)
    (hαβ : α + β ≠ 0) {p : ℕ × ℕ} (hp : p ∈ expS) (hpL : p ∉ O.list α β) :
    p.1 • α + p.2 • β ∉ roots (isFiniteType_cartanC n) ∅ := by
  intro hr
  refine hpL ((O.mem_iff α hα β hβ hαβ p).2 ⟨?_, ?_, hr⟩) <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp <;>
    rcases hp with rfl | rfl | rfl <;> norm_num

theorem mem_expS_of_mem_list (O : CommOrder (Φ n F)) {α β : Fin n → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC n) ∅) (hβ : β ∈ roots (isFiniteType_cartanC n) ∅)
    (hαβ : α + β ≠ 0) {p : ℕ × ℕ} (hp : p ∈ O.list α β) : p ∈ expS :=
  mem_expS_of_mem_expPairs hα hβ hαβ ((O.mem_iff α hα β hβ hαβ p).1 hp)

theorem commutatorFormula (O : CommOrder (Φ n F)) : CommutatorFormula (x n F) O commC := by
  intro α hα β hβ hαβ c d
  apply mat_injective
  rw [mat_commutator hα hβ hαβ c d, mat_prod_list hα hβ hαβ (O.list α β) (O.nodup α β)
    (fun p hp => mem_expS_of_mem_list O hα hβ hαβ hp)
    (fun p hp hpL => notMem_roots_of_notMem_list O hα hβ hαβ hp hpL)]

theorem ne_zero_of_mem_roots {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) :
    γ ≠ 0 := by
  rintro rfl
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  have h := dot_stdVec r
  rw [hr, toStd_zero'] at h
  simp at h

theorem comb_ne {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) {p q : ℕ × ℕ} (hp : p ∈ expS) (hq : q ∈ expS)
    (hpq : p ≠ q) (hr : p.1 • α + p.2 • β ∈ roots (isFiniteType_cartanC n) ∅) :
    p.1 • α + p.2 • β ≠ q.1 • α + q.2 • β := by
  intro h
  have hk : ∀ k, (p.1 : ℤ) * α k + p.2 * β k = q.1 * α k + q.2 * β k := fun k => by
    simpa using congrFun h k
  have hα0 := ne_zero_of_mem_roots hα
  have hβ0 := ne_zero_of_mem_roots hβ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    first
    | exact hpq rfl
    | exact hα0 (funext fun k => by
        have := hk k
        simp only [Pi.zero_apply]
        push_cast at this
        omega)
    | exact hβ0 (funext fun k => by
        have := hk k
        simp only [Pi.zero_apply]
        push_cast at this
        omega)
    | skip
  all_goals
    have hαβ : α = β := funext fun k => by have := hk k; push_cast at this; omega
    subst hαβ
    obtain ⟨r, hr'⟩ := exists_stdVec_of_mem_roots hα
    obtain ⟨t, ht⟩ := exists_stdVec_of_mem_roots hr
    have h3 : toStd n (2 • α + 1 • α) = 3 • stdVec r := by
      rw [toStd_comb, hr', ← add_nsmul]
    have h3' : toStd n (1 • α + 2 • α) = 3 • stdVec r := by
      rw [toStd_comb, hr', ← add_nsmul]
    have htt := dot_stdVec t
    have hrr := dot_stdVec r
    first | rw [ht, h3] at htt | rw [ht, h3'] at htt
    rw [smul_dotProduct, dotProduct_smul, smul_smul] at htt
    simp only [nsmul_eq_mul] at htt
    push_cast at htt
    omega

theorem cast_eq_commC {O : CommOrder (Φ n F)} {C : (Fin n → ℤ) → (Fin n → ℤ) → ℕ × ℕ → ℤ}
    (hC : CommutatorFormula (x n F) O C) {α β : Fin n → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC n) ∅) (hβ : β ∈ roots (isFiniteType_cartanC n) ∅)
    (hαβ : α + β ≠ 0) {p : ℕ × ℕ} (hp : p ∈ expPairs (Φ n F) α β) :
    (C α β p : F) = (commC α β p : F) := by
  have hLS := fun q (hq : q ∈ O.list α β) => mem_expS_of_mem_list O hα hβ hαβ hq
  have hLe := fun q (hq : q ∈ expS) (hqL : q ∉ O.list α β) =>
    notMem_roots_of_notMem_list O hα hβ hαβ hq hqL
  have hmat := congrArg (mat n F)
    ((hC α hα β hβ hαβ 1 1).symm.trans (commutatorFormula O α hα β hβ hαβ 1 1))
  rw [mat_prod_list hα hβ hαβ _ (O.nodup α β) hLS hLe,
    mat_prod_list hα hβ hαβ _ (O.nodup α β) hLS hLe] at hmat
  have hsum := add_left_cancel hmat
  have hpS := mem_expS_of_mem_expPairs hα hβ hαβ hp
  obtain ⟨t, ht⟩ := exists_stdVec_of_mem_roots hp.2.2
  have hent : ∀ a : ℕ × ℕ → F,
      (∑ q ∈ expS, a q • Ex F (q.1 • α + q.2 • β)) (pos1 t).1 (pos1 t).2 = a p := by
    intro a
    rw [Matrix.sum_apply, Finset.sum_eq_single p]
    · rw [Matrix.smul_apply, Ex_eq ht, E_pos1, smul_eq_mul, mul_one]
    · intro q hq hqp
      rw [Matrix.smul_apply]
      by_cases hqr : ∃ t' : RootSubgroupIndex n, stdVec t' = toStd n (q.1 • α + q.2 • β)
      · obtain ⟨t', ht'⟩ := hqr
        have h0 : E F t' (pos1 t).1 (pos1 t).2 = 0 := by
          by_contra hne
          have hw := hasDeg_E t' _ _ hne
          rw [wt_pos1, ht, ht'] at hw
          exact comb_ne hα hβ hpS hq (Ne.symm hqp) hp.2.2 (toStd_inj hw)
        rw [Ex_eq ht', h0, smul_zero]
      · rw [Ex_of_not hqr, Matrix.zero_apply, smul_zero]
    · exact fun h => absurd hpS h
  have h := congrArg (fun M => M (pos1 t).1 (pos1 t).2) hsum
  simp only [hent, one_pow, mul_one] at h
  exact h

theorem commC_natAbs {α β : Fin n → ℤ} (hα : α ∈ roots (isFiniteType_cartanC n) ∅)
    (hβ : β ∈ roots (isFiniteType_cartanC n) ∅) {p : ℕ × ℕ} (hp : p ∈ expPairs (Φ n F) α β) :
    (commC α β p).natAbs = 1 ∨ (commC α β p).natAbs = 2 := by
  by_cases hαβ : α + β = 0
  · rw [commC_eq_zero hαβ]
    exact Or.inl rfl
  have hpS := mem_expS_of_mem_expPairs hα hβ hαβ hp
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hα
  obtain ⟨s, hs⟩ := exists_stdVec_of_mem_roots hβ
  have hrs : stdVec r + stdVec s ≠ 0 := by
    rw [hr, hs]
    exact toStd_add_ne_zero hαβ
  obtain ⟨t, ht⟩ := exists_stdVec_of_mem_roots hp.2.2
  rw [toStd_comb, ← hr, ← hs] at ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpS
  rcases hpS with rfl | rfl | rfl
  · rw [commC_one_one hαβ, Exz_eq hr, Exz_eq hs,
      entryAt_eq _ (ht.trans (by rw [toStd_add', hr, hs, one_smul, one_smul]))]
    rcases coeff11_spec (ht.trans (by rw [one_smul, one_smul])) with h | h
    · exact Or.inl h
    · exact Or.inr h.1
  · rw [commC_two_one hαβ, Exz_eq hr, Exz_eq hs,
      entryAt_eq _ (ht.trans (by rw [toStd_add', toStd_nsmul', hr, hs, one_smul])),
      Matrix.neg_apply, Int.natAbs_neg]
    exact Or.inl (coeff21_spec (ht.trans (by rw [one_smul])) hrs)
  · rw [commC_one_two hαβ, Exz_eq hr, Exz_eq hs,
      entryAt_eq _ (ht.trans (by rw [toStd_add', toStd_nsmul', hr, hs, one_smul]))]
    exact Or.inl (coeff21_spec (ht.trans (by rw [one_smul, add_comm]))
      (by rwa [add_comm]))

theorem commC_natAbs_mem (α : Fin n → ℤ) (hα : α ∈ (Φ n F).roots) (β : Fin n → ℤ)
    (hβ : β ∈ (Φ n F).roots) (p : ℕ × ℕ) (hp : p ∈ expPairs (Φ n F) α β) :
    (commC α β p).natAbs ∈ ({1, 2, 3} : Set ℕ) := by
  rcases commC_natAbs (F := F) hα hβ hp with h | h <;> simp [h]

end CFSG.LieType.Steinberg.Sp
