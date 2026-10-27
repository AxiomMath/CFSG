module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrth
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLProofs

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthMain

open Matrix
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthAlg
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthPow
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthCore
open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [Field R]

public theorem transvection_one_mul_self (h2 : (1 : R) + 1 = 0) {p q : ι} (hpq : p ≠ q) :
    Matrix.SpecialLinearGroup.transvection hpq (1 : R) *
      Matrix.SpecialLinearGroup.transvection hpq (1 : R) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.coe_one]
  have e : single p q (1 : R) + single p q 1 = 0 := by rw [← single_add, h2, single_zero]
  have hSS : single p q (1 : R) * single p q 1 = 0 := by
    simp [single_mul_single_of_ne, hpq.symm]
  calc (1 + single p q (1 : R)) * (1 + single p q 1)
      = 1 + (single p q (1 : R) + single p q 1) + single p q (1 : R) * single p q 1 := by
        noncomm_ring
    _ = 1 := by rw [e, hSS, add_zero, add_zero]

public theorem coe_transvection_pair (p q : ι) (hpq : p ≠ q) :
    ((Matrix.SpecialLinearGroup.transvection hpq (1 : R) *
        Matrix.SpecialLinearGroup.transvection hpq.symm (1 : R) :
          Matrix.SpecialLinearGroup ι R) : Matrix ι ι R) = 1 + Sx R p q := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  exact trans_mul_Sx p q hpq

public theorem cube_eq_one_of_coe (h2 : (1 : R) + 1 = 0) {p q : ι} (hpq : p ≠ q)
    (u : Matrix.SpecialLinearGroup ι R) (hu : (u : Matrix ι ι R) = 1 + Sx R p q) :
    u ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hu, Matrix.SpecialLinearGroup.coe_one, pow_three,
    ← mul_assoc]
  exact w_cube h2 hpq

public theorem ne_one_of_coe {p q : ι} (hpq : p ≠ q) (u : Matrix.SpecialLinearGroup ι R)
    (hu : (u : Matrix ι ι R) = 1 + Sx R p q) : u ≠ 1 := by
  intro h
  have h' : (u : Matrix ι ι R) = 1 := by rw [h, Matrix.SpecialLinearGroup.coe_one]
  have e := congrFun (congrFun (hu.symm.trans h') p) q
  simp [Sx, Matrix.add_apply, hpq, hpq.symm] at e

omit [Fintype ι] in
public theorem one_add_Sx_apply_self {p q : ι} (hpq : p ≠ q) :
    (1 + Sx R p q) p q = 1 := by
  simp [Sx, Matrix.add_apply, hpq, hpq.symm]

omit [Fintype ι] in
public theorem Sx_row_zero {p q a : ι} (ha1 : a ≠ p) (ha2 : a ≠ q) (c : ι) :
    Sx R p q a c = 0 := by
  simp [Sx, ha1.symm, ha2.symm]

public theorem rowFix_mul {a : ι} {g h : Matrix.SpecialLinearGroup ι R}
    (hg : ∀ b, (g : Matrix ι ι R) a b = (1 : Matrix ι ι R) a b)
    (hh : ∀ b, (h : Matrix ι ι R) a b = (1 : Matrix ι ι R) a b) :
    ∀ b, ((g * h : Matrix.SpecialLinearGroup ι R) : Matrix ι ι R) a b =
      (1 : Matrix ι ι R) a b := by
  intro b
  rw [Matrix.SpecialLinearGroup.coe_mul]
  calc ((g : Matrix ι ι R) * (h : Matrix ι ι R)) a b
      = ((1 : Matrix ι ι R) * (h : Matrix ι ι R)) a b := by
        simp only [Matrix.mul_apply, hg]
    _ = (h : Matrix ι ι R) a b := by rw [Matrix.one_mul]
    _ = (1 : Matrix ι ι R) a b := hh b

public theorem rowFix_zpow {a : ι} (u : Matrix.SpecialLinearGroup ι R) (hu3 : u ^ 3 = 1)
    (hu : ∀ b, (u : Matrix ι ι R) a b = (1 : Matrix ι ι R) a b) (k : ℤ) :
    ∀ b, ((u ^ k : Matrix.SpecialLinearGroup ι R) : Matrix ι ι R) a b =
      (1 : Matrix ι ι R) a b := by
  have h3 : u * (u * u) = 1 := by rw [← pow_three]; exact hu3
  have hinv : u⁻¹ = u * u := inv_eq_of_mul_eq_one_right h3
  induction k using Int.induction_on with
  | zero => intro b; simp
  | succ i ih => intro b; rw [_root_.zpow_add_one]; exact rowFix_mul ih hu b
  | pred i ih =>
    intro b
    rw [_root_.zpow_sub_one, hinv]
    exact rowFix_mul ih (rowFix_mul hu hu) b

public theorem not_mem_zpowers_of_row {a b : ι} (u v : Matrix.SpecialLinearGroup ι R)
    (hu3 : u ^ 3 = 1) (hu : ∀ c, (u : Matrix ι ι R) a c = (1 : Matrix ι ι R) a c)
    (hv : (v : Matrix ι ι R) a b ≠ (1 : Matrix ι ι R) a b) :
    v ∉ Subgroup.zpowers u := by
  intro hmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact hv (rowFix_zpow u hu3 hu k b)

public theorem eq_one_of_sq_cube {G : Type*} [Group G] (g : G) (h2 : g * g = 1) (h3 : g ^ 3 = 1) :
    g = 1 := by
  calc g = g * (g * g) := by rw [h2, mul_one]
    _ = g ^ 3 := (pow_three g).symm
    _ = 1 := h3

public theorem coe_mul_of_transvections (h2 : (1 : R) + 1 = 0)
    (hc01 : ∀ c : R, c = 0 ∨ c = 1) {p q : ι} (hpq : p ≠ q)
    (x y : Matrix.SpecialLinearGroup ι R) (c d : R)
    (hx : (x : Matrix ι ι R) = Matrix.transvection p q c)
    (hy : (y : Matrix ι ι R) = Matrix.transvection q p d)
    (hxy3 : (x * y) ^ 3 = 1) (hxy1 : x * y ≠ 1) :
    ((x * y : Matrix.SpecialLinearGroup ι R) : Matrix ι ι R) = 1 + Sx R p q := by
  have hx' : x = Matrix.SpecialLinearGroup.transvection hpq c :=
    Subtype.ext (by rw [Matrix.SpecialLinearGroup.transvection_coe]; exact hx)
  have hy' : y = Matrix.SpecialLinearGroup.transvection hpq.symm d :=
    Subtype.ext (by rw [Matrix.SpecialLinearGroup.transvection_coe]; exact hy)
  rcases hc01 c with rfl | rfl <;> rcases hc01 d with rfl | rfl
  · exfalso
    have hx1 : x = 1 := by
      rw [hx']; apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.coe_one,
        single_zero, add_zero]
    have hy1 : y = 1 := by
      rw [hy']; apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.coe_one,
        single_zero, add_zero]
    exact hxy1 (by rw [hx1, hy1, mul_one])
  · exfalso
    have hx1 : x = 1 := by
      rw [hx']; apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.coe_one,
        single_zero, add_zero]
    rw [hx1, one_mul] at hxy3 hxy1
    have hyy : y * y = 1 := by
      rw [hy']; exact transvection_one_mul_self h2 hpq.symm
    exact hxy1 (eq_one_of_sq_cube y hyy hxy3)
  · exfalso
    have hy1 : y = 1 := by
      rw [hy']; apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.coe_one,
        single_zero, add_zero]
    rw [hy1, mul_one] at hxy3 hxy1
    have hxx : x * x = 1 := by
      rw [hx']; exact transvection_one_mul_self h2 hpq
    exact hxy1 (eq_one_of_sq_cube x hxx hxy3)
  · rw [hx', hy']
    exact coe_transvection_pair p q hpq

public theorem root_pair {m : ℕ} {F : Type} [Field F] (h2 : (1 : F) + 1 = 0) (k : Fin m) :
    ∃ x ∈ (rootDatum m F).rootGroup (Pi.single k 1),
    ∃ y ∈ (rootDatum m F).rootGroup (-Pi.single k 1),
      (x * y) ^ 3 = 1 ∧ x * y ≠ 1 ∧
        ((x * y : Matrix.SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
          = 1 + Sx F k.castSucc k.succ := by
  have hk : k.castSucc ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
  refine ⟨Matrix.SpecialLinearGroup.transvection hk 1,
    RankTwoCoverSL.transvection_mem_of_root hk (toStd_single (m := m) k) 1,
    Matrix.SpecialLinearGroup.transvection hk.symm 1,
    RankTwoCoverSL.transvection_mem_of_root hk.symm (toStd_neg_single (m := m) k) 1,
    cube_eq_one_of_coe h2 hk _ (coe_transvection_pair k.castSucc k.succ hk),
    ne_one_of_coe hk _ (coe_transvection_pair k.castSucc k.succ hk),
    coe_transvection_pair k.castSucc k.succ hk⟩

public theorem coe_mul_root {m : ℕ} {F : Type} [Field F] (hF : Nat.card F = 2)
    (h2 : (1 : F) + 1 = 0) (k : Fin m)
    (x y : Matrix.SpecialLinearGroup (Fin (m + 1)) F)
    (hx : x ∈ (rootDatum m F).rootGroup (Pi.single k 1))
    (hy : y ∈ (rootDatum m F).rootGroup (-Pi.single k 1))
    (hxy3 : (x * y) ^ 3 = 1) (hxy1 : x * y ≠ 1) :
    ((x * y : Matrix.SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      = 1 + Sx F k.castSucc k.succ := by
  obtain ⟨c, hc⟩ := RankTwoCoverSLOrth.mem_rootGroup_single k x hx
  obtain ⟨d, hd⟩ := RankTwoCoverSLOrth.mem_rootGroup_neg_single k y hy
  exact coe_mul_of_transvections h2 (RankTwoCoverSLOrth.eq_zero_or_one_of_card_two hF)
    (Fin.castSucc_lt_succ (i := k)).ne x y c d hc hd hxy3 hxy1

public theorem sl_orth {m : ℕ} {F : Type} [Field F] (hF : Nat.card F = 2) (i j : Fin m)
    (hij : i.val + 2 ≤ j.val) :
    ∃ xi ∈ (rootDatum m F).rootGroup (Pi.single i 1),
    ∃ yi ∈ (rootDatum m F).rootGroup (-Pi.single i 1),
    ∃ xj ∈ (rootDatum m F).rootGroup (Pi.single j 1),
    ∃ yj ∈ (rootDatum m F).rootGroup (-Pi.single j 1),
      (xi * yi) ^ 3 = 1 ∧ xi * yi ≠ 1 ∧ (xj * yj) ^ 3 = 1 ∧ xj * yj ≠ 1 ∧
      xj * yj ∉ Subgroup.zpowers (xi * yi) ∧
      ∀ k : Fin m, ∀ x ∈ (rootDatum m F).rootGroup (Pi.single k 1),
        ∀ y ∈ (rootDatum m F).rootGroup (-Pi.single k 1),
        (x * y) ^ 3 = 1 → x * y ≠ 1 → ∀ g : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
          ∀ e : ℕ, g * (x * y) ^ e * g⁻¹ ≠ xi * yi * (xj * yj) := by
  have h2 : (1 : F) + 1 = 0 := by
    rcases RankTwoCoverSLOrth.eq_zero_or_one_of_card_two hF (1 + 1) with h | h
    · exact h
    · have h1 : (1 : F) = 0 := by linear_combination h
      exact absurd h1 one_ne_zero
  obtain ⟨xi, hxi, yi, hyi, hi3, hi1, hXi⟩ := root_pair h2 i
  obtain ⟨xj, hxj, yj, hyj, hj3, hj1, hXj⟩ := root_pair h2 j
  have hci : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  have hcj : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ (i := j)).ne
  have d1 : i.castSucc ≠ j.castSucc := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc] at this
    omega
  have d2 : i.castSucc ≠ j.succ := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  have d3 : i.succ ≠ j.castSucc := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  have d4 : i.succ ≠ j.succ := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_succ] at this
    omega
  have hT : ((xi * yi * (xj * yj) : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        1 + Sx F i.castSucc i.succ + Sx F j.castSucc j.succ := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hXi, hXj]
    rw [show (1 + Sx F i.castSucc i.succ) * (1 + Sx F j.castSucc j.succ) =
        1 + Sx F i.castSucc i.succ + Sx F j.castSucc j.succ +
          Sx F i.castSucc i.succ * Sx F j.castSucc j.succ by noncomm_ring,
      Sx_disjoint d1 d2 d3 d4, add_zero]
  have hT1 : ((xi * yi * (xj * yj) : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) ≠ 1 := by
    intro h
    rw [hT] at h
    have e := congrFun (congrFun h i.castSucc) i.succ
    rw [Matrix.add_apply, one_add_Sx_apply_self hci,
      Sx_row_zero d1 d2, add_zero, Matrix.one_apply_ne hci] at e
    exact one_ne_zero e
  have hzp : xj * yj ∉ Subgroup.zpowers (xi * yi) := by
    apply not_mem_zpowers_of_row (a := j.castSucc) (b := j.succ) (xi * yi) (xj * yj) hi3
    · intro c
      rw [hXi, Matrix.add_apply, Sx_row_zero d1.symm d3.symm, add_zero]
    · rw [hXj, one_add_Sx_apply_self hcj, Matrix.one_apply_ne hcj]
      exact one_ne_zero
  refine ⟨xi, hxi, yi, hyi, xj, hxj, yj, hyj, hi3, hi1, hj3, hj1, hzp, ?_⟩
  intro k x hx y hy hxy3 hxy1 g e
  have hk : k.castSucc ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
  have hu := coe_mul_root hF h2 k x y hx hy hxy3 hxy1
  have hTtr : trace ((xi * yi * (xj * yj) : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) ≠ trace (1 + Sx F k.castSucc k.succ) := by
    intro h
    rw [hT] at h
    simp only [trace_add, trace_one, trace_Sx i.castSucc i.succ hci,
      trace_Sx j.castSucc j.succ hcj, trace_Sx k.castSucc k.succ hk] at h
    have h1 : (1 : F) = 0 := by linear_combination h
    exact one_ne_zero h1
  exact not_conj_core h2 hk (x * y) (xi * yi * (xj * yj)) hu hxy3 hT1 hTtr g e

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrthMain
