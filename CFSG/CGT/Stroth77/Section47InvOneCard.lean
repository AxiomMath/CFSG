module

public import CFSG.CGT.Stroth77.Section47InvOneAction

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core Stroth34T200

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))
  {e : G}

theorem t200inv1_even_j {j : ℕ} (hj : j = 0 ∨ j = 2 ^ (m + 1)) : Even j := by
  rcases hj with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨2 ^ m, by rw [← two_mul, pow_succ']⟩

theorem t200inv1_not_dvd_j_sub_two {j : ℕ} (hm : 1 ≤ m)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) : ¬ (2 : ℤ) ^ (m + 2) ∣ (j : ℤ) - 2 := by
  intro h
  have h4 := Stroth42Core.two_pow_dvd_four (n := m + 2) (by omega) h
  rcases hj with rfl | rfl
  · norm_num at h4
  · have hpow : (4 : ℤ) ∣ (2 : ℤ) ^ (m + 1) := by
      have h4 : (4 : ℤ) = 2 ^ 2 := by norm_num
      rw [h4]
      exact pow_dvd_pow 2 (by omega : 2 ≤ m + 1)
    have h2 : (4 : ℤ) ∣ 2 := by
      simpa using dvd_sub hpow h4
    norm_num at h2

theorem t200inv1_jm1_sq {j : ℕ} (hj : j = 0 ∨ j = 2 ^ (m + 1)) :
    (2 : ℤ) ^ (m + 2) ∣ ((j : ℤ) - 1) ^ 2 - 1 := by
  rcases hj with rfl | rfl
  · norm_num
  · have hsq : ((2 : ℤ) ^ (m + 1)) ^ 2 = (2 : ℤ) ^ (m + 2) * 2 ^ m := by
      rw [← pow_mul, show (m + 1) * 2 = (m + 2) + m by ring, pow_add]
    refine ⟨(2 : ℤ) ^ m - 1, ?_⟩
    rw [sub_sq]
    push_cast
    rw [hsq]
    ring

theorem t200inv1_dvd_two_pow_succ_of_dvd_j_sub_two {j : ℕ} (hm : 1 ≤ m)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) {x : ℤ}
    (h : (2 : ℤ) ^ (m + 2) ∣ ((j : ℤ) - 2) * x) : (2 : ℤ) ^ (m + 1) ∣ x := by
  rcases hj with rfl | rfl
  · have h' : (2 : ℤ) ^ (m + 2) ∣ 2 * (-x) := by
      convert h using 1
      ring
    rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) by rw [pow_succ']] at h'
    exact dvd_neg.mp ((mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h')
  · have h' : (2 : ℤ) ^ (m + 2) ∣ 2 * ((1 - (2 : ℤ) ^ m) * x) := by
      convert h.neg_right using 1
      push_cast
      rw [show (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ']]
      ring
    rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) by rw [pow_succ']] at h'
    have h'' : (2 : ℤ) ^ (m + 1) ∣ (1 - (2 : ℤ) ^ m) * x :=
      (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h'
    have hodd : Odd (1 - (2 : ℤ) ^ m) := by
      have h2m : Even ((2 : ℤ) ^ m) :=
        (even_two : Even (2 : ℤ)).pow_of_ne_zero (by omega : m ≠ 0)
      exact Odd.sub_even odd_one h2m
    have hunit : IsUnit (((1 - (2 : ℤ) ^ m : ℤ)) : ZMod (2 ^ (m + 1))) :=
      isUnit_intCast_of_odd hodd
    have hzero : (((1 - (2 : ℤ) ^ m) * x : ℤ) : ZMod (2 ^ (m + 1))) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h''
    rw [Int.cast_mul] at hzero
    have hx : ((x : ℤ) : ZMod (2 ^ (m + 1))) = 0 := hunit.mul_right_eq_zero.mp hzero
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx

theorem t200inv1_card_two_torsion_le_two {n : ℕ} (hn : 1 ≤ n) :
    Nat.card {x : ZMod (2 ^ n) // 2 * x = 0} ≤ 2 := by
  classical
  have hle : Nat.card {x : ZMod (2 ^ n) // 2 * x = 0} ≤ Nat.card Bool := by
    refine Nat.card_le_card_of_injective (fun x : {x : ZMod (2 ^ n) // 2 * x = 0} =>
      decide (x.1 = 0)) ?_
    intro x y hxy
    simp only [decide_eq_decide] at hxy
    rcases (zmod_two_mul_eq_zero_iff hn x.1).mp x.2 with hx | hx <;>
      rcases (zmod_two_mul_eq_zero_iff hn y.1).mp y.2 with hy | hy
    · exact Subtype.ext (hx.trans hy.symm)
    · rw [hx, hy] at hxy
      simp at hxy
      exact absurd hxy (two_pow_pred_ne_zero hn)
    · rw [hx, hy] at hxy
      simp at hxy
      exact absurd hxy (two_pow_pred_ne_zero hn)
    · exact Subtype.ext (hx.trans hy.symm)
  have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  rwa [h2] at hle

theorem t200inv1_card_le_mul_card_inf [Finite G] {A : Subgroup G} {ι : Type*} [Finite ι]
    (r : ι → G) (hr : ∀ i, r i ∈ A)
    (hcov : ∀ y ∈ A, ∃ i, y * (r i)⁻¹ ∈ D) :
    Nat.card A ≤ Nat.card ι * Nat.card ↥(A ⊓ D) := by
  have hle := Stroth42Core.natCard_le_of_subset_range
    (f := fun w : ι × ↥(A ⊓ D) => (w.2.1 : G) * r w.1) (E := A) ?_
  · rw [Nat.card_prod ι ↥(A ⊓ D)] at hle
    exact hle
  · intro y hy
    obtain ⟨i, hi⟩ := hcov y hy
    refine ⟨(i, ⟨y * (r i)⁻¹, Subgroup.mem_inf.mpr
      ⟨mul_mem hy (inv_mem (hr i)), hi⟩⟩), ?_⟩
    show (y * (r i)⁻¹) * r i = y
    group

theorem t200inv1_mem_nf {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    ∃ (v : Torus (StrothTypeIndex.t200 m).k) (l k : Bool),
      y = dD.ofTorus v * dD.d8 false false l * bpow e k :=
  t200_eAction_mem_CSc₁ dD (dD.t200inv1EAction hrel)
    (t200inv1_φe_om dD hrel hm (t200inv1_even_j hj) _) hm hy

theorem t200inv1_not_word {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) (i j' l : Bool)
    (h : ∀ v, (dD.t200inv1EAction hrel).φe v =
      (StrothTypeIndex.t200 m).action.d8Act i j' l v) : False := by
  have hf : Even j := t200inv1_even_j hj
  have hc : (StrothTypeIndex.t200 m).action.d8Act i j' l (om200 m ![1, 0, 0]) =
      om200 m ![1, 0, 0] := by
    rw [← h (om200 m ![1, 0, 0]), t200inv1_φe_om dD hrel hm hf]
  have ha : (StrothTypeIndex.t200 m).action.d8Act i j' l (om200 m ![0, 1, 0]) =
      om200 m ![0, 1, 0] := by
    rw [← h (om200 m ![0, 1, 0]), t200inv1_φe_om dD hrel hm hf]
  obtain ⟨rfl, rfl, rfl⟩ := t200_faithful_om hm i j' l hc ha
  have h1 := h (Torus.ofInt _ ![0, 1, 0])
  rw [StrothWeakTypeData.t200inv1_φe dD hrel] at h1
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply] at h1
  rw [t200_ofInt_eq_iff] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h1
  obtain ⟨-, hcoord, -⟩ := h1
  apply t200inv1_not_dvd_j_sub_two (m := m) hm hj
  rw [show (j : ℤ) - 2 = -(1 - (-1 + (j : ℤ))) by ring]
  exact dvd_neg.mpr (by simpa [mul_one] using hcoord)

theorem t200inv1_card_le_four_mul_card_inf [Finite G] {j p : ℕ} (hm : 1 ≤ m)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 p) {A : Subgroup G}
    (hA : A ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    Nat.card A ≤ 4 * Nat.card ↥(A ⊓ D) := by
  classical
  let r : Bool × Bool → G := fun lk =>
    if h : ∃ y ∈ A, ∃ v : Torus (StrothTypeIndex.t200 m).k,
        y = dD.ofTorus v * dD.d8 false false lk.1 * bpow e lk.2 then h.choose else 1
  have hr : ∀ lk, r lk ∈ A := by
    intro lk
    simp only [r]
    split_ifs with h
    · exact h.choose_spec.1
    · exact A.one_mem
  have hcov : ∀ y ∈ A, ∃ lk, y * (r lk)⁻¹ ∈ D := by
    intro y hy
    obtain ⟨v, l, k, rfl⟩ := t200inv1_mem_nf dD hm hj hrel (hA hy)
    refine ⟨(l, k), ?_⟩
    have h : ∃ y ∈ A, ∃ v : Torus (StrothTypeIndex.t200 m).k,
        y = dD.ofTorus v * dD.d8 false false l * bpow e k :=
      ⟨_, hy, v, rfl⟩
    simp only [r, h, dite_true]
    obtain ⟨-, v', hv'⟩ := h.choose_spec
    rw [hv']
    exact nfe_mul_inv_mem dD v v' l k
  have h := t200inv1_card_le_mul_card_inf r hr hcov
  have h4 : Nat.card (Bool × Bool) = 4 := by simp [Nat.card_eq_fintype_card]
  rwa [h4] at h

theorem t200inv1_card_le_two_mul_card_inf [Finite G] {A : Subgroup G}
    (hNF : ∀ y ∈ A, ∃ (v : Torus (StrothTypeIndex.t200 m).k) (k : Bool),
      y = dD.ofTorus v * bpow e k) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ D) := by
  classical
  let r : Bool → G := fun k =>
    if h : ∃ y ∈ A, ∃ v : Torus (StrothTypeIndex.t200 m).k,
        y = dD.ofTorus v * bpow e k then h.choose else 1
  have hr : ∀ k, r k ∈ A := by
    intro k
    simp only [r]
    split_ifs with h
    · exact h.choose_spec.1
    · exact A.one_mem
  have hcov : ∀ y ∈ A, ∃ k, y * (r k)⁻¹ ∈ D := by
    intro y hy
    obtain ⟨v, k, rfl⟩ := hNF y hy
    refine ⟨k, ?_⟩
    have h : ∃ y ∈ A, ∃ v : Torus (StrothTypeIndex.t200 m).k,
        y = dD.ofTorus v * bpow e k := ⟨_, hy, v, rfl⟩
    simp only [r, h, dite_true]
    obtain ⟨-, v', hv'⟩ := h.choose_spec
    rw [hv']
    have hd : dD.ofTorus v * bpow e k * (dD.ofTorus v' * bpow e k)⁻¹ =
        dD.ofTorus v * (dD.ofTorus v')⁻¹ := by group
    rw [hd]
    exact mul_mem (dD.ofTorus_mem _) (inv_mem (dD.ofTorus_mem _))
  have h := t200inv1_card_le_mul_card_inf r hr hcov
  have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  rwa [h2] at h

theorem t200inv1_card_le_eight_of_two_zsmul [Finite G] {A : Subgroup G} (hm : 1 ≤ m)
    (hAD : A ≤ D)
    (h2 : ∀ y ∈ A, ∀ v : Torus (StrothTypeIndex.t200 m).k, y = dD.ofTorus v →
      v + v = 0) : Nat.card A ≤ 8 := by
  classical
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  have : NeZero (2 ^ (m + 2)) := ⟨by positivity⟩
  let P₀ := {x : ZMod (2 ^ m) // 2 * x = 0}
  let P₁ := {x : ZMod (2 ^ (m + 2)) // 2 * x = 0}
  let f : P₀ × (P₁ × P₁) → G := fun p =>
    dD.ofTorus (Torus.ofInt _ ![(p.1.1.val : ℤ), (p.2.1.1.val : ℤ), (p.2.2.1.val : ℤ)])
  have hsurj : ∀ y ∈ A, ∃ p, f p = y := by
    intro y hy
    obtain ⟨v, hv⟩ := dD.exists_ofTorus (hAD hy)
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
    have h2x : Torus.ofInt (StrothTypeIndex.t200 m).k x +
        Torus.ofInt (StrothTypeIndex.t200 m).k x = 0 := by
      exact h2 y hy _ hv
    have h2x' : Torus.ofInt (StrothTypeIndex.t200 m).k (x + x) = 0 := by
      simpa using h2x
    rw [t200_ofInt_eq_zero_iff] at h2x'
    obtain ⟨h0, h1, h2'⟩ := h2x'
    have hx0 : 2 * ((x 0 : ℤ) : ZMod (2 ^ m)) = 0 := by
      have hd : ((2 * x 0 : ℤ) : ZMod (2 ^ m)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        simpa [Pi.add_apply, two_mul] using h0
      push_cast at hd
      exact hd
    have hx1 : 2 * ((x 1 : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      have hd : ((2 * x 1 : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        simpa [Pi.add_apply, two_mul] using h1
      push_cast at hd
      exact hd
    have hx2 : 2 * ((x 2 : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      have hd : ((2 * x 2 : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        simpa [Pi.add_apply, two_mul] using h2'
      push_cast at hd
      exact hd
    refine ⟨(⟨(x 0 : ZMod (2 ^ m)), hx0⟩,
      ⟨(x 1 : ZMod (2 ^ (m + 2))), hx1⟩, ⟨(x 2 : ZMod (2 ^ (m + 2))), hx2⟩), ?_⟩
    rw [hv]
    dsimp only [f]
    congr 1
    rw [t200_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    exact ⟨by
      have h := (Stroth44Core.dvd_sub_val (2 ^ m) (x 0)).neg_right
      push_cast at h
      simpa only [neg_sub] using h,
      by
      have h := (Stroth44Core.dvd_sub_val (2 ^ (m + 2)) (x 1)).neg_right
      push_cast at h
      simpa only [neg_sub] using h,
      by
      have h := (Stroth44Core.dvd_sub_val (2 ^ (m + 2)) (x 2)).neg_right
      push_cast at h
      simpa only [neg_sub] using h⟩
  have hle := Stroth42Core.natCard_le_of_subset_range f hsurj
  have h0 : Nat.card P₀ ≤ 2 := t200inv1_card_two_torsion_le_two hm
  have h1 : Nat.card P₁ ≤ 2 := t200inv1_card_two_torsion_le_two (by omega)
  change Nat.card A ≤ Nat.card (P₀ × (P₁ × P₁)) at hle
  rw [Nat.card_prod, Nat.card_prod] at hle
  calc Nat.card A ≤ Nat.card P₀ * (Nat.card P₁ * Nat.card P₁) := hle
    _ ≤ 2 * (2 * 2) := Nat.mul_le_mul h0 (Nat.mul_le_mul h1 h1)
    _ = 8 := by norm_num

theorem t200inv1_card_le_four_of_fix_u [Finite G] {A : Subgroup G} (hm : 1 ≤ m)
    (hAD : A ≤ D)
    (h2 : ∀ y ∈ A, ∀ v : Torus (StrothTypeIndex.t200 m).k, y = dD.ofTorus v →
      v + v = 0)
    (hfix : ∀ y ∈ A, ∀ v : Torus (StrothTypeIndex.t200 m).k, y = dD.ofTorus v →
      (StrothTypeIndex.t200 m).action.d8Act false false true v = v) :
    Nat.card A ≤ 4 := by
  classical
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  have : NeZero (2 ^ (m + 2)) := ⟨by positivity⟩
  let P₀ := {x : ZMod (2 ^ m) // 2 * x = 0}
  let P₁ := {x : ZMod (2 ^ (m + 2)) // 2 * x = 0}
  let f : P₀ × P₁ → G := fun p =>
    dD.ofTorus (Torus.ofInt _ ![(p.1.1.val : ℤ), (p.2.1.val : ℤ), (p.2.1.val : ℤ)])
  have hsurj : ∀ y ∈ A, ∃ p, f p = y := by
    intro y hy
    obtain ⟨v, hv⟩ := dD.exists_ofTorus (hAD hy)
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
    have h2x : Torus.ofInt (StrothTypeIndex.t200 m).k x +
        Torus.ofInt (StrothTypeIndex.t200 m).k x = 0 := by
      exact h2 y hy _ hv
    have hfx : (StrothTypeIndex.t200 m).action.d8Act false false true
        (Torus.ofInt (StrothTypeIndex.t200 m).k x) = Torus.ofInt _ x := by
      exact hfix y hy _ hv
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hfx
    rw [t200_φu, t200_ofInt_eq_iff] at hfx
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hfx
    obtain ⟨-, hx12, -⟩ := hfx
    have h2x' : Torus.ofInt (StrothTypeIndex.t200 m).k (x + x) = 0 := by
      simpa using h2x
    rw [t200_ofInt_eq_zero_iff] at h2x'
    obtain ⟨h0, h1, -⟩ := h2x'
    have hx0 : 2 * ((x 0 : ℤ) : ZMod (2 ^ m)) = 0 := by
      have hd : ((2 * x 0 : ℤ) : ZMod (2 ^ m)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        simpa [Pi.add_apply, two_mul] using h0
      push_cast at hd
      exact hd
    have hx1 : 2 * ((x 1 : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
      have hd : ((2 * x 1 : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        simpa [Pi.add_apply, two_mul] using h1
      push_cast at hd
      exact hd
    refine ⟨(⟨(x 0 : ZMod (2 ^ m)), hx0⟩,
      ⟨(x 1 : ZMod (2 ^ (m + 2))), hx1⟩), ?_⟩
    rw [hv]
    dsimp only [f]
    congr 1
    rw [t200_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨by
      have h := (Stroth44Core.dvd_sub_val (2 ^ m) (x 0)).neg_right
      push_cast at h
      simpa only [neg_sub] using h,
      by
      have h := (Stroth44Core.dvd_sub_val (2 ^ (m + 2)) (x 1)).neg_right
      push_cast at h
      simpa only [neg_sub] using h, ?_⟩
    have hx12' : (2 : ℤ) ^ (m + 2) ∣ x 1 - x 2 := hx12
    have h := (dvd_add (Stroth44Core.dvd_sub_val (2 ^ (m + 2)) (x 1)) hx12').neg_right
    push_cast at h
    convert h using 1; ring_nf
  have hle := Stroth42Core.natCard_le_of_subset_range f hsurj
  have h0 : Nat.card P₀ ≤ 2 := t200inv1_card_two_torsion_le_two hm
  have h1 : Nat.card P₁ ≤ 2 := t200inv1_card_two_torsion_le_two (by omega)
  change Nat.card A ≤ Nat.card (P₀ × P₁) at hle
  rw [Nat.card_prod] at hle
  calc Nat.card A ≤ Nat.card P₀ * Nat.card P₁ := hle
    _ ≤ 2 * 2 := Nat.mul_le_mul h0 h1
    _ = 4 := by norm_num

theorem t200inv1_card_le_of_fix_ue [Finite G] {j p : ℕ} (hm : 1 ≤ m)
    (hrel : Rel34inv dD e j 1 p) {A : Subgroup G} (hAD : A ≤ D)
    (hfix : ∀ y ∈ A, ∀ v : Torus (StrothTypeIndex.t200 m).k, y = dD.ofTorus v →
      (StrothTypeIndex.t200 m).action.d8Act false false true
        ((dD.t200inv1EAction hrel).φe v) = v) :
    Nat.card A ≤ 2 ^ (m + 3) := by
  classical
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  have : NeZero (2 ^ (m + 2)) := ⟨by positivity⟩
  let P₀ := {x : ZMod (2 ^ m) // 2 * x = 0}
  let f : P₀ × ZMod (2 ^ (m + 2)) → G := fun p =>
    dD.ofTorus (Torus.ofInt _ ![(p.1.1.val : ℤ), ((j : ℤ) - 1) * (p.2.val : ℤ), (p.2.val : ℤ)])
  have hsurj : ∀ y ∈ A, ∃ p, f p = y := by
    intro y hy
    obtain ⟨v, hv⟩ := dD.exists_ofTorus (hAD hy)
    obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
    have hfx : (StrothTypeIndex.t200 m).action.d8Act false false true
        ((dD.t200inv1EAction hrel).φe (Torus.ofInt (StrothTypeIndex.t200 m).k x)) =
          Torus.ofInt _ x := by
      exact hfix y hy _ hv
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
      AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hfx
    rw [StrothWeakTypeData.t200inv1_φe dD hrel, t200_φu, t200_ofInt_eq_iff] at hfx
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hfx
    obtain ⟨hx0, hx12, -⟩ := hfx
    have hx0' : 2 * ((x 0 : ℤ) : ZMod (2 ^ m)) = 0 := by
      have hd : ((2 * x 0 : ℤ) : ZMod (2 ^ m)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        rw [show (2 : ℤ) * x 0 = x 0 - -x 0 by ring]
        exact hx0
      push_cast at hd
      exact hd
    refine ⟨(⟨(x 0 : ZMod (2 ^ m)), hx0'⟩, (x 2 : ZMod (2 ^ (m + 2)))), ?_⟩
    rw [hv]
    dsimp only [f]
    congr 1
    rw [t200_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨by
      have h := (Stroth44Core.dvd_sub_val (2 ^ m) (x 0)).neg_right
      push_cast at h
      simpa only [neg_sub] using h, ?_, by
      have h := (Stroth44Core.dvd_sub_val (2 ^ (m + 2)) (x 2)).neg_right
      push_cast at h
      simpa only [neg_sub] using h⟩
    · have hzx : (2 : ℤ) ^ (m + 2) ∣ ((x 2 : ZMod (2 ^ (m + 2))).val : ℤ) - x 2 :=
        Stroth44Core.dvd_sub_val (2 ^ (m + 2)) (x 2)
      have h1 : (2 : ℤ) ^ (m + 2) ∣ ((j : ℤ) - 1) *
          (((x 2 : ZMod (2 ^ (m + 2))).val : ℤ) - x 2) :=
        dvd_mul_of_dvd_right hzx _
      have h2 : (2 : ℤ) ^ (m + 2) ∣ ((j : ℤ) - 1) * x 2 - x 1 := by
        rw [show ((j : ℤ) - 1) * x 2 - x 1 = -(x 1 - ((j : ℤ) - 1) * x 2) by ring]
        exact dvd_neg.mpr hx12
      have h := (dvd_add h1 h2).neg_right
      convert h using 1; ring_nf
  have hle := Stroth42Core.natCard_le_of_subset_range f hsurj
  have h0 : Nat.card P₀ ≤ 2 := t200inv1_card_two_torsion_le_two hm
  have h1 : Nat.card (ZMod (2 ^ (m + 2))) = 2 ^ (m + 2) := Nat.card_zmod (2 ^ (m + 2))
  change Nat.card A ≤ Nat.card (P₀ × ZMod (2 ^ (m + 2))) at hle
  rw [Nat.card_prod, h1] at hle
  calc Nat.card A ≤ Nat.card P₀ * 2 ^ (m + 2) := hle
    _ ≤ 2 * 2 ^ (m + 2) := Nat.mul_le_mul_right _ h0
    _ = 2 ^ (m + 3) := by ring

theorem t200inv1_not_dvd_two_pow_pred (hm : 1 ≤ m) :
    ¬ (2 : ℤ) ^ m ∣ (2 : ℤ) ^ (m - 1) := by
  intro h
  have hpos : (0 : ℤ) < 2 ^ (m - 1) := by positivity
  have hle := Int.le_of_dvd hpos h
  have hlt : (2 : ℤ) ^ (m - 1) < 2 ^ m := by
    exact pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) (by omega : m - 1 < m)
  omega

theorem t200inv1_bool_eq_of_dvd (hm : 1 ≤ m) {b b' : Bool}
    (h : (2 : ℤ) ^ m ∣ (if b then (2 : ℤ) ^ (m - 1) else 0) -
      (if b' then (2 : ℤ) ^ (m - 1) else 0)) : b = b' := by
  cases b <;> cases b'
  · rfl
  · exfalso
    exact t200inv1_not_dvd_two_pow_pred hm (by simpa using h)
  · exfalso
    exact t200inv1_not_dvd_two_pow_pred hm (by simpa using h.neg_right)
  · rfl

theorem t200inv1_e_comm_u {j p : ℕ} (hrel : Rel34inv dD e j 1 p) :
    e * dD.u = dD.u * e := by
  have he : e⁻¹ = e := inv_eq_of_mul_eq_one_right hrel.e_sq
  have h := hrel.u_conj
  rw [he] at h
  calc e * dD.u = (e * dD.u) * (e * e) := by rw [hrel.e_sq, mul_one]
    _ = (e * dD.u * e) * e := by group
    _ = dD.u * e := by rw [h]

theorem t200inv1_u_comm_ue {j p : ℕ} (hrel : Rel34inv dD e j 1 p) :
    dD.u * (dD.u * e) = (dD.u * e) * dD.u := by
  have heu := t200inv1_e_comm_u dD hrel
  calc dD.u * (dD.u * e) = (dD.u * dD.u) * e := by group
    _ = e := by rw [dD.u_sq, one_mul]
    _ = (dD.u * e) * dD.u := by rw [mul_assoc, heu, ← mul_assoc, dD.u_sq, one_mul]

theorem t200inv1_e_comm_ue {j p : ℕ} (hrel : Rel34inv dD e j 1 p) :
    e * (dD.u * e) = (dD.u * e) * e := by
  rw [← mul_assoc, t200inv1_e_comm_u dD hrel]

theorem t200inv1_u_comm_c₁ :
    dD.u * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * dD.u := by
  rw [dD.t200_c_pow]
  have h := dD.u_mul_ofTorus (om200 m ![1, 0, 0])
  rwa [t200_φu_om] at h

theorem t200inv1_φe_c₁ {j p : ℕ} (hm : 1 ≤ m) (hrel : Rel34inv dD e j 1 p) :
    (dD.t200inv1EAction hrel).φe (om200 m ![1, 0, 0]) = om200 m ![1, 0, 0] := by
  rw [om200_apply, StrothWeakTypeData.t200inv1_φe]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, one_mul, zero_mul, mul_zero]
  rw [t200_ofInt_eq_iff]
  refine ⟨?_, by simp, by simp⟩
  simp only [Matrix.cons_val_zero]
  have h2 : (2 : ℤ) ^ (m - 1) - (-(2 : ℤ) ^ (m - 1)) = (2 : ℤ) ^ m := by
    have h := congrArg (fun k => (2 : ℤ) ^ k) (show m = (m - 1) + 1 by omega)
    rw [pow_add] at h
    rw [h]
    ring
  rw [h2]

theorem t200inv1_e_comm_c₁ {j p : ℕ} (hm : 1 ≤ m) (hrel : Rel34inv dD e j 1 p) :
    e * (dD.c : G) ^ 2 ^ (m - 1) = (dD.c : G) ^ 2 ^ (m - 1) * e := by
  rw [dD.t200_c_pow]
  have h := (dD.t200inv1EAction hrel).e_mul_ofTorus (om200 m ![1, 0, 0])
  rwa [t200inv1_φe_c₁ dD hm hrel] at h

theorem t200inv1_u_mem_T :
    dD.u ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} := by
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_), ?_⟩
  · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact t200inv1_u_comm_c₁ dD

theorem t200inv1_e_mem_T {j p : ℕ} (hm : 1 ≤ m) (hrel : Rel34inv dD e j 1 p) :
    e ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} := by
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers e), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact t200inv1_e_comm_c₁ dD hm hrel

theorem t200inv1_comm_ue_ofTorus {j p : ℕ} (hrel : Rel34inv dD e j 1 p)
    (v : Torus (StrothTypeIndex.t200 m).k)
    (hfix : (StrothTypeIndex.t200 m).action.d8Act false false true
      ((dD.t200inv1EAction hrel).φe v) = v) :
    dD.ofTorus v * (dD.u * e) = (dD.u * e) * dD.ofTorus v := by
  let hE := dD.t200inv1EAction hrel
  have h := (t200_e_comm_iff dD hE 0 v true true).mpr hfix
  simpa [dD.ofTorus_zero, dD.d8_fft, bpow] using h

theorem t200inv1_fix_ue_bool {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) (b : Bool) (z : ZMod (2 ^ (m + 2))) :
    (StrothTypeIndex.t200 m).action.d8Act false false true
        ((dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![
          (if b then (2 : ℤ) ^ (m - 1) else 0), ((j : ℤ) - 1) * (z.val : ℤ), (z.val : ℤ)])) =
      Torus.ofInt _ ![(if b then (2 : ℤ) ^ (m - 1) else 0),
        ((j : ℤ) - 1) * (z.val : ℤ), (z.val : ℤ)] := by
  rw [StrothWeakTypeData.t200inv1_φe dD hrel]
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, t200_φu]
  rw [t200_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · cases b
    · norm_num
    · simp only [↓reduceIte]
      have h : (2 : ℤ) ^ (m - 1) - -2 ^ (m - 1) = 2 ^ m := by
        conv_rhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
        ring
      rw [h]
  · convert dvd_zero ((2 : ℤ) ^ (m + 2)) using 1
    ring
  · have h := t200inv1_jm1_sq (m := m) hj
    have h' : (2 : ℤ) ^ (m + 2) ∣ ((j : ℤ) - 1) ^ 2 - 1 := h
    have h'' : (2 : ℤ) ^ (m + 2) ∣
        -(((j : ℤ) - 1) ^ 2 - 1) * (z.val : ℤ) := by
      have h1 : (2 : ℤ) ^ (m + 2) ∣ ((j : ℤ) - 1) ^ 2 - 1 := h'
      have h2 : (2 : ℤ) ^ (m + 2) ∣
          (((j : ℤ) - 1) ^ 2 - 1) * (z.val : ℤ) := dvd_mul_of_dvd_left h1 _
      rw [neg_mul]
      exact dvd_neg.mpr h2
    convert h'' using 1
    ring

theorem t200inv1_card_le_sixteen [Finite G] {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) {A : Subgroup G}
    (hA : A ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)})
    (hA2 : ∀ x ∈ A, x * x = 1) :
    Nat.card A ≤ 16 := by
  classical
  let hE := dD.t200inv1EAction hrel
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have h1 := inv_eq_of_mul_eq_one_right (hA2 a ha)
    have h2 := inv_eq_of_mul_eq_one_right (hA2 b hb)
    have h3 := inv_eq_of_mul_eq_one_right (hA2 _ (mul_mem ha hb))
    calc a * b = (a * b)⁻¹ := h3.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [h1, h2]
  have htwo : ∀ y ∈ A ⊓ D, ∀ v : Torus (StrothTypeIndex.t200 m).k,
      y = dD.ofTorus v → v + v = 0 := by
    intro y hy v hyv
    have hyy := hA2 y hy.1
    rw [hyv, dD.ofTorus_mul_self, dD.ofTorus_eq_one_iff] at hyy
    exact hyy
  have hA8 : Nat.card ↥(A ⊓ D) ≤ 8 :=
    t200inv1_card_le_eight_of_two_zsmul dD hm inf_le_right htwo
  by_cases hl : ∃ x ∈ A, ∃ (v : Torus (StrothTypeIndex.t200 m).k) (k : Bool),
      x = dD.ofTorus v * dD.d8 false false true * bpow e k
  · have hA4 : Nat.card ↥(A ⊓ D) ≤ 4 := by
      refine t200inv1_card_le_four_of_fix_u dD hm inf_le_right htwo ?_
      intro y hy w hyw
      obtain ⟨x, hxA, v₀, k, hx⟩ := hl
      have hc := (t200_e_comm_iff dD hE v₀ w true k).mp (by
        simpa [hyw, hx] using (hcomm x hxA y hy.1).symm)
      have hw2 : (2 : ℤ) • w = 0 := by
        rw [two_zsmul]
        exact htwo y hy w hyw
      obtain ⟨ε, hε, rfl⟩ :=
        (Torus.two_zsmul_eq_zero_iff (t200_one_le_k hm) w).mp hw2
      have hφ : hE.φe (Torus.ofInt _ (fun i => ε i * 2 ^ ((StrothTypeIndex.t200 m).k i - 1))) =
          Torus.ofInt _ (fun i => ε i * 2 ^ ((StrothTypeIndex.t200 m).k i - 1)) := by
        simpa [om200] using t200inv1_φe_om dD hrel hm (t200inv1_even_j hj) ε
      rw [hφ] at hc
      simpa [SigmaFourAction.d8Act] using hc
    have hfour := t200inv1_card_le_four_mul_card_inf dD hm hj hrel hA
    calc Nat.card A ≤ 4 * Nat.card ↥(A ⊓ D) := hfour
      _ ≤ 4 * 4 := Nat.mul_le_mul_left 4 hA4
      _ = 16 := by norm_num
  · have hNF : ∀ y ∈ A, ∃ (v : Torus (StrothTypeIndex.t200 m).k) (k : Bool),
        y = dD.ofTorus v * bpow e k := by
      intro y hy
      obtain ⟨v, l, k, rfl⟩ := t200inv1_mem_nf dD hm hj hrel (hA hy)
      cases l
      · exact ⟨v, k, by rw [dD.d8_fff, mul_one]⟩
      · exact absurd ⟨_, hy, v, k, rfl⟩ hl
    have htwo' := t200inv1_card_le_two_mul_card_inf dD hNF
    calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ D) := htwo'
      _ ≤ 2 * 8 := Nat.mul_le_mul_left 2 hA8
      _ = 16 := by norm_num

theorem t200inv1_two_zsmul_of_fix_e {j p : ℕ} (hm : 1 ≤ m)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 p)
    {w : Torus (StrothTypeIndex.t200 m).k}
    (h : (dD.t200inv1EAction hrel).φe w = w) : w + w = 0 := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
  rw [StrothWeakTypeData.t200inv1_φe dD hrel, t200_ofInt_eq_iff] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h
  obtain ⟨h0, h1, h2⟩ := h
  have h0' : (2 : ℤ) ^ m ∣ 2 * x 0 := by
    convert h0 using 1
    ring
  have h1' : (2 : ℤ) ^ (m + 2) ∣ ((j : ℤ) - 2) * x 1 := by
    convert h1.neg_right using 1
    ring
  have h2' : (2 : ℤ) ^ (m + 2) ∣ ((j : ℤ) - 2) * x 2 := by
    convert h2.neg_right using 1
    ring
  obtain ⟨c1, hc1⟩ :=
    t200inv1_dvd_two_pow_succ_of_dvd_j_sub_two (m := m) (j := j) hm hj h1'
  obtain ⟨c2, hc2⟩ :=
    t200inv1_dvd_two_pow_succ_of_dvd_j_sub_two (m := m) (j := j) hm hj h2'
  have hxx : Torus.ofInt (StrothTypeIndex.t200 m).k (x + x) = 0 := by
    rw [t200_ofInt_eq_zero_iff]
    refine ⟨?_, ?_, ?_⟩
    · simpa [Pi.add_apply, two_mul] using h0'
    · refine ⟨c1, ?_⟩
      rw [show (x + x) 1 = 2 * x 1 by simp [two_mul], hc1]
      rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) by rw [pow_succ']]
      ring
    · refine ⟨c2, ?_⟩
      rw [show (x + x) 2 = 2 * x 2 by simp [two_mul], hc2]
      rw [show (2 : ℤ) ^ (m + 2) = 2 * 2 ^ (m + 1) by rw [pow_succ']]
      ring
  simpa using hxx

theorem t200inv1_card_inf_centralizer_e_le_eight [Finite G] {j p : ℕ} (hm : 1 ≤ m)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 p)
    (v₀ : Torus (StrothTypeIndex.t200 m).k) :
    Nat.card ↥(D ⊓ Subgroup.centralizer
      {dD.ofTorus v₀ * dD.d8 false false false * bpow e true}) ≤ 8 := by
  classical
  let hE := dD.t200inv1EAction hrel
  refine t200inv1_card_le_eight_of_two_zsmul dD hm inf_le_left ?_
  intro d hd w hw
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).2
  have hc := (t200_e_comm_iff dD hE v₀ w false true).mp (by
    simpa [hw] using hcomm)
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hc
  exact t200inv1_two_zsmul_of_fix_e dD hm hj hrel hc

theorem t200inv1_card_inf_centralizer_ue_le [Finite G] {j p : ℕ} (hm : 1 ≤ m)
    (hrel : Rel34inv dD e j 1 p) (v₀ : Torus (StrothTypeIndex.t200 m).k) :
    Nat.card ↥(D ⊓ Subgroup.centralizer
      {dD.ofTorus v₀ * dD.d8 false false true * bpow e true}) ≤ 2 ^ (m + 3) := by
  classical
  let hE := dD.t200inv1EAction hrel
  refine t200inv1_card_le_of_fix_ue dD hm hrel inf_le_left ?_
  intro d hd w hw
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).2
  have hc := (t200_e_comm_iff dD hE v₀ w true true).mp (by
    simpa [hw] using hcomm)
  exact hc

theorem t200inv1_card_inf_centralizer_mul_e_le [Finite G] {j p : ℕ} (hm : 1 ≤ m)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 p)
    (v₀ : Torus (StrothTypeIndex.t200 m).k) (l : Bool) :
    Nat.card ↥(D ⊓ Subgroup.centralizer
      {dD.ofTorus v₀ * dD.d8 false false l * bpow e true}) ≤ 2 ^ (m + 3) := by
  cases l
  · exact (t200inv1_card_inf_centralizer_e_le_eight dD hm hj hrel v₀).trans
      (by
        have h2 : (2 : ℕ) ^ 3 ≤ 2 ^ (m + 3) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        simpa using h2)
  · exact t200inv1_card_inf_centralizer_ue_le dD hm hrel v₀

theorem t200inv1_mem_of_not_mem_Du {j p : ℕ} (hm : 1 ≤ m)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 p) {y : G}
    (hyT : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)})
    (hyDu : y ∉ D ⊔ Subgroup.zpowers dD.u) :
    ∃ (v : Torus (StrothTypeIndex.t200 m).k) (l : Bool),
      y = dD.ofTorus v * dD.d8 false false l * bpow e true := by
  obtain ⟨v, l, k, rfl⟩ := t200inv1_mem_nf dD hm hj hrel hyT
  cases k
  · exfalso
    apply hyDu
    simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one]
    refine mul_mem (Subgroup.mem_sup_left (dD.ofTorus_mem v)) ?_
    cases l
    · rw [dD.d8_fff]; exact Subgroup.one_mem _
    · rw [dD.d8_fft]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers dD.u)
  · exact ⟨v, l, rfl⟩

theorem t200inv1_card_centralizer_ue_ge [Finite G] {j p : ℕ} (hm : 1 ≤ m)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 p) :
    4 * 2 ^ (m + 3) ≤
      Nat.card ((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} ⊓
          Subgroup.centralizer {dD.u * e} : Subgroup G) := by
  classical
  let hE := dD.t200inv1EAction hrel
  let S := D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e
  let T := S ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}
  let U := T ⊓ Subgroup.centralizer {dD.u * e}
  have hDT : D ≤ T := by
    intro d hd
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_left hd), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : IsMulCommutative D := dD.isMulCommutative
    exact Subgroup.mul_comm_of_mem_isMulCommutative D hd (D.pow_mem dD.c.2 _)
  have hmemU : ∀ p : (Bool × Bool) × (Bool × ZMod (2 ^ (m + 2))), 
      dD.ofTorus (Torus.ofInt _ ![(if p.2.1 then (2 : ℤ) ^ (m - 1) else 0),
        ((j : ℤ) - 1) * (p.2.2.val : ℤ), (p.2.2.val : ℤ)]) *
        dD.d8 false false p.1.1 * bpow e p.1.2 ∈ U := by
    intro p
    set v : Torus (StrothTypeIndex.t200 m).k := Torus.ofInt _ ![
      (if p.2.1 then (2 : ℤ) ^ (m - 1) else 0),
      ((j : ℤ) - 1) * (p.2.2.val : ℤ), (p.2.2.val : ℤ)] with hv
    have hS1 : dD.ofTorus v ∈ S := Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (dD.ofTorus_mem v))
    have hS2 : dD.d8 false false p.1.1 ∈ S := Subgroup.mem_sup_left
      (Subgroup.mem_sup_right (dD.d8_mem _ _ _))
    have hS3 : bpow e p.1.2 ∈ S := by
      cases p.1.2
      · exact S.one_mem
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
    have hc1_1 : dD.ofTorus v * (dD.c : G) ^ 2 ^ (m - 1) =
        (dD.c : G) ^ 2 ^ (m - 1) * dD.ofTorus v := by
      have : IsMulCommutative D := dD.isMulCommutative
      exact Subgroup.mul_comm_of_mem_isMulCommutative D (dD.ofTorus_mem v)
        (D.pow_mem dD.c.2 _)
    have hc1_2 : dD.d8 false false p.1.1 * (dD.c : G) ^ 2 ^ (m - 1) =
        (dD.c : G) ^ 2 ^ (m - 1) * dD.d8 false false p.1.1 := by
      cases p.1.1
      · rw [dD.d8_fff, one_mul, mul_one]
      · rw [dD.d8_fft]
        exact t200inv1_u_comm_c₁ dD
    have hc1_3 : bpow e p.1.2 * (dD.c : G) ^ 2 ^ (m - 1) =
        (dD.c : G) ^ 2 ^ (m - 1) * bpow e p.1.2 := by
      cases p.1.2
      · simp [bpow]
      · simpa [bpow] using t200inv1_e_comm_c₁ dD hm hrel
    have hc1 : (dD.ofTorus v * dD.d8 false false p.1.1 * bpow e p.1.2) *
        (dD.c : G) ^ 2 ^ (m - 1) =
        (dD.c : G) ^ 2 ^ (m - 1) * (dD.ofTorus v * dD.d8 false false p.1.1 *
          bpow e p.1.2) := by
      have h1 : Commute (dD.ofTorus v) ((dD.c : G) ^ 2 ^ (m - 1)) :=
        (commute_iff_eq _ _).mpr hc1_1
      have h2 : Commute (dD.d8 false false p.1.1) ((dD.c : G) ^ 2 ^ (m - 1)) :=
        (commute_iff_eq _ _).mpr hc1_2
      have h3 : Commute (bpow e p.1.2) ((dD.c : G) ^ 2 ^ (m - 1)) :=
        (commute_iff_eq _ _).mpr hc1_3
      exact ((h1.mul_left h2).mul_left h3).eq
    have hf : dD.ofTorus v * (dD.u * e) = (dD.u * e) * dD.ofTorus v :=
      t200inv1_comm_ue_ofTorus dD hrel v
        (t200inv1_fix_ue_bool dD hm hj hrel p.2.1 p.2.2)
    have hcu_1 : dD.d8 false false p.1.1 * (dD.u * e) =
        (dD.u * e) * dD.d8 false false p.1.1 := by
      cases p.1.1
      · rw [dD.d8_fff, one_mul, mul_one]
      · rw [dD.d8_fft]; exact t200inv1_u_comm_ue dD hrel
    have hcu_2 : bpow e p.1.2 * (dD.u * e) = (dD.u * e) * bpow e p.1.2 := by
      cases p.1.2
      · simp [bpow]
      · simpa [bpow] using t200inv1_e_comm_ue dD hrel
    have hcu : (dD.ofTorus v * dD.d8 false false p.1.1 * bpow e p.1.2) *
        (dD.u * e) = (dD.u * e) *
          (dD.ofTorus v * dD.d8 false false p.1.1 * bpow e p.1.2) := by
      have h1 : Commute (dD.ofTorus v) (dD.u * e) := (commute_iff_eq _ _).mpr hf
      have h2 : Commute (dD.d8 false false p.1.1) (dD.u * e) :=
        (commute_iff_eq _ _).mpr hcu_1
      have h3 : Commute (bpow e p.1.2) (dD.u * e) :=
        (commute_iff_eq _ _).mpr hcu_2
      exact ((h1.mul_left h2).mul_left h3).eq
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mul_mem (mul_mem hS1 hS2) hS3
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hc1
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hcu
  let g : ((Bool × Bool) × (Bool × ZMod (2 ^ (m + 2)))) → ↥U := fun p =>
    ⟨_, hmemU p⟩
  have hinj : Function.Injective g := by
    intro p p' hp
    have hp' : dD.ofTorus (Torus.ofInt _ ![(if p.2.1 then (2 : ℤ) ^ (m - 1) else 0),
        ((j : ℤ) - 1) * (p.2.2.val : ℤ), (p.2.2.val : ℤ)]) *
        dD.d8 false false p.1.1 * bpow e p.1.2 =
        dD.ofTorus (Torus.ofInt _ ![(if p'.2.1 then (2 : ℤ) ^ (m - 1) else 0),
        ((j : ℤ) - 1) * (p'.2.2.val : ℤ), (p'.2.2.val : ℤ)]) *
        dD.d8 false false p'.1.1 * bpow e p'.1.2 := congrArg Subtype.val hp
    obtain ⟨hv, -, -, hl, hk⟩ := hE.nfe_inj (t200_faithful hm)
      (fun i j l => t200inv1_not_word dD hm hj hrel i j l) hp'
    rw [t200_ofInt_eq_iff] at hv
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hv
    obtain ⟨hb, -, hz⟩ := hv
    have hz' : p'.2.2 = p.2.2 := by
      have hcast : (((p'.2.2.val : ℤ)) : ZMod (2 ^ (m + 2))) =
          (((p.2.2.val : ℤ)) : ZMod (2 ^ (m + 2))) := by
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
        have h : ((2 ^ (m + 2) : ℕ) : ℤ) ∣ (p.2.2.val : ℤ) - (p'.2.2.val : ℤ) := by
          push_cast
          simpa only [neg_sub] using hz.neg_right
        exact h
      push_cast at hcast
      rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
    have hb' : p'.2.1 = p.2.1 := t200inv1_bool_eq_of_dvd hm hb
    exact Prod.ext (Prod.ext hl hk) (Prod.ext hb'.symm hz'.symm)
  have hle := Nat.card_le_card_of_injective g hinj
  have hcard : Nat.card ((Bool × Bool) × (Bool × ZMod (2 ^ (m + 2)))) = 4 * 2 ^ (m + 3) := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
    have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
    rw [h2]
    ring
  rw [hcard] at hle
  change 4 * 2 ^ (m + 3) ≤ Nat.card ↥U
  exact hle

theorem t200inv1_card_centralizer_T_le [Finite G] {j p : ℕ} (hm : 1 ≤ m)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 p) {y : G}
    (_hyT : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    Nat.card (((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) ⊓
        Subgroup.centralizer {y} : Subgroup G) ≤
      4 * Nat.card ↥(D ⊓ Subgroup.centralizer {y}) := by
  have hA : ((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) ⊓ Subgroup.centralizer {y} ≤
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} := inf_le_left
  have h := t200inv1_card_le_four_mul_card_inf dD hm hj hrel hA
  have hinf : (((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) ⊓ Subgroup.centralizer {y}) ⊓ D =
      D ⊓ Subgroup.centralizer {y} := by
    have hDT : D ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} := by
      intro d hd
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_left hd), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : IsMulCommutative D := dD.isMulCommutative
      exact Subgroup.mul_comm_of_mem_isMulCommutative D hd (D.pow_mem dD.c.2 _)
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨-, hxC⟩, hxD⟩
      exact ⟨hxD, hxC⟩
    · rintro ⟨hxD, hxC⟩
      exact ⟨⟨hDT hxD, hxC⟩, hxD⟩
  rwa [hinf] at h

theorem t200inv1_card_centralizer_le [Finite G] {j p : ℕ} (hm : 1 ≤ m)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 p) :
    ∀ y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
      y ∉ D ⊔ Subgroup.zpowers dD.u → y * y = 1 →
        Nat.card ((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
            Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} ⊓ Subgroup.centralizer {y} :
              Subgroup G) ≤
          Nat.card ((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
            Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} ⊓
              Subgroup.centralizer {dD.u * e} : Subgroup G) := by
  intro y hyT hyDu hy2
  obtain ⟨v₀, l, rfl⟩ := t200inv1_mem_of_not_mem_Du dD hm hj hrel hyT hyDu
  have hTbound := t200inv1_card_centralizer_T_le dD hm hj hrel (y :=
    dD.ofTorus v₀ * dD.d8 false false l * bpow e true) hyT
  have hDbound := t200inv1_card_inf_centralizer_mul_e_le dD hm hj hrel v₀ l
  have hlow := t200inv1_card_centralizer_ue_ge dD hm hj hrel
  calc Nat.card (((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) ⊓ Subgroup.centralizer
          {dD.ofTorus v₀ * dD.d8 false false l * bpow e true} : Subgroup G)
      ≤ 4 * Nat.card ↥(D ⊓ Subgroup.centralizer
          {dD.ofTorus v₀ * dD.d8 false false l * bpow e true}) := hTbound
    _ ≤ 4 * 2 ^ (m + 3) := Nat.mul_le_mul_left 4 hDbound
    _ = 2 ^ (m + 5) := by ring
    _ ≤ Nat.card (((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) ⊓ Subgroup.centralizer
          {dD.u * e} : Subgroup G) := by
      rw [show (2 : ℕ) ^ (m + 5) = 4 * 2 ^ (m + 3) by ring]
      exact hlow

theorem t200inv1_card_centralizer_lt [Finite G] {j p : ℕ} (hm : 1 ≤ m)
    (hj : j = 0 ∨ j = 2 ^ (m + 1)) (hrel : Rel34inv dD e j 1 p) :
    ∀ y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
      y ∉ D ⊔ Subgroup.zpowers dD.u → y * y = 1 → y ∉ D ⊔ Subgroup.zpowers (dD.u * e) →
        Nat.card ((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
            Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} ⊓ Subgroup.centralizer {y} :
              Subgroup G) <
          Nat.card ((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
            Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} ⊓
              Subgroup.centralizer {dD.u * e} : Subgroup G) := by
  intro y hyT hyDu hy2 hyDue
  obtain ⟨v₀, l, rfl⟩ := t200inv1_mem_of_not_mem_Du dD hm hj hrel hyT hyDu
  have hl : l = false := by
    by_contra hl
    have hl' : l = true := by cases l <;> simp_all
    apply hyDue
    rw [hl']
    have h : dD.ofTorus v₀ * dD.d8 false false true * bpow e true =
        dD.ofTorus v₀ * (dD.u * e) := by
      simp [dD.d8_fft, bpow, mul_assoc]
    rw [h]
    exact mul_mem (Subgroup.mem_sup_left (dD.ofTorus_mem v₀))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers (dD.u * e)))
  subst hl
  have hTbound := t200inv1_card_centralizer_T_le dD hm hj hrel (y :=
    dD.ofTorus v₀ * dD.d8 false false false * bpow e true) hyT
  have hD8 := t200inv1_card_inf_centralizer_e_le_eight dD hm hj hrel v₀
  have hlow := t200inv1_card_centralizer_ue_ge dD hm hj hrel
  have h32 : Nat.card (((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) ⊓
        Subgroup.centralizer {dD.ofTorus v₀ * dD.d8 false false false * bpow e true} :
          Subgroup G) ≤ 32 := by
    calc Nat.card (((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
          Subgroup.zpowers e) ⊓ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) ⊓
            Subgroup.centralizer
              {dD.ofTorus v₀ * dD.d8 false false false * bpow e true} : Subgroup G)
        ≤ 4 * Nat.card ↥(D ⊓ Subgroup.centralizer
            {dD.ofTorus v₀ * dD.d8 false false false * bpow e true}) := hTbound
      _ ≤ 4 * 8 := Nat.mul_le_mul_left 4 hD8
      _ = 32 := by norm_num
  have h16 : 16 ≤ 2 ^ (m + 3) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (m + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : 32 < 4 * 2 ^ (m + 3) := by nlinarith
  exact lt_of_le_of_lt h32 (lt_of_lt_of_le hlt hlow)

theorem t200inv1_u_mem_U {j p : ℕ} (hrel : Rel34inv dD e j 1 p) :
    dD.u ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} ⊓
          Subgroup.centralizer {dD.u * e} := by
  refine Subgroup.mem_inf.mpr ⟨t200inv1_u_mem_T dD, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact t200inv1_u_comm_ue dD hrel

theorem t200inv1_e_mem_U {j p : ℕ} (hm : 1 ≤ m) (hrel : Rel34inv dD e j 1 p) :
    e ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} ⊓
          Subgroup.centralizer {dD.u * e} := by
  refine Subgroup.mem_inf.mpr ⟨t200inv1_e_mem_T dD hm hrel, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact t200inv1_e_comm_ue dD hrel

theorem t200inv1_f_mem_U {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) :
    dD.ofTorus (Torus.ofInt _ ![0, (j : ℤ) - 1, 1]) ∈
      (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} ⊓
          Subgroup.centralizer {dD.u * e} := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (dD.ofTorus_mem _)), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : IsMulCommutative D := dD.isMulCommutative
    exact Subgroup.mul_comm_of_mem_isMulCommutative D (dD.ofTorus_mem _)
      (D.pow_mem dD.c.2 _)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h := t200inv1_fix_ue_bool dD hm hj hrel false (1 : ZMod (2 ^ (m + 2)))
    have hval : ((1 : ZMod (2 ^ (m + 2))).val : ℤ) = 1 := by
      have : Fact (1 < 2 ^ (m + 2)) :=
        ⟨Nat.one_lt_pow (by omega : m + 2 ≠ 0) (by norm_num : 1 < 2)⟩
      have : NeZero (2 ^ (m + 2)) := ⟨by positivity⟩
      rw [ZMod.val_one]
      norm_num
    simpa [hval] using t200inv1_comm_ue_ofTorus dD hrel
      (Torus.ofInt _ ![0, (j : ℤ) - 1, 1]) (by simpa [hval] using h)

theorem t200inv1_φe_f_ne {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) :
    (dD.t200inv1EAction hrel).φe (Torus.ofInt _ ![0, (j : ℤ) - 1, 1]) ≠
      Torus.ofInt _ ![0, (j : ℤ) - 1, 1] := by
  intro h
  rw [StrothWeakTypeData.t200inv1_φe dD hrel, t200_ofInt_eq_iff] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h
  obtain ⟨-, -, h2⟩ := h
  apply t200inv1_not_dvd_j_sub_two (m := m) hm hj
  rw [show (j : ℤ) - 2 = -(1 - (-1 + (j : ℤ))) by ring]
  exact dvd_neg.mpr (by simpa [mul_one] using h2)

theorem t200inv1_φu_f_ne {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (_hrel : Rel34inv dD e j 1 p) :
    (StrothTypeIndex.t200 m).action.d8Act false false true
        (Torus.ofInt _ ![0, (j : ℤ) - 1, 1]) ≠
      Torus.ofInt _ ![0, (j : ℤ) - 1, 1] := by
  intro h
  rw [show (StrothTypeIndex.t200 m).action.d8Act false false true =
      (StrothTypeIndex.t200 m).action.φu by
    simp [SigmaFourAction.d8Act]] at h
  rw [t200_φu, t200_ofInt_eq_iff] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h
  obtain ⟨-, h2, -⟩ := h
  apply t200inv1_not_dvd_j_sub_two (m := m) hm hj
  convert h2 using 1
  ring

theorem t200inv1_w0_eq :
    dD.ofTorus (om200 m ![0, 1, 1]) =
      (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) := by
  rw [dD.t200_a_pow, dD.t200_b_pow, ← dD.ofTorus_add]
  congr 1
  rw [om200_apply, om200_apply, om200_apply, ← Torus.ofInt_add]
  congr 1
  funext i
  fin_cases i <;> simp

theorem t200inv1_c1w0_eq :
    dD.ofTorus (om200 m ![1, 1, 1]) =
      (dD.c : G) ^ 2 ^ (m - 1) *
        ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) := by
  rw [dD.t200_c_pow, ← t200inv1_w0_eq dD, ← dD.ofTorus_add]
  congr 1
  rw [om200_apply, om200_apply, om200_apply, ← Torus.ofInt_add]
  congr 1
  funext i
  fin_cases i <;> simp

theorem t200inv1_d_four {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) (v : Torus (StrothTypeIndex.t200 m).k)
    (hzu : dD.ofTorus v * dD.u = dD.u * dD.ofTorus v)
    (hze : dD.ofTorus v * e = e * dD.ofTorus v) :
    dD.ofTorus v = 1 ∨ dD.ofTorus v = (dD.c : G) ^ 2 ^ (m - 1) ∨
      dD.ofTorus v = (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) ∨
      dD.ofTorus v = (dD.c : G) ^ 2 ^ (m - 1) *
        ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) := by
  classical
  let hE := dD.t200inv1EAction hrel
  have hφu : (StrothTypeIndex.t200 m).action.d8Act false false true v = v := by
    have h := (t200_e_comm_iff dD hE 0 v true false).mp (by
      simpa [dD.ofTorus_zero, dD.d8_fft, bpow] using hzu)
    simpa [SigmaFourAction.d8Act] using h
  have hφe : hE.φe v = v := by
    have h := (t200_e_comm_iff dD hE 0 v false true).mp (by
      simpa [dD.ofTorus_zero, dD.d8_fff, bpow, one_mul] using hze)
    simpa [SigmaFourAction.d8Act] using h
  have hv2 : v + v = 0 := t200inv1_two_zsmul_of_fix_e dD hm hj hrel hφe
  have hy2 : dD.ofTorus v * dD.ofTorus v = 1 := by
    rw [dD.ofTorus_mul_self, hv2, dD.ofTorus_zero]
  obtain ⟨ε, hε, hεv⟩ := dD.t200_eq_om_of_mul_self hm (dD.ofTorus_mem v) hy2
  have hvε : v = om200 m ε := dD.ofTorus_inj hεv
  subst hvε
  have hφu' : (StrothTypeIndex.t200 m).action.φu (om200 m ε) = om200 m ε := by
    simpa [SigmaFourAction.d8Act] using hφu
  rw [t200_φu_om] at hφu'
  have hε12 : ε 1 = ε 2 := by
    have h := (om200_eq_iff hm _ _).mp hφu' 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2 | h2 <;>
      rw [h1, h2] at h ⊢ <;> norm_num at h
  let a : Bool := decide (ε 0 = 1)
  let b : Bool := decide (ε 1 = 1)
  have hεeq : ε = ![(a.toNat : ℤ), (b.toNat : ℤ), (b.toNat : ℤ)] := by
    funext i
    fin_cases i
    · exact (Stroth42Core.bool_toNat_cast_eq (hε 0)).symm
    · exact (Stroth42Core.bool_toNat_cast_eq (hε 1)).symm
    · show ε 2 = ((decide (ε 1 = 1)).toNat : ℤ)
      rw [← hε12]
      exact (Stroth42Core.bool_toNat_cast_eq (hε 1)).symm
  rw [hεeq]
  cases a <;> cases b
  · left
    norm_num
    rw [show om200 m (![0, 0, 0] : Fin 3 → ℤ) = 0 by
      rw [← om200_zero]
      congr 1
      funext i
      fin_cases i <;> rfl]
    exact dD.ofTorus_zero
  · right; right; left
    norm_num
    exact t200inv1_w0_eq dD
  · right; left
    norm_num
    exact (dD.t200_c_pow (m := m)).symm
  · right; right; right
    norm_num
    exact t200inv1_c1w0_eq dD

theorem t200inv1_center_ue {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) :
    ∀ z ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} ⊓ Subgroup.centralizer {dD.u * e},
      (∀ y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
          Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} ⊓ Subgroup.centralizer {dD.u * e},
        z * y = y * z) →
      z = 1 ∨ z = (dD.c : G) ^ 2 ^ (m - 1) ∨
        z = (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) ∨
        z = (dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) ∨
        z = dD.u * e ∨ z = (dD.c : G) ^ 2 ^ (m - 1) * (dD.u * e) ∨
        z = (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) * (dD.u * e) ∨
        z = (dD.c : G) ^ 2 ^ (m - 1) * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) *
          (dD.u * e) := by
  classical
  intro z hz hzcomm
  let hE := dD.t200inv1EAction hrel
  let w : Torus (StrothTypeIndex.t200 m).k := Torus.ofInt _ ![0, (j : ℤ) - 1, 1]
  let f := dD.ofTorus w
  have hzT : z ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} := (Subgroup.mem_inf.mp hz).1
  obtain ⟨v, l, k, hzv⟩ := t200inv1_mem_nf dD hm hj hrel hzT
  have hfU := t200inv1_f_mem_U dD hm hj hrel
  have hzf : z * f = f * z := hzcomm f hfU
  have hc := (t200_e_comm_iff dD hE v w l k).mp (by
    simpa [f, hzv] using hzf.symm)
  have hcases : (l = false ∧ k = false) ∨ (l = true ∧ k = true) := by
    cases l <;> cases k
    · exact Or.inl ⟨rfl, rfl⟩
    · exfalso
      have h : hE.φe w = w := by simpa [SigmaFourAction.d8Act] using hc
      exact t200inv1_φe_f_ne dD hm hj hrel (by simpa [w] using h)
    · exfalso
      have h : (StrothTypeIndex.t200 m).action.d8Act false false true w = w := by
        simpa [SigmaFourAction.d8Act] using hc
      exact t200inv1_φu_f_ne dD hm hj hrel (by simpa [w] using h)
    · exact Or.inr ⟨rfl, rfl⟩
  have huU := t200inv1_u_mem_U dD hrel
  have heU := t200inv1_e_mem_U dD hm hrel
  rcases hcases with ⟨hl, hk⟩ | ⟨hl, hk⟩
  · have hz_eq : z = dD.ofTorus v := by
      rw [hzv, hl, hk]
      simp [bpow, dD.d8_fff]
    have hzu : dD.ofTorus v * dD.u = dD.u * dD.ofTorus v := by
      have h := hzcomm dD.u huU
      rwa [hz_eq] at h
    have hze : dD.ofTorus v * e = e * dD.ofTorus v := by
      have h := hzcomm e heU
      rwa [hz_eq] at h
    have hd := t200inv1_d_four dD hm hj hrel v hzu hze
    rw [← hz_eq] at hd
    rcases hd with h1 | h2 | h3 | h4
    · left; exact h1
    · right; left; exact h2
    · right; right; left; exact h3
    · right; right; right; left; exact h4
  · have hz_eq : z = dD.ofTorus v * (dD.u * e) := by
      rw [hzv, hl, hk]
      simp [bpow, dD.d8_fft, mul_assoc]
    have hzu_z : z * dD.u = dD.u * z := hzcomm dD.u huU
    have hze_z : z * e = e * z := hzcomm e heU
    have hzu' : dD.ofTorus v * dD.u * (dD.u * e) =
        dD.u * dD.ofTorus v * (dD.u * e) := by
      calc dD.ofTorus v * dD.u * (dD.u * e) =
          dD.ofTorus v * (dD.u * (dD.u * e)) := by group
        _ = dD.ofTorus v * ((dD.u * e) * dD.u) := by
          rw [t200inv1_u_comm_ue dD hrel]
        _ = dD.ofTorus v * (dD.u * e) * dD.u := by group
        _ = z * dD.u := by rw [← hz_eq]
        _ = dD.u * z := hzu_z
        _ = dD.u * (dD.ofTorus v * (dD.u * e)) := by rw [hz_eq]
        _ = dD.u * dD.ofTorus v * (dD.u * e) := by group
    have hdu : dD.ofTorus v * dD.u = dD.u * dD.ofTorus v :=
      (mul_right_cancel_iff).mp hzu'
    have hze' : dD.ofTorus v * e * (dD.u * e) =
        e * dD.ofTorus v * (dD.u * e) := by
      calc dD.ofTorus v * e * (dD.u * e) =
          dD.ofTorus v * (e * (dD.u * e)) := by group
        _ = dD.ofTorus v * ((dD.u * e) * e) := by
          rw [t200inv1_e_comm_ue dD hrel]
        _ = dD.ofTorus v * (dD.u * e) * e := by group
        _ = z * e := by rw [← hz_eq]
        _ = e * z := hze_z
        _ = e * (dD.ofTorus v * (dD.u * e)) := by rw [hz_eq]
        _ = e * dD.ofTorus v * (dD.u * e) := by group
    have hde : dD.ofTorus v * e = e * dD.ofTorus v :=
      (mul_right_cancel_iff).mp hze'
    have hd := t200inv1_d_four dD hm hj hrel v hdu hde
    rcases hd with h1 | h2 | h3 | h4
    · right; right; right; right; left
      rw [hz_eq, h1, one_mul]
    · right; right; right; right; right; left
      rw [hz_eq, h2]
    · right; right; right; right; right; right; left
      rw [hz_eq, h3]
    · right; right; right; right; right; right; right
      rw [hz_eq, h4, mul_assoc]

end Stroth47Core

end CFSG.CGT.Stroth77
