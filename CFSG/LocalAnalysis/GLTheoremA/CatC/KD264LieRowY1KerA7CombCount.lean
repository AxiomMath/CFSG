module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7CombSymm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

open Finset

open scoped Classical

variable {P : Type} [Group P] [Fintype P] {L : Type} [Field L]

section Basic

variable {ζ : L}

theorem sq_sq_eq {u : L} (hu : u ^ 3 = 1) : (u ^ 2) ^ 2 = u := by
  calc (u ^ 2) ^ 2 = u * u ^ 3 := by ring
    _ = u := by rw [hu, mul_one]

theorem sq_fun_inj {u v : P → L} (hu : ∀ x, u x ^ 3 = 1) (hv : ∀ x, v x ^ 3 = 1)
    (h : (fun x => u x ^ 2) = fun x => v x ^ 2) : u = v := by
  funext x
  calc u x = (u x ^ 2) ^ 2 := (sq_sq_eq (hu x)).symm
    _ = (v x ^ 2) ^ 2 := by rw [congrFun h x]
    _ = v x := sq_sq_eq (hv x)

theorem sq_fun_eq {u v : P → L} (hu : ∀ x, u x ^ 3 = 1)
    (h : (fun x => u x ^ 2) = v) : u = fun x => v x ^ 2 := by
  funext x
  calc u x = (u x ^ 2) ^ 2 := (sq_sq_eq (hu x)).symm
    _ = v x ^ 2 := by rw [congrFun h x]

theorem sq_fun_ne (hζ : IsPrimitiveRoot ζ 3) {u : P → L} (hu : ∀ x, u x ^ 3 = 1)
    (hnt : ∃ x, u x ≠ 1) : (fun x => u x ^ 2) ≠ u := by
  obtain ⟨x, hx⟩ := hnt
  intro h
  have hx' : u x ^ 2 = u x := congrFun h x
  rcases mu3_cases hζ (hu x) with h1 | h1 | h1
  · exact hx h1
  · rw [h1] at hx'
    exact ne_sq_of_prim hζ hx'.symm
  · rw [h1] at hx'
    exact ne_sq_of_prim hζ ((sq_sq_eq hζ.pow_eq_one).symm.trans hx')

theorem exists_eq_zeta {c : P → L} (hζ : IsPrimitiveRoot ζ 3)
    (hcmul : ∀ x y, c (x * y) = c x * c y) (hcpow : ∀ x, c x ^ 3 = 1)
    (hcnt : ∃ x, c x ≠ 1) : ∃ y, c y = ζ := by
  obtain ⟨x0, hx0⟩ := hcnt
  rcases mu3_cases hζ (hcpow x0) with h | h | h
  · exact absurd h hx0
  · exact ⟨x0, h⟩
  · refine ⟨x0 * x0, ?_⟩
    rw [hcmul, h]
    calc ζ ^ 2 * ζ ^ 2 = ζ * ζ ^ 3 := by ring
      _ = ζ := by rw [hζ.pow_eq_one, mul_one]

theorem ker_card (hζ : IsPrimitiveRoot ζ 3) {c : P → L}
    (hcmul : ∀ x y, c (x * y) = c x * c y) (hcpow : ∀ x, c x ^ 3 = 1)
    (hcnt : ∃ x, c x ≠ 1) (hcard : Fintype.card P = 27) :
    (univ.filter fun x => c x = 1).card = 9 := by
  obtain ⟨y, hy⟩ := exists_eq_zeta hζ hcmul hcpow hcnt
  have hc1 : c 1 = 1 := char_one hcmul hcpow
  have hyinv : c y⁻¹ * ζ = 1 := by rw [← hy, ← hcmul, inv_mul_cancel, hc1]
  have hyy : c (y * y) = ζ ^ 2 := by rw [hcmul, hy]; ring
  have hyyinv : c (y * y)⁻¹ * ζ ^ 2 = 1 := by rw [← hyy, ← hcmul, inv_mul_cancel, hc1]
  have hz1 : (univ.filter fun x => c x = ζ).card = (univ.filter fun x => c x = 1).card := by
    apply Finset.card_nbij' (fun z => z * y⁻¹) (fun x => x * y)
    · intro z hz
      simp only [Finset.coe_filter, Finset.mem_coe, Set.mem_setOf_eq, Finset.mem_filter,
        Finset.mem_univ, true_and] at hz ⊢
      show c (z * y⁻¹) = 1
      rw [hcmul, hz, mul_comm, hyinv]
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_coe, Set.mem_setOf_eq, Finset.mem_filter,
        Finset.mem_univ, true_and] at hx ⊢
      show c (x * y) = ζ
      rw [hcmul, hx, hy, one_mul]
    · intro z _
      exact inv_mul_cancel_right _ _
    · intro x _
      exact mul_inv_cancel_right _ _
  have hz2 : (univ.filter fun x => c x = ζ ^ 2).card = (univ.filter fun x => c x = 1).card := by
    apply Finset.card_nbij' (fun z => z * (y * y)⁻¹) (fun x => x * (y * y))
    · intro z hz
      simp only [Finset.coe_filter, Finset.mem_coe, Set.mem_setOf_eq, Finset.mem_filter,
        Finset.mem_univ, true_and] at hz ⊢
      show c (z * (y * y)⁻¹) = 1
      rw [hcmul, hz, mul_comm, hyyinv]
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_coe, Set.mem_setOf_eq, Finset.mem_filter,
        Finset.mem_univ, true_and] at hx ⊢
      show c (x * (y * y)) = ζ ^ 2
      rw [hcmul, hx, hyy, one_mul]
    · intro z _
      exact inv_mul_cancel_right _ _
    · intro x _
      exact mul_inv_cancel_right _ _
  have hpt : ∀ x, ((if c x = 1 then 1 else 0) + (if c x = ζ then 1 else 0) +
      (if c x = ζ ^ 2 then 1 else 0) : ℕ) = 1 := by
    intro x
    rcases mu3_cases hζ (hcpow x) with h | h | h
    · simp [h, one_ne_of_prim hζ, one_ne_sq_of_prim hζ]
    · simp [h, ne_one_of_prim hζ, ne_sq_of_prim hζ]
    · simp [h, sq_ne_one_of_prim hζ, ne_sq_of_prim hζ, (ne_sq_of_prim hζ).symm]
  have hpart : (univ.filter fun x => c x = 1).card + (univ.filter fun x => c x = ζ).card +
      (univ.filter fun x => c x = ζ ^ 2).card = Fintype.card P := by
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.card_univ,
      Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl (fun x _ => hpt x)
  omega

theorem common_kernel (hζ : IsPrimitiveRoot ζ 3) {c c' : P → L}
    (hcmul : ∀ x y, c (x * y) = c x * c y) (hcpow : ∀ x, c x ^ 3 = 1)
    (hc'mul : ∀ x y, c' (x * y) = c' x * c' y) (hc'pow : ∀ x, c' x ^ 3 = 1)
    (hcard : Fintype.card P = 27) :
    ∃ x, x ≠ 1 ∧ c x = 1 ∧ c' x = 1 := by
  let g : L → Fin 3 := fun u => if u = 1 then 0 else if u = ζ then 1 else 2
  have ginj : ∀ {u v : L}, u ^ 3 = 1 → v ^ 3 = 1 → g u = g v → u = v := by
    intro u v hu hv huv
    rcases mu3_cases hζ hu with h1 | h1 | h1 <;> rcases mu3_cases hζ hv with h2 | h2 | h2 <;>
      simp only [g, h1, h2] at huv <;> simp_all [ne_one_of_prim hζ, one_ne_of_prim hζ,
        ne_sq_of_prim hζ, (ne_sq_of_prim hζ).symm, sq_ne_one_of_prim hζ,
        one_ne_sq_of_prim hζ]
  let φ : P → Fin 3 × Fin 3 := fun x => (g (c x), g (c' x))
  have hlt : Fintype.card (Fin 3 × Fin 3) < Fintype.card P := by
    rw [hcard, Fintype.card_prod, Fintype.card_fin]
    norm_num
  obtain ⟨x, z, hxz, hφ⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hlt
  have hcxz : c x = c z := ginj (hcpow x) (hcpow z) (congrArg Prod.fst hφ)
  have hc'xz : c' x = c' z := ginj (hc'pow x) (hc'pow z) (congrArg Prod.snd hφ)
  have hc1 : c 1 = 1 := char_one hcmul hcpow
  have hc'1 : c' 1 = 1 := char_one hc'mul hc'pow
  have hzinv : c z⁻¹ * c z = 1 := by rw [← hcmul, inv_mul_cancel, hc1]
  have hzinv' : c' z⁻¹ * c' z = 1 := by rw [← hc'mul, inv_mul_cancel, hc'1]
  have hz0 : c z ≠ 0 := by
    intro h0
    have := hcpow z
    rw [h0] at this
    norm_num at this
  have hz0' : c' z ≠ 0 := by
    intro h0
    have := hc'pow z
    rw [h0] at this
    norm_num at this
  refine ⟨x * z⁻¹, fun h => hxz (mul_inv_eq_one.mp h), ?_, ?_⟩
  · have key : c (x * z⁻¹) * c z = c z := by
      rw [hcmul, mul_assoc, hzinv, mul_one, hcxz]
    exact mul_right_cancel₀ hz0 (by rw [one_mul]; exact key)
  · have key : c' (x * z⁻¹) * c' z = c' z := by
      rw [hc'mul, mul_assoc, hzinv', mul_one, hc'xz]
    exact mul_right_cancel₀ hz0' (by rw [one_mul]; exact key)

theorem triv_mem (hζ : IsPrimitiveRoot ζ 3) {c d : P → L}
    (hcmul : ∀ x y, c (x * y) = c x * c y) (hcpow : ∀ x, c x ^ 3 = 1)
    (hdmul : ∀ x y, d (x * y) = d x * d y) (hdpow : ∀ x, d x ^ 3 = 1)
    (hcnt : ∃ x, c x ≠ 1) (htriv : ∀ x, c x = 1 → d x = 1) :
    d = (fun _ => 1) ∨ d = c ∨ d = fun x => c x ^ 2 := by
  obtain ⟨y, hy⟩ := exists_eq_zeta hζ hcmul hcpow hcnt
  rcases mu3_cases hζ (hdpow y) with h | h | h
  · left
    funext x
    obtain ⟨j, _, _, hdx⟩ := triv_pow hζ hcmul hcpow hdmul hy htriv x
    show d x = 1
    rw [hdx, h, one_pow]
  · right; left
    funext x
    obtain ⟨j, _, hcx, hdx⟩ := triv_pow hζ hcmul hcpow hdmul hy htriv x
    show d x = c x
    rw [hdx, h, hcx]
  · right; right
    funext x
    obtain ⟨j, _, hcx, hdx⟩ := triv_pow hζ hcmul hcpow hdmul hy htriv x
    show d x = c x ^ 2
    rw [hdx, h, hcx]
    ring

theorem exists_good_char (hζ : IsPrimitiveRoot ζ 3) {d : Fin 7 → P → L}
    (hdmul : ∀ i x y, d i (x * y) = d i x * d i y) (hdpow : ∀ i x, d i x ^ 3 = 1)
    (hsymm : ∀ z, (univ.filter fun i => d i z = ζ).card =
      (univ.filter fun i => d i z = ζ ^ 2).card)
    (hfaith : ∀ x : P, (∀ i, d i x = 1) → x = 1) (hcard : Fintype.card P = 27) :
    ∃ c : P → L, (∀ x y, c (x * y) = c x * c y) ∧ (∀ x, c x ^ 3 = 1) ∧ (∃ x, c x ≠ 1) ∧
      (univ.filter fun x => c x = 1).card = 9 ∧
      (univ.filter fun i => ∀ x, c x = 1 → d i x = 1).card = 3 := by
  have hnt : ∃ i, ∃ x, d i x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ x : P, x = 1 := fun x => hfaith x (fun i => hcon i x)
    have hle : Fintype.card P ≤ 1 :=
      Fintype.card_le_one_iff.mpr (fun a b => (hall a).trans (hall b).symm)
    omega
  obtain ⟨i1, x1, hx1⟩ := hnt
  have hc1cnt : ∃ x, d i1 x ≠ 1 := ⟨x1, hx1⟩
  have hc1ne : d i1 ≠ fun _ => 1 := fun h => hx1 (congrFun h x1)
  obtain ⟨x0, hx0, hx0c⟩ : ∃ x0 : P, x0 ≠ 1 ∧ d i1 x0 = 1 := by
    have hc : 1 < (univ.filter fun x => d i1 x = 1).card := by
      rw [ker_card hζ (hdmul i1) (hdpow i1) hc1cnt hcard]
      norm_num
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
    by_cases ha1 : a = 1
    · have hb1' : b ≠ 1 := fun h => hab (ha1.trans h.symm)
      exact ⟨b, hb1', (Finset.mem_filter.mp hb).2⟩
    · exact ⟨a, ha1, (Finset.mem_filter.mp ha).2⟩
  obtain ⟨i2, hi2⟩ : ∃ i2, ¬ (d i2 = (fun _ => 1) ∨ d i2 = d i1 ∨
      d i2 = fun x => d i1 x ^ 2) := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ i, d i x0 = 1 := by
      intro i
      rcases hcon i with h | h | h
      · rw [h]
      · rw [h, hx0c]
      · rw [h]
        show d i1 x0 ^ 2 = 1
        rw [hx0c]
        norm_num
    exact hx0 (hfaith x0 hall)
  have h2a : d i2 ≠ fun _ => 1 := fun h => hi2 (Or.inl h)
  have h2b : d i2 ≠ d i1 := fun h => hi2 (Or.inr (Or.inl h))
  have h2c : d i2 ≠ fun x => d i1 x ^ 2 := fun h => hi2 (Or.inr (Or.inr h))
  have hc2cnt : ∃ x, d i2 x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h2a (funext hcon)
  obtain ⟨x2, hx2, hx2a, hx2b⟩ :=
    common_kernel hζ (hdmul i1) (hdpow i1) (hdmul i2) (hdpow i2) hcard
  obtain ⟨i3, hi3⟩ : ∃ i3, ¬ (d i3 = (fun _ => 1) ∨ d i3 = d i1 ∨
      d i3 = (fun x => d i1 x ^ 2) ∨ d i3 = d i2 ∨ d i3 = fun x => d i2 x ^ 2) := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ i, d i x2 = 1 := by
      intro i
      rcases hcon i with h | h | h | h | h
      · rw [h]
      · rw [h, hx2a]
      · rw [h]
        show d i1 x2 ^ 2 = 1
        rw [hx2a]
        norm_num
      · rw [h, hx2b]
      · rw [h]
        show d i2 x2 ^ 2 = 1
        rw [hx2b]
        norm_num
    exact hx2 (hfaith x2 hall)
  have h3a : d i3 ≠ fun _ => 1 := fun h => hi3 (Or.inl h)
  have h3b : d i3 ≠ d i1 := fun h => hi3 (Or.inr (Or.inl h))
  have h3c : d i3 ≠ fun x => d i1 x ^ 2 := fun h => hi3 (Or.inr (Or.inr (Or.inl h)))
  have h3d : d i3 ≠ d i2 := fun h => hi3 (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have h3e : d i3 ≠ fun x => d i2 x ^ 2 := fun h => hi3 (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hc3cnt : ∃ x, d i3 x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h3a (funext hcon)
  have hsq1 := sq_fun_ne hζ (hdpow i1) hc1cnt
  have hsq2 := sq_fun_ne hζ (hdpow i2) hc2cnt
  have hsq3 := sq_fun_ne hζ (hdpow i3) hc3cnt
  have hD1 : d i1 ∉ ({fun x => d i1 x ^ 2, d i2, fun x => d i2 x ^ 2, d i3,
      fun x => d i3 x ^ 2} : Finset (P → L)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨hsq1.symm, h2b.symm, fun h => ?_, h3b.symm, fun h => ?_⟩
    · exact h2c (sq_fun_eq (hdpow i2) h.symm)
    · exact h3c (sq_fun_eq (hdpow i3) h.symm)
  have hD2 : (fun x => d i1 x ^ 2) ∉ ({d i2, fun x => d i2 x ^ 2, d i3,
      fun x => d i3 x ^ 2} : Finset (P → L)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h2c.symm, fun h => h2b (sq_fun_inj (hdpow i1) (hdpow i2) h).symm, h3c.symm,
      fun h => h3b (sq_fun_inj (hdpow i1) (hdpow i3) h).symm⟩
  have hD3 : d i2 ∉ ({fun x => d i2 x ^ 2, d i3, fun x => d i3 x ^ 2} : Finset (P → L)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hsq2.symm, h3d.symm, fun h => h3e (sq_fun_eq (hdpow i3) h.symm)⟩
  have hD4 : (fun x => d i2 x ^ 2) ∉ ({d i3, fun x => d i3 x ^ 2} : Finset (P → L)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => h3e h.symm, fun h => h3d (sq_fun_inj (hdpow i2) (hdpow i3) h).symm⟩
  have hD5 : d i3 ∉ ({fun x => d i3 x ^ 2} : Finset (P → L)) := by
    simp only [Finset.mem_singleton]
    exact hsq3.symm
  obtain ⟨m, hm⟩ : ∃ m : (P → L) → ℕ, ∀ χ, m χ = (univ.filter fun i => d i = χ).card :=
    ⟨fun χ => (univ.filter fun i => d i = χ).card, fun χ => rfl⟩
  have hmsq : ∀ j, d j ≠ (fun _ => 1) → m (fun x => d j x ^ 2) = m (d j) := by
    intro j hj
    have hjnt : ∃ x, d j x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hj (funext hcon)
    rw [hm, hm]
    exact (mult_inv_eq hζ hdmul hdpow hsymm (hdmul j) (hdpow j) hjnt).symm
  have hmpos : ∀ j, 0 < m (d j) := by
    intro j
    rw [hm]
    exact Finset.card_pos.mpr ⟨j, by simp⟩
  have hnt_of : ∀ j, d j ≠ (fun _ => 1) → ∃ x, d j x ≠ 1 := by
    intro j hj
    by_contra hcon
    push Not at hcon
    exact hj (funext hcon)
  have sq_ne_one : ∀ j, d j ≠ (fun _ => 1) → (fun x => d j x ^ 2) ≠ fun _ => 1 := by
    intro j hj h
    apply hj
    have := sq_fun_eq (hdpow j) h
    simpa using this
  have hsqpos : ∀ j, d j ≠ (fun _ => 1) → 0 < m (fun x => d j x ^ 2) := by
    intro j hj
    rw [hmsq j hj]
    exact hmpos j
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset (P → L), Z = insert (fun _ => 1) (univ.image d) :=
    ⟨_, rfl⟩
  have hmemZ : ∀ j, d j ∈ Z := fun j => by
    rw [hZ]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem d (mem_univ j))
  have hZof : ∀ χ, 0 < m χ → χ ∈ Z := by
    intro χ hχ
    rw [hm] at hχ
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hχ
    rw [← (Finset.mem_filter.mp hj).2]
    exact hmemZ j
  have h7 : ∑ χ ∈ Z, m χ = 7 := by
    have key := Finset.card_eq_sum_card_fiberwise (f := d) (s := univ) (t := Z)
      (fun i _ => hmemZ i)
    simp only [hm]
    rw [← key]
    simp
  have h1Z : (fun _ => 1 : P → L) ∈ Z := by
    rw [hZ]
    exact Finset.mem_insert_self _ _
  have hm1 := Finset.add_sum_erase Z m h1Z
  obtain ⟨W, hW⟩ : ∃ W : Finset (P → L), W = Z.erase (fun _ => 1) := ⟨_, rfl⟩
  rw [← hW] at hm1
  obtain ⟨S, hS⟩ : ∃ S : Finset (P → L), S = {d i1, fun x => d i1 x ^ 2, d i2,
      fun x => d i2 x ^ 2, d i3, fun x => d i3 x ^ 2} := ⟨_, rfl⟩
  have hSsum : ∑ χ ∈ S, m χ = m (d i1) + m (fun x => d i1 x ^ 2) + m (d i2) +
      m (fun x => d i2 x ^ 2) + m (d i3) + m (fun x => d i3 x ^ 2) := by
    rw [hS, Finset.sum_insert hD1, Finset.sum_insert hD2, Finset.sum_insert hD3,
      Finset.sum_insert hD4, Finset.sum_insert hD5, Finset.sum_singleton]
    ring
  have hSW : S ⊆ W := by
    intro χ hχ
    rw [hS] at hχ
    rw [hW, Finset.mem_erase]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
    rcases hχ with h | h | h | h | h | h <;> rw [h]
    · exact ⟨hc1ne, hmemZ i1⟩
    · exact ⟨sq_ne_one i1 hc1ne, hZof _ (hsqpos i1 hc1ne)⟩
    · exact ⟨h2a, hmemZ i2⟩
    · exact ⟨sq_ne_one i2 h2a, hZof _ (hsqpos i2 h2a)⟩
    · exact ⟨h3a, hmemZ i3⟩
    · exact ⟨sq_ne_one i3 h3a, hZof _ (hsqpos i3 h3a)⟩
  have hsplit : ∑ χ ∈ W \ S, m χ + ∑ χ ∈ S, m χ = ∑ χ ∈ W, m χ :=
    Finset.sum_sdiff hSW
  have hclos : ∀ j, (fun x => d j x ^ 2) ∈ S → d j ∈ S := by
    intro j hj
    rw [hS] at hj ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj ⊢
    rcases hj with h | h | h | h | h | h
    · exact Or.inr (Or.inl (sq_fun_eq (hdpow j) h))
    · exact Or.inl (sq_fun_inj (hdpow j) (hdpow i1) h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (sq_fun_eq (hdpow j) h))))
    · exact Or.inr (Or.inr (Or.inl (sq_fun_inj (hdpow j) (hdpow i2) h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (sq_fun_eq (hdpow j) h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (sq_fun_inj (hdpow j) (hdpow i3) h)))))
  have hr2 : ∑ χ ∈ W \ S, m χ = 0 ∨ 2 ≤ ∑ χ ∈ W \ S, m χ := by
    by_cases hE : W \ S = ∅
    · left
      rw [hE, Finset.sum_empty]
    · right
      obtain ⟨χ, hχ⟩ := Finset.nonempty_iff_ne_empty.mpr hE
      have hχmem := hχ
      rw [Finset.mem_sdiff, hW, Finset.mem_erase] at hχ
      obtain ⟨⟨hχ1, hχZ⟩, hχS⟩ := hχ
      have hχj : ∃ j, d j = χ := by
        rw [hZ] at hχZ
        rcases Finset.mem_insert.mp hχZ with h | h
        · exact absurd h hχ1
        · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
          exact ⟨j, hj⟩
      obtain ⟨j, rfl⟩ := hχj
      have hsqS : (fun x => d j x ^ 2) ∉ S := fun h => hχS (hclos j h)
      have hsqW : (fun x => d j x ^ 2) ∈ W \ S := by
        rw [Finset.mem_sdiff, hW, Finset.mem_erase]
        exact ⟨⟨sq_ne_one j hχ1, hZof _ (hsqpos j hχ1)⟩, hsqS⟩
      have hpair : ({d j, fun x => d j x ^ 2} : Finset (P → L)) ⊆ W \ S := by
        intro y hy
        rcases Finset.mem_insert.mp hy with h | h
        · rw [h]
          exact hχmem
        · rw [Finset.mem_singleton.mp h]
          exact hsqW
      have hsum2 := Finset.sum_le_sum_of_subset_of_nonneg (f := m) hpair
        (fun _ _ _ => Nat.zero_le _)
      rw [Finset.sum_pair (sq_fun_ne hζ (hdpow j) (hnt_of j hχ1)).symm] at hsum2
      have h1 := hmpos j
      have h2 := hmsq j hχ1
      omega
  have hall := hsplit
  have hsq1m := hmsq i1 hc1ne
  have hsq2m := hmsq i2 h2a
  have hsq3m := hmsq i3 h3a
  have ha1 := hmpos i1
  have ha2 := hmpos i2
  have ha3 := hmpos i3
  have hm1val : m (fun _ => 1) = 1 ∧ m (d i1) = 1 := by
    omega
  refine ⟨d i1, hdmul i1, hdpow i1, hc1cnt, ker_card hζ (hdmul i1) (hdpow i1) hc1cnt hcard, ?_⟩
  have hfilt : (univ.filter fun i => ∀ x, d i1 x = 1 → d i x = 1) =
      ((univ.filter fun i => d i = fun _ => 1) ∪ (univ.filter fun i => d i = d i1)) ∪
        (univ.filter fun i => d i = fun x => d i1 x ^ 2) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases triv_mem hζ (hdmul i1) (hdpow i1) (hdmul i) (hdpow i) hc1cnt h with h' | h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
    · rintro ((h | h) | h) x hx
      · rw [h]
      · rw [h]
        exact hx
      · rw [h]
        show d i1 x ^ 2 = 1
        rw [hx]
        norm_num
  have hdisj1 : Disjoint (univ.filter fun i => d i = fun _ => 1)
      (univ.filter fun i => d i = d i1) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    exact hc1ne (h2.symm.trans h1)
  have hdisj2 : Disjoint ((univ.filter fun i => d i = fun _ => 1) ∪
      (univ.filter fun i => d i = d i1)) (univ.filter fun i => d i = fun x => d i1 x ^ 2) := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_filter]
      intro i _ h1 h2
      exact sq_ne_one i1 hc1ne (h2.symm.trans h1)
    · rw [Finset.disjoint_filter]
      intro i _ h1 h2
      exact hsq1 (h1.symm.trans h2).symm
  rw [hfilt, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1]
  rw [← hm, ← hm, ← hm]
  omega

end Basic

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

end
