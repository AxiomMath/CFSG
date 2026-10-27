module

public import CFSG.LieType.Ree.LargeReeEightCollection
public import CFSG.LieType.Ree.LargeReeEightTorus

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag

abbrev Coord : Type := Fin 3 × Fin 4

@[expose] def coordRoot (p : Coord) : Fin F4.tag.rank → ℤ :=
  ![twoRoot p.2 0, fourRoot p.2 0, fourRoot p.2 2] p.1

abbrev Exceptional (p q : Coord) : Prop :=
  p.2 = q.2 ∧ ((p.1 = 1 ∧ q.1 = 2) ∨ (p.1 = 2 ∧ q.1 = 1))

theorem coord_pair_check' : ∀ p q : Coord, ¬ Exceptional p q →
    ∀ i, i < 2 * 1 + 1 → ∀ j, j < 2 * 1 + 1 →
      ¬ ((2 * (2 ^ 1 : ℤ) ^ 2 - 1) ∣
          2 ^ i * torusExp0 (2 ^ 1) (coordRoot p) + 2 ^ j * torusExp0 (2 ^ 1) (coordRoot q) ∧
        (2 * (2 ^ 1 : ℤ) ^ 2 - 1) ∣
          2 ^ i * torusExp1 (2 ^ 1) (coordRoot p) + 2 ^ j * torusExp1 (2 ^ 1) (coordRoot q)) := by
  decide +kernel

theorem coord_pair_check {p q : Coord} (hpq : ¬ Exceptional p q) :
    ∀ i j : ℕ, i < 2 * 1 + 1 → j < 2 * 1 + 1 →
      ¬ ((2 * (2 ^ 1 : ℤ) ^ 2 - 1) ∣
          2 ^ i * torusExp0 (2 ^ 1) (coordRoot p) + 2 ^ j * torusExp0 (2 ^ 1) (coordRoot q) ∧
        (2 * (2 ^ 1 : ℤ) ^ 2 - 1) ∣
          2 ^ i * torusExp1 (2 ^ 1) (coordRoot p) + 2 ^ j * torusExp1 (2 ^ 1) (coordRoot q)) :=
  fun i j hi hj => coord_pair_check' p q hpq i hi j hj

variable {K : Type} [Field K]

@[expose] def coordElt
    (p : Coord) (s : K) : ModGL F4.tag K :=
  ![twoCoord p.2 s, fourCoord p.2 s 0, fourCoord p.2 0 s] p.1

variable [CharP K F4.prime]

theorem coordElt_zero
    (p : Coord) : coordElt p (0 : K) = 1 := by
  obtain ⟨i, t⟩ := p
  fin_cases i <;> simp [coordElt, twoCoord_eq, fourCoord_eq, pinnedX_zero]

theorem coordElt_mem_heightSeries
    (p : Coord) (s : K) :
    coordElt p s ∈ heightSeries F4.tag K (height (coordRoot p)) := by
  obtain ⟨i, t⟩ := p
  fin_cases i
  · exact twoCoord_mem_heightSeries t s
  · exact fourCoord_mem_heightSeries t s 0
  · exact fourCoord_zero_mem_heightSeries t s

variable [Finite K]

theorem coordElt_mem
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (p : Coord) (s : K) :
    coordElt p s ∈ F4.reeFixedPosUnipotent K 1 := by
  obtain ⟨i, t⟩ := p
  fin_cases i
  · exact twoCoord_mem hK t s
  · exact fourCoord_mem hK t s 0
  · exact fourCoord_mem hK t 0 s

theorem coordElt_mem_inf
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (p : Coord) (s : K) :
    coordElt p s ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K (height (coordRoot p)) :=
  Subgroup.mem_inf.2 ⟨coordElt_mem hK p s, coordElt_mem_heightSeries p s⟩

theorem coordElt_conj
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (u : Kˣ × Kˣ) (p : Coord) (s : K) :
    torusPair 1 u * coordElt p s * (torusPair 1 u)⁻¹ =
      coordElt p ((torusWeight 1 (coordRoot p) u : K) * s) := by
  obtain ⟨i, t⟩ := p
  fin_cases i
  · exact torusPair_conj_twoCoord hK u t s
  · simpa [coordElt, coordRoot] using torusPair_conj_fourCoord hK u t s 0
  · simpa [coordElt, coordRoot] using torusPair_conj_fourCoord hK u t 0 s

theorem coordElt_mul
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (p : Coord) (s s' : K) :
    ∃ r ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K (height (coordRoot p) + 1),
      coordElt p s * coordElt p s' = coordElt p (s + s') * r := by
  obtain ⟨i, t⟩ := p
  fin_cases i
  · exact ⟨1, one_mem _, by simp [coordElt, twoCoord_add]⟩
  · refine ⟨fourCoord t 0 (s ^ 4 * s'), Subgroup.mem_inf.2 ⟨fourCoord_mem hK t 0 _, ?_⟩,
      fourCoord_add_zero hK t s s'⟩
    obtain ⟨-, -, h2, -⟩ := height_check.2 t
    exact heightSeries_antitone (by simp only [coordRoot]; simp; omega)
      (fourCoord_zero_mem_heightSeries t _)
  · exact ⟨1, one_mem _, by simp [coordElt, fourCoord_zero_add hK]⟩

theorem coordElt_mem_succ_or
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) {h : ℤ} (p : Coord) {s : K}
    (hs : height (coordRoot p) < h → s = 0) :
    coordElt p s ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K (h + 1) ∨
      height (coordRoot p) = h := by
  rcases lt_trichotomy (height (coordRoot p)) h with hlt | heq | hgt
  · left
    rw [hs hlt, coordElt_zero]
    exact one_mem _
  · exact Or.inr heq
  · left
    exact Subgroup.mem_inf.2 ⟨coordElt_mem hK p s,
      heightSeries_antitone (by omega) (coordElt_mem_heightSeries p s)⟩

theorem exists_list_prod_eq
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) {h : ℤ} {x : ModGL F4.tag K}
    (hx : x ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h) :
    ∃ l : List (ModGL F4.tag K), (∀ e ∈ l,
      e ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K (h + 1) ∨
        ∃ p s, height (coordRoot p) = h ∧ e = coordElt p s) ∧ l.prod = x := by
  obtain ⟨hxU, hxV⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨s, c, d, rfl⟩ := exists_blockProd_eq hK hxU
  obtain ⟨hs, hc, hd⟩ := blockProd_mem_heightSeries hxV
  let pv : List (Coord × K) := [((0, 0), s 0), ((0, 1), s 1), ((0, 2), s 2), ((0, 3), s 3),
    ((1, 0), c 0), ((2, 0), d 0), ((1, 1), c 1), ((2, 1), d 1), ((1, 2), c 2), ((2, 2), d 2),
    ((1, 3), c 3), ((2, 3), d 3)]
  have hpv : ∀ q ∈ pv, height (coordRoot q.1) < h → q.2 = 0 := by
    intro q hq
    simp only [pv, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact hc 0
    · exact hd 0
    · exact hc 1
    · exact hd 1
    · exact hc 2
    · exact hd 2
    · exact hc 3
    · exact hd 3
  refine ⟨pv.map fun q => coordElt q.1 q.2, fun e he => ?_, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
    rcases coordElt_mem_succ_or hK q.1 (hpv q hq) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨q.1, q.2, h1, rfl⟩
  · simp only [pv, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, coordElt,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [blockProd, fourCoord_eq_mul hK 0 (c 0) (d 0), fourCoord_eq_mul hK 1 (c 1) (d 1),
      fourCoord_eq_mul hK 2 (c 2) (d 2), fourCoord_eq_mul hK 3 (c 3) (d 3)]
    simp only [mul_assoc]

theorem eq_zero_of_list_prod {G : Type*} [Group G] (W : Subgroup G) (φ : G → ZMod 2)
    (hφ : ∀ x ∈ W, ∀ x' ∈ W, φ (x * x') = φ x + φ x') :
    ∀ l : List G, (∀ e ∈ l, e ∈ W ∧ φ e = 0) → φ l.prod = 0
  | [], _ => by
    have h := hφ 1 W.one_mem 1 W.one_mem
    rwa [mul_one, left_eq_add] at h
  | e :: l, hl => by
    have he := hl e List.mem_cons_self
    have ih := eq_zero_of_list_prod W φ hφ l fun x hx => hl x (List.mem_cons_of_mem e hx)
    rw [List.prod_cons, hφ e he.1 _ (W.list_prod_mem fun x hx => (hl x
      (List.mem_cons_of_mem e hx)).1), he.2, ih, add_zero]

theorem form_eq_zero_of_inf_eight
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (h h' : ℤ)
    (b : ModGL F4.tag K → ModGL F4.tag K → ZMod 2)
    (hb₁ : ∀ x ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h,
      ∀ x' ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h,
      ∀ y ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h', b (x * x') y = b x y + b x' y)
    (hb₂ : ∀ x ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h,
      ∀ y ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h',
      ∀ y' ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h', b x (y * y') = b x y + b x y')
    (hb₃ : ∀ x ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K (h + 1),
      ∀ y ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h', b x y = 0)
    (hb₄ : ∀ x ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h,
      ∀ y ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K (h' + 1), b x y = 0)
    (hb₅ : ∀ (t : Kˣ × Kˣ), ∀ x ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h,
      ∀ y ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h',
      b (torusPair 1 t * x * (torusPair 1 t)⁻¹) (torusPair 1 t * y * (torusPair 1 t)⁻¹) = b x y)
    (hb₆ : ∀ (f : Fin 4) (c d : K),
      b (fourCoord f c 0) (fourCoord f 0 d) = 0 ∧ b (fourCoord f 0 d) (fourCoord f c 0) = 0) :
    ∀ x ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h,
      ∀ y ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h', b x y = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hsucc : ∀ k : ℤ, F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K (k + 1) ≤
      F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K k :=
    fun k => inf_le_inf_left _ (heightSeries_antitone (by omega))
  have hpair : ∀ p q : Coord, height (coordRoot p) = h → height (coordRoot q) = h' →
      ∀ s s' : K, b (coordElt p s) (coordElt q s') = 0 := by
    intro p q hp hq
    have hpm : ∀ s : K, coordElt p s ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h :=
      fun s => hp ▸ coordElt_mem_inf hK p s
    have hqm : ∀ s : K, coordElt q s ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h' :=
      fun s => hq ▸ coordElt_mem_inf hK q s
    by_cases hex : Exceptional p q
    · obtain ⟨i, f⟩ := p
      obtain ⟨j, f'⟩ := q
      obtain ⟨hff, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := hex
      · intro s s'
        simp only at hff
        subst hff
        exact (hb₆ f s s').1
      · intro s s'
        simp only at hff
        subst hff
        exact (hb₆ f s' s).2
    · refine torusWeight_form_eq_zero_of 1 hK (coord_pair_check hex)
        (fun s s' => b (coordElt p s) (coordElt q s')) (fun s₁ s₂ s' => ?_)
        (fun s s₁ s₂ => ?_) (fun u s s' => ?_)
      · obtain ⟨r, hr, e⟩ := coordElt_mul hK p s₁ s₂
        rw [hp] at hr
        have h1 := hb₁ _ (hpm s₁) _ (hpm s₂) _ (hqm s')
        rw [e, hb₁ _ (hpm _) _ (hsucc h hr) _ (hqm s'), hb₃ _ hr _ (hqm s'), add_zero] at h1
        exact h1
      · obtain ⟨r, hr, e⟩ := coordElt_mul hK q s₁ s₂
        rw [hq] at hr
        have h1 := hb₂ _ (hpm s) _ (hqm s₁) _ (hqm s₂)
        rw [e, hb₂ _ (hpm s) _ (hqm _) _ (hsucc h' hr), hb₄ _ (hpm s) _ hr, add_zero] at h1
        exact h1
      · rw [← coordElt_conj hK u p s, ← coordElt_conj hK u q s', hb₅ u _ (hpm s) _ (hqm s')]
  have hleft : ∀ p : Coord, height (coordRoot p) = h → ∀ s : K,
      ∀ y ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h', b (coordElt p s) y = 0 := by
    intro p hp s y hy
    have hpm : coordElt p s ∈ F4.reeFixedPosUnipotent K 1 ⊓ heightSeries F4.tag K h :=
      hp ▸ coordElt_mem_inf hK p s
    obtain ⟨l, hl, rfl⟩ := exists_list_prod_eq hK hy
    refine eq_zero_of_list_prod _ (b (coordElt p s)) (fun y hy y' hy' => hb₂ _ hpm _ hy _ hy') l
      fun e he => ?_
    rcases hl e he with h1 | ⟨q, s', hq, rfl⟩
    · exact ⟨hsucc h' h1, hb₄ _ hpm _ h1⟩
    · exact ⟨hq ▸ coordElt_mem_inf hK q s', hpair p q hp hq s s'⟩
  intro x hx y hy
  obtain ⟨l, hl, rfl⟩ := exists_list_prod_eq hK hx
  refine eq_zero_of_list_prod _ (fun x => b x y) (fun x hx x' hx' => hb₁ _ hx _ hx' _ hy) l
    fun e he => ?_
  rcases hl e he with h1 | ⟨p, s, hp, rfl⟩
  · exact ⟨hsucc h h1, hb₃ _ h1 _ hy⟩
  · exact ⟨hp ▸ coordElt_mem_inf hK p s, hleft p hp s y hy⟩

end CFSG.LieType.Ree.LargeReeCover
