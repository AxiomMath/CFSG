module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneTableBasic

public section

open Finset

namespace CFSG.Semidihedral.FieldFactorOne

namespace TableCoordinates

variable {L : Type*} [DecidableEq L]

structure Hyp (k : ℕ) (B : Finset L) (deg Θ : L → ℤ) (E F : ℕ → L → ℤ) (U V : L → ℤ) :
    Prop where
  hk : 2 ≤ k
  hk24 : k = 2 ∨ 4 ≤ k
  heven : Even k
  hdeg : ∀ x ∈ B, 0 < deg x
  hΘΘ : ∑ x ∈ B, Θ x * Θ x = 4
  hΘE : ∀ l ∈ Icc 1 (k - 1), ∑ x ∈ B, Θ x * E l x = 2
  hEE : ∀ l ∈ Icc 1 (k - 1), ∀ l' ∈ Icc 1 (k - 1),
    ∑ x ∈ B, E l x * E l' x = 2 + if l = l' then 1 else 0
  hΘF : ∀ j ∈ Icc 1 (k - 1), ∑ x ∈ B, Θ x * F j x = 0
  hEF : ∀ l ∈ Icc 1 (k - 1), ∀ j ∈ Icc 1 (k - 1), ∑ x ∈ B, E l x * F j x = 0
  hFF : ∀ j ∈ Icc 1 (k - 1), ∀ j' ∈ Icc 1 (k - 1),
    ∑ x ∈ B, F j x * F j' x = 1 + if j = j' then 1 else 0
  hUU : ∑ x ∈ B, U x * U x = 8
  hUV : ∑ x ∈ B, U x * V x = -4
  hVV : ∑ x ∈ B, V x * V x = 2 * k + 2
  hUΘ : ∑ x ∈ B, U x * Θ x = 0
  hVΘ : ∑ x ∈ B, V x * Θ x = 0
  hUE : ∀ l ∈ Icc 1 (k - 1), ∑ x ∈ B, U x * E l x = 0
  hVE : ∀ l ∈ Icc 1 (k - 1), ∑ x ∈ B, V x * E l x = 0
  hUF : ∀ j ∈ Icc 1 (k - 1), ∑ x ∈ B, U x * F j x = 0
  hVF : ∀ j ∈ Icc 1 (k - 1), ∑ x ∈ B, V x * F j x = 0
  hdegΘ : ∑ x ∈ B, deg x * Θ x = 0
  hdegE : ∀ l ∈ Icc 1 (k - 1), ∑ x ∈ B, deg x * E l x = 0
  hdegF : ∀ j ∈ Icc 1 (k - 1), ∑ x ∈ B, deg x * F j x = 0
  hdegU : ∑ x ∈ B, deg x * U x = 0
  hdegV : ∑ x ∈ B, deg x * V x = 0
  hcong : ∀ x ∈ B, (2 * k : ℤ) ∣ U x + 2 * V x + Θ x +
    2 * ∑ l ∈ Icc 1 (k - 1), E l x + 2 * ∑ j ∈ Icc 1 (k - 1), F j x

section Hyp

variable {k : ℕ} {B : Finset L} {deg Θ : L → ℤ} {E F : ℕ → L → ℤ} {U V : L → ℤ}

omit [DecidableEq L] in
theorem Hyp.one_mem (h : Hyp k B deg Θ E F U V) : 1 ∈ Icc 1 (k - 1) :=
  Finset.mem_Icc.mpr ⟨le_rfl, by have := h.hk; omega⟩

omit [DecidableEq L] in
theorem Hyp.par (h : Hyp k B deg Θ E F U V) : ∀ x ∈ B, Even (U x + Θ x) := by
  intro x hx
  obtain ⟨c, hc⟩ := h.hcong x hx
  refine ⟨k * c - V x - ∑ l ∈ Icc 1 (k - 1), E l x - ∑ j ∈ Icc 1 (k - 1), F j x, ?_⟩
  linear_combination hc

theorem Hyp.stageA (h : Hyp k B deg Θ E F U V) :
    ∃ (c₀ c₁ c₂ c₃ c₄ : L) (δ₀ δ₁ δ₂ δ₃ δ₄ : ℤ), ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄ :=
  TableCoordinates.stageA h.hdeg h.hΘΘ h.hUU h.hUΘ h.hdegΘ h.par

end Hyp

section ShapeE

variable {B : Finset L} {Θ U : L → ℤ} {c₀ c₁ c₂ c₃ c₄ : L} {δ₀ δ₁ δ₂ δ₃ δ₄ : ℤ}

theorem five_swap02 : ({c₂, c₁, c₀, c₃, c₄} : Finset L) = {c₀, c₁, c₂, c₃, c₄} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem five_swap13 : ({c₀, c₃, c₂, c₁, c₄} : Finset L) = {c₀, c₁, c₂, c₃, c₄} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem ShapeE.swap02 {E : L → ℤ} {a b : ℤ} {p : L} {s : ℤ}
    (hE : ShapeE B c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ E a b p s) :
    ShapeE B c₂ c₁ c₀ c₃ c₄ δ₂ δ₁ δ₀ δ₃ E (1 - a) b p s where
  ha := by rcases hE.ha with h | h <;> rw [h] <;> norm_num
  hb := hE.hb
  hp := by rw [five_swap02]; exact hE.hp
  hs := hE.hs
  e₀ := hE.e₂
  e₁ := hE.e₁
  e₂ := by rw [hE.e₀]; ring
  e₃ := hE.e₃
  e₄ := hE.e₄
  ep := hE.ep
  eout x hx hxp := hE.eout x (by rw [five_swap02] at hx; exact hx) hxp

theorem ShapeE.swap13 {E : L → ℤ} {a b : ℤ} {p : L} {s : ℤ}
    (hE : ShapeE B c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ E a b p s) :
    ShapeE B c₀ c₃ c₂ c₁ c₄ δ₀ δ₃ δ₂ δ₁ E a (1 - b) p s where
  ha := hE.ha
  hb := by rcases hE.hb with h | h <;> rw [h] <;> norm_num
  hp := by rw [five_swap13]; exact hE.hp
  hs := hE.hs
  e₀ := hE.e₀
  e₁ := hE.e₃
  e₂ := hE.e₂
  e₃ := by rw [hE.e₁]; ring
  e₄ := hE.e₄
  ep := hE.ep
  eout x hx hxp := hE.eout x (by rw [five_swap13] at hx; exact hx) hxp

theorem ShapeE.sum_mul (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) {E : L → ℤ}
    {a b : ℤ} {p : L} {s : ℤ} (hE : ShapeE B c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ E a b p s)
    (f : L → ℤ) :
    ∑ x ∈ B, f x * E x = δ₀ * a * f c₀ + δ₁ * b * f c₁ + δ₂ * (1 - a) * f c₂ +
      δ₃ * (1 - b) * f c₃ + s * f p := by
  rw [A.sum_split, Finset.sum_eq_single_of_mem p hE.hp fun x hx hxp => by
    rw [hE.eout x hx hxp, mul_zero], hE.e₀, hE.e₁, hE.e₂, hE.e₃, hE.e₄, hE.ep]
  ring

theorem ShapeE.inner (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) {E E' : L → ℤ}
    {a b a' b' : ℤ} {p p' : L} {s s' : ℤ}
    (hE : ShapeE B c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ E a b p s)
    (hE' : ShapeE B c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ E' a' b' p' s') :
    ∑ x ∈ B, E x * E' x = a * a' + (1 - a) * (1 - a') + b * b' + (1 - b) * (1 - b') +
      (if p = p' then s * s' else 0) := by
  have hE'p : E' p = if p = p' then s' else 0 := by
    split_ifs with hpp
    · rw [hpp, hE'.ep]
    · exact hE'.eout p hE.hp hpp
  rw [Finset.sum_congr rfl fun x _ => mul_comm (E x) (E' x), hE.sum_mul A E', hE'.e₀, hE'.e₁,
    hE'.e₂, hE'.e₃, hE'p]
  have h0 := sign_mul_self A.s₀
  have h1 := sign_mul_self A.s₁
  have h2 := sign_mul_self A.s₂
  have h3 := sign_mul_self A.s₃
  split_ifs
  · linear_combination (a * a') * h0 + (b * b') * h1 + ((1 - a) * (1 - a')) * h2 +
      ((1 - b) * (1 - b')) * h3
  · linear_combination (a * a') * h0 + (b * b') * h1 + ((1 - a) * (1 - a')) * h2 +
      ((1 - b) * (1 - b')) * h3

theorem ShapeE.unique (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) {E : L → ℤ}
    {a b a' b' : ℤ} {p p' : L} {s s' : ℤ}
    (hE : ShapeE B c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ E a b p s)
    (hE' : ShapeE B c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ E a' b' p' s') :
    a = a' ∧ b = b' ∧ p = p' ∧ s = s' := by
  have hpp : p = p' := by
    by_contra hne
    have e := hE'.eout p hE.hp hne
    rw [hE.ep] at e
    exact sign_ne_zero hE.hs e
  refine ⟨mul_left_cancel₀ (sign_ne_zero A.s₀) (hE.e₀.symm.trans hE'.e₀),
    mul_left_cancel₀ (sign_ne_zero A.s₁) (hE.e₁.symm.trans hE'.e₁), hpp, ?_⟩
  rw [← hE.ep, ← hE'.ep, hpp]

theorem ShapeE.apply_one (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) {E : L → ℤ} {p : L}
    {s : ℤ} (hE : ShapeE B c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ E 1 1 p s) {x : L} (hx : x ∈ B) :
    E x = δ₀ * (if x = c₀ then 1 else 0) + δ₁ * (if x = c₁ then 1 else 0) +
      s * (if x = p then 1 else 0) := by
  obtain ⟨-, p0, p1, p2, p3, p4⟩ := mem_sdiff_five.mp hE.hp
  by_cases e0 : x = c₀
  · subst e0
    simp [hE.e₀, A.n01, p0.symm]
  by_cases e1 : x = c₁
  · subst e1
    simp [hE.e₁, A.n01.symm, p1.symm]
  by_cases ep : x = p
  · subst ep
    simp [hE.ep, p0, p1]
  by_cases e2 : x = c₂
  · subst e2
    simp [hE.e₂, A.n02.symm, A.n12.symm, p2.symm]
  by_cases e3 : x = c₃
  · subst e3
    simp [hE.e₃, A.n03.symm, A.n13.symm, p3.symm]
  by_cases e4 : x = c₄
  · subst e4
    simp [hE.e₄, A.n04.symm, A.n14.symm, p4.symm]
  rw [hE.eout x (mem_sdiff_five.mpr ⟨hx, e0, e1, e2, e3, e4⟩) ep]
  simp [e0, e1, ep]

end ShapeE

theorem E_types {I : Finset ℕ} {a b s : ℕ → ℤ} {p : ℕ → L} (h1 : 1 ∈ I)
    (hthird : ∀ l ∈ I, ∃ m ∈ I, m ≠ 1 ∧ m ≠ l)
    (ha : ∀ l ∈ I, a l = 0 ∨ a l = 1) (hb : ∀ l ∈ I, b l = 0 ∨ b l = 1)
    (hs : ∀ l ∈ I, s l = 1 ∨ s l = -1)
    (hinner : ∀ l ∈ I, ∀ m ∈ I, l ≠ m → a l * a m + (1 - a l) * (1 - a m) + b l * b m +
      (1 - b l) * (1 - b m) + (if p l = p m then s l * s m else 0) = 2)
    (ha1 : a 1 = 1) (hb1 : b 1 = 1) : ∀ l ∈ I, a l = 1 ∧ b l = 1 := by
  intro l hl
  by_contra hne
  have hl1 : l ≠ 1 := fun e => hne (e ▸ ⟨ha1, hb1⟩)
  have hab : a l + b l = 1 := by
    have e1 := hinner 1 h1 l hl (Ne.symm hl1)
    rw [ha1, hb1] at e1
    have hP1 : (if p 1 = p l then s 1 * s l else 0) ≤ 1 := by
      split_ifs
      · rcases hs 1 h1 with hs1 | hs1 <;> rcases hs l hl with hsl | hsl <;> rw [hs1, hsl] <;>
          norm_num
      · norm_num
    rcases ha l hl with h | h <;> rcases hb l hl with h' | h' <;> rw [h, h'] at e1 hne ⊢
    · linarith
    · norm_num
    · norm_num
    · exact absurd ⟨rfl, rfl⟩ hne
  have e1 := hinner 1 h1 l hl (Ne.symm hl1)
  rw [ha1, hb1] at e1
  have hpl : p 1 = p l ∧ s l = s 1 := by
    split_ifs at e1 with hp
    · refine ⟨hp, ?_⟩
      rcases hs 1 h1 with hs1 | hs1 <;> rcases hs l hl with hsl | hsl <;> rw [hs1, hsl] at e1 ⊢ <;>
        linarith
    · linarith
  obtain ⟨m, hm, hm1, hml⟩ := hthird l hl
  have e2 := hinner 1 h1 m hm (Ne.symm hm1)
  have e3 := hinner l hl m hm (Ne.symm hml)
  rw [ha1, hb1] at e2
  rw [← hpl.1, hpl.2] at e3
  generalize hP : (if p 1 = p m then s 1 * s m else 0) = P at e2 e3
  have hPv : P = 0 ∨ P = 1 ∨ P = -1 := by
    rw [← hP]
    split_ifs
    · rcases hs 1 h1 with h | h <;> rcases hs m hm with h' | h' <;> rw [h, h'] <;> norm_num
    · exact Or.inl rfl
  rcases ha l hl with h | h <;> rcases hb l hl with h' | h' <;> rcases ha m hm with h'' | h'' <;>
    rcases hb m hm with h''' | h''' <;> rcases hPv with hP' | hP' | hP' <;>
    · rw [h, h', h'', h''', hP'] at e3
      rw [h'', h''', hP'] at e2
      rw [h, h'] at hab
      revert e2 e3 hab
      norm_num

structure ESystem (k : ℕ) (B : Finset L) (E : ℕ → L → ℤ) (c₀ c₁ c₂ c₃ c₄ : L) (δ₀ δ₁ δ : ℤ)
    (ψ : ℕ → L) : Prop where
  hδ : δ = 1 ∨ δ = -1
  hψ : ∀ l ∈ Icc 1 (k - 1), ψ l ∈ B \ {c₀, c₁, c₂, c₃, c₄}
  inj : Set.InjOn ψ (Icc 1 (k - 1) : Set ℕ)
  hE : ∀ l ∈ Icc 1 (k - 1), ∀ x ∈ B, E l x = δ₀ * (if x = c₀ then 1 else 0) +
    δ₁ * (if x = c₁ then 1 else 0) - δ * (if x = ψ l then 1 else 0)

section StageE

variable {k : ℕ} {B : Finset L} {deg Θ : L → ℤ} {E F : ℕ → L → ℤ} {U V : L → ℤ}
  {c₀ c₁ c₂ c₃ c₄ : L} {δ₀ δ₁ δ₂ δ₃ δ₄ : ℤ}

theorem Hyp.shapeE (h : Hyp k B deg Θ E F U V) (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄)
    {l : ℕ} (hl : l ∈ Icc 1 (k - 1)) :
    ∃ (a b : ℤ) (p : L) (s : ℤ), ShapeE B c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ (E l) a b p s :=
  stageB A h.hdeg h.hdegΘ h.hdegU (by simpa using h.hEE l hl l hl) (h.hΘE l hl) (h.hUE l hl)
    (h.hdegE l hl)

theorem Hyp.eSystem_of_normalized (h : Hyp k B deg Θ E F U V)
    (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄) {p₁ : L} {s₁ : ℤ}
    (hE1 : ShapeE B c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ (E 1) 1 1 p₁ s₁) :
    ∃ (ψ : ℕ → L) (δ : ℤ), ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ := by
  have hI1 := h.one_mem
  have hshape : ∀ l, ∃ (a b : ℤ) (p : L) (s : ℤ), l ∈ Icc 1 (k - 1) →
      ShapeE B c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ (E l) a b p s := by
    intro l
    by_cases hl : l ∈ Icc 1 (k - 1)
    · obtain ⟨a, b, p, s, hS⟩ := h.shapeE A hl
      exact ⟨a, b, p, s, fun _ => hS⟩
    · exact ⟨0, 0, c₀, 0, fun h' => absurd h' hl⟩
  choose a b p s hS using hshape
  obtain ⟨ha1, hb1, hp1, hs1⟩ := (hS 1 hI1).unique A hE1
  have hinner : ∀ l ∈ Icc 1 (k - 1), ∀ m ∈ Icc 1 (k - 1), l ≠ m →
      a l * a m + (1 - a l) * (1 - a m) + b l * b m + (1 - b l) * (1 - b m) +
        (if p l = p m then s l * s m else 0) = 2 := by
    intro l hl m hm hlm
    have e := h.hEE l hl m hm
    rw [ite_eq_right hlm, add_zero, (hS l hl).inner A (hS m hm)] at e
    exact e
  have htype : ∀ l ∈ Icc 1 (k - 1), a l = 1 ∧ b l = 1 := by
    rcases h.hk24 with hk2 | hk4
    · intro l hl
      have : l = 1 := by
        rw [Finset.mem_Icc] at hl
        omega
      rw [this]
      exact ⟨ha1, hb1⟩
    · refine E_types hI1 ?_ (fun l hl => (hS l hl).ha) (fun l hl => (hS l hl).hb)
        (fun l hl => (hS l hl).hs) hinner ha1 hb1
      intro l _
      by_cases hl2 : l = 2
      · exact ⟨3, Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩, by norm_num, by omega⟩
      · exact ⟨2, Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩, by norm_num, Ne.symm hl2⟩
  have hS' : ∀ l ∈ Icc 1 (k - 1), ShapeE B c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ (E l) 1 1 (p l) (s l) :=
    fun l hl => by
      have := hS l hl
      rwa [(htype l hl).1, (htype l hl).2] at this
  have hdegs : ∀ l ∈ Icc 1 (k - 1), s l * deg (p l) = -(δ₀ * deg c₀ + δ₁ * deg c₁) := by
    intro l hl
    have e := h.hdegE l hl
    rw [(hS' l hl).sum_mul A deg] at e
    linear_combination e
  have hsign : ∀ l ∈ Icc 1 (k - 1), s l = s 1 := by
    intro l hl
    have e := (hdegs l hl).trans (hdegs 1 hI1).symm
    have hp := h.hdeg (p l) (Finset.mem_sdiff.mp (hS' l hl).hp).1
    have hp' := h.hdeg (p 1) (Finset.mem_sdiff.mp (hS' 1 hI1).hp).1
    rcases (hS' l hl).hs with e1 | e1 <;> rcases (hS' 1 hI1).hs with e2 | e2 <;>
      rw [e1, e2] at e ⊢ <;> linarith
  have hs1' : s 1 = 1 ∨ s 1 = -1 := (hS' 1 hI1).hs
  refine ⟨p, -s 1, ?_, fun l hl => (hS' l hl).hp, ?_, ?_⟩
  · rcases hs1' with e | e <;> rw [e] <;> norm_num
  · intro l hl m hm hlm
    by_contra hne
    have e := hinner l hl m hm hne
    rw [(htype l hl).1, (htype l hl).2, (htype m hm).1, (htype m hm).2, ite_eq_left hlm,
      hsign l hl, hsign m hm, sign_mul_self hs1'] at e
    norm_num at e
  · intro l hl x hx
    rw [(hS' l hl).apply_one A hx, hsign l hl]
    ring

theorem Hyp.stageE (h : Hyp k B deg Θ E F U V) :
    ∃ (c₀ c₁ c₂ c₃ c₄ : L) (δ₀ δ₁ δ₂ δ₃ δ₄ : ℤ), ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄ ∧
      ∃ (ψ : ℕ → L) (δ : ℤ), ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ := by
  obtain ⟨c₀, c₁, c₂, c₃, c₄, δ₀, δ₁, δ₂, δ₃, δ₄, A⟩ := h.stageA
  obtain ⟨a, b, p, s, hE1⟩ := h.shapeE A h.one_mem
  have e10 : (1 : ℤ) - 0 = 1 := by norm_num
  rcases hE1.ha with ha | ha <;> rcases hE1.hb with hb | hb
  · have hE := hE1.swap02.swap13
    rw [ha, hb, e10] at hE
    exact ⟨_, _, _, _, _, _, _, _, _, _, A.swap02.swap13,
      h.eSystem_of_normalized A.swap02.swap13 hE⟩
  · have hE := hE1.swap02
    rw [ha, hb, e10] at hE
    exact ⟨_, _, _, _, _, _, _, _, _, _, A.swap02, h.eSystem_of_normalized A.swap02 hE⟩
  · have hE := hE1.swap13
    rw [ha, hb, e10] at hE
    exact ⟨_, _, _, _, _, _, _, _, _, _, A.swap13, h.eSystem_of_normalized A.swap13 hE⟩
  · rw [ha, hb] at hE1
    exact ⟨_, _, _, _, _, _, _, _, _, _, A, h.eSystem_of_normalized A hE1⟩

end StageE

section StageF

variable {k : ℕ} {B : Finset L} {deg Θ : L → ℤ} {E F : ℕ → L → ℤ} {U V : L → ℤ}
  {c₀ c₁ c₂ c₃ c₄ : L} {δ₀ δ₁ δ₂ δ₃ δ₄ δ : ℤ} {ψ : ℕ → L}

theorem ESystem.sum_E_mul (S : ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ) (h₀ : c₀ ∈ B)
    (h₁ : c₁ ∈ B) {l : ℕ} (hl : l ∈ Icc 1 (k - 1)) (f : L → ℤ) :
    ∑ x ∈ B, E l x * f x = δ₀ * f c₀ + δ₁ * f c₁ - δ * f (ψ l) := by
  rw [Finset.sum_congr rfl fun x hx => by rw [S.hE l hl x hx]]
  have hψ := (Finset.mem_sdiff.mp (S.hψ l hl)).1
  simp [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, h₀, h₁, hψ]

theorem ESystem.sum_mul_E (S : ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ) (h₀ : c₀ ∈ B)
    (h₁ : c₁ ∈ B) {l : ℕ} (hl : l ∈ Icc 1 (k - 1)) (f : L → ℤ) :
    ∑ x ∈ B, f x * E l x = δ₀ * f c₀ + δ₁ * f c₁ - δ * f (ψ l) := by
  rw [← S.sum_E_mul h₀ h₁ hl f]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

theorem stageF_arith {u₀ u₁ u₂ u₃ u₄ ug : ℤ} (b0 : u₀ * u₀ ≤ 1) (b1 : u₁ * u₁ ≤ 1)
    (b4 : u₄ * u₄ ≤ 1) (h15 : u₀ + u₁ + u₂ + u₃ = 0) (hU : u₀ - u₁ + u₂ - u₃ + 2 * u₄ = 0)
    (h14 : u₀ + u₁ - ug = 0)
    (hsq : u₀ * u₀ + u₁ * u₁ + u₂ * u₂ + u₃ * u₃ + u₄ * u₄ + ug * ug ≤ 2) :
    u₀ = 0 ∧ u₁ = 0 ∧ u₂ = 0 ∧ u₃ = 0 ∧ u₄ = 0 ∧ ug = 0 := by
  have e2 : u₂ = -u₄ - u₀ := by omega
  have e3 : u₃ = u₄ - u₁ := by omega
  have eg : ug = u₀ + u₁ := by omega
  subst e2 e3 eg
  rcases eq_zero_or_one_or_neg_one b0 with h0 | h0 | h0 <;>
  rcases eq_zero_or_one_or_neg_one b1 with h1 | h1 | h1 <;>
  rcases eq_zero_or_one_or_neg_one b4 with h4 | h4 | h4 <;>
  · subst h0 h1 h4
    revert hsq
    norm_num

theorem Hyp.shapeF (h : Hyp k B deg Θ E F U V) (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄)
    (S : ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ) {j : ℕ} (hj : j ∈ Icc 1 (k - 1)) :
    ∃ P N : L, P ≠ N ∧ P ∈ B \ {c₀, c₁, c₂, c₃, c₄} ∧ N ∈ B \ {c₀, c₁, c₂, c₃, c₄} ∧
      (∀ l ∈ Icc 1 (k - 1), P ≠ ψ l ∧ N ≠ ψ l) ∧
      ∀ x ∈ B, F j x = (if x = P then 1 else 0) - (if x = N then 1 else 0) := by
  have hFF : ∑ x ∈ B, F j x * F j x = 2 := by simpa using h.hFF j hj j hj
  have hF1 : ∀ x ∈ B, F j x * F j x ≤ 1 := fun x hx => mul_self_le_one_of_lt_four (by
    have := Finset.single_le_sum (f := fun x => F j x * F j x) (fun x _ => mul_self_nonneg _) hx
    omega)
  have hΘF := h.hΘF j hj
  rw [A.sum_Θ_mul] at hΘF
  have hUF := h.hUF j hj
  rw [A.sum_U_mul] at hUF
  have hEF : ∀ l ∈ Icc 1 (k - 1), δ₀ * F j c₀ + δ₁ * F j c₁ - δ * F j (ψ l) = 0 :=
    fun l hl => by rw [← S.sum_E_mul A.h₀ A.h₁ hl]; exact h.hEF l hl j hj
  have hI1 := h.one_mem
  have hψ1 := S.hψ 1 hI1
  have hsplit := A.sum_split (fun x => F j x * F j x)
  have hψsq : F j (ψ 1) * F j (ψ 1) ≤ ∑ x ∈ B \ {c₀, c₁, c₂, c₃, c₄}, F j x * F j x :=
    Finset.single_le_sum (f := fun x => F j x * F j x) (fun x _ => mul_self_nonneg _) hψ1
  have hsq : ∀ {σ : ℤ}, (σ = 1 ∨ σ = -1) → ∀ e : ℤ, (σ * e) * (σ * e) = e * e := by
    intro σ hσ e
    rw [show σ * e * (σ * e) = (σ * σ) * (e * e) by ring, sign_mul_self hσ, one_mul]
  obtain ⟨z0, z1, z2, z3, z4, zg⟩ := stageF_arith (u₀ := δ₀ * F j c₀) (u₁ := δ₁ * F j c₁)
    (u₂ := δ₂ * F j c₂) (u₃ := δ₃ * F j c₃) (u₄ := δ₄ * F j c₄) (ug := δ * F j (ψ 1))
    (by rw [hsq A.s₀]; exact hF1 _ A.h₀) (by rw [hsq A.s₁]; exact hF1 _ A.h₁)
    (by rw [hsq A.s₄]; exact hF1 _ A.h₄) (by linear_combination hΘF)
    (by linear_combination hUF) (by linear_combination hEF 1 hI1)
    (by rw [hsq A.s₀, hsq A.s₁, hsq A.s₂, hsq A.s₃, hsq A.s₄, hsq S.hδ]; linarith)
  have f0 : F j c₀ = 0 := (mul_eq_zero.mp z0).resolve_left (sign_ne_zero A.s₀)
  have f1 : F j c₁ = 0 := (mul_eq_zero.mp z1).resolve_left (sign_ne_zero A.s₁)
  have f2 : F j c₂ = 0 := (mul_eq_zero.mp z2).resolve_left (sign_ne_zero A.s₂)
  have f3 : F j c₃ = 0 := (mul_eq_zero.mp z3).resolve_left (sign_ne_zero A.s₃)
  have f4 : F j c₄ = 0 := (mul_eq_zero.mp z4).resolve_left (sign_ne_zero A.s₄)
  have fψ : ∀ l ∈ Icc 1 (k - 1), F j (ψ l) = 0 := by
    intro l hl
    have e := hEF l hl
    rw [f0, f1] at e
    have : δ * F j (ψ l) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (sign_ne_zero S.hδ)
  have hcard := sum_mul_self_eq_card hF1
  rw [hFF] at hcard
  obtain ⟨P, N, hPN, hsupp⟩ := Finset.card_eq_two.mp (by exact_mod_cast hcard.symm)
  have hmem : ∀ x, x ∈ B ∧ F j x ≠ 0 ↔ x = P ∨ x = N := by
    intro x
    have := Finset.ext_iff.mp hsupp x
    simpa only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] using this
  obtain ⟨hPB, hP0⟩ := (hmem P).mpr (Or.inl rfl)
  obtain ⟨hNB, hN0⟩ := (hmem N).mpr (Or.inr rfl)
  have hout : ∀ x ∈ B, x ≠ P → x ≠ N → F j x = 0 := by
    intro x hx hxP hxN
    by_contra hne
    rcases (hmem x).mp ⟨hx, hne⟩ with e | e
    exacts [hxP e, hxN e]
  have hvP := (eq_zero_or_one_or_neg_one (hF1 P hPB)).resolve_left hP0
  have hvN := (eq_zero_or_one_or_neg_one (hF1 N hNB)).resolve_left hN0
  have hdeg2 : deg P * F j P + deg N * F j N = 0 := by
    rw [← h.hdegF j hj, ← Finset.sum_pair (f := fun x => deg x * F j x) hPN]
    refine Finset.sum_subset (fun x hx => ?_) fun x hx hx' => ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      exacts [hPB, hNB]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
      rw [hout x hx hx'.1 hx'.2, mul_zero]
  have hdP := h.hdeg P hPB
  have hdN := h.hdeg N hNB
  have hC : ∀ x, F j x ≠ 0 → x ∈ B → x ∈ B \ {c₀, c₁, c₂, c₃, c₄} ∧
      ∀ l ∈ Icc 1 (k - 1), x ≠ ψ l := by
    intro x hx hxB
    refine ⟨mem_sdiff_five.mpr ⟨hxB, ?_, ?_, ?_, ?_, ?_⟩, fun l hl e => hx (e ▸ fψ l hl)⟩
    · exact fun e => hx (e ▸ f0)
    · exact fun e => hx (e ▸ f1)
    · exact fun e => hx (e ▸ f2)
    · exact fun e => hx (e ▸ f3)
    · exact fun e => hx (e ▸ f4)
  obtain ⟨hPC, hPψ⟩ := hC P hP0 hPB
  obtain ⟨hNC, hNψ⟩ := hC N hN0 hNB
  rcases hvP with eP | eP <;> rcases hvN with eN | eN
  · rw [eP, eN] at hdeg2
    linarith
  · refine ⟨P, N, hPN, hPC, hNC, fun l hl => ⟨hPψ l hl, hNψ l hl⟩, fun x hx => ?_⟩
    by_cases xP : x = P
    · subst xP
      simp [eP, hPN]
    by_cases xN : x = N
    · subst xN
      simp [eN, hPN.symm]
    simp [xP, xN, hout x hx xP xN]
  · refine ⟨N, P, hPN.symm, hNC, hPC, fun l hl => ⟨hNψ l hl, hPψ l hl⟩, fun x hx => ?_⟩
    by_cases xP : x = P
    · subst xP
      simp [eP, hPN]
    by_cases xN : x = N
    · subst xN
      simp [eN, hPN.symm]
    simp [xP, xN, hout x hx xP xN]
  · rw [eP, eN] at hdeg2
    linarith

theorem pair_rel {P N P' N' : L} (hPN : P ≠ N) (hPN' : P' ≠ N')
    (h : ((if P = P' then (1 : ℤ) else 0) - (if P = N' then 1 else 0)) -
      ((if N = P' then 1 else 0) - (if N = N' then 1 else 0)) = 1) :
    ((P = P' ∧ N ≠ N') ∨ (P ≠ P' ∧ N = N')) ∧ P ≠ N' ∧ N ≠ P' := by
  split_ifs at h with h1 h2 h3 h4 h4 h3 h4 h4 h2 h3 h4 h4 h3 h4 h4 <;> norm_num at h <;>
    first
    | exact ⟨Or.inl ⟨h1, h4⟩, h2, h3⟩
    | exact ⟨Or.inr ⟨h1, h4⟩, h2, h3⟩
    | (subst_vars; exact absurd rfl hPN)

theorem star {I : Finset ℕ} {P N : ℕ → L} (h1 : 1 ∈ I) (h2 : 2 ∈ I)
    (hrel : ∀ j ∈ I, ∀ j' ∈ I, j ≠ j' →
      ((P j = P j' ∧ N j ≠ N j') ∨ (P j ≠ P j' ∧ N j = N j')) ∧ P j ≠ N j' ∧ N j ≠ P j') :
    (∀ j ∈ I, P j = P 1) ∨ (∀ j ∈ I, N j = N 1) := by
  rcases (hrel 1 h1 2 h2 (by norm_num)).1 with ⟨hP, hN⟩ | ⟨hP, hN⟩
  · left
    intro j hj
    by_cases hj1 : j = 1
    · rw [hj1]
    by_cases hj2 : j = 2
    · rw [hj2]
      exact hP.symm
    by_contra hne
    rcases (hrel 1 h1 j hj (Ne.symm hj1)).1 with ⟨e, -⟩ | ⟨-, e1⟩
    · exact hne e.symm
    rcases (hrel 2 h2 j hj (Ne.symm hj2)).1 with ⟨e, -⟩ | ⟨-, e2⟩
    · exact hne (e.symm.trans hP.symm)
    · exact hN (e1.trans e2.symm)
  · right
    intro j hj
    by_cases hj1 : j = 1
    · rw [hj1]
    by_cases hj2 : j = 2
    · rw [hj2]
      exact hN.symm
    by_contra hne
    rcases (hrel 1 h1 j hj (Ne.symm hj1)).1 with ⟨e1, -⟩ | ⟨-, e⟩
    swap
    · exact hne e.symm
    rcases (hrel 2 h2 j hj (Ne.symm hj2)).1 with ⟨e2, -⟩ | ⟨-, e⟩
    · exact hP (e1.trans e2.symm)
    · exact hne (e.symm.trans hN.symm)

structure FSystem (k : ℕ) (B : Finset L) (F : ℕ → L → ℤ) (c₀ c₁ c₂ c₃ c₄ : L) (ψ ν : ℕ → L)
    (δF : ℤ) : Prop where
  hδF : δF = 1 ∨ δF = -1
  hν : ∀ i ∈ range k, ν i ∈ B \ {c₀, c₁, c₂, c₃, c₄}
  νψ : ∀ i ∈ range k, ∀ l ∈ Icc 1 (k - 1), ν i ≠ ψ l
  inj : Set.InjOn ν (range k : Set ℕ)
  hF : ∀ j ∈ Icc 1 (k - 1), ∀ x ∈ B,
    F j x = δF * ((if x = ν j then 1 else 0) - (if x = ν 0 then 1 else 0))

theorem FSystem.of_center {z : L} {w : ℕ → L} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hz : z ∈ B \ {c₀, c₁, c₂, c₃, c₄}) (hzψ : ∀ l ∈ Icc 1 (k - 1), z ≠ ψ l)
    (hw : ∀ j ∈ Icc 1 (k - 1), w j ∈ B \ {c₀, c₁, c₂, c₃, c₄})
    (hwψ : ∀ j ∈ Icc 1 (k - 1), ∀ l ∈ Icc 1 (k - 1), w j ≠ ψ l)
    (hwz : ∀ j ∈ Icc 1 (k - 1), w j ≠ z) (hwinj : Set.InjOn w (Icc 1 (k - 1) : Set ℕ))
    (hF : ∀ j ∈ Icc 1 (k - 1), ∀ x ∈ B,
      F j x = σ * ((if x = w j then 1 else 0) - (if x = z then 1 else 0))) :
    FSystem k B F c₀ c₁ c₂ c₃ c₄ ψ (fun i => if i = 0 then z else w i) σ := by
  have hI : ∀ i ∈ range k, i ≠ 0 → i ∈ Icc 1 (k - 1) := fun i hi hi0 => by
    rw [Finset.mem_range] at hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  refine ⟨hσ, fun i hi => ?_, fun i hi l hl => ?_, fun i hi i' hi' e => ?_, fun j hj x hx => ?_⟩
  · by_cases hi0 : i = 0
    · simp only [hi0, ↓reduceIte]
      exact hz
    · simp only [hi0, ↓reduceIte]
      exact hw i (hI i hi hi0)
  · by_cases hi0 : i = 0
    · simp only [hi0, ↓reduceIte]
      exact hzψ l hl
    · simp only [hi0, ↓reduceIte]
      exact hwψ i (hI i hi hi0) l hl
  · by_cases hi0 : i = 0 <;> by_cases hi0' : i' = 0
    · rw [hi0, hi0']
    · simp only [hi0, hi0', ↓reduceIte] at e
      exact absurd e.symm (hwz i' (hI i' hi' hi0'))
    · simp only [hi0, hi0', ↓reduceIte] at e
      exact absurd e (hwz i (hI i hi hi0))
    · simp only [hi0, hi0', ↓reduceIte] at e
      exact hwinj (hI i hi hi0) (hI i' hi' hi0') e
  · have hj0 : j ≠ 0 := by
      rw [Finset.mem_Icc] at hj
      omega
    simp only [hj0, ↓reduceIte]
    exact hF j hj x hx

theorem Hyp.stageF (h : Hyp k B deg Θ E F U V) (A : ShapeA B Θ U c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ₂ δ₃ δ₄)
    (S : ESystem k B E c₀ c₁ c₂ c₃ c₄ δ₀ δ₁ δ ψ) :
    ∃ (ν : ℕ → L) (δF : ℤ), FSystem k B F c₀ c₁ c₂ c₃ c₄ ψ ν δF := by
  have hshape : ∀ j, ∃ P N : L, j ∈ Icc 1 (k - 1) → P ≠ N ∧
      P ∈ B \ {c₀, c₁, c₂, c₃, c₄} ∧ N ∈ B \ {c₀, c₁, c₂, c₃, c₄} ∧
      (∀ l ∈ Icc 1 (k - 1), P ≠ ψ l ∧ N ≠ ψ l) ∧
      ∀ x ∈ B, F j x = (if x = P then 1 else 0) - (if x = N then 1 else 0) := by
    intro j
    by_cases hj : j ∈ Icc 1 (k - 1)
    · obtain ⟨P, N, hS⟩ := h.shapeF A S hj
      exact ⟨P, N, fun _ => hS⟩
    · exact ⟨c₀, c₀, fun h' => absurd h' hj⟩
  choose P N hPN using hshape
  have hB : ∀ j ∈ Icc 1 (k - 1), P j ∈ B ∧ N j ∈ B := fun j hj =>
    ⟨(Finset.mem_sdiff.mp (hPN j hj).2.1).1, (Finset.mem_sdiff.mp (hPN j hj).2.2.1).1⟩
  have hrel : ∀ j ∈ Icc 1 (k - 1), ∀ j' ∈ Icc 1 (k - 1), j ≠ j' →
      ((P j = P j' ∧ N j ≠ N j') ∨ (P j ≠ P j' ∧ N j = N j')) ∧ P j ≠ N j' ∧ N j ≠ P j' := by
    intro j hj j' hj' hne
    refine pair_rel (hPN j hj).1 (hPN j' hj').1 ?_
    have e := h.hFF j hj j' hj'
    rw [ite_eq_right hne, add_zero,
      Finset.sum_congr rfl fun x hx => by rw [(hPN j hj).2.2.2.2 x hx]] at e
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', (hB j hj).1, (hB j hj).2, ↓reduceIte] at e
    rw [(hPN j' hj').2.2.2.2 _ (hB j hj).1, (hPN j' hj').2.2.2.2 _ (hB j hj).2] at e
    exact e
  have hI1 := h.one_mem
  have hNcase : (∀ j ∈ Icc 1 (k - 1), N j = N 1) → Set.InjOn P (Icc 1 (k - 1) : Set ℕ) →
      ∃ (ν : ℕ → L) (δF : ℤ), FSystem k B F c₀ c₁ c₂ c₃ c₄ ψ ν δF := by
    intro hN hPinj
    refine ⟨_, _, FSystem.of_center (Or.inl rfl) (hPN 1 hI1).2.2.1
      (fun l hl => ((hPN 1 hI1).2.2.2.1 l hl).2) (fun j hj => (hPN j hj).2.1)
      (fun j hj l hl => ((hPN j hj).2.2.2.1 l hl).1) (fun j hj => by
        rw [← hN j hj]
        exact (hPN j hj).1) hPinj fun j hj x hx => ?_⟩
    rw [(hPN j hj).2.2.2.2 x hx, hN j hj, one_mul]
  rcases h.hk24 with hk2 | hk4
  · have hI : ∀ j ∈ Icc 1 (k - 1), j = 1 := fun j hj => by
      rw [Finset.mem_Icc] at hj
      omega
    refine hNcase (fun j hj => by rw [hI j hj]) fun j hj j' hj' _ => ?_
    rw [hI j hj, hI j' hj']
  have hI2 : 2 ∈ Icc 1 (k - 1) := Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩
  rcases star hI1 hI2 hrel with hP | hN
  · refine ⟨_, _, FSystem.of_center (Or.inr rfl) (hPN 1 hI1).2.1
      (fun l hl => ((hPN 1 hI1).2.2.2.1 l hl).1) (fun j hj => (hPN j hj).2.2.1)
      (fun j hj l hl => ((hPN j hj).2.2.2.1 l hl).2) (fun j hj => by
        rw [← hP j hj]
        exact (hPN j hj).1.symm) (fun j hj j' hj' e => ?_) fun j hj x hx => ?_⟩
    · by_contra hne
      rcases (hrel j hj j' hj' hne).1 with ⟨-, h'⟩ | ⟨h', -⟩
      · exact h' e
      · exact h' ((hP j hj).trans (hP j' hj').symm)
    · rw [(hPN j hj).2.2.2.2 x hx, hP j hj]
      ring
  · refine hNcase hN fun j hj j' hj' e => ?_
    by_contra hne
    rcases (hrel j hj j' hj' hne).1 with ⟨-, h'⟩ | ⟨h', -⟩
    · exact h' ((hN j hj).trans (hN j' hj').symm)
    · exact h' e

end StageF

end TableCoordinates

end CFSG.Semidihedral.FieldFactorOne
