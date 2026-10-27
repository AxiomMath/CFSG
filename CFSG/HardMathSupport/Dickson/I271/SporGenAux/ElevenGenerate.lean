module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ElevenFusion

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance

@[expose] def lineAct3 (l : ℕ) (v : ℕ × ℕ) : ℕ × ℕ :=
  if l = 0 then ((6 * v.1 + 4 * v.2) % 11, (3 * v.1 + 4 * v.2) % 11)
  else if l = 1 then ((8 * v.2) % 11, (4 * v.1) % 11)
  else ((3 * v.1) % 11, (3 * v.2) % 11)

@[expose] def wordAct3 : List ℕ → ℕ × ℕ → ℕ × ℕ
  | [], v => v
  | l :: w, v => wordAct3 w (lineAct3 l v)

theorem lineAct3_zero (v : ℕ × ℕ) :
    lineAct3 0 v = ((6 * v.1 + 4 * v.2) % 11, (3 * v.1 + 4 * v.2) % 11) := by simp [lineAct3]

theorem lineAct3_one (v : ℕ × ℕ) : lineAct3 1 v = ((8 * v.2) % 11, (4 * v.1) % 11) := by
  simp [lineAct3]

theorem lineAct3_other {l : ℕ} (h0 : l ≠ 0) (h1 : l ≠ 1) (v : ℕ × ℕ) :
    lineAct3 l v = ((3 * v.1) % 11, (3 * v.2) % 11) := by simp [lineAct3, h0, h1]

@[expose] def facData : ℕ → List (List ℕ × (ℕ × ℕ))
  | 0 => [([2, 1, 0], (1, 8)), ([2, 0, 1], (1, 9)), ([2, 2, 2, 1, 0, 1, 0], (1, 5))]
  | 1 => [([2, 1, 0], (1, 8)), ([2, 1, 0, 0, 1, 0], (1, 6)),
      ([2, 2, 2, 0, 0, 1, 0, 1, 0, 0], (1, 3))]
  | _ => [([2, 2, 2, 1, 0, 1, 0], (1, 5)), ([2, 2, 2, 1, 0, 1, 0, 1, 0], (1, 8))]

@[expose] def facWord (l : ℕ) : List ℕ := (facData l).flatMap Prod.fst

theorem facData_fix : ∀ l < 3, ∀ r ∈ facData l,
    r.2.1 < 11 ∧ r.2.2 < 11 ∧ r.2 ≠ (0, 0) ∧ wordAct3 r.1 r.2 = r.2 := by decide +kernel

theorem facWord_act : ∀ l < 3, ∀ a < 11, ∀ b < 11,
    wordAct3 (facWord l) (a, b) = lineAct3 l (a, b) := by decide +kernel

section Group

variable {G : Type*} [Group G]

@[expose] def letter3 (x₃ x₄ x₅ : G) (l : ℕ) : G :=
  if l = 0 then x₃ else if l = 1 then x₄ else x₅

@[expose] def wordG3 (x₃ x₄ x₅ : G) : List ℕ → G
  | [] => 1
  | l :: w => wordG3 x₃ x₄ x₅ w * letter3 x₃ x₄ x₅ l

theorem letter3_zero (x₃ x₄ x₅ : G) : letter3 x₃ x₄ x₅ 0 = x₃ := by simp [letter3]

theorem letter3_one (x₃ x₄ x₅ : G) : letter3 x₃ x₄ x₅ 1 = x₄ := by simp [letter3]

theorem letter3_other (x₃ x₄ x₅ : G) {l : ℕ} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    letter3 x₃ x₄ x₅ l = x₅ := by simp [letter3, h0, h1]

theorem wordG3_append (x₃ x₄ x₅ : G) (w₁ w₂ : List ℕ) :
    wordG3 x₃ x₄ x₅ (w₁ ++ w₂) = wordG3 x₃ x₄ x₅ w₂ * wordG3 x₃ x₄ x₅ w₁ := by
  induction w₁ with
  | nil => simp [wordG3]
  | cons l w ih =>
    show wordG3 x₃ x₄ x₅ (w ++ w₂) * letter3 x₃ x₄ x₅ l = _
    rw [ih, mul_assoc]
    rfl

variable {x y x₃ x₄ x₅ : G} (hx : x ^ 11 = 1) (hy : y ^ 11 = 1) (hxy : x * y = y * x)
  (h3x : x₃ * x * x₃⁻¹ = x ^ 6 * y ^ 3) (h3y : x₃ * y * x₃⁻¹ = x ^ 4 * y ^ 4)
  (h4x : x₄ * x * x₄⁻¹ = y ^ 4) (h4y : x₄ * y * x₄⁻¹ = x ^ 8)
  (h5x : x₅ * x * x₅⁻¹ = x ^ 3) (h5y : x₅ * y * x₅⁻¹ = y ^ 3)

include hx hy hxy h3x h3y h4x h4y h5x h5y in
theorem conj_letter3_eps (l : ℕ) (v : ℕ × ℕ) :
    letter3 x₃ x₄ x₅ l * eps x y v * (letter3 x₃ x₄ x₅ l)⁻¹ = eps x y (lineAct3 l v) := by
  rw [conj_eps]
  by_cases h0 : l = 0
  · subst h0
    rw [letter3_zero, lineAct3_zero, h3x, h3y]
    have e1 : (x ^ 6 * y ^ 3) ^ v.1 = eps x y (6 * v.1, 3 * v.1) := by
      have := eps_pow hxy (6, 3) v.1
      simp only [eps] at this ⊢
      rw [this]; ring_nf
    have e2 : (x ^ 4 * y ^ 4) ^ v.2 = eps x y (4 * v.2, 4 * v.2) := by
      have := eps_pow hxy (4, 4) v.2
      simp only [eps] at this ⊢
      rw [this]; ring_nf
    rw [e1, e2, eps_mul_eps hxy, eps_mod hx hy]
  by_cases h1 : l = 1
  · subst h1
    rw [letter3_one, lineAct3_one, h4x, h4y]
    have e1 : (y ^ 4) ^ v.1 = eps x y (0, 4 * v.1) := by simp [eps, ← pow_mul, mul_comm]
    have e2 : (x ^ 8) ^ v.2 = eps x y (8 * v.2, 0) := by simp [eps, ← pow_mul, mul_comm]
    rw [e1, e2, eps_mul_eps hxy, eps_mod hx hy]
    simp
  · rw [letter3_other x₃ x₄ x₅ h0 h1, lineAct3_other h0 h1, h5x, h5y]
    have e1 : (x ^ 3) ^ v.1 = eps x y (3 * v.1, 0) := by simp [eps, ← pow_mul, mul_comm]
    have e2 : (y ^ 3) ^ v.2 = eps x y (0, 3 * v.2) := by simp [eps, ← pow_mul, mul_comm]
    rw [e1, e2, eps_mul_eps hxy, eps_mod hx hy]
    simp

include hx hy hxy h3x h3y h4x h4y h5x h5y in
theorem conj_word3_eps (w : List ℕ) (v : ℕ × ℕ) :
    wordG3 x₃ x₄ x₅ w * eps x y v * (wordG3 x₃ x₄ x₅ w)⁻¹ = eps x y (wordAct3 w v) := by
  induction w generalizing v with
  | nil => simp [wordG3, wordAct3]
  | cons l w ih =>
    rw [wordG3, wordAct3, ← ih]
    rw [← conj_letter3_eps hx hy hxy h3x h3y h4x h4y h5x h5y l v]
    group

include hx h4x h4y in
theorem y_ne_pow_x (hx1 : x ≠ 1) : ∀ k : ℕ, y ≠ x ^ k := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hox : orderOf x = 11 := orderOf_eq_prime hx hx1
  intro k hk
  have h1 : x₄ * y * x₄⁻¹ = (x₄ * x * x₄⁻¹) ^ k := by
    rw [hk, ← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  rw [h4y, h4x, hk, ← pow_mul, ← pow_mul] at h1
  have h2 := (pow_eq_pow_iff_modEq.1 h1)
  rw [hox] at h2
  have h3 : (8 : ℕ) % 11 = (k * (4 * k)) % 11 := h2
  have h4 : (k * (4 * k)) % 11 = (4 * ((k % 11) * (k % 11))) % 11 := by
    rw [show k * (4 * k) = 4 * (k * k) by ring, Nat.mul_mod, Nat.mul_mod k k]
    simp [Nat.mul_mod]
  rw [h4] at h3
  have hk11 : k % 11 < 11 := Nat.mod_lt _ (by norm_num)
  generalize k % 11 = r at h3 hk11
  interval_cases r <;> norm_num at h3

include hx hy hxy h4x h4y in
theorem eps_ne_one (hx1 : x ≠ 1) {v : ℕ × ℕ} (h1 : v.1 < 11) (h2 : v.2 < 11) (hv : v ≠ (0, 0)) :
    eps x y v ≠ 1 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hox : orderOf x = 11 := orderOf_eq_prime hx hx1
  have hyx := y_ne_pow_x hx h4x h4y hx1
  intro h
  obtain ⟨a, b⟩ := v
  simp only [eps] at h
  simp only at h1 h2
  by_cases hb : b = 0
  · subst hb
    rw [pow_zero, mul_one] at h
    have : 11 ∣ a := hox ▸ orderOf_dvd_of_pow_eq_one h
    have ha : a = 0 := Nat.eq_zero_of_dvd_of_lt this h1
    exact hv (by rw [ha])
  · have hb' : 0 < b := Nat.pos_of_ne_zero hb
    have hcop : Nat.Coprime b 11 := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2
      (fun hd => by have := Nat.le_of_dvd hb' hd; omega)))
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
    have hyb : y ^ b = (x ^ a)⁻¹ := eq_inv_of_mul_eq_one_right h
    have hym : y = (y ^ b) ^ m := by
      calc y = y ^ 1 := (pow_one y).symm
        _ = y ^ (b * m % 11) := by rw [hm]
        _ = y ^ (b * m) := (pow_eq_pow_mod _ hy).symm
        _ = (y ^ b) ^ m := pow_mul y b m
    have hk : y = x ^ (10 * (a * m)) := by
      calc y = (y ^ b) ^ m := hym
        _ = ((x ^ a)⁻¹) ^ m := by rw [hyb]
        _ = (x ^ (a * m))⁻¹ := by rw [inv_pow, ← pow_mul]
        _ = x ^ (10 * (a * m)) := by
          apply inv_eq_of_mul_eq_one_right
          rw [← pow_add, show a * m + 10 * (a * m) = 11 * (a * m) by ring, pow_mul, hx, one_pow]
    exact hyx _ hk

include hx hy hxy h3x h3y h4x h4y h5x h5y in
theorem closure_centralizers_eq_top (hx1 : x ≠ 1) {t : G} (htx : t * x = x * t)
    (hgen : Subgroup.closure ({x, y, x₃, x₄, x₅, t} : Set G) = ⊤) :
    Subgroup.closure {σ : G | ∃ e ∈ epsSubgroup hx hy hxy, e ≠ 1 ∧ σ * e = e * σ} = ⊤ := by
  obtain ⟨T, hT⟩ : ∃ T : Set G, T = {σ : G | ∃ e ∈ epsSubgroup hx hy hxy, e ≠ 1 ∧ σ * e = e * σ} :=
    ⟨_, rfl⟩
  rw [← hT]
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, H = Subgroup.closure T := ⟨_, rfl⟩
  rw [← hH]
  have hTH : T ⊆ H := hH ▸ Subgroup.subset_closure
  have hxE : x ∈ epsSubgroup hx hy hxy := ⟨(1, 0), by simp [eps]⟩
  have hxe : eps x y (1, 0) = x := by simp [eps]
  have hxT : x ∈ T := hT ▸ ⟨x, hxE, hx1, rfl⟩
  have hyT : y ∈ T := hT ▸ ⟨x, hxE, hx1, hxy.symm⟩
  have htT : t ∈ T := hT ▸ ⟨x, hxE, hx1, htx⟩
  have hrefl : ∀ (w : List ℕ) (v : ℕ × ℕ), v.1 < 11 → v.2 < 11 → v ≠ (0, 0) →
      wordAct3 w v = v → wordG3 x₃ x₄ x₅ w ∈ T := by
    intro w v h1 h2 hv hw
    rw [hT]
    refine ⟨eps x y v, ⟨v, rfl⟩, eps_ne_one hx hy hxy h4x h4y hx1 h1 h2 hv, ?_⟩
    have := conj_word3_eps hx hy hxy h3x h3y h4x h4y h5x h5y w v
    rw [hw] at this
    calc wordG3 x₃ x₄ x₅ w * eps x y v
        = (wordG3 x₃ x₄ x₅ w * eps x y v * (wordG3 x₃ x₄ x₅ w)⁻¹) * wordG3 x₃ x₄ x₅ w := by group
      _ = eps x y v * wordG3 x₃ x₄ x₅ w := by rw [this]
  have hmem : ∀ L : List (List ℕ × (ℕ × ℕ)),
      (∀ r ∈ L, r.2.1 < 11 ∧ r.2.2 < 11 ∧ r.2 ≠ (0, 0) ∧ wordAct3 r.1 r.2 = r.2) →
        wordG3 x₃ x₄ x₅ (L.flatMap Prod.fst) ∈ H := by
    intro L
    induction L with
    | nil => intro _; exact H.one_mem
    | cons r L ih =>
      intro hL
      rw [List.flatMap_cons, wordG3_append]
      obtain ⟨hr1, hr2, hr3, hr4⟩ := hL r (List.mem_cons_self ..)
      exact H.mul_mem (ih fun r' hr' => hL r' (List.mem_cons_of_mem _ hr'))
        (hTH (hrefl r.1 r.2 hr1 hr2 hr3 hr4))
  have hlet : ∀ l < 3, letter3 x₃ x₄ x₅ l ∈ H := by
    intro l hl
    have hg := hmem (facData l) (facData_fix l hl)
    have hg' : wordG3 x₃ x₄ x₅ (facWord l) ∈ H := hg
    obtain ⟨g, hgdef⟩ : ∃ g : G, g = wordG3 x₃ x₄ x₅ (facWord l) := ⟨_, rfl⟩
    rw [← hgdef] at hg'
    obtain ⟨L, hLdef⟩ : ∃ L : G, L = letter3 x₃ x₄ x₅ l := ⟨_, rfl⟩
    have hconj1 := conj_word3_eps hx hy hxy h3x h3y h4x h4y h5x h5y (facWord l) (1, 0)
    have hconj2 := conj_letter3_eps hx hy hxy h3x h3y h4x h4y h5x h5y l (1, 0)
    rw [facWord_act l hl 1 (by norm_num) 0 (by norm_num), ← hgdef, hxe] at hconj1
    rw [hxe, ← hLdef] at hconj2
    have hgL : g * x * g⁻¹ = L * x * L⁻¹ := hconj1.trans hconj2.symm
    have hc : (g⁻¹ * L) * x = x * (g⁻¹ * L) := by
      calc g⁻¹ * L * x = g⁻¹ * (L * x * L⁻¹) * L := by group
        _ = g⁻¹ * (g * x * g⁻¹) * L := by rw [hgL]
        _ = x * (g⁻¹ * L) := by group
    have hcT : g⁻¹ * L ∈ T := hT ▸ ⟨x, hxE, hx1, hc⟩
    have : L = g * (g⁻¹ * L) := by group
    rw [← hLdef, this]
    exact H.mul_mem hg' (hTH hcT)
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hTH hxT
  · exact hTH hyT
  · exact (letter3_zero a x₄ x₅) ▸ hlet 0 (by norm_num)
  · exact (letter3_one x₃ a x₅) ▸ hlet 1 (by norm_num)
  · exact (letter3_other x₃ x₄ a (by norm_num) (by norm_num) : letter3 x₃ x₄ a 2 = a) ▸
      hlet 2 (by norm_num)
  · exact hTH htT

end Group

end CFSG.HardMathSupport.Dickson.I271
