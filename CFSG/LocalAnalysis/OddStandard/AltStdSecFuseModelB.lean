module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseGam

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

theorem fixG_cons (a : ℕ) (l : List ℕ) (x : W a) (y : Gam l) :
    fixG (a :: l) (Gam.cons x y) = fixW a x + fixG l y := rfl

theorem exists_sign_W (a : ℕ) (ha : 1 ≤ a) (ε : ℤˣ) : ∃ w : W a, sgW a w = ε := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact exists_odd_W a ha

theorem exists_sign_Gam : ∀ l : List ℕ, l ≠ [] → (∀ b ∈ l, 1 ≤ b) → ∀ ε : ℤˣ,
    ∃ u : Gam l, sgG l u = ε
  | [], h, _, _ => absurd rfl h
  | b :: l, _, hl, ε => by
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact ⟨1, map_one _⟩
    · obtain ⟨x, hx⟩ := exists_odd_W b (hl b List.mem_cons_self)
      exact ⟨Gam.cons x 1, by rw [sgG_cons, hx, map_one, mul_one]⟩

theorem eq_cL_of_central : ∀ l : List ℕ, (∀ a ∈ l, 2 ≤ a) → ∀ γ : Gam l,
    (∀ x : Gam l, x * γ = γ * x) → γ * γ = 1 → fixG l γ ≤ 3 → γ = cL l := by
  intro l
  induction l with
  | nil => intro _ γ _ _ _; exact Subsingleton.elim _ _
  | cons a l ih =>
    rintro hl ⟨γ₁, γ₂⟩ hc hsq hf
    obtain ⟨hc₁, hc₂⟩ := central_cons hc
    obtain ⟨hs₁, hs₂⟩ := sq_cons hsq
    have ha : 2 ≤ a := hl a List.mem_cons_self
    have hl' : ∀ b ∈ l, 2 ≤ b := fun b hb => hl b (List.mem_cons_of_mem _ hb)
    have hf' : fixW a γ₁ + fixG l γ₂ ≤ 3 := hf
    have h1 : γ₁ = cc a := by
      rcases central_inv_W a γ₁ hc₁ hs₁ with rfl | ⟨_, h⟩
      · exfalso
        have h4 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
        rw [fixW_one] at hf'
        omega
      · exact h
    have h2 : γ₂ = cL l := ih hl' γ₂ hc₂ hs₂ (by omega)
    rw [h1, h2]
    rfl

theorem sgW_wr_one (n : ℕ) (a b : W n) : sgW (n + 1) (wr a b 1) = sgW n a * sgW n b := by
  rw [sgW_succ]
  simp

theorem sgW_wr_z2 (n : ℕ) (a b : W n) :
    sgW (n + 1) (wr a b z2) = sgW n a * sgW n b * (-1) ^ (2 ^ n) := by
  rw [sgW_succ]
  simp [z2_ne_one]

theorem sgW_cc_even (b : ℕ) (hb : 2 ≤ b) : sgW b (cc b) = 1 := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  exact sgW_cc_succ b' (by omega)

theorem eq_diag_cc_of_commute_even (b : ℕ) (hb : 2 ≤ b) (u₀ : W b ≀ᵣ Z2)
    (hc : ∀ δ : W b ≀ᵣ Z2, sgW (b + 1) δ = 1 → δ * u₀ = u₀ * δ) (h2 : u₀ * u₀ = 1)
    (hf : fixW (b + 1) u₀ ≤ 3) : u₀ = diag (cc b) := by
  have hb1 : 1 ≤ b := by omega
  obtain ⟨u, v, q, rfl⟩ : ∃ (u v : W b) (q : Z2), u₀ = wr u v q := ⟨_, _, _, (wr_eta u₀).symm⟩
  rcases z2_cases q with rfl | rfl
  ·
    have hsq : u * u = 1 ∧ v * v = 1 := by
      have h := wr_inj.1 ((wr_mul_one u v u v 1).symm.trans (h2.trans wr_one.symm))
      exact ⟨h.1, h.2.1⟩
    have hu : ∀ w : W b, w * u = u * w := by
      intro w
      obtain ⟨s, hs⟩ := exists_sign_W b hb1 (sgW b w)
      have h := hc (wr w s 1) (by rw [sgW_wr_one, hs]; exact Int.units_mul_self _)
      rw [wr_mul_one, wr_mul_one, wr_inj] at h
      exact h.1
    have hv : ∀ w : W b, w * v = v * w := by
      intro w
      obtain ⟨s, hs⟩ := exists_sign_W b hb1 (sgW b w)
      have h := hc (wr s w 1) (by rw [sgW_wr_one, hs]; exact Int.units_mul_self _)
      rw [wr_mul_one, wr_mul_one, wr_inj] at h
      exact h.2.1
    have huv : v = u := by
      have hy : sgW (b + 1) (wr (1 : W b) 1 z2) = 1 := by
        rw [sgW_wr_z2, map_one, one_mul, one_mul]
        exact Even.neg_one_pow (Nat.even_pow.2 ⟨even_two, by omega⟩)
      have h := hc (wr 1 1 z2) hy
      rw [wr_mul_z2, wr_mul_one, wr_inj] at h
      simpa using h.1
    subst huv
    have hu1 : v ≠ 1 := by
      rintro rfl
      have h : fixW (b + 1) (wr (1 : W b) 1 1) = 2 ^ b + 2 ^ b := by
        simp [fixW_wr, fixW_one]
      have h4 : 2 ^ 2 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
      omega
    rcases central_inv_W b v hu hsq.1 with h | ⟨_, h⟩
    · exact absurd h hu1
    · rw [h, diag_eq_wr]
  ·
    exfalso
    have hw : sgW (b + 1) (wr (cc b) (1 : W b) 1) = 1 := by
      rw [sgW_wr_one, sgW_cc_even b hb, map_one, one_mul]
    have h := hc (wr (cc b) 1 1) hw
    rw [wr_mul_one, wr_mul_z2, wr_inj] at h
    have h1 : cc b * u = 1 * u := by simpa using h.1
    exact cc_ne_one b hb1 (mul_right_cancel h1)

theorem central_far (l : List ℕ) (hl : ∀ a ∈ l, 2 ≤ a) (hbig : 2 ≤ l.length ∨ ∃ a ∈ l, 3 ≤ a)
    (γ : Gam l) (hK : sgG l γ = 1) (hc : ∀ δ : Gam l, sgG l δ = 1 → δ * γ = γ * δ)
    (h2 : γ * γ = 1) (hf : fixG l γ ≤ 3) : γ = cL l := by
  have _ := hK
  rcases l with _ | ⟨a, l'⟩
  · exfalso
    rcases hbig with h | ⟨a, ha, _⟩
    · simp at h
    · simp at ha
  · have ha : 2 ≤ a := hl a List.mem_cons_self
    rcases l' with _ | ⟨b, l''⟩
    ·
      have ha3 : 3 ≤ a := by
        rcases hbig with h | ⟨c, hc', hc3⟩
        · simp at h
        · rw [List.mem_singleton] at hc'
          omega
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      obtain ⟨u₀, y⟩ := γ
      have hc' : ∀ δ : W (b + 1), sgW (b + 1) δ = 1 → δ * u₀ = u₀ * δ := by
        intro δ hδ
        have h := hc (Gam.cons δ 1) (by rw [sgG_cons, hδ, map_one, one_mul])
        exact (Prod.ext_iff.1 h).1
      have hf' : fixW (b + 1) u₀ ≤ 3 := by
        have h : fixW (b + 1) u₀ + fixG [] y ≤ 3 := hf
        have h0 : fixG [] y = 0 := rfl
        omega
      have hsingle : u₀ = diag (cc b) :=
        eq_diag_cc_of_commute_even b (by omega) u₀ hc' (sq_cons h2).1 hf'
      refine Prod.ext ?_ (Subsingleton.elim _ _)
      exact hsingle.trans (cc_succ b (by omega)).symm
    ·
      have hl1 : ∀ c ∈ b :: l'', 1 ≤ c := fun c hc' => by
        have := hl c (List.mem_cons_of_mem _ hc')
        omega
      obtain ⟨γ₁, γ₂⟩ := γ
      have hc₁ : ∀ w : W a, w * γ₁ = γ₁ * w := by
        intro w
        obtain ⟨u, hu⟩ := exists_sign_Gam (b :: l'') (List.cons_ne_nil _ _) hl1 (sgW a w)
        have h := hc (Gam.cons w u) (by rw [sgG_cons, hu]; exact Int.units_mul_self _)
        exact (Prod.ext_iff.1 h).1
      have hc₂ : ∀ u : Gam (b :: l''), u * γ₂ = γ₂ * u := by
        intro u
        obtain ⟨w, hw⟩ := exists_sign_W a (by omega) (sgG (b :: l'') u)
        have h := hc (Gam.cons w u) (by rw [sgG_cons, hw]; exact Int.units_mul_self _)
        exact (Prod.ext_iff.1 h).2
      exact eq_cL_of_central (a :: b :: l'') hl (γ₁, γ₂)
        (fun x => Prod.ext (hc₁ x.1) (hc₂ x.2)) h2 hf

end CFSG.OddStandard.AltStdSec.SylowSn
