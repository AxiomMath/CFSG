module

public import CFSG.ClassicalInvolution.Phan.PhanQ14PentW0

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

section Plane

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem inW0_conj {v : V8 K} (hv : InW0 v) : InW0 (conj D v) := by
  intro i hi
  obtain ⟨h1, h2⟩ := hv i hi
  simp [conj, h1, h2]

theorem inW2_comb {ω₁ ω₂ : V8 K} (h1 : InW2 ω₁) (h2 : InW2 ω₂) (c₁ c₂ : K) :
    InW2 (c₁ • ω₁ + c₂ • ω₂) := by
  intro i hi
  obtain ⟨a1, a2⟩ := h1 i hi
  obtain ⟨b1, b2⟩ := h2 i hi
  simp [a1, a2, b1, b2]

structure RatPlane (ω₁ ω₂ : V8 K) : Prop where
  inW2₁ : InW2 ω₁
  inW2₂ : InW2 ω₂
  fix₁ : conj D ω₁ = ω₁
  fix₂ : conj D ω₂ = ω₂
  q₁ : Q8 ω₁ = 0
  q₂ : Q8 ω₂ = 0
  b₁₂ : B8 ω₁ ω₂ = 0

variable {D} {ω₁ ω₂ : V8 K}

theorem RatPlane.b₁₁ (P : RatPlane D ω₁ ω₂) : B8 ω₁ ω₁ = 0 := by
  rw [B8_self, P.q₁, mul_zero]

theorem RatPlane.b₂₂ (P : RatPlane D ω₁ ω₂) : B8 ω₂ ω₂ = 0 := by
  rw [B8_self, P.q₂, mul_zero]

theorem RatPlane.b₂₁ (P : RatPlane D ω₁ ω₂) : B8 ω₂ ω₁ = 0 := by
  rw [B8_comm]
  exact P.b₁₂

theorem RatPlane.B_comb (P : RatPlane D ω₁ ω₂) (c₁ c₂ c₁' c₂' : K) :
    B8 (c₁ • ω₁ + c₂ • ω₂) (c₁' • ω₁ + c₂' • ω₂) = 0 := by
  rw [B8_lin_left, B8_lin_right, B8_lin_right, P.b₁₁, P.b₁₂, P.b₂₁, P.b₂₂]
  ring

theorem RatPlane.Q_comb (P : RatPlane D ω₁ ω₂) (c₁ c₂ : K) :
    Q8 (c₁ • ω₁ + c₂ • ω₂) = 0 := by
  rw [Q8_lin, P.q₁, P.q₂, P.b₁₂]
  ring

theorem RatPlane.conj_comb (P : RatPlane D ω₁ ω₂) (c₁ c₂ : K) :
    conj D (c₁ • ω₁ + c₂ • ω₂) = D.τ c₁ • ω₁ + D.τ c₂ • ω₂ := by
  rw [conj_add, conj_smul, conj_smul, P.fix₁, P.fix₂]

theorem RatPlane.her_comb (P : RatPlane D ω₁ ω₂) (c₁ c₂ c₁' c₂' : K) :
    her D (c₁ • ω₁ + c₂ • ω₂) (c₁' • ω₁ + c₂' • ω₂) = 0 := by
  rw [her, P.conj_comb]
  exact P.B_comb _ _ _ _

end Plane

section Pencil

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} {D : KData F K ε}
  {ω₁ ω₂ : V8 K}

theorem pencil_algebra (D : KData F K ε) {u v x y ws wt : V8 K} (hu : InW0 u) (hv : InW0 v)
    (hws : InW2 ws) (hwt : InW2 wt) (hQu : Q8 u = 0) (hQv : Q8 v = 0) (huv : B8 u v = 0)
    (hvx : B8 v x = 0) (hyu : B8 y u = 0) (hQws : Q8 ws = 0) (hQwt : Q8 wt = 0)
    (hBw : B8 ws wt = 0) (hss : her D ws ws = 0) (hst : her D ws wt = 0) (hts : her D wt ws = 0)
    (htt : her D wt wt = 0) (hsx : B8 ws x = -B8 u x) (hsy : B8 ws y = 0) (htx : B8 wt x = 0)
    (hty : B8 wt y = -B8 v y) :
    Q8 (u + ws) = 0 ∧ Q8 (v + wt) = 0 ∧ B8 (u + ws) (v + wt) = 0 ∧ B8 (u + ws) x = 0 ∧
      B8 (u + ws) y = 0 ∧ B8 (u + ws) u = 0 ∧ B8 (u + ws) v = 0 ∧ B8 (v + wt) x = 0 ∧
      B8 (v + wt) y = 0 ∧ B8 (v + wt) u = 0 ∧ B8 (v + wt) v = 0 ∧
      her D (u + ws) (u + ws) = her D u u ∧ her D (u + ws) (v + wt) = her D u v ∧
      her D (v + wt) (u + ws) = her D v u ∧ her D (v + wt) (v + wt) = her D v v ∧
      her D (u + ws) v = her D u v ∧ her D (v + wt) v = her D v v := by
  have b0 : ∀ {a w : V8 K}, InW0 a → InW2 w → B8 a w = 0 := fun ha hw =>
    B8_eq_zero_of_support ha hw
  have b1 : ∀ {a w : V8 K}, InW0 a → InW2 w → B8 w a = 0 := fun ha hw => by
    rw [B8_comm]
    exact b0 ha hw
  have h0 : ∀ {a w : V8 K}, InW0 a → InW2 w → her D a w = 0 := fun ha hw =>
    b0 ha (inW2_conj D hw)
  have h1 : ∀ {a w : V8 K}, InW0 a → InW2 w → her D w a = 0 := fun ha hw => by
    rw [her, B8_comm]
    exact b0 (inW0_conj D ha) hw
  have Q8_add : ∀ a b : V8 K, Q8 (a + b) = Q8 a + Q8 b + B8 a b := fun a b => by
    have h := Q8_lin (1 : K) 1 a b
    rw [one_smul, one_smul] at h
    rw [h]
    ring
  have hxu : B8 u y = 0 := by rw [B8_comm]; exact hyu
  have hvu : B8 v u = 0 := by rw [B8_comm]; exact huv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Q8_add, hQu, hQws, b0 hu hws]
    ring
  · rw [Q8_add, hQv, hQwt, b0 hv hwt]
    ring
  · rw [B8_add_left, B8_add_right, B8_add_right, huv, b0 hu hwt, b1 hv hws, hBw]
    ring
  · rw [B8_add_left, hsx]
    ring
  · rw [B8_add_left, hsy, hxu]
    ring
  · rw [B8_add_left, b1 hu hws, B8_self, hQu]
    ring
  · rw [B8_add_left, b1 hv hws, huv]
    ring
  · rw [B8_add_left, htx, hvx]
    ring
  · rw [B8_add_left, hty]
    ring
  · rw [B8_add_left, b1 hu hwt, hvu]
    ring
  · rw [B8_add_left, b1 hv hwt, B8_self, hQv]
    ring
  · rw [her_add_left, her_add_right, her_add_right, h0 hu hws, h1 hu hws, hss]
    ring
  · rw [her_add_left, her_add_right, her_add_right, h0 hu hwt, h1 hv hws, hst]
    ring
  · rw [her_add_left, her_add_right, her_add_right, h0 hv hws, h1 hu hwt, hts]
    ring
  · rw [her_add_left, her_add_right, her_add_right, h0 hv hwt, h1 hv hwt, htt]
    ring
  · rw [her_add_left, h1 hv hws]
    ring
  · rw [her_add_left, h1 hv hwt]
    ring

end Pencil

section Solve

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} {D : KData F K ε}
  {ω₁ ω₂ : V8 K}

theorem exists_ws_wt (P : RatPlane D ω₁ ω₂) {x y : V8 K} (A R : K)
    (hdet : B8 ω₁ x * B8 ω₂ y - B8 ω₂ x * B8 ω₁ y ≠ 0) :
    ∃ ws wt : V8 K, InW2 ws ∧ InW2 wt ∧ Q8 ws = 0 ∧ Q8 wt = 0 ∧ B8 ws wt = 0 ∧
      her D ws ws = 0 ∧ her D ws wt = 0 ∧ her D wt ws = 0 ∧ her D wt wt = 0 ∧
      B8 ws x = -A ∧ B8 ws y = 0 ∧ B8 wt x = 0 ∧ B8 wt y = -R := by
  set Δ := B8 ω₁ x * B8 ω₂ y - B8 ω₂ x * B8 ω₁ y with hΔ
  refine ⟨(-(A * B8 ω₂ y) / Δ) • ω₁ + (A * B8 ω₁ y / Δ) • ω₂,
    (R * B8 ω₂ x / Δ) • ω₁ + (-(R * B8 ω₁ x) / Δ) • ω₂,
    inW2_comb P.inW2₁ P.inW2₂ _ _, inW2_comb P.inW2₁ P.inW2₂ _ _, P.Q_comb _ _, P.Q_comb _ _,
    P.B_comb _ _ _ _, P.her_comb _ _ _ _, P.her_comb _ _ _ _, P.her_comb _ _ _ _,
    P.her_comb _ _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [B8_lin_left]
    field_simp
    ring
  · rw [B8_lin_left]
    field_simp
    ring
  · rw [B8_lin_left]
    field_simp
    ring
  · rw [B8_lin_left]
    field_simp
    ring

end Solve

section Main

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} {D : KData F K ε}
  {ω₁ ω₂ : V8 K} [Fintype K] [DecidableEq K]

theorem exists_common_nbr_of_plane (hq2 : 2 ≤ Nat.card F)
    (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2) (P : RatPlane D ω₁ ω₂) {u v x y : V8 K}
    (hu : InW0 u) (hv : InW0 v) (huf : ffK D u) (hvf : ffK D v) (hxf : ffK D x) (hyf : ffK D y)
    (huv : ColK D u v) (hvx : ColK D v x) (hyu : ColK D y u)
    (hdet : B8 ω₁ x * B8 ω₂ y - B8 ω₂ x * B8 ω₁ y ≠ 0) :
    ∃ e : V8 K, ffK D e ∧ ColK D e u ∧ ColK D e v ∧ ColK D e x ∧ ColK D e y := by
  obtain ⟨ws, wt, hws, hwt, hQws, hQwt, hBw, hss, hst, hts, htt, hsx, hsy, htx, hty⟩ :=
    exists_ws_wt P (B8 u x) (B8 v y) hdet
  obtain ⟨hQs, hQt, hB0, hBsx, hBsy, hBsu, hBsv, hBtx, hBty, hBtu, hBtv, hhss, hhst, hhts, hhtt,
    hhsv, hhtv⟩ := pencil_algebra D hu hv hws hwt huf.1 hvf.1 huv.1 hvx.1 hyu.1 hQws hQwt hBw
    hss hst hts htt hsx hsy htx hty
  have hG : gram D (u + ws) (v + wt) ≠ 0 := by
    unfold gram
    rw [hhss, hhst, hhts, hhtt]
    exact huv.2
  have hx : ∀ i, ffK D (![x, y, u] i) := by
    intro i
    fin_cases i
    exacts [hxf, hyf, huf]
  have hsx' : ∀ i, B8 (u + ws) (![x, y, u] i) = 0 := by
    intro i
    fin_cases i
    exacts [hBsx, hBsy, hBsu]
  have htx' : ∀ i, B8 (v + wt) (![x, y, u] i) = 0 := by
    intro i
    fin_cases i
    exacts [hBtx, hBty, hBtu]
  have hm : (3 + 1) * (Nat.card F + 1) < Nat.card F ^ 2 := hq5
  obtain ⟨μ, hff, hcol⟩ := exists_good_pencil D hq2 (m := 3) hm hQs hQt hB0 hG ![x, y, u] hx hsx'
    htx'
  refine ⟨u + ws + μ • (v + wt), hff, hcol 2, ?_, hcol 0, hcol 1⟩
  refine ⟨?_, ?_⟩
  · rw [B8_add_left, B8_smul_left, hBsv, hBtv]
    ring
  · have e1 : D.τ (her D u v) = her D v u := (her_conj_symm D u v).symm
    have e2 : D.τ (her D v v) = her D v v := her_self_fixed D v
    rw [gram_pencil, hhss, hhsv, hhst, hhtv, hhtt]
    have : gram D u v = her D u u * her D v v - her D u v * her D v u := rfl
    intro h0
    apply huv.2
    rw [this]
    simp only [map_sub, map_mul, e1, e2] at h0
    linear_combination h0

end Main

section Six

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

@[expose] def wvec (a b c d : K) : V8 K := Sum.elim ![0, 0, a, b] ![0, 0, c, d]

theorem inW2_wvec (a b c d : K) : InW2 (wvec a b c d) := by
  intro i hi
  fin_cases i <;> simp [wvec] at hi ⊢

theorem conj_wvec (a b c d : K) :
    conj D (wvec a b c d) = wvec (D.τ a) (D.τ b) (D.τ c) (D.τ d) := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [conj, wvec]

theorem Q8_wvec (a b c d : K) : Q8 (wvec a b c d) = a * c + b * d := by
  rw [Q8_eq_sum]
  simp [wvec, Fin.sum_univ_four]

theorem B8_wvec_left (a b c d : K) (z : V8 K) :
    B8 (wvec a b c d) z = a * z (Sum.inr 2) + b * z (Sum.inr 3) + c * z (Sum.inl 2) +
      d * z (Sum.inl 3) := by
  rw [B8_eq_sum]
  simp [wvec, Fin.sum_univ_four]
  ring

theorem B8_wvec_wvec (a b c d a' b' c' d' : K) :
    B8 (wvec a b c d) (wvec a' b' c' d') = a * c' + b * d' + c * a' + d * b' := by
  rw [B8_wvec_left]
  simp [wvec]

theorem ratPlane_wvec {a b c d a' b' c' d' : K} (ha : D.τ a = a) (hb : D.τ b = b)
    (hc : D.τ c = c) (hd : D.τ d = d) (ha' : D.τ a' = a') (hb' : D.τ b' = b')
    (hc' : D.τ c' = c') (hd' : D.τ d' = d') (h1 : a * c + b * d = 0) (h2 : a' * c' + b' * d' = 0)
    (h12 : a * c' + b * d' + c * a' + d * b' = 0) :
    RatPlane D (wvec a b c d) (wvec a' b' c' d') :=
  ⟨inW2_wvec a b c d, inW2_wvec a' b' c' d', by rw [conj_wvec, ha, hb, hc, hd],
    by rw [conj_wvec, ha', hb', hc', hd'], by rw [Q8_wvec]; exact h1, by rw [Q8_wvec]; exact h2,
    by rw [B8_wvec_wvec]; exact h12⟩

end Six

section Wedge

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} {D : KData F K ε}
  [Fintype K] [DecidableEq K]

@[expose] def wc (z : V8 K) : Fin 4 → K :=
  ![z (Sum.inl 2), z (Sum.inl 3), z (Sum.inr 2), z (Sum.inr 3)]

@[expose] def wedge (x y : V8 K) (i j : Fin 4) : K := wc x i * wc y j - wc x j * wc y i

theorem exists_common_nbr_of_wedge (h2 : (2 : K) ≠ 0) (hq2 : 2 ≤ Nat.card F)
    (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2) {u v x y : V8 K} (hu : InW0 u) (hv : InW0 v)
    (huf : ffK D u) (hvf : ffK D v) (hxf : ffK D x) (hyf : ffK D y) (huv : ColK D u v)
    (hvx : ColK D v x) (hyu : ColK D y u) (hw : ∃ i j, wedge x y i j ≠ 0) :
    ∃ e : V8 K, ffK D e ∧ ColK D e u ∧ ColK D e v ∧ ColK D e x ∧ ColK D e y := by
  have key : ∀ {a b c d a' b' c' d' : K}, D.τ a = a → D.τ b = b → D.τ c = c → D.τ d = d →
      D.τ a' = a' → D.τ b' = b' → D.τ c' = c' → D.τ d' = d' → a * c + b * d = 0 →
      a' * c' + b' * d' = 0 → a * c' + b * d' + c * a' + d * b' = 0 →
      (a * x (Sum.inr 2) + b * x (Sum.inr 3) + c * x (Sum.inl 2) + d * x (Sum.inl 3)) *
          (a' * y (Sum.inr 2) + b' * y (Sum.inr 3) + c' * y (Sum.inl 2) + d' * y (Sum.inl 3)) -
        (a' * x (Sum.inr 2) + b' * x (Sum.inr 3) + c' * x (Sum.inl 2) + d' * x (Sum.inl 3)) *
          (a * y (Sum.inr 2) + b * y (Sum.inr 3) + c * y (Sum.inl 2) + d * y (Sum.inl 3)) ≠ 0 →
      ∃ e : V8 K, ffK D e ∧ ColK D e u ∧ ColK D e v ∧ ColK D e x ∧ ColK D e y := by
    intro a b c d a' b' c' d' ha hb hc hd ha' hb' hc' hd' h1 h2' h12 hΔ
    refine exists_common_nbr_of_plane hq2 hq5
      (ratPlane_wvec D ha hb hc hd ha' hb' hc' hd' h1 h2' h12) hu hv huf hvf hxf hyf huv hvx hyu ?_
    rw [B8_wvec_left, B8_wvec_left, B8_wvec_left, B8_wvec_left]
    exact hΔ
  by_contra hno
  set x1 := x (Sum.inl 2) with hx1
  set x2 := x (Sum.inl 3) with hx2
  set x3 := x (Sum.inr 2) with hx3
  set x4 := x (Sum.inr 3) with hx4
  set y1 := y (Sum.inl 2) with hy1
  set y2 := y (Sum.inl 3) with hy2
  set y3 := y (Sum.inr 2) with hy3
  set y4 := y (Sum.inr 3) with hy4
  have n1 : x3 * y4 - x4 * y3 = 0 := by
    by_contra h
    exact hno (key (a := 1) (b := 0) (c := 0) (d := 0) (a' := 0) (b' := 1) (c' := 0) (d' := 0)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by ring) (by ring) (by ring) (by intro h0; apply h; linear_combination h0))
  have n2 : x1 * y2 - x2 * y1 = 0 := by
    by_contra h
    exact hno (key (a := 0) (b := 0) (c := 1) (d := 0) (a' := 0) (b' := 0) (c' := 0) (d' := -1)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by ring) (by ring) (by ring) (by intro h0; apply h; linear_combination -h0))
  have n3 : (x3 - x2) * (y4 + y1) - (x4 + x1) * (y3 - y2) = 0 := by
    by_contra h
    exact hno (key (a := 1) (b := 0) (c := 0) (d := -1) (a' := 0) (b' := 1) (c' := 1) (d' := 0)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by ring) (by ring) (by ring) (by intro h0; apply h; linear_combination h0))
  have n4 : x2 * y3 - x3 * y2 = 0 := by
    by_contra h
    exact hno (key (a := 1) (b := 0) (c := 0) (d := 0) (a' := 0) (b' := 0) (c' := 0) (d' := -1)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by ring) (by ring) (by ring) (by intro h0; apply h; linear_combination h0))
  have n5 : x4 * y1 - x1 * y4 = 0 := by
    by_contra h
    exact hno (key (a := 0) (b := 1) (c := 0) (d := 0) (a' := 0) (b' := 0) (c' := 1) (d' := 0)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by ring) (by ring) (by ring) (by intro h0; apply h; linear_combination h0))
  have n6 : (x3 + x4) * (y1 - y2) - (x1 - x2) * (y3 + y4) = 0 := by
    by_contra h
    exact hno (key (a := 1) (b := 1) (c := 0) (d := 0) (a' := 0) (b' := 0) (c' := 1) (d' := -1)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by ring) (by ring) (by ring) (by intro h0; apply h; linear_combination h0))
  have p13 : x1 * y3 - x3 * y1 = 0 := by
    have h : (2 : K) * (x1 * y3 - x3 * y1) = 0 := by
      linear_combination n1 + n2 - n3 - n6 + n4 + n5
    exact (mul_eq_zero.1 h).resolve_left h2
  have p24 : x2 * y4 - x4 * y2 = 0 := by
    have h : (2 : K) * (x2 * y4 - x4 * y2) = 0 := by
      linear_combination n1 + n2 - n3 + n6 - n4 - n5
    exact (mul_eq_zero.1 h).resolve_left h2
  obtain ⟨i, j, hij⟩ := hw
  fin_cases i <;> fin_cases j <;> simp [wedge, wc] at hij
  · apply hij
    linear_combination n2
  · apply hij
    linear_combination p13
  · apply hij
    linear_combination -n5
  · apply hij
    linear_combination -n2
  · apply hij
    linear_combination n4
  · apply hij
    linear_combination p24
  · apply hij
    linear_combination -p13
  · apply hij
    linear_combination -n4
  · apply hij
    linear_combination n1
  · apply hij
    linear_combination n5
  · apply hij
    linear_combination -p24
  · apply hij
    linear_combination -n1

end Wedge

end CFSG.ClassicalInvolution.PhanQ
