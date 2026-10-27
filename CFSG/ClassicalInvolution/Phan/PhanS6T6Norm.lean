module

public import CFSG.ClassicalInvolution.Phan.PhanS6T1Lin
public import CFSG.ClassicalInvolution.Phan.PhanS6T5Count

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.T

variable {K : Type} [Field K] (M : Model K)

@[expose] def InW (a b x : Vec K) : Prop :=
  bf M x a = 0 ∧ bf M x b = 0 ∧ bf M x (tauV M a) = 0 ∧ bf M x (tauV M b) = 0

variable {M}

theorem InW.tau {a b x : Vec K} (h : InW M a b x) : InW M a b (tauV M x) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := bf_tauV M x (tauV M a)
    rw [tauV_tauV, h3, map_zero] at this
    exact this
  · have := bf_tauV M x (tauV M b)
    rw [tauV_tauV, h4, map_zero] at this
    exact this
  · have := bf_tauV M x a
    rw [h1, map_zero] at this
    exact this
  · have := bf_tauV M x b
    rw [h2, map_zero] at this
    exact this

theorem InW.add {a b x y : Vec K} (h : InW M a b x) (h' : InW M a b y) : InW M a b (x + y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h1', h2', h3', h4'⟩ := h'
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [bf_add_left] <;> simp [*]

theorem InW.smul {a b x : Vec K} (c : K) (h : InW M a b x) : InW M a b (c • x) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [bf_smul_left] <;> simp [*]

theorem InW.sub {a b x y : Vec K} (h : InW M a b x) (h' : InW M a b y) : InW M a b (x - y) := by
  rw [sub_eq_add_neg, ← neg_one_smul K y]
  exact h.add (h'.smul _)

theorem coeff_zero {a b y : Vec K} (hD : gram M a b ≠ 0) {g₀ g₁ : K}
    (hy : g₀ • a + g₁ • b + y = 0) (hyA : bf M y (tauV M a) = 0)
    (hyB : bf M y (tauV M b) = 0) : g₀ = 0 ∧ g₁ = 0 := by
  have e1 := congrArg (fun x => bf M x (tauV M a)) hy
  have e2 := congrArg (fun x => bf M x (tauV M b)) hy
  simp only [bf_add_left, bf_smul_left, hyA, hyB, bf_zero_left, add_zero] at e1 e2
  have h1 : bf M a (tauV M a) = her M a a := rfl
  have h2 : bf M b (tauV M a) = her M b a := rfl
  have h3 : bf M a (tauV M b) = her M a b := rfl
  have h4 : bf M b (tauV M b) = her M b b := rfl
  rw [h1, h2] at e1
  rw [h3, h4] at e2
  have hD' : her M a a * her M b b - her M a b * her M b a ≠ 0 := hD
  constructor
  · have : g₀ * (her M a a * her M b b - her M a b * her M b a) = 0 := by
      linear_combination her M b b * e1 - her M b a * e2
    exact (mul_eq_zero.1 this).resolve_right hD'
  · have : g₁ * (her M a a * her M b b - her M a b * her M b a) = 0 := by
      linear_combination her M a a * e2 - her M a b * e1
    exact (mul_eq_zero.1 this).resolve_right hD'

structure TriData (M : Model K) (a b c : Vec K) : Prop where
  ha : IsFF M a
  hb : IsFF M b
  hc : IsFF M c
  hab : Col M a b
  hbc : Col M b c
  hca : Col M c a
  hdet : det3 M a b c = 0
  hnd : ¬ ∃ s t : K, c = s • a + t • b

theorem exists_decomp {a b c : Vec K} (T : TriData M a b c) :
    ∃ α β : K, InW M a b (c - α • a - β • b) ∧ bf M (c - α • a - β • b) (c - α • a - β • b) = 0 ∧
      her M (c - α • a - β • b) (c - α • a - β • b) = 0 ∧ c - α • a - β • b ≠ 0 := by
  have hD : gram M a b ≠ 0 := T.hab.2
  have hD' : her M a a * her M b b - her M a b * her M b a ≠ 0 := hD
  have hbca : bf M c a = 0 := T.hca.1
  have hbcb : bf M c b = 0 := by rw [bf_comm]; exact T.hbc.1
  have hbab : bf M a b = 0 := T.hab.1
  have hbba : bf M b a = 0 := by rw [bf_comm]; exact hbab
  have hbaa : bf M a a = 0 := T.ha.1
  have hbbb : bf M b b = 0 := T.hb.1
  have hbcc : bf M c c = 0 := T.hc.1
  have hbac : bf M a c = 0 := by rw [bf_comm]; exact hbca
  have hbbc : bf M b c = 0 := T.hbc.1
  set α : K := (her M c a * her M b b - her M b a * her M c b) / gram M a b with hα
  set β : K := (her M a a * her M c b - her M a b * her M c a) / gram M a b with hβ
  have hAa : α * her M a a + β * her M b a = her M c a := by
    rw [hα, hβ]
    have : gram M a b = her M a a * her M b b - her M a b * her M b a := rfl
    field_simp
    rw [this]
    ring
  have hBb : α * her M a b + β * her M b b = her M c b := by
    rw [hα, hβ]
    have : gram M a b = her M a a * her M b b - her M a b * her M b a := rfl
    field_simp
    rw [this]
    ring
  have hp : ∀ x : Vec K, bf M (c - α • a - β • b) x =
      bf M c x - α * bf M a x - β * bf M b x := by
    intro x
    simp only [bf_sub_left, bf_smul_left]
  have hq : ∀ x : Vec K, bf M x (c - α • a - β • b) =
      bf M x c - α * bf M x a - β * bf M x b := by
    intro x
    simp only [bf_sub_right, bf_smul_right]
  have hW : InW M a b (c - α • a - β • b) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hp]
      simp [hbca, hbaa, hbba]
    · rw [hp]
      simp [hbcb, hbab, hbbb]
    · rw [hp]
      have e1 : bf M c (tauV M a) = her M c a := rfl
      have e2 : bf M a (tauV M a) = her M a a := rfl
      have e3 : bf M b (tauV M a) = her M b a := rfl
      rw [e1, e2, e3]
      linear_combination -hAa
    · rw [hp]
      have e1 : bf M c (tauV M b) = her M c b := rfl
      have e2 : bf M a (tauV M b) = her M a b := rfl
      have e3 : bf M b (tauV M b) = her M b b := rfl
      rw [e1, e2, e3]
      linear_combination -hBb
  have hss : bf M (c - α • a - β • b) (c - α • a - β • b) = 0 := by
    rw [hp, hq, hq, hq]
    simp [hbca, hbcb, hbaa, hbab, hbba, hbbb, hbcc, hbac, hbbc]
  refine ⟨α, β, hW, hss, ?_, ?_⟩
  ·
    have hc : c = (c - α • a - β • b) + α • a + β • b := by abel
    have hr1 : her M (c - α • a - β • b) a = 0 := hW.2.2.1
    have hr2 : her M (c - α • a - β • b) b = 0 := hW.2.2.2
    have hr3 : her M a (c - α • a - β • b) = 0 := by
      rw [her_conj_symm, hr1, map_zero]
    have hr4 : her M b (c - α • a - β • b) = 0 := by
      rw [her_conj_symm, hr2, map_zero]
    have key : det3 M a b c = gram M a b * her M (c - α • a - β • b) (c - α • a - β • b) := by
      generalize c - α • a - β • b = r at hc hr1 hr2 hr3 hr4
      rw [hc]
      simp only [det3, gram, her_add_left, her_add_right, her_smul_left, her_smul_right, hr1,
        hr2, hr3, hr4]
      ring
    rw [T.hdet] at key
    exact (mul_eq_zero.1 key.symm).resolve_left hD
  · intro h0
    apply T.hnd
    refine ⟨α, β, ?_⟩
    have : c - α • a - β • b = 0 := h0
    rw [sub_sub, sub_eq_zero] at this
    exact this

theorem exists_lambda {a b r : Vec K} (hFa : IsFF M a) (hab : bf M a b = 0)
    (hbb : bf M b b = 0) (hD : gram M a b ≠ 0) (hr : InW M a b r) (hrr : bf M r r = 0)
    (hr2 : her M r r = 0) (hr0 : r ≠ 0) : ∃ l : K, l ≠ 0 ∧ tauV M r = l • r := by
  have hbaz : bf M b a = 0 := by rw [bf_comm]; exact hab
  have hra : bf M r a = 0 := hr.1
  have hrb : bf M r b = 0 := hr.2.1
  have hrA : bf M r (tauV M a) = 0 := hr.2.2.1
  have hrB : bf M r (tauV M b) = 0 := hr.2.2.2
  have hart : bf M a (tauV M r) = 0 := by
    have := her_conj_symm M r a
    have e : her M a r = bf M a (tauV M r) := rfl
    have e' : her M r a = bf M r (tauV M a) := rfl
    rw [e, e', hrA, map_zero] at this
    exact this
  have hbrt : bf M b (tauV M r) = 0 := by
    have := her_conj_symm M r b
    have e : her M b r = bf M b (tauV M r) := rfl
    have e' : her M r b = bf M r (tauV M b) := rfl
    rw [e, e', hrB, map_zero] at this
    exact this
  have hrrt : bf M r (tauV M r) = 0 := hr2
  have htt : bf M (tauV M r) (tauV M r) = 0 := by
    rw [bf_tauV, hrr, map_zero]
  have hli : ¬ LinearIndependent K ![a, b, r, tauV M r] := by
    intro hli
    have h3 := ts3 M ![a, b, r, tauV M r] hli (by
      intro i j
      fin_cases i <;> fin_cases j
      · exact hFa.1
      · exact hab
      · simpa using (bf_comm M a r).trans hra
      · simpa using hart
      · simpa using hbaz
      · simpa using hbb
      · simpa using (bf_comm M b r).trans hrb
      · simpa using hbrt
      · simpa using hra
      · simpa using hrb
      · simpa using hrr
      · simpa using hrrt
      · simpa using (bf_comm M _ _).trans hart
      · simpa using (bf_comm M _ _).trans hbrt
      · simpa using (bf_comm M _ _).trans hrrt
      · simpa using htt)
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
  have hg' : g 0 • a + g 1 • b + (g 2 • r + g 3 • tauV M r) = 0 := by
    simpa [Fin.sum_univ_four, add_assoc] using hg
  have hy : InW M a b (g 2 • r + g 3 • tauV M r) := (hr.smul _).add (hr.tau.smul _)
  obtain ⟨h0, h1⟩ := coeff_zero hD hg' hy.2.2.1 hy.2.2.2
  rw [h0, h1, zero_smul, zero_smul, zero_add, zero_add] at hg'
  have hg3 : g 3 ≠ 0 := by
    intro h3
    rw [h3, zero_smul, add_zero] at hg'
    have h2 : g 2 = 0 := (smul_eq_zero.1 hg').resolve_right hr0
    fin_cases i
    · exact hi h0
    · exact hi h1
    · exact hi h2
    · exact hi h3
  have hτ : tauV M r = (-(g 2 / g 3)) • r := by
    have h4 : g 3 • tauV M r = -(g 2 • r) := eq_neg_of_add_eq_zero_right hg'
    have h5 : tauV M r = (g 3)⁻¹ • (g 3 • tauV M r) := by
      rw [smul_smul, inv_mul_cancel₀ hg3, one_smul]
    rw [h5, h4, smul_neg, smul_smul, ← neg_smul]
    congr 1
    field_simp
  refine ⟨-(g 2 / g 3), ?_, hτ⟩
  intro hl
  rw [hl, zero_smul] at hτ
  have : r = 0 := by
    have := congrArg (tauV M) hτ
    rw [tauV_tauV] at this
    rw [this]
    simpa using tauV_smul M 0 r
  exact hr0 this

theorem exists_mu {l : K} (hl : M.τ l * l = 1) (hδ : ∃ δ : K, M.τ δ ≠ δ) :
    ∃ μ : K, μ ≠ 0 ∧ M.τ μ * l = μ := by
  by_cases h : l = -1
  · obtain ⟨δ, hδ⟩ := hδ
    refine ⟨δ - M.τ δ, sub_ne_zero.2 hδ.symm, ?_⟩
    rw [h, map_sub, M.tau_tau]
    ring
  · refine ⟨1 + l, fun h0 => h (eq_neg_of_add_eq_zero_right h0), ?_⟩
    rw [map_add, map_one]
    linear_combination hl

theorem exists_rational_r [Finite K] (hq : 1 < M.q) {a b c : Vec K} (T : TriData M a b c) :
    ∃ (α β μ : K) (r : Vec K), μ ≠ 0 ∧ μ • c = α • a + β • b + r ∧ InW M a b r ∧
      bf M r r = 0 ∧ tauV M r = r ∧ r ≠ 0 := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨α, β, hW, hss, hhh, hne⟩ := exists_decomp T
  obtain ⟨l, hl0, hl⟩ := exists_lambda T.ha T.hab.1 T.hb.1 T.hab.2 hW hss hhh hne
  have hll : M.τ l * l = 1 := by
    have h1 : tauV M (tauV M (c - α • a - β • b)) = c - α • a - β • b := tauV_tauV M _
    rw [hl, tauV_smul, hl, smul_smul] at h1
    have h2 : (M.τ l * l - 1) • (c - α • a - β • b) = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    have := (smul_eq_zero.1 h2).resolve_right hne
    linear_combination this
  obtain ⟨δ, hδ⟩ := exists_not_fixed M hq
  obtain ⟨μ, hμ0, hμ⟩ := exists_mu hll ⟨δ, hδ⟩
  refine ⟨μ * α, μ * β, μ, μ • (c - α • a - β • b), hμ0, ?_, hW.smul μ, ?_, ?_, ?_⟩
  · have hc : c = (c - α • a - β • b) + α • a + β • b := by abel
    conv_lhs => rw [hc]
    simp only [smul_add, smul_smul]
    abel
  · rw [bf_smul_left, bf_smul_right, hss, mul_zero, mul_zero]
  · rw [tauV_smul, hl, smul_smul, hμ]
  · exact smul_ne_zero hμ0 hne

end CFSG.ClassicalInvolution.PhanB3.S.Std.T
