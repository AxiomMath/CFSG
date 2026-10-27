module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelRoot
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import CFSG.ClassicalGroups.Orthogonal.Transitive

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open QuadraticMap Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {Q : QuadraticForm K N}

structure MinusThreeFrame (Q : QuadraticForm K N) (e f p p' u v : N) : Prop where
  e_sing : Q e = 0
  f_sing : Q f = 0
  p_sing : Q p = 0
  p'_sing : Q p' = 0
  ef : polar Q e f = 1
  pp' : polar Q p p' = 1
  ep : polar Q e p = 0
  ep' : polar Q e p' = 0
  fp : polar Q f p = 0
  fp' : polar Q f p' = 0
  u_perp : polar Q u e = 0 ∧ polar Q u f = 0 ∧ polar Q u p = 0 ∧ polar Q u p' = 0
  v_perp : polar Q v e = 0 ∧ polar Q v f = 0 ∧ polar Q v p = 0 ∧ polar Q v p' = 0
  Qu : Q u = 1
  aniso : ∀ α β : K, Q (α • u + β • v) = 0 → α = 0 ∧ β = 0
  span : ∀ x : N, x ∈ Submodule.span K {e, f, p, p', u, v}

variable [CharP K 2]

private theorem polar_self_charTwo (x : N) : polar Q x x = 0 := by
  rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

private theorem two_smul_vec (x : N) : (2 : K) • x = 0 := by
  rw [CharTwo.two_eq_zero, zero_smul]

private theorem linearIndependent_six {e f p p' u v : N} (he : Q e = 0) (hf : Q f = 0)
    (hp : Q p = 0) (hp' : Q p' = 0) (hef : polar Q e f = 1) (hpp' : polar Q p p' = 1)
    (hep : polar Q e p = 0) (hep' : polar Q e p' = 0) (hfp : polar Q f p = 0)
    (hfp' : polar Q f p' = 0) (hue : polar Q u e = 0) (huf : polar Q u f = 0)
    (hup : polar Q u p = 0) (hup' : polar Q u p' = 0) (hve : polar Q v e = 0)
    (hvf : polar Q v f = 0) (hvp : polar Q v p = 0) (hvp' : polar Q v p' = 0)
    (huv : polar Q u v ≠ 0) : LinearIndependent K ![e, f, p, p', u, v] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  replace hg : g 0 • e + g 1 • f + g 2 • p + g 3 • p' + g 4 • u + g 5 • v = 0 := by
    simpa [Fin.sum_univ_six] using hg
  have hR : ∀ z : N, g 0 * polar Q e z + g 1 * polar Q f z + g 2 * polar Q p z +
      g 3 * polar Q p' z + g 4 * polar Q u z + g 5 * polar Q v z = 0 := fun z => by
    have := congrArg (fun w => polar Q w z) hg
    simpa only [polar_add_left, polar_smul_left_eq, polar_zero_left] using this
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hef
  have hp'p : polar Q p' p = 1 := by rw [polar_comm]; exact hpp'
  have hpe : polar Q p e = 0 := by rw [polar_comm]; exact hep
  have hp'e : polar Q p' e = 0 := by rw [polar_comm]; exact hep'
  have hpf : polar Q p f = 0 := by rw [polar_comm]; exact hfp
  have hp'f : polar Q p' f = 0 := by rw [polar_comm]; exact hfp'
  have g0 : g 0 = 0 := by
    have := hR f
    simp only [hef, polar_self_eq_zero hf, hpf, hp'f, huf, hvf] at this
    linear_combination this
  have g1 : g 1 = 0 := by
    have := hR e
    simp only [polar_self_eq_zero he, hfe, hpe, hp'e, hue, hve] at this
    linear_combination this
  have g2 : g 2 = 0 := by
    have := hR p'
    simp only [hep', hfp', hpp', polar_self_eq_zero hp', hup', hvp'] at this
    linear_combination this
  have g3 : g 3 = 0 := by
    have := hR p
    simp only [hep, hfp, polar_self_eq_zero hp, hp'p, hup, hvp] at this
    linear_combination this
  have g4 : g 4 = 0 := by
    have := hR v
    simp only [g0, g1, g2, g3, polar_self_charTwo v, zero_mul, zero_add, mul_zero, add_zero] at this
    exact (mul_eq_zero.mp this).resolve_right huv
  have g5 : g 5 = 0 := by
    have := hR u
    simp only [g0, g1, g2, g3, g4, polar_self_charTwo u, zero_mul, zero_add, mul_zero,
      add_zero] at this
    exact (mul_eq_zero.mp this).resolve_right (by rw [polar_comm]; exact huv)
  intro i
  fin_cases i <;> assumption

theorem exists_minusThreeFrame [FiniteDimensional K N] (hdim : finrank K N = 6)
    (P : Fin 2 → HypPair Q) (hP : (P 0).Orth (P 1)) {u v : N}
    (huv : ∀ i, u ∈ (P i).perp ∧ v ∈ (P i).perp) (hQu : Q u = 1) (hpuv : polar Q u v ≠ 0)
    (hroot : ∀ s : K, s ^ 2 + polar Q u v * s + Q v ≠ 0) :
    MinusThreeFrame Q (P 0).e (P 0).f (P 1).e (P 1).f u v := by
  obtain ⟨hue, huf⟩ := HypPair.mem_perp.mp (huv 0).1
  obtain ⟨hve, hvf⟩ := HypPair.mem_perp.mp (huv 0).2
  obtain ⟨hup, hup'⟩ := HypPair.mem_perp.mp (huv 1).1
  obtain ⟨hvp, hvp'⟩ := HypPair.mem_perp.mp (huv 1).2
  rw [polar_comm] at hue huf hve hvf hup hup' hvp hvp'
  have hli := linearIndependent_six (P 0).Q_e (P 0).Q_f (P 1).Q_e (P 1).Q_f (P 0).polar_ef
    (P 1).polar_ef hP.ee hP.ef hP.fe hP.ff hue huf hup hup' hve hvf hvp hvp' hpuv
  have hspan : Submodule.span K (Set.range ![(P 0).e, (P 0).f, (P 1).e, (P 1).f, u, v]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [hdim])
  refine ⟨(P 0).Q_e, (P 0).Q_f, (P 1).Q_e, (P 1).Q_f, (P 0).polar_ef, (P 1).polar_ef, hP.ee,
    hP.ef, hP.fe, hP.ff, ⟨hue, huf, hup, hup'⟩, ⟨hve, hvf, hvp, hvp'⟩, hQu, ?_, fun x => ?_⟩
  · intro α β h
    have hQ : Q (α • u + β • v) = α ^ 2 + polar Q u v * (α * β) + β ^ 2 * Q v := by
      rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hQu, polar_smul_left_eq,
        polar_smul_right_eq]
      ring
    rw [hQ] at h
    by_cases hβ : β = 0
    · subst hβ
      have : α ^ 2 = 0 := by simpa using h
      exact ⟨pow_eq_zero_iff two_ne_zero |>.mp this, rfl⟩
    · exfalso
      apply hroot (α / β)
      field_simp
      linear_combination h
  · have hx : x ∈ Submodule.span K (Set.range ![(P 0).e, (P 0).f, (P 1).e, (P 1).f, u, v]) := by
      rw [hspan]
      exact Submodule.mem_top
    simpa only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
      using hx

section Coordinates

variable {e f p p' u v : N}

omit [CharP K 2] in
private theorem MinusThreeFrame.polar_H (hF : MinusThreeFrame Q e f p p' u v) (c d x y : K) :
    polar Q e (c • p + d • p' + (x • u + y • v)) = 0 ∧
    polar Q f (c • p + d • p' + (x • u + y • v)) = 0 ∧
    polar Q p (c • p + d • p' + (x • u + y • v)) = d ∧
    polar Q p' (c • p + d • p' + (x • u + y • v)) = c := by
  obtain ⟨hue, huf, hup, hup'⟩ := hF.u_perp
  obtain ⟨hve, hvf, hvp, hvp'⟩ := hF.v_perp
  have hpp := polar_self_eq_zero hF.p_sing
  have hp'p' := polar_self_eq_zero hF.p'_sing
  have hp'p : polar Q p' p = 1 := by rw [polar_comm]; exact hF.pp'
  simp only [polar_add_right, polar_smul_right_eq, polar_comm Q e u, polar_comm Q e v,
    polar_comm Q f u, polar_comm Q f v, polar_comm Q p u, polar_comm Q p v, polar_comm Q p' u,
    polar_comm Q p' v, hue, hve, huf, hvf, hup, hvp, hup', hvp', hF.ep, hF.ep', hF.fp, hF.fp', hpp,
    hp'p', hF.pp', hp'p]
  exact ⟨by ring, by ring, by ring, by ring⟩

omit [CharP K 2] in
private theorem MinusThreeFrame.exists_coords (hF : MinusThreeFrame Q e f p p' u v) (w : N) :
    ∃ a b c d x y : K, w = a • e + b • f + (c • p + d • p' + (x • u + y • v)) := by
  have hw := hF.span w
  simp only [Submodule.mem_span_insert, Submodule.mem_span_singleton] at hw
  obtain ⟨a₀, z₀, ⟨a₁, z₁, ⟨a₂, z₂, ⟨a₃, z₃, ⟨a₄, z₄, ⟨a₅, h5⟩, h4⟩, h3⟩, h2⟩, h1⟩, h0⟩ := hw
  refine ⟨a₀, a₁, a₂, a₃, a₄, a₅, ?_⟩
  rw [h0, h1, h2, h3, h4, ← h5]
  abel

omit [CharP K 2] in
private theorem MinusThreeFrame.exists_coordsH (hF : MinusThreeFrame Q e f p p' u v) {w : N}
    (hwe : polar Q e w = 0) (hwf : polar Q f w = 0) :
    ∃ c d x y : K, w = c • p + d • p' + (x • u + y • v) := by
  obtain ⟨a, b, c, d, x, y, rfl⟩ := hF.exists_coords w
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hF.ef
  obtain ⟨h1, h2, -, -⟩ := hF.polar_H c d x y
  simp only [polar_add_right, polar_smul_right_eq, polar_self_eq_zero hF.e_sing, hF.ef, h1, hfe,
    polar_self_eq_zero hF.f_sing, h2] at hwe hwf
  have ha : a = 0 := by linear_combination hwf
  have hb : b = 0 := by linear_combination hwe
  exact ⟨c, d, x, y, by rw [ha, hb]; simp⟩

omit [CharP K 2] in
private theorem MinusThreeFrame.map_H (hF : MinusThreeFrame Q e f p p' u v) {δ : N}
    (hδp : polar Q p δ = 0) (hδp' : polar Q p' δ = 0) (c d : K) :
    Q (c • p + d • p' + δ) = c * d + Q δ := by
  simp only [QuadraticMap.map_add Q, map_smul_eq_sq, hF.p_sing, hF.p'_sing, polar_add_left,
    polar_smul_left_eq, polar_smul_right_eq, hF.pp', hδp, hδp']
  ring

omit [CharP K 2] in
private theorem MinusThreeFrame.polar_HH (hF : MinusThreeFrame Q e f p p' u v) {δ δ' : N}
    (hδp : polar Q p δ = 0) (hδp' : polar Q p' δ = 0) (hδ'p : polar Q p δ' = 0)
    (hδ'p' : polar Q p' δ' = 0) (c d c' d' : K) :
    polar Q (c • p + d • p' + δ) (c' • p + d' • p' + δ') = c * d' + d * c' + polar Q δ δ' := by
  have hpp := polar_self_eq_zero hF.p_sing
  have hp'p' := polar_self_eq_zero hF.p'_sing
  have hp'p : polar Q p' p = 1 := by rw [polar_comm]; exact hF.pp'
  have hδp_ : polar Q δ p = 0 := by rw [polar_comm]; exact hδp
  have hδp'_ : polar Q δ p' = 0 := by rw [polar_comm]; exact hδp'
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, hpp, hp'p',
    hF.pp', hp'p, hδ'p, hδ'p', hδp_, hδp'_]
  ring

omit [CharP K 2] in
private theorem MinusThreeFrame.polar_delta (hF : MinusThreeFrame Q e f p p' u v) (x y : K) :
    polar Q p (x • u + y • v) = 0 ∧ polar Q p' (x • u + y • v) = 0 := by
  obtain ⟨-, -, hup, hup'⟩ := hF.u_perp
  obtain ⟨-, -, hvp, hvp'⟩ := hF.v_perp
  simp only [polar_add_right, polar_smul_right_eq, polar_comm Q p u, polar_comm Q p v,
    polar_comm Q p' u, polar_comm Q p' v, hup, hup', hvp, hvp']
  exact ⟨by ring, by ring⟩

omit [CharP K 2] in
private theorem MinusThreeFrame.polar_delta_ef (hF : MinusThreeFrame Q e f p p' u v) (x y : K) :
    polar Q e (x • u + y • v) = 0 ∧ polar Q f (x • u + y • v) = 0 := by
  obtain ⟨hue, huf, -, -⟩ := hF.u_perp
  obtain ⟨hve, hvf, -, -⟩ := hF.v_perp
  simp only [polar_add_right, polar_smul_right_eq, polar_comm Q e u, polar_comm Q e v,
    polar_comm Q f u, polar_comm Q f v, hue, hve, huf, hvf]
  exact ⟨by ring, by ring⟩

omit [CharP K 2] in
private theorem MinusThreeFrame.map_delta (hF : MinusThreeFrame Q e f p p' u v) (x y : K) :
    Q (x • u + y • v) = x ^ 2 + polar Q u v * (x * y) + y ^ 2 * Q v := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hF.Qu, polar_smul_left_eq,
    polar_smul_right_eq]
  ring

private theorem polar_delta_delta (u v : N) (x y x' y' : K) :
    polar Q (x • u + y • v) (x' • u + y' • v) = polar Q u v * (x * y' + y * x') := by
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    polar_self_charTwo, polar_comm Q v u]
  ring

omit [CharP K 2] in
private theorem eq_smul_scalar {t s : K}
    (aniso : ∀ α β : K, α ^ 2 + t * (α * β) + β ^ 2 * s = 0 → α = 0 ∧ β = 0)
    (h2 : (2 : K) = 0) {c d x y c' d' x' y' : K}
    (H1 : c * d + (x ^ 2 + t * (x * y) + y ^ 2 * s) = 0)
    (H2 : c' * d' + (x' ^ 2 + t * (x' * y') + y' ^ 2 * s) = 0)
    (H3 : c * d' + d * c' + t * (x * y' + y * x') = 0)
    (hw0 : ¬(c = 0 ∧ d = 0 ∧ x = 0 ∧ y = 0)) :
    ∃ l : K, c' = l * c ∧ d' = l * d ∧ x' = l * x ∧ y' = l * y := by
  by_cases hc : c = 0
  · subst hc
    obtain ⟨hx, hy⟩ := aniso x y (by linear_combination H1)
    subst hx hy
    have hd : d ≠ 0 := fun hd => hw0 ⟨rfl, hd, rfl, rfl⟩
    have hc' : c' = 0 := by
      have : d * c' = 0 := by linear_combination H3
      exact (mul_eq_zero.mp this).resolve_left hd
    subst hc'
    obtain ⟨hx', hy'⟩ := aniso x' y' (by linear_combination H2)
    subst hx' hy'
    exact ⟨d' / d, by simp, by field_simp, by simp, by simp⟩
  · obtain ⟨hα, hβ⟩ := aniso (c' * x - c * x') (c' * y - c * y')
      (by linear_combination c' ^ 2 * H1 + c ^ 2 * H2 - c * c' * H3 -
        (c * c' * (x * x' + y * y' * s)) * h2)
    have hxx : c' * x = c * x' := by linear_combination hα
    have hyy : c' * y = c * y' := by linear_combination hβ
    have hdd : c' * d = c * d' := by
      have h3 : c * (c * d' + d * c') = 0 := by
        linear_combination c * H3 + t * x * hyy + t * y * hxx - (t * c' * x * y) * h2
      have h4 : c * d' + d * c' = 0 := (mul_eq_zero.mp h3).resolve_left hc
      linear_combination h4 - (c * d') * h2
    refine ⟨c' / c, by field_simp, ?_, ?_, ?_⟩
    · field_simp
      linear_combination -hdd
    · field_simp
      linear_combination -hxx
    · field_simp
      linear_combination -hyy

end Coordinates

theorem MinusThreeFrame.eq_smul_of_polar_eq_zero {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) {w w' : N} (hwe : polar Q w e = 0)
    (hwf : polar Q w f = 0) (hw'e : polar Q w' e = 0) (hw'f : polar Q w' f = 0) (hw : Q w = 0)
    (hw' : Q w' = 0) (hw0 : w ≠ 0) (hww' : polar Q w w' = 0) : ∃ c : K, w' = c • w := by
  obtain ⟨c, d, x, y, rfl⟩ :=
    hF.exists_coordsH ((polar_comm Q e w).trans hwe) ((polar_comm Q f w).trans hwf)
  obtain ⟨c', d', x', y', rfl⟩ :=
    hF.exists_coordsH ((polar_comm Q e w').trans hw'e) ((polar_comm Q f w').trans hw'f)
  obtain ⟨hδp, hδp'⟩ := hF.polar_delta x y
  obtain ⟨hδ'p, hδ'p'⟩ := hF.polar_delta x' y'
  rw [hF.map_H hδp hδp', hF.map_delta] at hw
  rw [hF.map_H hδ'p hδ'p', hF.map_delta] at hw'
  rw [hF.polar_HH hδp hδp' hδ'p hδ'p', polar_delta_delta] at hww'
  obtain ⟨l, hc, hd, hx, hy⟩ := eq_smul_scalar
    (fun α β h => hF.aniso α β (by rw [hF.map_delta]; exact h)) CharTwo.two_eq_zero hw hw' hww'
    (fun ⟨h1, h2, h3, h4⟩ => hw0 (by rw [h1, h2, h3, h4]; simp))
  exact ⟨l, by rw [hc, hd, hx, hy]; module⟩

theorem exists_fourth_point [Finite K] (hK : 2 < Nat.card K) {w₀ w₁ w : N} (h₀ : Q w₀ = 0)
    (h₁ : Q w₁ = 0) (h : Q w = 0) (h01 : polar Q w₀ w₁ ≠ 0) (h0 : polar Q w₀ w ≠ 0) :
    ∃ α β γ : K, α ≠ 0 ∧ β ≠ 0 ∧ γ ≠ 0 ∧ Q (α • w₀ + β • w₁ + γ • w) = 0 := by
  classical
  have hfin := Fintype.ofFinite K
  obtain ⟨α, hα, hD⟩ : ∃ α : K, α ≠ 0 ∧ α * polar Q w₀ w + polar Q w₁ w ≠ 0 := by
    have hu : (Finset.univ : Finset K).card = Nat.card K := by
      rw [Finset.card_univ, Nat.card_eq_fintype_card]
    have hcard : ({0, -(polar Q w₁ w) / polar Q w₀ w} : Finset K).card <
        (Finset.univ : Finset K).card :=
      lt_of_le_of_lt Finset.card_le_two (hu ▸ hK)
    obtain ⟨α, -, hα⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hα
    refine ⟨α, hα.1, fun hz => hα.2 ?_⟩
    field_simp
    linear_combination hz
  obtain ⟨γ, hγ, hγ0⟩ : ∃ γ : K, γ * (α * polar Q w₀ w + polar Q w₁ w) = α * polar Q w₀ w₁ ∧
      γ ≠ 0 :=
    ⟨α * polar Q w₀ w₁ / (α * polar Q w₀ w + polar Q w₁ w), div_mul_cancel₀ _ hD,
      div_ne_zero (mul_ne_zero hα h01) hD⟩
  refine ⟨α, 1, γ, hα, one_ne_zero, hγ0, ?_⟩
  simp only [QuadraticMap.map_add Q, map_smul_eq_sq, polar_add_left, polar_smul_left_eq,
    polar_smul_right_eq, h₀, h₁, h]
  linear_combination hγ + (α * polar Q w₀ w₁) * (CharTwo.two_eq_zero : (2 : K) = 0)

omit [CharP K 2] in
private theorem exists_dual_pair (hnd : ∀ x : N, (∀ y, polar Q x y = 0) → x = 0) {a b : N}
    (hli : LinearIndependent K ![a, b]) :
    ∃ y₁ y₂ : N, polar Q a y₁ = 1 ∧ polar Q b y₁ = 0 ∧ polar Q a y₂ = 0 ∧ polar Q b y₂ = 1 := by
  have hex : ∀ x : N, x ≠ 0 → ∃ y, polar Q x y ≠ 0 := fun x hx => by
    by_contra! h
    exact hx (hnd x h)
  have hpair := LinearIndependent.pair_iff.mp hli
  have ha0 : a ≠ 0 := by simpa using hli.ne_zero 0
  obtain ⟨y₁₀, h1⟩ : ∃ y, polar Q a y = 1 := by
    obtain ⟨y, hy⟩ := hex a ha0
    exact ⟨(polar Q a y)⁻¹ • y, by rw [polar_smul_right_eq, inv_mul_cancel₀ hy]⟩
  have hbt : b - polar Q b y₁₀ • a ≠ 0 := by
    intro h0
    have := (hpair (-polar Q b y₁₀) 1 (by rw [← h0]; module)).2
    exact one_ne_zero this
  obtain ⟨y₂₀, h2⟩ : ∃ y, polar Q (b - polar Q b y₁₀ • a) y = 1 := by
    obtain ⟨z, hz⟩ := hex _ hbt
    exact ⟨(polar Q (b - polar Q b y₁₀ • a) z)⁻¹ • z,
      by rw [polar_smul_right_eq, inv_mul_cancel₀ hz]⟩
  simp only [polar_sub_left, polar_smul_left_eq] at h2
  refine ⟨y₁₀ - polar Q b y₁₀ • (y₂₀ - polar Q a y₂₀ • y₁₀), y₂₀ - polar Q a y₂₀ • y₁₀, ?_, ?_,
    ?_, ?_⟩
  · simp only [polar_sub_right, polar_smul_right_eq]
    linear_combination (1 + polar Q b y₁₀ * polar Q a y₂₀) * h1
  · simp only [polar_sub_right, polar_smul_right_eq]
    linear_combination (-polar Q b y₁₀) * h2
  · simp only [polar_sub_right, polar_smul_right_eq]
    linear_combination (-polar Q a y₂₀) * h1
  · simp only [polar_sub_right, polar_smul_right_eq]
    linear_combination h2

theorem exists_quadrangle (hnd : ∀ x : N, (∀ y, polar Q x y = 0) → x = 0) {a b : N}
    (ha : Q a = 0) (hb : Q b = 0) (hab : polar Q a b = 0) (hli : LinearIndependent K ![a, b]) :
    ∃ a' b' : N, Q a' = 0 ∧ Q b' = 0 ∧ polar Q a a' = 1 ∧ polar Q b b' = 1 ∧
      polar Q b a' = 0 ∧ polar Q a b' = 0 ∧ polar Q a' b' = 0 := by
  obtain ⟨y₁, y₂, h11, h21, h12, h22⟩ := exists_dual_pair hnd hli
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hba : polar Q b a = 0 := by rw [polar_comm]; exact hab
  have haa : polar Q a a = 0 := polar_self_eq_zero ha
  have hbb : polar Q b b = 0 := polar_self_eq_zero hb
  obtain ⟨a', ha'⟩ : ∃ a', a' = y₁ + Q y₁ • a := ⟨_, rfl⟩
  obtain ⟨b'', hb''⟩ : ∃ b'', b'' = y₂ + Q y₂ • b := ⟨_, rfl⟩
  have hQa' : Q a' = 0 := by
    rw [ha', QuadraticMap.map_add Q, map_smul_eq_sq, ha, polar_smul_right_eq, polar_comm Q y₁ a,
      h11]
    linear_combination (Q y₁) * h2
  have haa' : polar Q a a' = 1 := by
    rw [ha', polar_add_right, polar_smul_right_eq, h11, haa]
    ring
  have hba' : polar Q b a' = 0 := by
    rw [ha', polar_add_right, polar_smul_right_eq, h21, hba]
    ring
  have hQb'' : Q b'' = 0 := by
    rw [hb'', QuadraticMap.map_add Q, map_smul_eq_sq, hb, polar_smul_right_eq, polar_comm Q y₂ b,
      h22]
    linear_combination (Q y₂) * h2
  have hbb'' : polar Q b b'' = 1 := by
    rw [hb'', polar_add_right, polar_smul_right_eq, h22, hbb]
    ring
  have hab'' : polar Q a b'' = 0 := by
    rw [hb'', polar_add_right, polar_smul_right_eq, h12, hab]
    ring
  obtain ⟨c, hc⟩ : ∃ c, c = polar Q a' b'' := ⟨_, rfl⟩
  have hQb' : Q (b'' + c • a) = 0 := by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, ha, hQb'', polar_smul_right_eq,
      polar_comm Q b'' a, hab'']
    ring
  have hbb' : polar Q b (b'' + c • a) = 1 := by
    rw [polar_add_right, polar_smul_right_eq, hbb'', hba]
    ring
  have hab' : polar Q a (b'' + c • a) = 0 := by
    rw [polar_add_right, polar_smul_right_eq, hab'', haa]
    ring
  have ha'b' : polar Q a' (b'' + c • a) = 0 := by
    rw [polar_add_right, polar_smul_right_eq, ← hc, polar_comm Q a' a, haa']
    linear_combination c * h2
  exact ⟨a', b'' + c • a, hQa', hQb', haa', hbb', hba', hab', ha'b'⟩

theorem eichler_mul_eichler_ne_of_quadrangle {a b a' b' : N} (ha : Q a = 0) (hb : Q b = 0)
    (ha' : Q a' = 0) (hb' : Q b' = 0) (haa' : polar Q a a' = 1)
    (hbb' : polar Q b b' = 1) (hba' : polar Q b a' = 0) (hab' : polar Q a b' = 0)
    (ha'b' : polar Q a' b' = 0) :
    eichler Q b a' * eichler Q a b' ≠ eichler Q a b' * eichler Q b a' := by
  intro h
  have ha'b : polar Q a' b = 0 := by rw [polar_comm]; exact hba'
  have haa'' : polar Q a' a = 1 := by rw [polar_comm]; exact haa'
  have hbb'' : polar Q b' b = 1 := by rw [polar_comm]; exact hbb'
  have hb'a' : polar Q b' a' = 0 := by rw [polar_comm]; exact ha'b'
  have e1 : eichler Q a b' a' = a' + b' := by
    rw [eichler_apply_of_singular ha hb' hab', haa'', ha'b', one_smul, zero_smul, add_zero]
  have e2 : eichler Q b a' a' = a' := by
    rw [eichler_apply_of_singular hb ha' hba', ha'b, polar_self_charTwo, zero_smul, zero_smul,
      add_zero, add_zero]
  have e3 : eichler Q b a' (a' + b') = b' := by
    rw [eichler_apply_of_singular hb ha' hba']
    simp only [polar_add_left, ha'b, hbb'', polar_self_charTwo, hb'a', zero_add, zero_smul,
      add_zero, one_smul]
    linear_combination (norm := module) two_smul_vec (K := K) a'
  have h1 := congrArg (fun g => g a') h
  simp only [LinearEquiv.mul_apply, e1, e2, e3] at h1
  have h2 : a' = 0 := by
    have := congrArg (fun x => x - b') h1
    simpa using this.symm
  have := haa'
  rw [h2, polar_zero_right] at this
  exact zero_ne_one this

private theorem MinusThreeFrame.torus_aux {e f p p' u v : N} (hF : MinusThreeFrame Q e f p p' u v)
    {d : N} (hde : polar Q d e = 0) (hdf : polar Q d f = 0) (hdp : polar Q d p = 0)
    (hdp' : polar Q d p' = 0) (hd : Q d ≠ 0) :
    ∃ n ∈ elementaryGroup Q, n e = e ∧ n f = f ∧ n p = (Q d)⁻¹ • p' ∧ n p' = Q d • p := by
  have hpd : polar Q p d = 0 := by rw [polar_comm]; exact hdp
  have hp'd : polar Q p' d = 0 := by rw [polar_comm]; exact hdp'
  have hed : polar Q e d = 0 := by rw [polar_comm]; exact hde
  have hfd : polar Q f d = 0 := by rw [polar_comm]; exact hdf
  have hp'p : polar Q p' p = 1 := by rw [polar_comm]; exact hF.pp'
  obtain ⟨c, hc⟩ : ∃ c, c = Q d := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := hc ▸ hd
  rw [← hc]
  obtain ⟨d', hd'⟩ : ∃ d', d' = c⁻¹ • d := ⟨_, rfl⟩
  have hQd' : Q d' = c⁻¹ := by rw [hd', map_smul_eq_sq, ← hc]; field_simp
  have hpd' : polar Q p d' = 0 := by rw [hd', polar_smul_right_eq, hpd, mul_zero]
  have hp'd'' : polar Q p' d' = 0 := by rw [hd', polar_smul_right_eq, hp'd, mul_zero]
  have hed' : polar Q e d' = 0 := by rw [hd', polar_smul_right_eq, hed, mul_zero]
  have hfd' : polar Q f d' = 0 := by rw [hd', polar_smul_right_eq, hfd, mul_zero]
  have hd'p : polar Q d' p = 0 := by rw [polar_comm]; exact hpd'
  have hdd' : polar Q d d' = 0 := by rw [hd', polar_smul_right_eq, polar_self_charTwo, mul_zero]
  have hd'd : polar Q d' d = 0 := by rw [polar_comm]; exact hdd'
  have hcd' : c • d' = d := by rw [hd', smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have h1 : c⁻¹ • c • p = p := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have h6 : c • c⁻¹ • p' = p' := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have E1p : eichler Q p d p = p := eichler_apply_self _ _
  have E1p' : eichler Q p d p' = p' + d + c • p := by
    rw [eichler_apply hF.p_sing hpd, hp'p, hp'd, ← hc]
    linear_combination (norm := module) (-c) • two_smul_vec (K := K) p
  have E2p' : eichler Q p' d' p' = p' := eichler_apply_self _ _
  have E2p : eichler Q p' d' p = p + d' + c⁻¹ • p' := by
    rw [eichler_apply hF.p'_sing hp'd'', hF.pp', hpd', hQd']
    linear_combination (norm := module) (-c⁻¹) • two_smul_vec (K := K) p'
  have E1d' : eichler Q p d d' = d' := eichler_apply_of_polar_eq_zero hd'p hd'd
  have E2d : eichler Q p' d' d = d := eichler_apply_of_polar_eq_zero hdp' hdd'
  have step1 : eichler Q p d (eichler Q p' d' p) = c⁻¹ • p' := by
    rw [E2p, map_add, map_add, map_smul, E1p, E1d', E1p']
    linear_combination (norm := module) hd' + h1 + two_smul_vec (K := K) p +
      c⁻¹ • two_smul_vec (K := K) d
  have step2 : eichler Q p' d' (eichler Q p d p') = c • p := by
    rw [E1p', map_add, map_add, map_smul, E2p', E2d, E2p]
    linear_combination (norm := module) hcd' + h6 + two_smul_vec (K := K) p' +
      two_smul_vec (K := K) d
  have he1 : eichler Q p d e = e := eichler_apply_of_polar_eq_zero hF.ep hed
  have he2 : eichler Q p' d' e = e := eichler_apply_of_polar_eq_zero hF.ep' hed'
  have hf1 : eichler Q p d f = f := eichler_apply_of_polar_eq_zero hF.fp hfd
  have hf2 : eichler Q p' d' f = f := eichler_apply_of_polar_eq_zero hF.fp' hfd'
  refine ⟨eichler Q p d * eichler Q p' d' * eichler Q p d, mul_mem (mul_mem
    (eichler_mem_elementaryGroup Q _ _) (eichler_mem_elementaryGroup Q _ _))
    (eichler_mem_elementaryGroup Q _ _), ?_, ?_, ?_, ?_⟩
  · simp only [LinearEquiv.mul_apply, he1, he2]
  · simp only [LinearEquiv.mul_apply, hf1, hf2]
  · simp only [LinearEquiv.mul_apply, E1p, step1]
  · simp only [LinearEquiv.mul_apply, step2, eichler_apply_smul_self]

theorem MinusThreeFrame.exists_torus [Finite K] {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) {μ : K} (hμ : μ ≠ 0) :
    ∃ g ∈ elementaryGroup Q, g e = e ∧ g f = f ∧ g p = μ • p := by
  obtain ⟨ν, hν⟩ := isSquare_of_charTwo' μ
  have hν0 : ν ≠ 0 := by
    rintro rfl
    exact hμ (by simpa using hν)
  obtain ⟨hue, huf, hup, hup'⟩ := hF.u_perp
  have hQu : Q u ≠ 0 := by rw [hF.Qu]; exact one_ne_zero
  obtain ⟨n₁, hn₁, hn₁e, hn₁f, hn₁p, -⟩ := hF.torus_aux hue huf hup hup' hQu
  have hQνu : Q (ν • u) ≠ 0 := by
    rw [map_smul_eq_sq, hF.Qu, mul_one]
    exact pow_ne_zero 2 hν0
  obtain ⟨n₂, hn₂, hn₂e, hn₂f, -, hn₂p'⟩ := hF.torus_aux (d := ν • u)
    (by rw [polar_smul_left_eq, hue, mul_zero]) (by rw [polar_smul_left_eq, huf, mul_zero])
    (by rw [polar_smul_left_eq, hup, mul_zero]) (by rw [polar_smul_left_eq, hup', mul_zero]) hQνu
  refine ⟨n₂ * n₁, mul_mem hn₂ hn₁, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hn₁e, hn₂e]
  · rw [LinearEquiv.mul_apply, hn₁f, hn₂f]
  · rw [LinearEquiv.mul_apply, hn₁p, map_smul, hn₂p', hF.Qu, inv_one, one_smul, map_smul_eq_sq,
      hF.Qu, mul_one, hν, _root_.sq]

omit [CharP K 2] in
private theorem exists_mem_elementaryGroup_hypPair' (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ : HypPair Q} (h : P₁.Orth P₂) (P P' : HypPair Q) :
    ∃ g ∈ elementaryGroup Q, g P.e = P'.e ∧ g P.f = P'.f := by
  obtain ⟨g₁, hg₁, hg₁e⟩ := exists_mem_elementaryGroup_apply_eq hQ h P.e_ne_zero P'.e_ne_zero
    (by rw [P.Q_e, P'.Q_e])
  have hg₁o := elementaryGroup_le_orthogonalGroup Q hg₁
  have hx : polar Q P'.e (g₁ P.f) = 1 := by
    rw [← hg₁e, polar_map_of_mem hg₁o]
    exact P.polar_ef
  have hQf : Q (g₁ P.f) = Q P'.f := by rw [map_of_mem hg₁o, P.Q_f, P'.Q_f]
  refine ⟨eichler Q P'.e ((1 : K)⁻¹ • (P'.f - g₁ P.f)) * g₁,
    mul_mem (eichler_mem_elementaryGroup Q _ _) hg₁, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hg₁e]
    exact eichler_apply_self _ _
  · rw [LinearEquiv.mul_apply]
    exact eichler_apply_eq_of_polar_eq P'.Q_e hQf hx P'.polar_ef one_ne_zero

private theorem MinusThreeFrame.exists_fix_to_smul {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) {a : N} (ha : Q a = 0) (ha0 : a ≠ 0)
    (hae : polar Q a e = 0) (haf : polar Q a f = 0) :
    ∃ g ∈ elementaryGroup Q, g e = e ∧ g f = f ∧ ∃ κ : K, κ ≠ 0 ∧ g a = κ • p := by
  obtain ⟨c, d, x, y, rfl⟩ :=
    hF.exists_coordsH ((polar_comm Q e a).trans hae) ((polar_comm Q f a).trans haf)
  obtain ⟨hδp, hδp'⟩ := hF.polar_delta x y
  obtain ⟨hδe, hδf⟩ := hF.polar_delta_ef x y
  rw [hF.map_H hδp hδp'] at ha
  by_cases hc : c = 0
  · subst hc
    obtain ⟨rfl, rfl⟩ := hF.aniso x y (by linear_combination ha)
    have hd : d ≠ 0 := by
      rintro rfl
      exact ha0 (by simp)
    obtain ⟨hue, huf, hup, hup'⟩ := hF.u_perp
    obtain ⟨n, hn, hne, hnf, -, hnp'⟩ :=
      hF.torus_aux hue huf hup hup' (by rw [hF.Qu]; exact one_ne_zero)
    refine ⟨n, hn, hne, hnf, d, hd, ?_⟩
    have : (0 : K) • p + d • p' + ((0 : K) • u + (0 : K) • v) = d • p' := by simp
    rw [this, map_smul, hnp', hF.Qu, one_smul]
  · obtain ⟨w, hw⟩ : ∃ w, w = c⁻¹ • (x • u + y • v) := ⟨_, rfl⟩
    have hQδ : Q (x • u + y • v) = c * d := by
      linear_combination ha - (c * d) * (CharTwo.two_eq_zero : (2 : K) = 0)
    have hpw : polar Q p' w = 0 := by rw [hw, polar_smul_right_eq, hδp', mul_zero]
    have hew : polar Q e w = 0 := by rw [hw, polar_smul_right_eq, hδe, mul_zero]
    have hfw : polar Q f w = 0 := by rw [hw, polar_smul_right_eq, hδf, mul_zero]
    have hcw : c • w = x • u + y • v := by rw [hw, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hQw : Q w * c = d := by
      rw [hw, map_smul_eq_sq, hQδ]
      field_simp
    have hpa : polar Q (c • p + d • p' + (x • u + y • v)) p' = c :=
      (polar_comm Q _ _).trans (hF.polar_H c d x y).2.2.2
    have haw : polar Q (c • p + d • p' + (x • u + y • v)) w = 0 := by
      rw [hw, polar_smul_right_eq]
      simp only [polar_add_left, polar_smul_left_eq, hδp, hδp', polar_self_charTwo, mul_zero,
        add_zero]
    refine ⟨eichler Q p' w, eichler_mem_elementaryGroup Q _ _,
      eichler_apply_of_polar_eq_zero hF.ep' hew, eichler_apply_of_polar_eq_zero hF.fp' hfw, c,
      hc, ?_⟩
    rw [eichler_apply hF.p'_sing hpw, hpa, haw, hcw, hQw]
    linear_combination (norm := module) x • two_smul_vec (K := K) u + y • two_smul_vec (K := K) v

theorem MinusThreeFrame.exists_mem_elementaryGroup_flag [Finite K] {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) (hnd : (polarBilin Q).Nondegenerate) {a b c : N}
    (ha : Q a = 0) (ha0 : a ≠ 0) (hb : Q b = 0) (hc : Q c = 0) (hab : polar Q a b = 0)
    (hac : polar Q a c = 0) (hbc : polar Q b c = 1) :
    ∃ g ∈ elementaryGroup Q, g a = p ∧ g b = e ∧ g c = f := by
  obtain ⟨g₁, hg₁, hg₁b, hg₁c⟩ := exists_mem_elementaryGroup_hypPair' hnd
    (P₁ := ⟨e, f, hF.e_sing, hF.f_sing, hF.ef⟩) (P₂ := ⟨p, p', hF.p_sing, hF.p'_sing, hF.pp'⟩)
    ⟨hF.ep, hF.ep', hF.fp, hF.fp'⟩ ⟨b, c, hb, hc, hbc⟩ ⟨e, f, hF.e_sing, hF.f_sing, hF.ef⟩
  replace hg₁b : g₁ b = e := hg₁b
  replace hg₁c : g₁ c = f := hg₁c
  have hg₁o := elementaryGroup_le_orthogonalGroup Q hg₁
  have h1 : Q (g₁ a) = 0 := by rw [map_of_mem hg₁o, ha]
  have h2 : g₁ a ≠ 0 := by
    intro h
    apply ha0
    apply g₁.injective
    rw [h, map_zero]
  have h3 : polar Q (g₁ a) e = 0 := by rw [← hg₁b, polar_map_of_mem hg₁o, hab]
  have h4 : polar Q (g₁ a) f = 0 := by rw [← hg₁c, polar_map_of_mem hg₁o, hac]
  obtain ⟨g₂, hg₂, hg₂e, hg₂f, κ, hκ, hg₂a⟩ := hF.exists_fix_to_smul h1 h2 h3 h4
  obtain ⟨g₃, hg₃, hg₃e, hg₃f, hg₃p⟩ := hF.exists_torus (inv_ne_zero hκ)
  refine ⟨g₃ * g₂ * g₁, mul_mem (mul_mem hg₃ hg₂) hg₁, ?_, ?_, ?_⟩
  · simp only [LinearEquiv.mul_apply, hg₂a, map_smul, hg₃p, smul_smul, mul_inv_cancel₀ hκ,
      one_smul]
  · simp only [LinearEquiv.mul_apply, hg₁b, hg₂e, hg₃e]
  · simp only [LinearEquiv.mul_apply, hg₁c, hg₂f, hg₃f]

omit [CharP K 2] in
theorem MinusThreeFrame.eichler_injOn {e f p p' u v : N} (hF : MinusThreeFrame Q e f p p' u v)
    {w w' : N} (hwe : polar Q e w = 0) (hwf : polar Q f w = 0) (hw'e : polar Q e w' = 0)
    (hw'f : polar Q f w' = 0) (h : eichler Q e w = eichler Q e w') : w = w' := by
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hF.ef
  have key : ∀ z : N, polar Q e z = 0 → polar Q f z = 0 →
      eichler Q e z f = f + (z - Q z • e) := by
    intro z hze hzf
    rw [eichler_apply hF.e_sing hze, hfe, hzf]
    module
  have h1 : eichler Q e w f = eichler Q e w' f := by rw [h]
  rw [key w hwe hwf, key w' hw'e hw'f] at h1
  have h2 : w - Q w • e = w' - Q w' • e := add_left_cancel h1
  have h3 : Q w = Q w' := by
    have h4 := congrArg (fun x => polar Q x f) h2
    simp only [polar_sub_left, polar_smul_left_eq, polar_comm Q w f, polar_comm Q w' f, hwf, hw'f,
      hF.ef] at h4
    linear_combination -h4
  rw [h3] at h2
  exact sub_left_inj.mp h2

omit [CharP K 2] in
theorem MinusThreeFrame.natCard_rootGroup [Finite K] {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) :
    Nat.card (rootGroup Q e) = Nat.card K ^ 4 := by
  let φ : (Fin 4 → K) → rootGroup Q e := fun c =>
    ⟨eichler Q e (c 0 • p + c 1 • p' + (c 2 • u + c 3 • v)),
      eichler_mem_rootGroup (hF.polar_H _ _ _ _).1⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun c c' h => ?_, ?_⟩
    · have h2 := hF.eichler_injOn (hF.polar_H _ _ _ _).1 (hF.polar_H _ _ _ _).2.1
        (hF.polar_H _ _ _ _).1 (hF.polar_H _ _ _ _).2.1 (congrArg Subtype.val h)
      have e0 : c 0 = c' 0 := by
        have := congrArg (polar Q p') h2
        rwa [(hF.polar_H _ _ _ _).2.2.2, (hF.polar_H _ _ _ _).2.2.2] at this
      have e1 : c 1 = c' 1 := by
        have := congrArg (polar Q p) h2
        rwa [(hF.polar_H _ _ _ _).2.2.1, (hF.polar_H _ _ _ _).2.2.1] at this
      rw [e0, e1] at h2
      have h3 : (c 2 - c' 2) • u + (c 3 - c' 3) • v = 0 := by
        linear_combination (norm := module) h2
      obtain ⟨e2, e3⟩ := hF.aniso _ _ (by rw [h3]; exact QuadraticMap.map_zero Q)
      refine funext fun i => ?_
      fin_cases i
      · exact e0
      · exact e1
      · exact sub_eq_zero.mp e2
      · exact sub_eq_zero.mp e3
    · rintro ⟨g, hg⟩
      obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
      obtain ⟨a, b, c, d, x, y, rfl⟩ := hF.exists_coords w
      have hb : b = 0 := by
        simp only [polar_add_right, polar_smul_right_eq, polar_self_eq_zero hF.e_sing, hF.ef,
          (hF.polar_H c d x y).1] at hw
        linear_combination hw
      refine ⟨![c, d, x, y], Subtype.ext ?_⟩
      show eichler Q e (c • p + d • p' + (x • u + y • v)) =
        eichler Q e (a • e + b • f + (c • p + d • p' + (x • u + y • v)))
      rw [hb, zero_smul, add_zero, add_comm (a • e), eichler_add_smul_self hF.e_sing]
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_fun]
  simp

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
