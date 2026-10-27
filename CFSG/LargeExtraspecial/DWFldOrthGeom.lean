module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.LargeExtraspecial.DW

open QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {t : V ≃ₗ[K] V}

theorem map_sub_add (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1)
    (x y : V) : Q (t (x + y) - (x + y)) = Q (t x - x) + Q (t y - y) := by
  have h : t (x + y) - (x + y) = (t x - x) + (t y - y) := by
    rw [map_add]
    abel
  rw [h, map_add_eq, polar_commSpace_eq_zero hO htt (sub_mem_commSpace t x)
    (sub_mem_commSpace t y), add_zero]

omit [CharP K 2] in
theorem map_sub_smul (c : K) (x : V) : Q (t (c • x) - c • x) = c * c * Q (t x - x) := by
  rw [map_smul, ← smul_sub, QuadraticMap.map_smul, smul_eq_mul]

theorem polar_sub_self (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (x : V) :
    polar Q (t x - x) x = Q (t x - x) := by
  rw [map_sub_eq_polar hO, QuadraticMap.polar_sub_left, polar_self_eq_zero, sub_zero]

theorem mem_span_of_singular_orth (hsq : ∀ a : K, ∃ r : K, r * r = a)
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1)
    (hstar : ∀ u, Q u = 0 → Q (t u - u) = 0 → t u - u = 0) {v₀ v' : V} (hv₀ : Q v₀ = 0)
    (hv' : Q v' = 0) (hperp : polar Q v₀ v' = 0) (hN₀ : t v₀ - v₀ ≠ 0) :
    t v' - v' ∈ K ∙ (t v₀ - v₀) := by
  by_cases hN' : t v' - v' = 0
  · rw [hN']
    exact Submodule.zero_mem _
  have hQ₀ : Q (t v₀ - v₀) ≠ 0 := fun h => hN₀ (hstar v₀ hv₀ h)
  have hQ' : Q (t v' - v') ≠ 0 := fun h => hN' (hstar v' hv' h)
  obtain ⟨l, hl⟩ := hsq (Q (t v₀ - v₀) / Q (t v' - v'))
  have hsing : Q (v₀ + l • v') = 0 := by
    rw [map_add_eq, QuadraticMap.map_smul, polar_smul_right, hv₀, hv', hperp]
    simp
  have hzero : Q (t (v₀ + l • v') - (v₀ + l • v')) = 0 := by
    rw [map_sub_add hO htt, map_sub_smul, hl, div_mul_cancel₀ _ hQ', CharTwo.add_self_eq_zero]
  have hN := hstar _ hsing hzero
  rw [map_add, map_smul, show t v₀ + l • t v' - (v₀ + l • v') = (t v₀ - v₀) + l • (t v' - v') by
    rw [smul_sub]; abel] at hN
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hN
    exact hN₀ hN
  rw [Submodule.mem_span_singleton]
  refine ⟨-l⁻¹, ?_⟩
  rw [eq_neg_of_add_eq_zero_left hN, smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hl0,
    one_smul]

theorem mem_span_of_orth (hsq : ∀ a : K, ∃ r : K, r * r = a)
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1)
    (hstar : ∀ u, Q u = 0 → Q (t u - u) = 0 → t u - u = 0) {b e f : V} (hb : Q b = 0)
    (hNb : t b - b ≠ 0) (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1)
    (heb : polar Q e b = 0) (hfb : polar Q f b = 0) {y : V} (hy : polar Q y b = 0) :
    t y - y ∈ K ∙ (t b - b) := by
  set S := K ∙ (t b - b)
  set N : V →ₗ[K] V := (t : V →ₗ[K] V) - 1 with hNdef
  have hN : ∀ v, N v = t v - v := fun v => rfl
  have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
  have hee : polar Q e e = 0 := polar_self_eq_zero Q e
  have hff : polar Q f f = 0 := polar_self_eq_zero Q f
  have hNe : N e ∈ S := mem_span_of_singular_orth hsq hO htt hstar hb he
    (by rw [polar_comm, heb]) hNb
  have hNf : N f ∈ S := mem_span_of_singular_orth hsq hO htt hstar hb hf
    (by rw [polar_comm, hfb]) hNb
  set y₂ := y - polar Q y f • e - polar Q y e • f with hy₂
  have hy₂e : polar Q y₂ e = 0 := by
    rw [hy₂, polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, hee, hfe]
    simp
  have hy₂f : polar Q y₂ f = 0 := by
    rw [hy₂, polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, hef, hff]
    simp
  have hy₂b : polar Q y₂ b = 0 := by
    rw [hy₂, polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, hy, heb, hfb]
    simp
  set y₃ := y₂ + e + Q y₂ • f with hy₃
  have hQy₃ : Q y₃ = 0 := by
    rw [hy₃, map_add_eq, map_add_eq, QuadraticMap.map_smul, he, hf, polar_add_left,
      polar_smul_right, polar_smul_right, hy₂e, hy₂f, hef]
    simp only [smul_eq_mul, mul_zero, add_zero, zero_add, mul_one]
    exact CharTwo.add_self_eq_zero _
  have hy₃b : polar Q b y₃ = 0 := by
    rw [polar_comm, hy₃, polar_add_left, polar_add_left, polar_smul_left, hy₂b, heb, hfb]
    simp
  have hNy₃ : N y₃ ∈ S := mem_span_of_singular_orth hsq hO htt hstar hb hQy₃ hy₃b hNb
  have hyeq : y = y₃ - e - Q y₂ • f + polar Q y f • e + polar Q y e • f := by
    rw [hy₃, hy₂]
    abel
  rw [← hN, hyeq, map_add, map_add, map_sub, map_sub, map_smul, map_smul, map_smul]
  exact S.add_mem (S.add_mem (S.sub_mem (S.sub_mem hNy₃ hNe) (S.smul_mem _ hNf))
    (S.smul_mem _ hNe)) (S.smul_mem _ hNf)

theorem exists_singular_or_line (hsq : ∀ a : K, ∃ r : K, r * r = a)
    (hQ : Q.polarBilin.Nondegenerate) (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (htt : t * t = 1) {b b' e f : V} (hb : Q b = 0) (hb' : Q b' = 0) (hbb' : polar Q b b' = 1)
    (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) (heb : polar Q e b = 0)
    (hfb : polar Q f b = 0) (heb' : polar Q e b' = 0) (hfb' : polar Q f b' = 0)
    (hNb : t b - b ≠ 0) :
    (∃ u, Q u = 0 ∧ Q (t u - u) = 0 ∧ t u - u ≠ 0) ∨ ∃ w₀ : V, ∀ y, t y - y ∈ K ∙ w₀ := by
  by_cases hstar : ∀ u, Q u = 0 → Q (t u - u) = 0 → t u - u = 0
  swap
  · push Not at hstar
    exact Or.inl hstar
  right
  set N : V →ₗ[K] V := (t : V →ₗ[K] V) - 1 with hNdef
  have hN : ∀ v, N v = t v - v := fun v => rfl
  have hNN : ∀ x, N (N x) = 0 := by
    intro x
    have := commSpace_le_fixSpace htt (sub_mem_commSpace t x)
    rw [mem_fixSpace] at this
    rw [hN, hN, this, sub_self]
  have hb'b : polar Q b' b = 1 := by rw [polar_comm, hbb']
  have hbb : polar Q b b = 0 := polar_self_eq_zero Q b
  have hb'b' : polar Q b' b' = 0 := polar_self_eq_zero Q b'
  have hb_line : ∀ y, polar Q y b = 0 → N y ∈ K ∙ N b := fun y hy =>
    mem_span_of_orth hsq hO htt hstar hb hNb he hf hef heb hfb hy
  by_cases hcase : N b' ∈ K ∙ N b
  · refine ⟨N b, fun y => ?_⟩
    have hy' : polar Q (y - polar Q y b • b') b = 0 := by
      rw [polar_sub_left, polar_smul_left, hb'b, smul_eq_mul, mul_one, sub_self]
    have hyeq : y = (y - polar Q y b • b') + polar Q y b • b' := by abel
    rw [← hN, hyeq, map_add, map_smul]
    exact Submodule.add_mem _ (hb_line _ hy') (Submodule.smul_mem _ _ hcase)
  exfalso
  have hNb' : N b' ≠ 0 := fun h => hcase (by rw [h]; exact Submodule.zero_mem _)
  have hb'_line : ∀ y, polar Q y b' = 0 → N y ∈ K ∙ N b' := fun y hy =>
    mem_span_of_orth hsq hO htt hstar hb' hNb' he hf hef heb' hfb' hy
  have hind : ∀ c d : K, c • N b + d • N b' = 0 → c = 0 ∧ d = 0 := by
    intro c d hcd
    have hd : d = 0 := by
      by_contra hd
      apply hcase
      rw [Submodule.mem_span_singleton]
      refine ⟨-(d⁻¹ * c), ?_⟩
      rw [neg_smul, mul_smul, eq_neg_of_add_eq_zero_left hcd, smul_neg, neg_neg, smul_smul,
        inv_mul_cancel₀ hd, one_smul]
    subst hd
    rw [zero_smul, add_zero] at hcd
    exact ⟨(smul_eq_zero.1 hcd).resolve_right hNb, rfl⟩
  have hformula : ∀ y, N y = polar Q y b' • N b + polar Q y b • N b' := by
    intro y
    set yC := y - polar Q y b' • b - polar Q y b • b' with hyC
    have hCb : polar Q yC b = 0 := by
      rw [hyC, polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, hbb, hb'b]
      simp
    have hCb' : polar Q yC b' = 0 := by
      rw [hyC, polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, hbb', hb'b']
      simp
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hb_line yC hCb)
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 (hb'_line yC hCb')
    have h0 := (hind c (-d) (by rw [neg_smul, hc, hd, add_neg_cancel])).1
    have hNC : N yC = 0 := by rw [← hc, h0, zero_smul]
    have hyeq : y = yC + polar Q y b' • b + polar Q y b • b' := by rw [hyC]; abel
    conv_lhs => rw [hyeq]
    rw [map_add, map_add, map_smul, map_smul, hNC, zero_add]
  have h1 := hind _ _ ((hformula (N b)).symm.trans (hNN b))
  have h2 := hind _ _ ((hformula (N b')).symm.trans (hNN b'))
  apply hNb
  refine hQ.1 (N b) fun z => ?_
  rw [polarBilin_apply_apply, hN, polar_sub_eq_polar_sub hO htt, ← hN, hformula,
    polar_add_right, polar_smul_right, polar_smul_right, polar_comm _ b (N b),
    polar_comm _ b (N b'), h1.2, h2.2]
  simp

theorem exists_eichler_plane (hQ : Q.polarBilin.Nondegenerate)
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) {u : V} (hu : Q u = 0)
    (hNu : Q (t u - u) = 0) (hw0 : t u - u ≠ 0) (x : K) :
    ∃ z : V, polar Q u z = 0 ∧ CFSG.ClassicalGroups.Orthogonal.eichler Q u z u = u ∧
      CFSG.ClassicalGroups.Orthogonal.eichler Q u z (t u - u) = (t u - u) + x • u := by
  have hwu' : polar Q (t u - u) u = 0 := by rw [polar_sub_self hO, hNu]
  have hNw' : t (t u - u) - (t u - u) = 0 := by
    have := commSpace_le_fixSpace htt (sub_mem_commSpace t u)
    rw [mem_fixSpace] at this
    rw [this, sub_self]
  have htu : t u = u + (t u - u) := by abel
  generalize hwdef : t u - u = w at hNu hw0 hwu' hNw' htu ⊢
  have hwu : polar Q w u = 0 := hwu'
  have huu : polar Q u u = 0 := polar_self_eq_zero Q u
  have hNw : t w - w = 0 := hNw'
  have hind : ∀ a c : K, a • u + c • w = 0 → a = 0 ∧ c = 0 := by
    intro a c hac
    have h' : t (a • u + c • w) - (a • u + c • w) = 0 := by rw [hac, map_zero, sub_zero]
    have htw : t w = w := sub_eq_zero.1 hNw
    rw [map_add, map_smul, map_smul, htu, htw] at h'
    have h'' : a • w = 0 := by
      rw [← h']
      module
    have ha : a = 0 := (smul_eq_zero.1 h'').resolve_right hw0
    subst ha
    rw [zero_smul, zero_add] at hac
    exact ⟨rfl, (smul_eq_zero.1 hac).resolve_right hw0⟩
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_add] at htu
    exact hw0 htu.symm
  obtain ⟨z₀, hz₀u, hz₀w⟩ : ∃ z₀, polar Q u z₀ = 0 ∧ polar Q w z₀ ≠ 0 := by
    by_contra! hcon
    obtain ⟨z₁, hz₁⟩ : ∃ z₁, polar Q u z₁ ≠ 0 := by
      by_contra! h
      exact hu0 (hQ.1 u fun z => by rw [polarBilin_apply_apply]; exact h z)
    set κ := polar Q w z₁ / polar Q u z₁
    have hwκ : w - κ • u = 0 := by
      refine hQ.1 _ fun z => ?_
      rw [polarBilin_apply_apply]
      have hz : polar Q u (z - (polar Q u z / polar Q u z₁) • z₁) = 0 := by
        rw [polar_sub_right, polar_smul_right, smul_eq_mul, div_mul_cancel₀ _ hz₁, sub_self]
      have := hcon _ hz
      rw [polar_sub_right, polar_smul_right, smul_eq_mul, sub_eq_zero] at this
      rw [polar_sub_left, polar_smul_left, smul_eq_mul, this]
      simp only [κ]
      field_simp
      ring
    have := (hind (-κ) 1 (by rw [neg_smul, one_smul, add_comm, ← sub_eq_add_neg, hwκ])).2
    exact one_ne_zero this
  set z := (x / polar Q w z₀) • z₀ with hzdef
  have hzu : polar Q u z = 0 := by rw [hzdef, polar_smul_right, hz₀u, smul_zero]
  have hzw : polar Q w z = x := by
    rw [hzdef, polar_smul_right, smul_eq_mul, div_mul_cancel₀ _ hz₀w]
  refine ⟨z, hzu, ?_, ?_⟩
  · rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hu hzu, huu, hzu, zero_smul, add_zero,
      mul_zero, add_zero, zero_smul, sub_zero]
  · rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hu hzu, hwu, hzw, zero_smul, add_zero,
      mul_zero, add_zero, sub_eq_add_vec K]

end CFSG.LargeExtraspecial.DW
