module

public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply nondegenerate_polarBilin_quadPlus)

private abbrev fk_K : Type := GaloisField 3 1

private abbrev fk_V : Type := Fin 4 ⊕ Fin 4 → fk_K

private lemma fk_two_ne_zero : (2 : fk_K) ≠ 0 :=
  (NeZero.of_not_dvd (R := fk_K) (n := 2) (p := 3) (by norm_num)).ne

private lemma fk_neg_two_eq_one : (-2 : fk_K) = 1 := by
  have h3 : (3 : fk_K) = 0 := CharP.cast_eq_zero fk_K 3
  rw [show (-2 : fk_K) = 1 - 3 by ring, h3, sub_zero]

private lemma fk_finrank : Module.finrank fk_K fk_V = 8 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
  norm_num

private lemma fk_quad_zero_of_anti
    (A : fk_V →ₗ[fk_K] fk_V)
    (hQ : ∀ v, quadPlus 4 fk_K (A v) = -quadPlus 4 fk_K v)
    {v : fk_V} (hv : quadPlus 4 fk_K (A v) = quadPlus 4 fk_K v) :
    quadPlus 4 fk_K v = 0 := by
  have h1 : quadPlus 4 fk_K v = -quadPlus 4 fk_K v := by
    calc quadPlus 4 fk_K v = quadPlus 4 fk_K (A v) := hv.symm
      _ = -quadPlus 4 fk_K v := hQ v
  have h2 : (2 : fk_K) * quadPlus 4 fk_K v = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp h1
  exact (mul_eq_zero.mp h2).resolve_left fk_two_ne_zero

private lemma fk_det_of_sq_one
    (a : fk_V ≃ₗ[fk_K] fk_V)
    (hQ : ∀ v, quadPlus 4 fk_K (a v) = -quadPlus 4 fk_K v)
    (hs : ∀ v, a (a v) = v) :
    LinearMap.det (a : fk_V →ₗ[fk_K] fk_V) = 1 := by
  classical
  let A : fk_V →ₗ[fk_K] fk_V := (a : fk_V →ₗ[fk_K] fk_V)
  change LinearMap.det A = 1
  have hA2 : ∀ v, A (A v) = v := fun v => by
    show a (a v) = v
    exact hs v
  have hQA : ∀ v, quadPlus 4 fk_K (A v) = -quadPlus 4 fk_K v := fun v => hQ v
  set p : Submodule fk_K fk_V := LinearMap.ker (A - 1) with hp
  set q : Submodule fk_K fk_V := LinearMap.ker (A + 1) with hq
  have hpA : ∀ v ∈ p, A v = v := by
    intro v hv
    rw [hp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    exact hv
  have hqA : ∀ v ∈ q, A v = -v := by
    intro v hv
    rw [hq, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg] at hv
    exact hv
  have hQzero_p : ∀ v ∈ p, quadPlus 4 fk_K v = 0 := by
    intro v hv
    exact fk_quad_zero_of_anti A hQA (by rw [hpA v hv])
  have hQzero_q : ∀ v ∈ q, quadPlus 4 fk_K v = 0 := by
    intro v hv
    refine fk_quad_zero_of_anti A hQA ?_
    rw [hqA v hv, QuadraticMap.map_neg]
  have hsing_p : ∀ u ∈ p, ∀ w ∈ p,
      QuadraticMap.polarBilin (quadPlus 4 fk_K) u w = 0 := by
    intro u hu w hw
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      hQzero_p (u + w) (p.add_mem hu hw), hQzero_p u hu, hQzero_p w hw]
    ring
  have hsing_q : ∀ u ∈ q, ∀ w ∈ q,
      QuadraticMap.polarBilin (quadPlus 4 fk_K) u w = 0 := by
    intro u hu w hw
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      hQzero_q (u + w) (q.add_mem hu hw), hQzero_q u hu, hQzero_q w hw]
    ring
  have hsym : ∀ u w : fk_V, QuadraticMap.polarBilin (quadPlus 4 fk_K) w u =
      QuadraticMap.polarBilin (quadPlus 4 fk_K) u w := by
    intro u w
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
    exact (QuadraticMap.polar_comm (quadPlus 4 fk_K) u w).symm
  have hle_p : p ≤
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (quadPlus 4 fk_K)) p := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [hsym u w]
    exact hsing_p u hu w hw
  have hle_q : q ≤
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (quadPlus 4 fk_K)) q := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [hsym u w]
    exact hsing_q u hu w hw
  have hdim_p : Module.finrank fk_K p ≤ 4 := by
    have h1 : Module.finrank fk_K p ≤
        Module.finrank fk_K
          (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (quadPlus 4 fk_K)) p) :=
      Submodule.finrank_mono hle_p
    rw [LinearMap.BilinForm.finrank_orthogonal
      (nondegenerate_polarBilin_quadPlus 4 fk_K), fk_finrank] at h1
    have h2 : Module.finrank fk_K p ≤ 8 := by
      rw [← fk_finrank]; exact Submodule.finrank_le p
    have h3 : Module.finrank fk_K p + Module.finrank fk_K p ≤ 8 := by
      have h4 := Nat.add_le_add_right h1 (Module.finrank fk_K p)
      rwa [Nat.sub_add_cancel h2] at h4
    omega
  have hdim_q : Module.finrank fk_K q ≤ 4 := by
    have h1 : Module.finrank fk_K q ≤
        Module.finrank fk_K
          (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin (quadPlus 4 fk_K)) q) :=
      Submodule.finrank_mono hle_q
    rw [LinearMap.BilinForm.finrank_orthogonal
      (nondegenerate_polarBilin_quadPlus 4 fk_K), fk_finrank] at h1
    have h2 : Module.finrank fk_K q ≤ 8 := by
      rw [← fk_finrank]; exact Submodule.finrank_le q
    have h3 : Module.finrank fk_K q + Module.finrank fk_K q ≤ 8 := by
      have h4 := Nat.add_le_add_right h1 (Module.finrank fk_K q)
      rwa [Nat.sub_add_cancel h2] at h4
    omega
  have hcompl : IsCompl p q := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff_inf_le]
      intro v hv
      rw [Submodule.mem_inf] at hv
      rw [Submodule.mem_bot]
      have hpv : A v = v := hpA v hv.1
      have hqv : A v = -v := hqA v hv.2
      have hvv : v = -v := by
        calc v = A v := hpv.symm
          _ = -v := hqv
      have h2 : (2 : fk_K) • v = 0 := by
        rw [two_smul]
        exact eq_neg_iff_add_eq_zero.mp hvv
      exact (smul_eq_zero.mp h2).resolve_left fk_two_ne_zero
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      rw [Submodule.mem_sup]
      refine ⟨(2 : fk_K)⁻¹ • (A v + v), ?_, (2 : fk_K)⁻¹ • (v - A v), ?_, ?_⟩
      · rw [hp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
        rw [LinearMap.map_smul, LinearMap.map_add, hA2 v, add_comm v (A v)]
      · rw [hq, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
        rw [LinearMap.map_smul, LinearMap.map_sub, hA2 v, ← smul_add,
          show A v - v + (v - A v) = 0 by abel, smul_zero]
      · rw [← smul_add, show (A v + v) + (v - A v) = (2 : fk_K) • v by module,
          smul_smul, show (2 : fk_K)⁻¹ * 2 = 1 by rw [inv_mul_cancel₀ fk_two_ne_zero],
          one_smul]
  have hcompl_dim : Module.finrank fk_K p + Module.finrank fk_K q = 8 := by
    rw [Submodule.finrank_add_eq_of_isCompl hcompl, fk_finrank]
  have hq_dim : Module.finrank fk_K q = 4 := by omega
  have hdet : LinearMap.det A = 1 := by
    have hp_inv : ∀ x ∈ p, A x ∈ p := fun x hx => by rw [hpA x hx]; exact hx
    have hq_inv : ∀ x ∈ q, A x ∈ q := fun x hx => by rw [hqA x hx]; exact q.neg_mem hx
    set Ap := A.restrict hp_inv with hAp_def
    set Aq := A.restrict hq_inv with hAq_def
    set e := Submodule.prodEquivOfIsCompl p q hcompl with he
    set A' := Ap.prodMap Aq with hA'_def
    have hconj : A' = (e.symm : fk_V →ₗ[fk_K] p × q) ∘ₗ A ∘ₗ
        (e : p × q →ₗ[fk_K] fk_V) := by
      refine LinearMap.ext fun x => ?_
      apply e.injective
      change e (A' x) = e (e.symm (A (e x)))
      rw [show e (e.symm (A (e x))) = A (e x) from e.apply_symm_apply (A (e x))]
      rw [hA'_def, LinearMap.prodMap_apply, he, Submodule.coe_prodEquivOfIsCompl',
        Submodule.coe_prodEquivOfIsCompl', hAp_def, hAq_def, LinearMap.map_add]
      simp only [LinearMap.coe_restrict_apply]
    have hdet_conj : LinearMap.det A' = LinearMap.det A := by
      rw [hconj]
      exact LinearMap.det_conj A e.symm
    have hdet_prod : LinearMap.det A' = LinearMap.det Ap * LinearMap.det Aq := by
      rw [hA'_def, LinearMap.det_prodMap]
    have hdet_Ap : LinearMap.det Ap = 1 := by
      have h1 : Ap = 1 := by
        rw [hAp_def]
        refine LinearMap.ext fun x => ?_
        apply Subtype.ext
        simpa using hpA x.1 x.2
      rw [h1]
      exact LinearMap.det_id
    have hdet_Aq : LinearMap.det Aq = (-1 : fk_K) ^ Module.finrank fk_K q := by
      have h1 : Aq = (-1 : fk_K) • (1 : q →ₗ[fk_K] q) := by
        rw [hAq_def]
        refine LinearMap.ext fun x => ?_
        apply Subtype.ext
        simp only [LinearMap.coe_restrict_apply, LinearMap.smul_apply, Module.End.one_apply,
          neg_one_smul]
        exact hqA x.1 x.2
      rw [h1, LinearMap.det_smul]
      rw [show LinearMap.det (1 : q →ₗ[fk_K] q) = 1 from LinearMap.det_id, mul_one]
    rw [← hdet_conj, hdet_prod, hdet_Ap, hdet_Aq, hq_dim]
    ring
  exact hdet

private lemma fk_det_of_sq_neg_one
    (a : fk_V ≃ₗ[fk_K] fk_V)
    (hQ : ∀ v, quadPlus 4 fk_K (a v) = -quadPlus 4 fk_K v)
    (hs : ∀ v, a (a v) = -v) :
    LinearMap.det (a : fk_V →ₗ[fk_K] fk_V) = 1 := by
  let A : fk_V →ₗ[fk_K] fk_V := (a : fk_V →ₗ[fk_K] fk_V)
  change LinearMap.det A = 1
  have hAeq : A = (1 - A) * (1 - A) := by
    refine LinearMap.ext fun v => ?_
    have hv : A (A v) = -v := by
      show a (a v) = -v
      exact hs v
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.map_sub, hv]
    rw [show (v - A v) - (A v - -v) = (-2 : fk_K) • A v by module,
      fk_neg_two_eq_one, one_smul]
  have hdet : LinearMap.det A = (LinearMap.det (1 - A)) ^ 2 := by
    conv_lhs => rw [hAeq]
    rw [map_mul, sq]
  have hdetne : LinearMap.det A ≠ 0 := by
    change LinearMap.det (a : fk_V →ₗ[fk_K] fk_V) ≠ 0
    exact (LinearEquiv.isUnit_det' a).ne_zero
  have hsquare : (LinearMap.det (1 - A)) ^ 2 = 1 := by
    have hne : LinearMap.det (1 - A) ≠ 0 := by
      intro h
      exact hdetne (by rw [hdet, h, pow_two, mul_zero])
    haveI : Fintype fk_K := Fintype.ofFinite fk_K
    have hcard : Fintype.card fk_K = 3 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num), pow_one]
    have hpow := FiniteField.pow_card_sub_one_eq_one (LinearMap.det (1 - A)) hne
    rw [hcard] at hpow
    simpa using hpow
  rw [hdet, hsquare]

theorem fk_det_eq_one
    (a : (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1] (Fin 4 ⊕ Fin 4 → GaloisField 3 1))
    (s : GaloisField 3 1)
    (hQ : ∀ v, quadPlus 4 (GaloisField 3 1) (a v) = -quadPlus 4 (GaloisField 3 1) v)
    (hs : ∀ v, a (a v) = s • v) :
    LinearMap.det (a : (Fin 4 ⊕ Fin 4 → GaloisField 3 1) →ₗ[GaloisField 3 1]
      (Fin 4 ⊕ Fin 4 → GaloisField 3 1)) = 1 := by
  have hs2 : s * s = 1 := by
    set v0 : fk_V := Pi.single (Sum.inl 0) (1 : fk_K) + Pi.single (Sum.inr 0) (1 : fk_K)
      with hv0
    have hQv0 : quadPlus 4 fk_K v0 = 1 := by
      rw [hv0]
      simp [quadPlus_apply, Pi.single_apply, Fin.sum_univ_succ]
    have h1 : quadPlus 4 fk_K (a (a v0)) = quadPlus 4 fk_K v0 := by
      rw [hQ (a v0), hQ v0, neg_neg]
    rw [hs v0] at h1
    rw [QuadraticMap.map_smul, hQv0] at h1
    simpa using h1
  have hs1 : s = 1 ∨ s = -1 := by
    have h : s ^ 2 = 1 := by rwa [sq]
    exact sq_eq_one_iff.mp h
  rcases hs1 with h | h
  · rw [h] at hs
    exact fk_det_of_sq_one a hQ (fun v => by simpa using hs v)
  · rw [h] at hs
    exact fk_det_of_sq_neg_one a hQ (fun v => by simpa using hs v)

end CFSG.OddStandard.SmallF3.Omega
