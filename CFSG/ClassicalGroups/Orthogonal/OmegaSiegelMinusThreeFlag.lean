module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeN

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.ClassicalGroups.Orthogonal QuadraticMap Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {Q : QuadraticForm K N}

theorem MinusThreeFrame.swapPairs {e f p p' u v : N} (hF : MinusThreeFrame Q e f p p' u v) :
    MinusThreeFrame Q p p' e f u v := by
  obtain ⟨he, hf, hp, hp', hef, hpp', hep, hep', hfp, hfp', hu, hv, hQu, han, hspan⟩ := hF
  have hpe : polar Q p e = 0 := by rw [polar_comm]; exact hep
  have hpf : polar Q p f = 0 := by rw [polar_comm]; exact hfp
  have hp'e : polar Q p' e = 0 := by rw [polar_comm]; exact hep'
  have hp'f : polar Q p' f = 0 := by rw [polar_comm]; exact hfp'
  refine ⟨hp, hp', he, hf, hpp', hef, hpe, hpf, hp'e, hp'f,
    ⟨hu.2.2.1, hu.2.2.2, hu.1, hu.2.1⟩, ⟨hv.2.2.1, hv.2.2.2, hv.1, hv.2.1⟩, hQu, han, fun x => ?_⟩
  have hset : ({p, p', e, f, u, v} : Set N) = {e, f, p, p', u, v} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset]
  exact hspan x

theorem MinusThreeFrame.swapRight {e f p p' u v : N} (hF : MinusThreeFrame Q e f p p' u v) :
    MinusThreeFrame Q e f p' p u v := by
  obtain ⟨he, hf, hp, hp', hef, hpp', hep, hep', hfp, hfp', hu, hv, hQu, han, hspan⟩ := hF
  have hp'p : polar Q p' p = 1 := by rw [polar_comm]; exact hpp'
  refine ⟨he, hf, hp', hp, hef, hp'p, hep', hep, hfp', hfp,
    ⟨hu.1, hu.2.1, hu.2.2.2, hu.2.2.1⟩, ⟨hv.1, hv.2.1, hv.2.2.2, hv.2.2.1⟩, hQu, han, fun x => ?_⟩
  have hset : ({e, f, p', p, u, v} : Set N) = {e, f, p, p', u, v} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset]
  exact hspan x

private theorem MinusThreeFrame.linearIndependent_six {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) : LinearIndependent K ![e, f, p, p', u, v] := by
  obtain ⟨hue, huf, hup, hup'⟩ := hF.u_perp
  obtain ⟨hve, hvf, hvp, hvp'⟩ := hF.v_perp
  rw [Fintype.linearIndependent_iff]
  intro g hg
  replace hg : g 0 • e + g 1 • f + g 2 • p + g 3 • p' + g 4 • u + g 5 • v = 0 := by
    simpa [Fin.sum_univ_six] using hg
  have hR : ∀ z : N, g 0 * polar Q e z + g 1 * polar Q f z + g 2 * polar Q p z +
      g 3 * polar Q p' z + g 4 * polar Q u z + g 5 * polar Q v z = 0 := fun z => by
    have := congrArg (fun w => polar Q w z) hg
    simpa only [polar_add_left, polar_smul_left_eq, polar_zero_left] using this
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hF.ef
  have hp'p : polar Q p' p = 1 := by rw [polar_comm]; exact hF.pp'
  have hpe : polar Q p e = 0 := by rw [polar_comm]; exact hF.ep
  have hp'e : polar Q p' e = 0 := by rw [polar_comm]; exact hF.ep'
  have hpf : polar Q p f = 0 := by rw [polar_comm]; exact hF.fp
  have hp'f : polar Q p' f = 0 := by rw [polar_comm]; exact hF.fp'
  have g0 : g 0 = 0 := by
    have := hR f
    simp only [hF.ef, polar_self_eq_zero hF.f_sing, hpf, hp'f, huf, hvf] at this
    linear_combination this
  have g1 : g 1 = 0 := by
    have := hR e
    simp only [polar_self_eq_zero hF.e_sing, hfe, hpe, hp'e, hue, hve] at this
    linear_combination this
  have g2 : g 2 = 0 := by
    have := hR p'
    simp only [hF.ep', hF.fp', hF.pp', polar_self_eq_zero hF.p'_sing, hup', hvp'] at this
    linear_combination this
  have g3 : g 3 = 0 := by
    have := hR p
    simp only [hF.ep, hF.fp, polar_self_eq_zero hF.p_sing, hp'p, hup, hvp] at this
    linear_combination this
  rw [g0, g1, g2, g3, zero_smul, zero_smul, zero_smul, zero_smul, zero_add, zero_add, zero_add,
    zero_add] at hg
  obtain ⟨g4, g5⟩ := hF.aniso (g 4) (g 5) (by rw [hg]; exact QuadraticMap.map_zero Q)
  intro i
  fin_cases i <;> assumption

private theorem MinusThreeFrame.finrank_eq_six [FiniteDimensional K N]
    {e f p p' u v : N} (hF : MinusThreeFrame Q e f p p' u v) : finrank K N = 6 := by
  have hx : ∀ x : N, x ∈ Submodule.span K (Set.range ![e, f, p, p', u, v]) := fun x => by
    simpa only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
      using hF.span x
  have htop : Submodule.span K (Set.range ![e, f, p, p', u, v]) = ⊤ :=
    eq_top_iff.mpr fun x _ => hx x
  have h1 : finrank K (Submodule.span K (Set.range ![e, f, p, p', u, v])) = finrank K N := by
    rw [htop]
    exact finrank_top K N
  have h2 := finrank_range_le_card (R := K) ![e, f, p, p', u, v]
  rw [Fintype.card_fin] at h2
  unfold Set.finrank at h2
  have h3 := hF.linearIndependent_six.fintype_card_le_finrank
  rw [Fintype.card_fin] at h3
  omega

private theorem exists_partner_of_pair [FiniteDimensional K N]
    (hnd : (polarBilin Q).Nondegenerate) {e p : N} (he : Q e = 0) (hep : polar Q e p = 0)
    (hli : LinearIndependent K ![e, p]) :
    ∃ f : N, Q f = 0 ∧ polar Q e f = 1 ∧ polar Q p f = 0 := by
  obtain ⟨g, hg⟩ := exists_dual_family hnd hli
  have h1 : polar Q e (g 0) = 1 := by simpa using hg 0 0
  have h2 : polar Q p (g 0) = 0 := by simpa using hg 1 0
  have hpe : polar Q p e = 0 := by rw [polar_comm]; exact hep
  refine ⟨(HypPair.ofPolarEqOne he h1).f, (HypPair.ofPolarEqOne he h1).Q_f,
    (HypPair.ofPolarEqOne he h1).polar_ef, ?_⟩
  rw [HypPair.polar_ofPolarEqOne_f he h1 hpe, h2]

private theorem exists_partner_perp (hnd : (polarBilin Q).Nondegenerate) {e f p : N}
    (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) (hp : Q p = 0) (hp0 : p ≠ 0)
    (hep : polar Q e p = 0) (hfp : polar Q f p = 0) :
    ∃ p' : N, Q p' = 0 ∧ polar Q p p' = 1 ∧ polar Q e p' = 0 ∧ polar Q f p' = 0 := by
  let P : HypPair Q := ⟨e, f, he, hf, hef⟩
  have hpP : p ∈ P.perp := HypPair.mem_perp.mpr ⟨hep, hfp⟩
  obtain ⟨y, hyP, hy⟩ := (P.polarNondegOn_perp hnd).exists_polar_ne_zero hpP hp0
  have h1 : polar Q p ((polar Q p y)⁻¹ • y) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hy]
  obtain ⟨hze, hzf⟩ := HypPair.mem_perp.mp (P.perp.smul_mem (polar Q p y)⁻¹ hyP)
  refine ⟨(HypPair.ofPolarEqOne hp h1).f, (HypPair.ofPolarEqOne hp h1).Q_f,
    (HypPair.ofPolarEqOne hp h1).polar_ef, ?_, ?_⟩
  · rw [HypPair.polar_ofPolarEqOne_f hp h1 hep]
    exact hze
  · rw [HypPair.polar_ofPolarEqOne_f hp h1 hfp]
    exact hzf

private theorem MinusThreeFrame.eq_zero_of_singular_perp [CharP K 2] [Finite K]
    {e₀ f₀ p₀ p₀' u₀ v₀ : N} (hF : MinusThreeFrame Q e₀ f₀ p₀ p₀' u₀ v₀)
    (hnd : (polarBilin Q).Nondegenerate) {e f p p' : N} (he : Q e = 0) (hf : Q f = 0)
    (hp : Q p = 0) (hp0 : p ≠ 0) (hef : polar Q e f = 1) (hpp' : polar Q p p' = 1)
    (hpe : polar Q p e = 0) (hpf : polar Q p f = 0) {w : N} (hw : Q w = 0)
    (hwe : polar Q w e = 0) (hwf : polar Q w f = 0) (hwp : polar Q w p = 0)
    (hwp' : polar Q w p' = 0) : w = 0 := by
  obtain ⟨g, hg, hgp, hge, hgf⟩ := hF.exists_mem_elementaryGroup_flag hnd hp hp0 he hf hpe hpf hef
  have hgO := elementaryGroup_le_orthogonalGroup Q hg
  have hp₀0 : p₀ ≠ 0 := by
    intro h
    have := hF.pp'
    rw [h, polar_zero_left] at this
    exact zero_ne_one this
  obtain ⟨c, hc⟩ := hF.eq_smul_of_polar_eq_zero (w := p₀) (w' := g w)
    (by rw [polar_comm]; exact hF.ep) (by rw [polar_comm]; exact hF.fp)
    (by rw [← hge, polar_map_of_mem hgO]; exact hwe)
    (by rw [← hgf, polar_map_of_mem hgO]; exact hwf) hF.p_sing
    (by rw [map_of_mem hgO]; exact hw) hp₀0
    (by rw [← hgp, polar_map_of_mem hgO, polar_comm]; exact hwp)
  have hw' : w = c • p := g.injective (by rw [map_smul, hgp, hc])
  have hc0 : c = 0 := by
    have := hwp'
    rwa [hw', polar_smul_left_eq, hpp', mul_one] at this
  rw [hw', hc0, zero_smul]

private theorem exists_two_perp [FiniteDimensional K N] (h6 : 6 ≤ finrank K N) (e f p p' : N) :
    ∃ x₁ x₂ : N, LinearIndependent K ![x₁, x₂] ∧
      (polar Q e x₁ = 0 ∧ polar Q f x₁ = 0 ∧ polar Q p x₁ = 0 ∧ polar Q p' x₁ = 0) ∧
      (polar Q e x₂ = 0 ∧ polar Q f x₂ = 0 ∧ polar Q p x₂ = 0 ∧ polar Q p' x₂ = 0) := by
  let Φ : N →ₗ[K] (Fin 4 → K) := LinearMap.pi fun i => polarBilin Q (![e, f, p, p'] i)
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  have h2 : finrank K (LinearMap.range Φ) ≤ 4 := by
    simpa using Submodule.finrank_le (LinearMap.range Φ)
  obtain ⟨g, hg⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := LinearMap.ker Φ)
    (n := 2) (by omega)
  have hmem : ∀ x : LinearMap.ker Φ, polar Q e x = 0 ∧ polar Q f x = 0 ∧ polar Q p x = 0 ∧
      polar Q p' x = 0 := fun x => by
    have hx : Φ x = 0 := x.2
    have h := fun j => congrFun hx j
    simp only [Φ, LinearMap.pi_apply, polarBilin_apply_apply, Pi.zero_apply] at h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2, by simpa using h 3⟩
  refine ⟨g 0, g 1, ?_, hmem (g 0), hmem (g 1)⟩
  have hli := hg.map' (LinearMap.ker Φ).subtype (LinearMap.ker Φ).ker_subtype
  convert hli using 1
  ext i
  fin_cases i <;> rfl

private theorem exists_normalized_pair [Finite K] [CharP K 2] {C : Submodule K N}
    (hC : ∀ w ∈ C, Q w = 0 → w = 0) {x₁ x₂ : N} (h1 : x₁ ∈ C) (h2 : x₂ ∈ C)
    (hx : LinearIndependent K ![x₁, x₂]) :
    ∃ u v : N, u ∈ C ∧ v ∈ C ∧ Q u = 1 ∧ polar Q u v ≠ 0 ∧
      ∀ r : K, r ^ 2 + polar Q u v * r + Q v ≠ 0 := by
  have hx10 : x₁ ≠ 0 := by simpa using hx.ne_zero 0
  have hQx₁ : Q x₁ ≠ 0 := fun h => hx10 (hC x₁ h1 h)
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (Q x₁)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hQx₁ (by rw [hs, mul_zero])
  obtain ⟨u, hu_def⟩ : ∃ u : N, u = s⁻¹ • x₁ := ⟨_, rfl⟩
  have hQu : Q u = 1 := by
    rw [hu_def, map_smul_eq_sq, hs]
    field_simp
  have hli' : LinearIndependent K ![u, x₂] := by
    rw [LinearIndependent.pair_iff] at hx ⊢
    intro a b hab
    obtain ⟨ha, hb⟩ := hx (a * s⁻¹) b (by rw [mul_smul, ← hu_def]; exact hab)
    exact ⟨by simpa [hs0] using ha, hb⟩
  have hq : ∀ a b : K, Q (a • u + b • x₂) = 0 → a = 0 ∧ b = 0 := fun a b hQ =>
    (LinearIndependent.pair_iff.mp hli') a b
      (hC _ (C.add_mem (C.smul_mem a (hu_def ▸ C.smul_mem _ h1)) (C.smul_mem b h2)) hQ)
  have hQab : ∀ a b : K, Q (a • u + b • x₂) = a ^ 2 + polar Q u x₂ * (a * b) + b ^ 2 * Q x₂ :=
    fun a b => by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq Q a u, map_smul_eq_sq Q b x₂, hQu,
      polar_smul_left_eq Q a u, polar_smul_right_eq Q b u x₂]
    ring
  refine ⟨u, x₂, hu_def ▸ C.smul_mem _ h1, h2, hQu, ?_, fun r hr => ?_⟩
  · intro h0
    obtain ⟨t, ht⟩ := isSquare_of_charTwo' (Q x₂)
    have h' : Q (t • u + (1 : K) • x₂) = 0 := by
      rw [hQab, h0, ht]
      linear_combination (t * t) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact one_ne_zero (hq t 1 h').2
  · have h' : Q (r • u + (1 : K) • x₂) = 0 := by
      rw [hQab]
      linear_combination hr
    exact one_ne_zero (hq r 1 h').2

theorem MinusThreeFrame.exists_frame_of_flag [Finite K] [CharP K 2] [FiniteDimensional K N]
    {e₀ f₀ p₀ p₀' u₀ v₀ : N} (hF : MinusThreeFrame Q e₀ f₀ p₀ p₀' u₀ v₀)
    (hnd : (polarBilin Q).Nondegenerate) {e p : N} (he : Q e = 0) (hp : Q p = 0)
    (hep : polar Q e p = 0) (hli : LinearIndependent K ![e, p]) :
    ∃ f p' u v : N, MinusThreeFrame Q e f p p' u v := by
  have hp0 : p ≠ 0 := by simpa using hli.ne_zero 1
  have hpe : polar Q p e = 0 := by rw [polar_comm]; exact hep
  obtain ⟨f, hf, hef, hpf⟩ := exists_partner_of_pair hnd he hep hli
  have hfp : polar Q f p = 0 := by rw [polar_comm]; exact hpf
  obtain ⟨p', hp', hpp', hep', hfp'⟩ := exists_partner_perp hnd he hf hef hp hp0 hep hfp
  let P₁ : HypPair Q := ⟨e, f, he, hf, hef⟩
  let P₂ : HypPair Q := ⟨p, p', hp, hp', hpp'⟩
  have hC : ∀ w ∈ P₁.perp ⊓ P₂.perp, Q w = 0 → w = 0 := fun w hw hQ => by
    obtain ⟨hwe, hwf⟩ := HypPair.mem_perp.mp (Submodule.mem_inf.mp hw).1
    obtain ⟨hwp, hwp'⟩ := HypPair.mem_perp.mp (Submodule.mem_inf.mp hw).2
    exact hF.eq_zero_of_singular_perp hnd he hf hp hp0 hef hpp' hpe hpf hQ
      (by rw [polar_comm]; exact hwe) (by rw [polar_comm]; exact hwf)
      (by rw [polar_comm]; exact hwp) (by rw [polar_comm]; exact hwp')
  obtain ⟨x₁, x₂, hx, ⟨h1e, h1f, h1p, h1p'⟩, ⟨h2e, h2f, h2p, h2p'⟩⟩ :=
    exists_two_perp (Q := Q) hF.finrank_eq_six.ge e f p p'
  obtain ⟨u, v, hu, hv, hQu, hpuv, hroot⟩ := exists_normalized_pair hC
    (Submodule.mem_inf.mpr ⟨HypPair.mem_perp.mpr ⟨h1e, h1f⟩, HypPair.mem_perp.mpr ⟨h1p, h1p'⟩⟩)
    (Submodule.mem_inf.mpr ⟨HypPair.mem_perp.mpr ⟨h2e, h2f⟩, HypPair.mem_perp.mpr ⟨h2p, h2p'⟩⟩) hx
  exact ⟨f, p', u, v, exists_minusThreeFrame (Q := Q) hF.finrank_eq_six ![P₁, P₂]
    ⟨hep, hep', hfp, hfp'⟩
    (Fin.forall_fin_two.mpr
      ⟨⟨(Submodule.mem_inf.mp hu).1, (Submodule.mem_inf.mp hv).1⟩,
        ⟨(Submodule.mem_inf.mp hu).2, (Submodule.mem_inf.mp hv).2⟩⟩)
    hQu hpuv hroot⟩

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
