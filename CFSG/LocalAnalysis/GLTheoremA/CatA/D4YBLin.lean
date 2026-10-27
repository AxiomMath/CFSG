module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankCount
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YFCount

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4YB

open Module QuadraticMap CFSG.StandardType.D4Rank

section Lin

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

@[expose] def fixSp (X : V ≃ₗ[K] V) : Submodule K V := LinearMap.ker ((X : V →ₗ[K] V) - 1)

theorem mem_fixSp {X : V ≃ₗ[K] V} {v : V} : v ∈ fixSp X ↔ X v = v := by
  simp [fixSp, sub_eq_zero]

theorem cube_apply {X : V ≃ₗ[K] V} (hX3 : X ^ 3 = 1) (v : V) : X (X (X v)) = v := by
  have := congrArg (fun f : V ≃ₗ[K] V => f v) hX3
  simpa [pow_succ] using this

theorem comm_apply {X Y : V ≃ₗ[K] V} (hXY : X * Y = Y * X) (v : V) : X (Y v) = Y (X v) := by
  have := congrArg (fun f : V ≃ₗ[K] V => f v) hXY
  simpa using this

@[expose] def pjv (T : V ≃ₗ[K] V) (v : V) : V := v + T v + T (T v)

theorem pjv_mem_fixSp {T : V ≃ₗ[K] V} (hT3 : T ^ 3 = 1) (v : V) : pjv T v ∈ fixSp T := by
  rw [mem_fixSp]
  simp only [pjv, map_add, cube_apply hT3]
  abel

theorem pjv_of_fix (h2 : (2 : K) = 0) {T : V ≃ₗ[K] V} {v : V} (h : T v = v) : pjv T v = v := by
  have hvv : v + v = 0 := by rw [← two_smul K v, h2, zero_smul]
  simp only [pjv, h]
  rw [add_assoc, hvv, add_zero]

theorem pjv_comm {T S : V ≃ₗ[K] V} (hTS : T * S = S * T) (v : V) : T (pjv S v) = pjv S (T v) := by
  simp only [pjv, map_add, comm_apply hTS]

variable (Q : QuadraticForm K V)

theorem polar_apply_isom {X : V ≃ₗ[K] V} (hX : ∀ v, Q (X v) = Q v) (a b : V) :
    polar Q (X a) (X b) = polar Q a b := by
  simp only [polar, ← map_add, hX]

theorem polar_apply_adj {X : V ≃ₗ[K] V} (hX : ∀ v, Q (X v) = Q v) (hX3 : X ^ 3 = 1) (a b : V) :
    polar Q (X a) b = polar Q a (X (X b)) := by
  have h := polar_apply_isom Q hX a (X (X b))
  rwa [cube_apply hX3] at h

theorem polar_pjv_left {X : V ≃ₗ[K] V} (hX : ∀ v, Q (X v) = Q v) (hX3 : X ^ 3 = 1) (a b : V) :
    polar Q (pjv X a) b = polar Q a (pjv X b) := by
  simp only [pjv]
  rw [polar_add_left, polar_add_left, polar_add_right, polar_add_right,
    polar_apply_adj Q hX hX3 a b, polar_apply_adj Q hX hX3 (X a) b,
    polar_apply_adj Q hX hX3 a (X (X b)), cube_apply hX3 (X b)]
  ring

theorem nondeg_fixSp (h2 : (2 : K) = 0) (hnd : ∀ v : V, (∀ w, polar Q v w = 0) → v = 0)
    {X : V ≃ₗ[K] V} (hX : ∀ v, Q (X v) = Q v) (hX3 : X ^ 3 = 1) {c : V} (hc : c ∈ fixSp X)
    (h : ∀ c' ∈ fixSp X, polar Q c c' = 0) : c = 0 := by
  refine hnd c fun w => ?_
  have h1 : polar Q c w = polar Q (pjv X c) w := by rw [pjv_of_fix h2 (mem_fixSp.1 hc)]
  rw [h1, polar_pjv_left Q hX hX3]
  exact h _ (pjv_mem_fixSp hX3 w)

theorem nondeg_fixSp_inf (h2 : (2 : K) = 0) (hnd : ∀ v : V, (∀ w, polar Q v w = 0) → v = 0)
    {X Y : V ≃ₗ[K] V} (hXi : ∀ v, Q (X v) = Q v) (hYi : ∀ v, Q (Y v) = Q v)
    (hX3 : X ^ 3 = 1) (hY3 : Y ^ 3 = 1) (hXY : X * Y = Y * X) {c : V}
    (hc : c ∈ fixSp X ⊓ fixSp Y) (h : ∀ c' ∈ fixSp X ⊓ fixSp Y, polar Q c c' = 0) : c = 0 := by
  refine hnd c fun w => ?_
  have h1 : polar Q c w = polar Q (pjv X (pjv Y c)) w := by
    rw [pjv_of_fix h2 (mem_fixSp.1 hc.2), pjv_of_fix h2 (mem_fixSp.1 hc.1)]
  rw [h1, polar_pjv_left Q hXi hX3, polar_pjv_left Q hYi hY3]
  refine h _ ⟨?_, pjv_mem_fixSp hY3 _⟩
  rw [SetLike.mem_coe, mem_fixSp, pjv_comm hXY, (mem_fixSp.1 (pjv_mem_fixSp hX3 w))]

end Lin

section Pair

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (Q : QuadraticForm K V)

theorem pair_lemma (hQ3 : Nat.card K % 3 = 2)
    (hnd : ∀ v : V, (∀ w, polar Q v w = 0) → v = 0)
    (hsing : Nat.card {v : V // Q v = 0} % 3 = 1)
    {X Y : V ≃ₗ[K] V} (hXi : ∀ v, Q (X v) = Q v) (hYi : ∀ v, Q (Y v) = Q v)
    (hX3 : X ^ 3 = 1) (hY3 : Y ^ 3 = 1) (hXY : X * Y = Y * X)
    {Z : Submodule K V} (hZY : ∀ v ∈ Z, Y v ∈ Z) (hZs : ∀ v ∈ Z, Q v = 0)
    {u : V} (huZ : u ∈ Z) (hu0 : u ≠ 0) (huX : X u = u)
    {n₀ d : ℕ} (hF : finrank K ↥(fixSp X ⊓ fixSp Y) = n₀) (hC : finrank K ↥(fixSp X) = d)
    (harith : (n₀ = 0 ∧ d = 2) ∨ (n₀ = 2 ∧ (d = 2 ∨ d = 4))) : False := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hvv : ∀ v : V, v + v = 0 := fun v => by rw [← two_smul K v, h2, zero_smul]
  have hcc : ∀ c : K, c + c = 0 := fun c => by rw [← two_mul, h2, zero_mul]
  have hω := CFSG.LocalAnalysis.GLTheoremA.D4YF.no_cube_root hQ3
  have hpolZ : ∀ a ∈ Z, ∀ b ∈ Z, ∀ hab : a + b ∈ Z, polar Q a b = 0 := fun a ha b hb hab => by
    simp only [polar]
    rw [hZs _ hab, hZs a ha, hZs b hb]
    ring
  have hXYv := comm_apply hXY
  have hY3v := cube_apply hY3
  by_cases hf : u + Y u + Y (Y u) = 0
  ·
    have hneg : ∀ v : V, -v = v := fun v => neg_eq_of_add_eq_zero_right (hvv v)
    have hYYu : Y (Y u) = u + Y u := by
      have h1 := eq_neg_of_add_eq_zero_right hf
      rw [h1, hneg]
    have hYu0 : Y u ≠ 0 := fun h => hu0 (Y.injective (by rw [h, map_zero]))
    have hYuZ : Y u ∈ Z := hZY u huZ
    have hli : LinearIndependent K ![u, Y u] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        rw [zero_smul, add_zero] at hst
        exact ⟨(smul_eq_zero.1 hst).resolve_right hu0, rfl⟩
      · exfalso
        have hYu : Y u = (s / t) • u := by
          have h1 : t • Y u = s • u := by
            have := eq_neg_of_add_eq_zero_right hst
            rw [this]
            have hs : s • u + s • u = 0 := by rw [← two_smul K (s • u), smul_smul, h2, zero_mul, zero_smul]
            exact (neg_eq_of_add_eq_zero_left hs)
          calc Y u = t⁻¹ • (t • Y u) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
            _ = (s / t) • u := by rw [h1, smul_smul, div_eq_inv_mul]
        have hf' : (1 + (s / t) + (s / t) ^ 2) • u = 0 := by
          have h3 := hf
          rw [hYu, map_smul, hYu, smul_smul] at h3
          rw [add_smul, add_smul, one_smul, pow_two]
          exact h3
        have h4 : 1 + (s / t) + (s / t) ^ 2 = 0 := (smul_eq_zero.1 hf').resolve_right hu0
        exact hω (s / t) (by linear_combination h4)
    set W : Submodule K V := Submodule.span K {u, Y u} with hW
    have hmemW : ∀ w, w ∈ W ↔ ∃ a b : K, a • u + b • Y u = w := fun w => Submodule.mem_span_pair
    have hW2 : finrank K W = 2 := by
      have h := finrank_span_eq_card hli
      have hr : Set.range ![u, Y u] = {u, Y u} := by
        ext v
        simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hr] at h
      simpa using h
    have hWZ : W ≤ Z := by
      rw [hW, Submodule.span_le]
      intro v hv
      rcases hv with rfl | rfl
      · exact huZ
      · exact hYuZ
    have hWX : W ≤ fixSp X := by
      rw [hW, Submodule.span_le]
      intro v hv
      rcases hv with rfl | rfl
      · exact mem_fixSp.2 huX
      · exact mem_fixSp.2 (by rw [hXYv, huX])
    have hWY : ∀ w ∈ W, Y w = w → w = 0 := by
      intro w hw hYw
      obtain ⟨a, b, rfl⟩ := (hmemW w).1 hw
      rw [map_add, map_smul, map_smul, hYYu] at hYw
      have hlc : (b - a) • u + a • Y u = 0 := by
        linear_combination (norm := module) hYw
      obtain ⟨h1, h2'⟩ := LinearIndependent.pair_iff.1 hli _ _ hlc
      have ha : a = 0 := h2'
      have hb : b = 0 := by rw [ha] at h1; simpa using h1
      rw [ha, hb]; simp
    have hWF : W ⊓ (fixSp X ⊓ fixSp Y) = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_bot]
      exact hWY w hw.1 (mem_fixSp.1 hw.2.2)
    have hcmp : ∀ f' ∈ fixSp X ⊓ fixSp Y, ∀ y' : V, polar Q f' (y' + Y y') = 0 := by
      intro f' hf' y'
      have hYf' : Y f' = f' := mem_fixSp.1 hf'.2
      have h1 := polar_apply_isom Q hYi f' y'
      rw [hYf'] at h1
      rw [polar_add_right, h1]
      exact hcc _
    have hBFW : ∀ f' ∈ fixSp X ⊓ fixSp Y, ∀ w ∈ W, polar Q f' w = 0 := by
      intro f' hf' w hw
      obtain ⟨a, b, rfl⟩ := (hmemW w).1 hw
      have hu' : polar Q f' u = 0 := by
        have h1 := hcmp f' hf' (Y u)
        have e1 : Y u + Y (Y u) = u := by
          rw [hYYu, add_comm u (Y u), ← add_assoc, hvv, zero_add]
        rwa [e1] at h1
      have hYu' : polar Q f' (Y u) = 0 := by
        have h1 := hcmp f' hf' u
        rw [polar_add_right, hu', zero_add] at h1
        exact h1
      rw [polar_add_right, polar_smul_right, polar_smul_right, hu', hYu']
      simp
    have hsup : W ⊔ (fixSp X ⊓ fixSp Y) ≤ fixSp X := sup_le hWX inf_le_left
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq W (fixSp X ⊓ fixSp Y)
    rw [hWF, finrank_bot, hW2, hF] at hdim
    have hle := Submodule.finrank_mono hsup
    rw [hC] at hle
    have hEq : W ⊔ (fixSp X ⊓ fixSp Y) = fixSp X :=
      Submodule.eq_of_le_of_finrank_eq hsup (by rw [hC]; omega)
    refine hu0 (nondeg_fixSp Q h2 hnd hXi hX3 (mem_fixSp.2 huX) fun c' hc' => ?_)
    rw [← hEq] at hc'
    obtain ⟨y', hy', z', hz', rfl⟩ := Submodule.mem_sup.1 hc'
    have huW : u ∈ W := Submodule.subset_span (by simp)
    rw [polar_add_right]
    have h1 : polar Q u y' = 0 := hpolZ u huZ y' (hWZ hy') (Z.add_mem huZ (hWZ hy'))
    have h2' : polar Q u z' = 0 := by rw [polar_comm]; exact hBFW z' hz' u huW
    rw [h1, h2', add_zero]
  ·
    set f : V := u + Y u + Y (Y u) with hfdef
    have hfZ : f ∈ Z := Z.add_mem (Z.add_mem huZ (hZY u huZ)) (hZY _ (hZY u huZ))
    have hYf : Y f = f := by
      simp only [hfdef, map_add, hY3v]
      abel
    have hXf : X f = f := by
      simp only [hfdef, map_add, hXYv, huX]
    have hfF : f ∈ fixSp X ⊓ fixSp Y := ⟨mem_fixSp.2 hXf, mem_fixSp.2 hYf⟩
    have hFne : fixSp X ⊓ fixSp Y ≠ ⊥ := fun h => hf (by
      have := hfF
      rw [h, Submodule.mem_bot] at this
      exact this)
    have hn0 : n₀ = 2 := by
      have h1 : 1 ≤ finrank K ↥(fixSp X ⊓ fixSp Y) := Submodule.one_le_finrank_iff.2 hFne
      omega
    set P : Set V := {v | Q v = 0} with hP
    have hPcard : P.ncard % 3 = 1 := by
      rw [← Nat.card_coe_set_eq]
      exact hsing
    have hPinv : ∀ T : V ≃ₗ[K] V, (∀ v, Q (T v) = Q v) → ∀ v ∈ P, T v ∈ P := fun T hT v hv => by
      show Q (T v) = 0
      rw [hT]
      exact hv
    have hm1 := CFSG.LocalAnalysis.GLTheoremA.D4T.ncard_modEq_fixed X (p := 3) hX3 P (hPinv X hXi)
    have hSinv : ∀ v ∈ P ∩ {v | X v = v}, Y v ∈ P ∩ {v | X v = v} := by
      rintro v ⟨hvP, hvX⟩
      refine ⟨hPinv Y hYi v hvP, ?_⟩
      show X (Y v) = Y v
      rw [hXYv, show X v = v from hvX]
    have hm2 := CFSG.LocalAnalysis.GLTheoremA.D4T.ncard_modEq_fixed Y (p := 3) hY3
      (P ∩ {v | X v = v}) hSinv
    have hset : P ∩ {v | X v = v} ∩ {v | Y v = v} = P ∩ ((fixSp X ⊓ fixSp Y : Submodule K V) : Set V) := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_inf, mem_fixSp]
      tauto
    rw [hset] at hm2
    have hmod : (P ∩ ((fixSp X ⊓ fixSp Y : Submodule K V) : Set V)).ncard % 3 = 1 := by
      have := hm1.trans hm2
      unfold Nat.ModEq at this
      omega
    have hFnd : ∀ c ∈ fixSp X ⊓ fixSp Y, (∀ c' ∈ fixSp X ⊓ fixSp Y, polar Q c c' = 0) → c = 0 :=
      fun c hc h => nondeg_fixSp_inf Q h2 hnd hXi hYi hX3 hY3 hXY hc h
    have hfQ : Q f = 0 := hZs _ hfZ
    have hcnt := CFSG.LocalAnalysis.GLTheoremA.D4YF.card_sing_plane Q (fixSp X ⊓ fixSp Y)
      (by rw [hF, hn0]) hFnd hfF hf hfQ
    have hcnt' : (P ∩ ((fixSp X ⊓ fixSp Y : Submodule K V) : Set V)).ncard + 1 = 2 * Nat.card K :=
      hcnt
    omega

theorem fp_apply (X : V ≃ₗ[K] V) (v : V) : fp (X : Module.End K V) v = pjv X v := by
  simp [fp, pjv, pow_two, Module.End.mul_apply, add_assoc]

theorem range_fp_mul (h2 : (2 : K) = 0) {X Y : V ≃ₗ[K] V} (hX3 : X ^ 3 = 1) (hY3 : Y ^ 3 = 1)
    (hXY : X * Y = Y * X) :
    LinearMap.range (fp (X : Module.End K V) * fp (Y : Module.End K V)) = fixSp X ⊓ fixSp Y := by
  ext v
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    rw [Module.End.mul_apply, fp_apply, fp_apply]
    refine ⟨pjv_mem_fixSp hX3 _, ?_⟩
    rw [SetLike.mem_coe, mem_fixSp]
    have := pjv_comm (T := Y) (S := X) hXY.symm (pjv Y w)
    rw [this, mem_fixSp.1 (pjv_mem_fixSp hY3 w)]
  · rintro ⟨hvX, hvY⟩
    refine ⟨v, ?_⟩
    rw [Module.End.mul_apply, fp_apply, fp_apply, pjv_of_fix h2 (mem_fixSp.1 hvY),
      pjv_of_fix h2 (mem_fixSp.1 hvX)]

theorem key_lemma (hQ3 : Nat.card K % 3 = 2) (hV : finrank K V = 8)
    (hnd : ∀ v : V, (∀ w, polar Q v w = 0) → v = 0)
    (hsing : Nat.card {v : V // Q v = 0} % 3 = 1)
    {E : Type} [Group E] [IsMulCommutative E] [Finite E]
    (ρ : E →* (V ≃ₗ[K] V)) (hiso : ∀ x v, Q (ρ x v) = Q v) (hexp : ∀ x : E, x ^ 3 = 1)
    (hcard : 9 ≤ Nat.card E)
    (hd : ∀ x : E, x ≠ 1 → finrank K ↥(fixSp (ρ x)) = 2 ∨ finrank K ↥(fixSp (ρ x)) = 4)
    (Z : Submodule K V) (hZE : ∀ x : E, ∀ v ∈ Z, ρ x v ∈ Z) (hZs : ∀ v ∈ Z, Q v = 0) :
    Z = ⊥ := by
  classical
  by_contra hZne
  obtain ⟨z, hzZ, hz0⟩ := (Submodule.ne_bot_iff Z).1 hZne
  have hord : ∀ x : E, orderOf x ≤ 3 := fun x => orderOf_le_of_pow_eq_one (by norm_num) (hexp x)
  obtain ⟨g, hg1⟩ : ∃ g : E, g ≠ 1 := by
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne (1 : E)
  obtain ⟨h, hh⟩ : ∃ h : E, h ∉ Subgroup.zpowers g := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (show (⊤ : Subgroup E) ≤ Subgroup.zpowers g from
      fun x _ => hcon x)
    rw [Subgroup.card_top, Nat.card_zpowers] at hle
    have := hord g
    omega
  obtain ⟨hh1, hgh1, hgh21⟩ := not_mem_zpowers_facts (hexp h) hh
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  let ρ' : E →* Module.End K V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V)).comp ρ
  obtain ⟨A, _, φ, ι, hφinj, hφι⟩ := exists_commRing_model ρ'
  have h2 : (2 : A) = 0 := hφinj (by rw [map_ofNat, map_zero, two_eq_zero_end h2K])
  have hι3 : ∀ x : E, ι x ^ 3 = 1 := fun x => by rw [← map_pow, hexp x, map_one]
  have hρ3 : ∀ x : E, ρ x ^ 3 = 1 := fun x => by rw [← map_pow, hexp x, map_one]
  have hidem : ∀ x : E, fp (ι x) * fp (ι x) = fp (ι x) := fun x => ring_fixProj_sq h2 (hι3 x)
  have hfpφ : ∀ x : E, φ (fp (ι x)) = fp (ρ' x) := fun x => by
    simp only [fp, map_add, map_one, map_pow, hφι]
  have hrk : ∀ x : E, rk (φ (fp (ι x))) = finrank K ↥(fixSp (ρ x)) := fun x => by
    rw [hfpφ, rk, range_fixProj h2K (by rw [← map_pow, hexp x, map_one])]
    rfl
  set T : A := fp (ι g) * fp (ι h) with hT
  set n₀ : ℕ := rk (φ T) with hn₀
  have R1 : finrank K ↥(fixSp (ρ g)) + finrank K ↥(fixSp (ρ h)) + finrank K ↥(fixSp (ρ (g * h))) +
      finrank K ↥(fixSp (ρ (g * h ^ 2))) = 8 + 3 * n₀ := by
    have hf := rank_formula φ h2 (hidem g) (hidem h) (hidem (g * h)) (hidem (g * h ^ 2)) rfl
      (by rw [map_mul]; exact ring_fixProj_mul_g_gh (hι3 g))
      (by rw [map_mul, map_pow]; exact ring_fixProj_mul_g_gh2 (hι3 g) (hι3 h))
      (by rw [map_mul]; exact ring_fixProj_mul_h_gh (hι3 h))
      (by rw [map_mul, map_pow]; exact ring_fixProj_mul_h_gh2 (hι3 h))
      (by rw [map_mul, map_mul, map_pow]; exact ring_fixProj_mul_gh_gh2 (hι3 g) (hι3 h))
      (P := 1) (by rw [map_mul, map_mul, map_pow]; exact ring_fixProj_sum h2 (hι3 h))
    rw [hrk, hrk, hrk, hrk, map_one] at hf
    rw [hf]
    congr 1
    rw [rk, LinearMap.range_eq_top.mpr fun v => ⟨v, rfl⟩, finrank_top, hV]
  have hdg := hd g hg1
  have hdh := hd h hh1
  have hdgh := hd (g * h) hgh1
  have hdgh2 := hd (g * h ^ 2) hgh21
  have hn0le : n₀ = 0 ∨ n₀ = 2 := by omega
  have hcomm : ∀ x y : E, ρ x * ρ y = ρ y * ρ x := fun x y => by
    rw [← map_mul, ← map_mul, (IsMulCommutative.is_comm (M := E)).comm x y]
  have hFdim : ∀ x y : E, fp (ι x) * fp (ι y) = T →
      finrank K ↥(fixSp (ρ x) ⊓ fixSp (ρ y)) = n₀ := fun x y hxy => by
    rw [hn₀, ← hxy, map_mul, hfpφ, hfpφ, rk]
    have := range_fp_mul h2K (hρ3 x) (hρ3 y) (hcomm x y)
    rw [show ((ρ x : V ≃ₗ[K] V) : Module.End K V) = ρ' x from rfl,
      show ((ρ y : V ≃ₗ[K] V) : Module.End K V) = ρ' y from rfl] at this
    rw [this]
  have hPmem : ∀ x : E, ∀ v ∈ Z, fp (ρ' x) v ∈ Z := fun x v hv => by
    rw [show fp (ρ' x) v = pjv (ρ x) v from fp_apply (ρ x) v]
    exact Z.add_mem (Z.add_mem hv (hZE x v hv)) (hZE x _ (hZE x v hv))
  have hPfix : ∀ x : E, ∀ v, ρ x (fp (ρ' x) v) = fp (ρ' x) v := fun x v => by
    rw [show fp (ρ' x) v = pjv (ρ x) v from fp_apply (ρ x) v]
    exact mem_fixSp.1 (pjv_mem_fixSp (hρ3 x) v)
  have hsumEnd : fp (ρ' g) + fp (ρ' h) + fp (ρ' (g * h)) + fp (ρ' (g * h ^ 2)) =
      1 + fp (ρ' g) * fp (ρ' h) := by
    have hS := congrArg φ (ring_fixProj_sum h2 (g := ι g) (h := ι h) (hι3 h))
    rw [map_add, map_add, map_add, map_add _ (1 : A), map_one, map_mul] at hS
    rw [← map_pow ι h 2, ← map_mul ι g (h ^ 2), ← map_mul ι g h, hfpφ, hfpφ, hfpφ, hfpφ] at hS
    exact hS
  have hex : ∃ x : E, (x = g ∨ x = h ∨ x = g * h ∨ x = g * h ^ 2) ∧ fp (ρ' x) z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have e1 := hcon g (Or.inl rfl)
    have e2 := hcon h (Or.inr (Or.inl rfl))
    have e3 := hcon (g * h) (Or.inr (Or.inr (Or.inl rfl)))
    have e4 := hcon (g * h ^ 2) (Or.inr (Or.inr (Or.inr rfl)))
    have := LinearMap.congr_fun hsumEnd z
    simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply, e1, e2, e3, e4,
      add_zero, map_zero] at this
    exact hz0 this.symm
  have hari : ∀ x : E, (x = g ∨ x = h ∨ x = g * h ∨ x = g * h ^ 2) →
      (n₀ = 0 ∧ finrank K ↥(fixSp (ρ x)) = 2) ∨
        (n₀ = 2 ∧ (finrank K ↥(fixSp (ρ x)) = 2 ∨ finrank K ↥(fixSp (ρ x)) = 4)) := by
    intro x hx
    rcases hx with hx | hx | hx | hx <;> rw [hx] <;> omega
  have partner : ∀ x : E, (x = g ∨ x = h ∨ x = g * h ∨ x = g * h ^ 2) →
      ∃ y : E, fp (ι x) * fp (ι y) = T := by
    intro x hx
    rcases hx with hx | hx | hx | hx
    · exact ⟨h, by rw [hx]⟩
    · exact ⟨g, by rw [hx, mul_comm]⟩
    · exact ⟨g, by
        rw [hx, mul_comm (fp (ι (g * h))) (fp (ι g)), map_mul]
        exact ring_fixProj_mul_g_gh (hι3 g)⟩
    · exact ⟨g, by
        rw [hx, mul_comm (fp (ι (g * h ^ 2))) (fp (ι g)), map_mul, map_pow]
        exact ring_fixProj_mul_g_gh2 (hι3 g) (hι3 h)⟩
  obtain ⟨x, hx, hPx⟩ := hex
  obtain ⟨y, hy⟩ := partner x hx
  exact pair_lemma Q hQ3 hnd hsing (X := ρ x) (Y := ρ y) (hiso x) (hiso y) (hρ3 x) (hρ3 y)
    (hcomm x y) (hZE y) hZs (hPmem x z hzZ) hPx (hPfix x z) (hFdim x y hy) rfl (hari x hx)

end Pair

end CFSG.LocalAnalysis.GLTheoremA.D4YB
