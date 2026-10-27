module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open QuadraticMap (polar polarBilin polar_add_left polar_add_right polar_comm polar_smul_left
  polar_smul_right polar_sub_left polar_sub_right)
open LinearMap (BilinForm)
open CFSG.ClassicalGroups.Orthogonal (map_of_mem map_smul_eq_sq polar_map_of_mem
  polar_self_eq_two_mul)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs (Frame)

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {U : Submodule F V} {t : V ≃ₗ[F] V}

private theorem oma2_t3 (ht3 : t ^ 3 = 1) (v : V) : t (t (t v)) = v := by
  have h : (t ^ 3) v = v := LinearEquiv.congr_fun ht3 v
  rwa [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h

private theorem oma2_tt [CharP F 2] (ht3 : t ^ 3 = 1) (htU : ∀ u ∈ U, t u ∈ U)
    (htfix : ∀ u ∈ U, t u = u → u = 0) {u : V} (hu : u ∈ U) : t (t u) = u + t u := by
  have h0 : t (t u) + (u + t u) = 0 := by
    refine htfix _ (U.add_mem (htU _ (htU _ hu)) (U.add_mem hu (htU _ hu))) ?_
    rw [map_add, map_add, oma2_t3 ht3]
    abel
  rw [eq_neg_of_add_eq_zero_left h0, ← neg_one_smul F, CharTwo.neg_eq (1 : F), one_smul]

private theorem oma2_polar_t [CharP F 2] (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht3 : t ^ 3 = 1) (htU : ∀ u ∈ U, t u ∈ U) (htfix : ∀ u ∈ U, t u = u → u = 0) {u : V}
    (hu : u ∈ U) : polar Q u (t u) = Q u := by
  have h : Q (t (t u)) = Q u := by rw [map_of_mem ht, map_of_mem ht]
  rw [oma2_tt ht3 htU htfix hu, QuadraticMap.map_add Q, map_of_mem ht,
    CharTwo.add_self_eq_zero, zero_add] at h
  exact h

private theorem oma2_exists_polar_ne
    (hUnd : (BilinForm.restrict (polarBilin Q) U).Nondegenerate) {x : V} (hx : x ∈ U)
    (hx0 : x ≠ 0) : ∃ y ∈ U, polar Q x y ≠ 0 := by
  by_contra h
  refine hx0 (congrArg Subtype.val (hUnd.1 ⟨x, hx⟩ fun y => ?_))
  by_contra hy
  exact h ⟨y, y.2, hy⟩

private theorem oma2_exists_singular [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hU : 4 ≤ Module.finrank F U) (hUnd : (BilinForm.restrict (polarBilin Q) U).Nondegenerate)
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht3 : t ^ 3 = 1)
    (htU : ∀ u ∈ U, t u ∈ U) (htfix : ∀ u ∈ U, t u = u → u = 0) :
    ∃ p ∈ U, Q p = 0 ∧ ∀ κ : F, t p ≠ κ • p := by
  classical
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hUbot : U ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hU
    omega
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUbot
  obtain ⟨y, hyU, hxy⟩ := oma2_exists_polar_ne hUnd hxU hx0
  obtain ⟨u, huU, hQu⟩ : ∃ u ∈ U, Q u ≠ 0 := by
    by_contra h
    have h0 : ∀ v ∈ U, Q v = 0 := fun v hv => by
      by_contra hv0
      exact h ⟨v, hv, hv0⟩
    exact hxy (by rw [QuadraticMap.polar, h0 _ (U.add_mem hxU hyU), h0 _ hxU, h0 _ hyU,
      sub_zero, sub_zero])
  have htuU := htU u huU
  have huu : polar Q u u = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have htt : polar Q (t u) (t u) = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hut : polar Q u (t u) = Q u := oma2_polar_t ht ht3 htU htfix huU
  have hQu' : (Q u)⁻¹ * Q u = 1 := inv_mul_cancel₀ hQu
  obtain ⟨S, hSu, hSt, hUS⟩ : ∃ S : Submodule F V, u ∈ S ∧ t u ∈ S ∧ ¬ U ≤ S := by
    refine ⟨Submodule.span F {u, t u}, Submodule.subset_span (Set.mem_insert _ _),
      Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)), fun hle => ?_⟩
    have h1 := finrank_span_finset_le_card (R := F) ({u, t u} : Finset V)
    rw [Finset.coe_insert, Finset.coe_singleton] at h1
    have := (Submodule.finrank_mono hle).trans (h1.trans Finset.card_le_two)
    omega
  obtain ⟨y₀, hy₀U, hy₀S⟩ := SetLike.not_le_iff_exists.1 hUS
  obtain ⟨pr, hpr⟩ : ∃ pr : V → V, ∀ y, pr y =
      y + (((Q u)⁻¹ * polar Q y (t u)) • u + ((Q u)⁻¹ * polar Q y u) • t u) :=
    ⟨_, fun _ => rfl⟩
  have hprU : ∀ y ∈ U, pr y ∈ U := fun y hy => by
    rw [hpr]
    exact U.add_mem hy (U.add_mem (U.smul_mem _ huU) (U.smul_mem _ htuU))
  have hprS : ∀ y, pr y - y ∈ S := fun y => by
    rw [hpr, add_sub_cancel_left]
    exact S.add_mem (S.smul_mem _ hSu) (S.smul_mem _ hSt)
  have hpru : ∀ y, polar Q (pr y) u = 0 := fun y => by
    simp only [hpr, polar_add_left, polar_smul_left, smul_eq_mul, huu, polar_comm Q (t u) u, hut]
    linear_combination polar Q y u * hQu' + polar Q y u * h2
  have hprt : ∀ y, polar Q (pr y) (t u) = 0 := fun y => by
    simp only [hpr, polar_add_left, polar_smul_left, smul_eq_mul, htt, hut]
    linear_combination polar Q y (t u) * hQu' + polar Q y (t u) * h2
  have hprp : ∀ v y, polar Q v u = 0 → polar Q v (t u) = 0 → polar Q v (pr y) = polar Q v y :=
    fun v y h1 h2' => by
      simp only [hpr, polar_add_right, polar_smul_right, smul_eq_mul, h1, h2', mul_zero, add_zero]
  have hv0 : pr y₀ ≠ 0 := fun h0 => hy₀S (by
    have h1 := hprS y₀
    rwa [h0, zero_sub, Submodule.neg_mem_iff] at h1)
  obtain ⟨z, hzU, hvz⟩ := oma2_exists_polar_ne hUnd (hprU y₀ hy₀U) hv0
  rw [← hprp _ z (hpru y₀) (hprt y₀)] at hvz
  obtain ⟨w, hwU, hwu, hwt, hQw⟩ :
      ∃ w ∈ U, polar Q w u = 0 ∧ polar Q w (t u) = 0 ∧ Q w ≠ 0 := by
    by_contra h
    have key : ∀ w ∈ U, polar Q w u = 0 → polar Q w (t u) = 0 → Q w = 0 :=
      fun w hw h1 h2' => by
        by_contra hQ
        exact h ⟨w, hw, h1, h2', hQ⟩
    refine hvz ?_
    rw [QuadraticMap.polar, key _ (U.add_mem (hprU y₀ hy₀U) (hprU z hzU))
      (by rw [polar_add_left, hpru, hpru, add_zero]) (by rw [polar_add_left, hprt, hprt, add_zero]),
      key _ (hprU y₀ hy₀U) (hpru y₀) (hprt y₀), key _ (hprU z hzU) (hpru z) (hprt z), sub_zero,
      sub_zero]
  obtain ⟨d, hd⟩ := isSquare_of_charTwo' (Q u / Q w)
  have hwu' : polar Q u w = 0 := by rw [polar_comm, hwu]
  have htw : polar Q u (t w) = 0 := by
    have h1 : polar Q (t (t u)) (t (t (t w))) = polar Q u (t w) := by
      rw [polar_map_of_mem ht, polar_map_of_mem ht]
    rw [← h1, oma2_t3 ht3, oma2_tt ht3 htU htfix huU, polar_add_left, hwu', polar_comm Q (t u),
      hwt, add_zero]
  refine ⟨u + d • w, U.add_mem huU (U.smul_mem d hwU), ?_, fun κ hκ => hQu ?_⟩
  · have hdw : d ^ 2 * Q w = Q u := by rw [sq, ← hd, div_mul_cancel₀ _ hQw]
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, hdw, polar_smul_right, hwu', smul_zero, add_zero,
      CharTwo.add_self_eq_zero]
  · have h1 := congrArg (polar Q u) hκ
    simp only [map_add, map_smul, polar_add_right, polar_smul_right, smul_eq_mul, hut, htw, huu,
      hwu', mul_zero, add_zero] at h1
    exact h1

private theorem oma2_exists_dual (hUnd : (BilinForm.restrict (polarBilin Q) U).Nondegenerate)
    {p q : V} (hpU : p ∈ U) (hqU : q ∈ U) (hpq : ∀ κ : F, q ≠ κ • p) (hp0 : p ≠ 0) :
    ∃ y ∈ U, polar Q p y = 0 ∧ polar Q q y = 1 := by
  obtain ⟨y₀, hy₀U, hy₀⟩ := oma2_exists_polar_ne hUnd hpU hp0
  obtain ⟨y₁, hy₁U, hy₁⟩ := oma2_exists_polar_ne hUnd
    (U.sub_mem hqU (U.smul_mem (polar Q q y₀ / polar Q p y₀) hpU)) fun h => hpq _ (sub_eq_zero.1 h)
  rw [polar_sub_left, polar_smul_left, smul_eq_mul] at hy₁
  have hy₂U : y₁ - (polar Q p y₁ / polar Q p y₀) • y₀ ∈ U := U.sub_mem hy₁U (U.smul_mem _ hy₀U)
  have hp₂ : polar Q p (y₁ - (polar Q p y₁ / polar Q p y₀) • y₀) = 0 := by
    rw [polar_sub_right, polar_smul_right, smul_eq_mul, div_mul_cancel₀ _ hy₀, sub_self]
  have hq₂ : polar Q q (y₁ - (polar Q p y₁ / polar Q p y₀) • y₀) ≠ 0 := by
    rw [polar_sub_right, polar_smul_right, smul_eq_mul]
    exact fun h => hy₁ (by linear_combination h)
  generalize y₁ - (polar Q p y₁ / polar Q p y₀) • y₀ = y₂ at hy₂U hp₂ hq₂
  refine ⟨(polar Q q y₂)⁻¹ • y₂, U.smul_mem _ hy₂U, ?_, ?_⟩
  · rw [polar_smul_right, hp₂, smul_zero]
  · rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hq₂]

theorem SG.exists_frame_incl_mul [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hU : 4 ≤ Module.finrank F U) (hUnd : (BilinForm.restrict (polarBilin Q) U).Nondegenerate)
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht3 : t ^ 3 = 1)
    (htU : ∀ u ∈ U, t u ∈ U) (htfix : ∀ u ∈ U, t u = u → u = 0) :
    ∃ Fr : Frame Q, (∀ X, Fr.incl X ∈ U) ∧
      ∀ X, t (Fr.incl X) = Fr.incl (X * !![0, 1; 1, 1]) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨p, hpU, hQp, hpt⟩ := oma2_exists_singular hU hUnd ht ht3 htU htfix
  have htpU := htU p hpU
  obtain ⟨y, hyU, hpy, htpy⟩ := oma2_exists_dual hUnd hpU htpU hpt
    fun h0 => hpt 0 (by rw [h0, map_zero, zero_smul])
  have hQtp : Q (t p) = 0 := by rw [map_of_mem ht, hQp]
  have hptp : polar Q p (t p) = 0 := by rw [oma2_polar_t ht ht3 htU htfix hpU, hQp]
  have htptp : polar Q (t p) (t p) = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hqU : y + Q y • t p ∈ U := U.add_mem hyU (U.smul_mem _ htpU)
  have hpq : polar Q p (y + Q y • t p) = 0 := by
    rw [polar_add_right, polar_smul_right, hpy, hptp, smul_zero, add_zero]
  have htpq : polar Q (t p) (y + Q y • t p) = 1 := by
    rw [polar_add_right, polar_smul_right, htpy, htptp, smul_zero, add_zero]
  have hQq : Q (y + Q y • t p) = 0 := by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, hQtp, mul_zero, add_zero, polar_smul_right,
      polar_comm Q y, htpy, smul_eq_mul, mul_one, CharTwo.add_self_eq_zero]
  generalize y + Q y • t p = q at hqU hpq htpq hQq
  have htqU := htU q hqU
  have hptq : polar Q p (t q) = 1 := by
    have h1 : polar Q (t (t p)) (t (t (t q))) = polar Q p (t q) := by
      rw [polar_map_of_mem ht, polar_map_of_mem ht]
    rw [← h1, oma2_t3 ht3, oma2_tt ht3 htU htfix hpU, polar_add_left, hpq, htpq, zero_add]
  have hfe : polar Q (t q) (t p) = 0 := by rw [polar_map_of_mem ht, polar_comm, hpq]
  have hff : polar Q (t q) q = 0 := by
    rw [polar_comm, oma2_polar_t ht ht3 htU htfix hqU, hQq]
  obtain ⟨Fr, he₁, hf₁, he₂, hf₂⟩ : ∃ Fr : Frame Q,
      Fr.e₁ = p ∧ Fr.f₁ = t q ∧ Fr.e₂ = t p ∧ Fr.f₂ = q :=
    ⟨⟨⟨p, t q, hQp, by rw [map_of_mem ht, hQq], hptq⟩, ⟨t p, q, hQtp, hQq, htpq⟩,
      ⟨hptp, hpq, hfe, hff⟩⟩, rfl, rfl, rfl, rfl⟩
  refine ⟨Fr, fun X => ?_, fun X => ?_⟩
  · rw [Fr.incl_apply, he₁, hf₁, he₂, hf₂]
    exact U.add_mem (U.add_mem (U.add_mem (U.smul_mem _ hpU) (U.smul_mem _ htqU))
      (U.smul_mem _ htpU)) (U.smul_mem _ hqU)
  · have hXM : X * !![0, 1; 1, 1] = !![X 0 1, X 0 0 + X 0 1; X 1 1, X 1 0 + X 1 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hXM, Fr.incl_apply, Fr.incl_apply, he₁, hf₁, he₂, hf₂]
    simp only [map_add, map_smul, oma2_tt ht3 htU htfix hpU, oma2_tt ht3 htU htfix hqU,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, CharTwo.neg_eq]
    module

end CFSG.LocalAnalysis.GLTheoremA.S265

end
