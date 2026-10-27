module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalModel
import CFSG.ClassicalInvolution.RouteD.TWYType

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

open Module QuadraticMap CFSG.GroupTheory.WeirSylow
open CFSG.LieType.Universal.Spin (quadMinus)

variable {K : Type} [Field K]

theorem three_ne_zero_of_card_eq [Finite K] {r f : ℕ} [Fact r.Prime] (hq : Nat.card K = r ^ f)
    (hr : r ≠ 3) : (3 : K) ≠ 0 := by
  haveI := Fintype.ofFinite K
  have hq' : Fintype.card K = r ^ f := by rw [← Nat.card_eq_fintype_card]; exact hq
  haveI : CharP K r := charP_of_card_eq_prime_pow hq'
  intro h3
  have hdvd : r ∣ 3 := (CharP.cast_eq_zero_iff K r 3).mp h3
  exact hr ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp hdvd)

private theorem card_mod_three_of_isSplit [Finite K] (h3 : (3 : K) ≠ 0) (h : IsSplit K) :
    Nat.card K % 3 = 1 := by
  obtain ⟨ω, hω⟩ := h
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    apply h3
    linear_combination hω
  have hω3 : ω ^ 3 = 1 := by
    have h : ω ^ 3 - 1 = 0 := by
      rw [show ω ^ 3 - 1 = (ω - 1) * (ω ^ 2 + ω + 1) by ring, hω, mul_zero]
    exact sub_eq_zero.mp h
  let u : Kˣ := Units.mk0 ω hω0
  have huval : (u : K) = ω := rfl
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, huval]
    exact hω3
  have hu1 : u ≠ 1 := by
    intro h
    apply hω1
    have := congrArg (fun u : Kˣ => (u : K)) h
    rw [Units.val_one, huval] at this
    exact this
  have horder : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdvd : 3 ∣ Nat.card Kˣ := horder ▸ orderOf_dvd_natCard u
  rw [Nat.card_units] at hdvd
  have hle : 1 ≤ Nat.card K := le_of_lt Finite.one_lt_card
  have hmodEq : 1 ≡ Nat.card K [MOD 3] := (Nat.modEq_iff_dvd' hle).mpr hdvd
  rw [Nat.ModEq, Nat.mod_eq_of_lt (by norm_num : 1 < 3)] at hmodEq
  exact hmodEq.symm

private theorem isSplit_of_card_mod_three [Finite K] (hmod : Nat.card K % 3 = 1) :
    IsSplit K := by
  have hle : 1 ≤ Nat.card K := le_of_lt Finite.one_lt_card
  have hdvdK : 3 ∣ Nat.card K - 1 := by
    have hmodEq : 1 ≡ Nat.card K [MOD 3] := by
      rw [Nat.ModEq, Nat.mod_eq_of_lt (by norm_num : 1 < 3)]
      exact hmod.symm
    exact (Nat.modEq_iff_dvd' hle).mp hmodEq
  have hdvd : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hdvdK
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hu3' : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hu3 : (u : K) ^ 3 = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) hu3'
  have hu1 : (u : K) ≠ 1 := by
    intro h
    have h1 : u = 1 := Units.ext h
    rw [h1, orderOf_one] at hu
    norm_num at hu
  refine ⟨(u : K), ?_⟩
  have hprod : ((u : K) - 1) * ((u : K) ^ 2 + (u : K) + 1) = 0 := by
    have h : (u : K) ^ 3 - 1 = ((u : K) - 1) * ((u : K) ^ 2 + (u : K) + 1) := by
      ring
    rw [← h, hu3, sub_self]
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd (sub_eq_zero.mp h) hu1
  · exact h

theorem isSplit_iff_card_mod_three [Finite K] (h3 : (3 : K) ≠ 0) :
    IsSplit K ↔ Nat.card K % 3 = 1 :=
  ⟨card_mod_three_of_isSplit h3, isSplit_of_card_mod_three⟩

theorem nondegenerate_polarBilin_binForm {b c : K} (h : b ^ 2 - 4 * c ≠ 0) :
    (polarBilin (binForm b c)).Nondegenerate := by
  have hpolar : ∀ v w : K × K, polar (binForm b c) v w =
      2 * v.1 * w.1 + b * (v.1 * w.2 + w.1 * v.2) + 2 * c * v.2 * w.2 := by
    intro v w
    rw [polar, binForm_apply, binForm_apply, binForm_apply]
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => ?_
  have h1 : 2 * v.1 + b * v.2 = 0 := by
    have := hv (1, 0)
    rw [hpolar] at this
    simpa using this
  have h2 : b * v.1 + 2 * c * v.2 = 0 := by
    have := hv (0, 1)
    rw [hpolar] at this
    simpa using this
  refine Prod.ext ?_ ?_
  · have e : (b ^ 2 - 4 * c) * v.1 = 0 := by linear_combination -(2 * c) * h1 + b * h2
    exact (mul_eq_zero.1 e).resolve_left h
  · have e : (b ^ 2 - 4 * c) * v.2 = 0 := by linear_combination b * h1 - 2 * h2
    exact (mul_eq_zero.1 e).resolve_left h

theorem rotForm_apply (p : K × K) : rotForm K p = p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 := by
  rw [rotForm, binForm_apply]
  ring

theorem wForm_of_isSplit {b c : K} (h : IsSplit K) : wForm b c = binForm b c := by
  rw [wForm, if_pos h]

theorem wForm_of_not_isSplit {b c : K} (h : ¬ IsSplit K) : wForm b c = binForm (-1) 0 := by
  rw [wForm, if_neg h]

theorem nondegenerate_polarBilin_rotForm (h3 : (3 : K) ≠ 0) :
    (polarBilin (rotForm K)).Nondegenerate := by
  refine nondegenerate_polarBilin_binForm (b := -1) (c := 1) ?_
  rw [show ((-1 : K) ^ 2 - 4 * 1) = -(3 : K) by ring]
  exact neg_ne_zero.mpr h3

theorem exists_rotForm_eq [Finite K] (h3 : (3 : K) ≠ 0) (d : K) :
    ∃ p : K × K, rotForm K p = d := by
  by_cases hsplit : IsSplit K
  · obtain ⟨ω, hω⟩ := hsplit
    have hne : (2 * ω + 1) ≠ 0 := by
      intro h0
      have hsq : (2 * ω + 1) ^ 2 = -(3 : K) := by linear_combination 4 * hω
      rw [h0, zero_pow (by norm_num : 2 ≠ 0)] at hsq
      exact h3 (neg_eq_zero.mp hsq.symm)
    set y : K := (d - 1) / (2 * ω + 1) with hy
    set x : K := d - ω * y with hx
    refine ⟨(x, y), ?_⟩
    have hxy : x + ω * y = d := by rw [hx]; ring
    have hxy' : x + (-1 - ω) * y = 1 := by
      rw [hx]
      have hmul : (2 * ω + 1) * y = d - 1 := by
        rw [hy]; exact mul_div_cancel₀ _ hne
      linear_combination -hmul
    rw [rotForm_apply,
      show x ^ 2 - x * y + y ^ 2 = (x + ω * y) * (x + (-1 - ω) * y) by
        linear_combination y ^ 2 * hω,
      hxy, hxy', mul_one]
  · have hirr : ∀ s : K, s ^ 2 + (-1) * s + 1 ≠ 0 := by
      intro s hs
      apply hsplit
      refine ⟨-s, ?_⟩
      linear_combination hs
    obtain ⟨p, hp⟩ := exists_binForm_eq (b := -1) (c := 1) hirr d
    exact ⟨p, hp⟩

theorem isPlusType_rotForm_iff (h3 : (3 : K) ≠ 0) : IsPlusType (rotForm K) ↔ IsSplit K := by
  have hdim : finrank K (K × K) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  constructor
  · rintro ⟨W, hW, hWs⟩
    have hW1 : finrank K W = 1 := by rw [hdim] at hW; omega
    have hbot : W ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hW1; exact zero_ne_one hW1
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hxQ : x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2 = 0 := by
      have := hWs x hxW
      rwa [rotForm_apply] at this
    have hx2 : x.2 ≠ 0 := by
      intro h2
      apply hx0
      have hx1 : x.1 = 0 := by
        have h : x.1 ^ 2 = 0 := by rw [h2] at hxQ; simpa using hxQ
        exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h
      exact Prod.ext hx1 h2
    set s : K := x.1 / x.2 with hs
    have hx1 : x.1 = s * x.2 := by rw [hs]; exact (div_mul_cancel₀ x.1 hx2).symm
    have hs0 : s ^ 2 - s + 1 = 0 := by
      have hmul : x.2 ^ 2 * (s ^ 2 - s + 1) = 0 := by
        have h : x.2 ^ 2 * (s ^ 2 - s + 1) = x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2 := by
          rw [hx1]; ring
        rw [h, hxQ]
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 hx2)
    exact ⟨-s, by linear_combination hs0⟩
  · rintro ⟨ω, hω⟩
    refine ⟨K ∙ (-ω, 1), ?_, ?_⟩
    · rw [finrank_span_singleton (v := (-ω, 1)) (by simp), hdim]
    · intro x hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      have hp : rotForm K (-ω, 1) = 0 := by rw [rotForm_apply]; linear_combination hω
      rw [QuadraticMap.map_smul, hp, smul_zero]

theorem nondegenerate_polarBilin_wForm [Finite K] {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : (polarBilin (wForm b c)).Nondegenerate := by
  by_cases h : IsSplit K
  · rw [wForm_of_isSplit h]
    exact nondegenerate_polarBilin_binForm
      (CFSG.LieType.Universal.Spin.discr_ne_zero_of_finite hbc)
  · rw [wForm_of_not_isSplit h]
    refine nondegenerate_polarBilin_binForm (b := -1) (c := 0) ?_
    norm_num

theorem exists_wForm_eq [Finite K] {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (d : K) :
    ∃ p : K × K, wForm b c p = d := by
  by_cases h : IsSplit K
  · rw [wForm_of_isSplit h]
    exact exists_binForm_eq hbc d
  · rw [wForm_of_not_isSplit h]
    refine ⟨(1, 1 - d), ?_⟩
    rw [binForm_apply]
    ring

theorem isPlusType_wForm_iff {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsPlusType (wForm b c) ↔ ¬ IsSplit K := by
  have hdim : finrank K (K × K) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  constructor
  · intro hQ hsplit
    rw [wForm_of_isSplit hsplit] at hQ
    obtain ⟨W, hW, hWs⟩ := hQ
    have hW1 : finrank K W = 1 := by rw [hdim] at hW; omega
    have hbot : W ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hW1; exact zero_ne_one hW1
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    exact hx0 (binForm_eq_zero hbc (hWs x hxW))
  · intro hns
    rw [wForm_of_not_isSplit hns]
    refine ⟨K ∙ (0, 1), ?_, ?_⟩
    · rw [finrank_span_singleton (v := (0, 1)) (by simp), hdim]
    · intro x hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      have hp : binForm (-1) 0 ((0, 1) : K × K) = 0 := by rw [binForm_apply]; ring
      rw [QuadraticMap.map_smul, hp, smul_zero]

theorem nonempty_isometry_pi_fin_three {V : Type} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) :
    Nonempty ((QuadraticMap.pi fun _ : Fin 3 => Q).IsometryEquiv ((Q.prod Q).prod Q)) := by
  let e : (Fin 3 → V) ≃ₗ[K] (V × V) × V :=
    { toFun := fun x => ((x 0, x 1), x 2)
      map_add' := fun x y => by ext <;> simp
      map_smul' := fun a x => by ext <;> simp
      invFun := fun p => ![p.1.1, p.1.2, p.2]
      left_inv := fun x => by funext i; fin_cases i <;> rfl
      right_inv := fun p => by ext <;> rfl }
  refine ⟨{ toLinearEquiv := e, map_app' := ?_ }⟩
  intro x
  change ((Q.prod Q).prod Q) (((x 0, x 1), x 2) : (V × V) × V) =
    (QuadraticMap.pi fun _ : Fin 3 => Q) x
  simp only [QuadraticMap.prod_apply, QuadraticMap.pi_apply, Fin.sum_univ_three]

theorem isPlusType_pi_fin_three_iff [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {d : ℕ}
    (hd : 1 ≤ d) (hdim : finrank K V = 2 * d) :
    IsPlusType (QuadraticMap.pi fun _ : Fin 3 => Q) ↔ IsPlusType Q := by
  obtain ⟨e⟩ := nonempty_isometry_pi_fin_three (K := K) Q
  rw [isPlusType_congr e]
  have hdd : finrank K (V × V) = 2 * (2 * d) := by
    rw [Module.finrank_prod, hdim]; ring
  rw [CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_prod_iff
      (nondegenerate_polarBilin_prod hQ hQ) hQ (by omega) hd hdd hdim,
    CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_prod_iff hQ hQ hd hd hdim hdim]
  tauto

theorem nondegenerate_polarBilin_modelForm [Finite K] (h3 : (3 : K) ≠ 0) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (polarBilin (modelForm b c)).Nondegenerate := by
  rw [modelForm]
  exact nondegenerate_polarBilin_prod
    (nondegenerate_polarBilin_pi fun _ => nondegenerate_polarBilin_rotForm h3)
    (nondegenerate_polarBilin_wForm hbc)

theorem finrank_modelSpace : finrank K (ModelSpace K) = 2 * 4 := by
  change finrank K ((Fin 3 → K × K) × (K × K)) = 2 * 4
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_prod, Module.finrank_self,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem not_isPlusType_modelForm [Finite K] (h3 : (3 : K) ≠ 0) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : ¬ IsPlusType (modelForm b c) := by
  have hdim1 : finrank K (Fin 3 → K × K) = 2 * 3 := by
    rw [Module.finrank_pi_fintype, Module.finrank_prod, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hdim2 : finrank K (K × K) = 2 * 1 := by
    rw [Module.finrank_prod, Module.finrank_self]
  intro h
  rw [modelForm] at h
  have hiff := (CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_prod_iff
    (Q₁ := QuadraticMap.pi fun _ : Fin 3 => rotForm K) (Q₂ := wForm b c)
    (nondegenerate_polarBilin_pi fun _ => nondegenerate_polarBilin_rotForm h3)
    (nondegenerate_polarBilin_wForm hbc) (by norm_num) (by norm_num) hdim1 hdim2).mp h
  rw [isPlusType_pi_fin_three_iff (nondegenerate_polarBilin_rotForm h3) (by norm_num) hdim2,
    isPlusType_rotForm_iff h3, isPlusType_wForm_iff hbc] at hiff
  by_cases hp : IsSplit K
  · exact (hiff.mp hp) hp
  · exact hp (hiff.mpr hp)

theorem nonempty_isometry_modelForm [Finite K] (h3 : (3 : K) ≠ 0) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nonempty ((quadMinus 4 K b c).IsometryEquiv (modelForm b c)) := by
  refine nonempty_isometry_of_isPlusType_iff
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 4 K hbc)
    (nondegenerate_polarBilin_modelForm h3 hbc)
    (finrank_quadMinus_space (m := 4) (by norm_num)) finrank_modelSpace ?_
  exact iff_of_false (not_isPlusType_quadMinus (n := 4) (by norm_num) hbc)
    (not_isPlusType_modelForm h3 hbc)

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
