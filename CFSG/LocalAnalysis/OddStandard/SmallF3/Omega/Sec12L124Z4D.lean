module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Sigma
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Prod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private lemma sec124_isEvenVec_add {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    IsEvenVec (v + w) := by
  unfold IsEvenVec at *
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hv, hw, add_zero]

private lemma sec124_isEvenVec_zero : IsEvenVec (0 : Fin 5 → ZMod 2) := by
  unfold IsEvenVec
  simp

private lemma sec124_conj_sq (u x : G) :
    (u * x * u⁻¹) * (u * x * u⁻¹) = u * (x * x) * u⁻¹ := by
  group

private lemma sec124_mul_inv_sq_of_comm {x a : G} (h : x * a = a * x) :
    (x * a⁻¹) * (x * a⁻¹) = (x * x) * (a * a)⁻¹ := by
  have h' : a⁻¹ * x = x * a⁻¹ := by
    calc a⁻¹ * x = a⁻¹ * (x * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * x) * a⁻¹ := by rw [h]
      _ = x * a⁻¹ := by group
  calc (x * a⁻¹) * (x * a⁻¹) = x * (a⁻¹ * x) * a⁻¹ := by group
    _ = x * (x * a⁻¹) * a⁻¹ := by rw [h']
    _ = (x * x) * (a⁻¹ * a⁻¹) := by group
    _ = (x * x) * (a * a)⁻¹ := by rw [mul_inv_rev]

private lemma sec124_mem_zpowers_pair {c : G} (hc : c * c = 1) :
    ∀ x : G, x ∈ zpowers c ↔ x = 1 ∨ x = c := by
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, hc, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hc, one_zpow, one_mul, zpow_one]
  · rintro (h | h)
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers c

private lemma sec124_sq_mem_zpowers {w c x : G} (hw : w * w = c) (hx : x ∈ zpowers w) :
    x * x ∈ zpowers c := by
  rw [Subgroup.mem_zpowers_iff] at hx ⊢
  obtain ⟨k, rfl⟩ := hx
  refine ⟨k, ?_⟩
  rw [← zpow_add, show k + k = 2 * k by ring, zpow_mul, zpow_two, hw]

private lemma sec124_mem_zpowers_of_sq_eq_one {w c x : G} (hw : w * w = c)
    (hc : c * c = 1) (hc1 : c ≠ 1) (hx : x ∈ zpowers w) (hx2 : x * x = 1) :
    x ∈ zpowers c := by
  rw [Subgroup.mem_zpowers_iff] at hx ⊢
  obtain ⟨k, rfl⟩ := hx
  have hsq : (w ^ k) * (w ^ k) = c ^ k := by
    rw [← zpow_add, show k + k = 2 * k by ring, zpow_mul, zpow_two, hw]
  have hck : c ^ k = 1 := by rw [← hsq, hx2]
  have horder : orderOf c = 2 := by
    rw [orderOf_eq_prime_iff]
    exact ⟨by rw [pow_two]; exact hc, hc1⟩
  have hdvd : (2 : ℤ) ∣ k := by
    have hmod : k ≡ 0 [ZMOD orderOf c] :=
      (zpow_eq_one_iff_modEq (x := c) (n := k)).mp hck
    rw [horder] at hmod
    exact Int.modEq_zero_iff_dvd.mp hmod
  obtain ⟨m, hm⟩ := hdvd
  exact ⟨m, by rw [hm, zpow_mul, zpow_two, hw]⟩

private lemma sec124_orderOf_eq_four {w c : G} (hw : w * w = c) (hc : c * c = 1)
    (hc1 : c ≠ 1) : orderOf w = 4 := by
  have hnot : ¬ w ^ (2 : ℕ) ^ 1 = 1 := by
    rw [show (2 : ℕ) ^ 1 = 2 by norm_num, pow_two, hw]
    exact hc1
  have hfin : w ^ (2 : ℕ) ^ (1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
    calc w ^ 4 = w ^ (2 + 2) := by rw [show (4 : ℕ) = 2 + 2 by norm_num]
      _ = w ^ 2 * w ^ 2 := by rw [pow_add]
      _ = (w * w) * (w * w) := by rw [pow_two]
      _ = c * c := by rw [hw]
      _ = 1 := hc
  have h := orderOf_eq_prime_pow (x := w) (p := 2) (n := 1) hnot hfin
  rwa [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num] at h

private lemma sec124_inf_zpowers_bot {w₁ w₂ c₁ c₂ : G}
    (hw₁ : w₁ * w₁ = c₁) (hw₂ : w₂ * w₂ = c₂)
    (hc₁ : c₁ * c₁ = 1) (hc₂ : c₂ * c₂ = 1)
    (hc₁1 : c₁ ≠ 1) (hc₂1 : c₂ ≠ 1) (hc₁₂ : c₁ ≠ c₂) :
    zpowers w₁ ⊓ zpowers w₂ = ⊥ := by
  have hcc : zpowers c₁ ⊓ zpowers c₂ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx₁, hx₂⟩ := hx
    rw [sec124_mem_zpowers_pair hc₁] at hx₁
    rw [sec124_mem_zpowers_pair hc₂] at hx₂
    rcases hx₁ with rfl | rfl
    · rfl
    · rcases hx₂ with h | h
      · exact absurd h hc₁1
      · exact absurd h hc₁₂
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hx₁, hx₂⟩ := hx
  have hx2 : x * x = 1 := by
    have hmem : x * x ∈ zpowers c₁ ⊓ zpowers c₂ :=
      ⟨sec124_sq_mem_zpowers hw₁ hx₁, sec124_sq_mem_zpowers hw₂ hx₂⟩
    rw [hcc] at hmem
    simpa using hmem
  have h₁ : x ∈ zpowers c₁ := sec124_mem_zpowers_of_sq_eq_one hw₁ hc₁ hc₁1 hx₁ hx2
  have h₂ : x ∈ zpowers c₂ := sec124_mem_zpowers_of_sq_eq_one hw₂ hc₂ hc₂1 hx₂ hx2
  have hmem : x ∈ zpowers c₁ ⊓ zpowers c₂ := ⟨h₁, h₂⟩
  rw [hcc] at hmem
  simpa using hmem

private lemma sec124_conj_mul_inv_self_inv {u x : G} (hu2 : u * u = 1) :
    u * (x * (u * x * u⁻¹)⁻¹) * u⁻¹ = (x * (u * x * u⁻¹)⁻¹)⁻¹ := by
  have huinv : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, hu2, inv_one]
  have hux : u * (u * x * u⁻¹) * u⁻¹ = x := by
    rw [show u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u⁻¹ * u⁻¹) by group, hu2, huinv,
      one_mul, mul_one]
  rw [show u * (x * (u * x * u⁻¹)⁻¹) * u⁻¹
      = (u * x * u⁻¹) * (u * (u * x * u⁻¹) * u⁻¹)⁻¹ by group, hux]
  rw [mul_inv_rev, inv_inv]

theorem sec124_Dsub {V B : Subgroup G} {t u : G} {φ : (Fin 5 → ZMod 2) → G}
    (hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hB2 : ∀ b ∈ B, b * b = 1)
    (hroot : ∀ b ∈ B, ∃ x ∈ V, x * x = b)
    (hφmul : ∀ v w, IsEvenVec v → IsEvenVec w → φ (v + w) = φ v * φ w)
    (hφB : ∀ v, IsEvenVec v → φ v ∈ B)
    (hφinj : ∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → v = w)
    (huV : ∀ v ∈ V, u * v * u⁻¹ ∈ V) (hu2 : u * u = 1)
    (huφ : ∀ v, IsEvenVec v → u * φ v * u⁻¹ = φ (permVec sec124Sigma v))
    (htinv : ∀ v ∈ V, t * v * t⁻¹ = v⁻¹) :
    ∃ D : Subgroup G, D ≤ V ∧ Nat.card D = 16 ∧
      (∀ d ∈ D, (t * u) * d * (t * u)⁻¹ = d) ∧ ∃ w ∈ D, w * w ≠ 1 := by
  have hφ0 : φ 0 = 1 := by
    have h : φ 0 = φ 0 * φ 0 := by
      simpa using hφmul 0 0 sec124_isEvenVec_zero sec124_isEvenVec_zero
    have h1 : φ 0 * 1 = φ 0 * φ 0 := by rw [mul_one]; exact h
    exact (mul_left_cancel h1).symm
  obtain ⟨n₁, n₂, hn₁, hn₂, hm₁0, hm₂0, hm₁₂, _⟩ := sec124_vectors
  have hm₁e : IsEvenVec (n₁ + permVec sec124Sigma n₁) :=
    sec124_isEvenVec_add hn₁ (isEvenVec_permVec sec124Sigma hn₁)
  have hm₂e : IsEvenVec (n₂ + permVec sec124Sigma n₂) :=
    sec124_isEvenVec_add hn₂ (isEvenVec_permVec sec124Sigma hn₂)
  obtain ⟨x₁, hx₁V, hx₁sq⟩ := hroot (φ n₁) (hφB n₁ hn₁)
  obtain ⟨x₂, hx₂V, hx₂sq⟩ := hroot (φ n₂) (hφB n₂ hn₂)
  set a₁ : G := u * x₁ * u⁻¹ with ha₁
  set a₂ : G := u * x₂ * u⁻¹ with ha₂
  set w₁ : G := x₁ * a₁⁻¹ with hw₁
  set w₂ : G := x₂ * a₂⁻¹ with hw₂
  have ha₁V : a₁ ∈ V := huV x₁ hx₁V
  have ha₂V : a₂ ∈ V := huV x₂ hx₂V
  have hw₁V : w₁ ∈ V := V.mul_mem hx₁V (V.inv_mem ha₁V)
  have hw₂V : w₂ ∈ V := V.mul_mem hx₂V (V.inv_mem ha₂V)
  have ha₁sq : a₁ * a₁ = u * (x₁ * x₁) * u⁻¹ := by rw [ha₁]; exact sec124_conj_sq u x₁
  have ha₂sq : a₂ * a₂ = u * (x₂ * x₂) * u⁻¹ := by rw [ha₂]; exact sec124_conj_sq u x₂
  have ha₁φ : a₁ * a₁ = φ (permVec sec124Sigma n₁) := by
    rw [ha₁sq, hx₁sq, huφ n₁ hn₁]
  have ha₂φ : a₂ * a₂ = φ (permVec sec124Sigma n₂) := by
    rw [ha₂sq, hx₂sq, huφ n₂ hn₂]
  have hperm₁ : (φ (permVec sec124Sigma n₁))⁻¹ = φ (permVec sec124Sigma n₁) :=
    inv_eq_of_mul_eq_one_right (hB2 _ (hφB _ (isEvenVec_permVec sec124Sigma hn₁)))
  have hperm₂ : (φ (permVec sec124Sigma n₂))⁻¹ = φ (permVec sec124Sigma n₂) :=
    inv_eq_of_mul_eq_one_right (hB2 _ (hφB _ (isEvenVec_permVec sec124Sigma hn₂)))
  have hw₁sq : w₁ * w₁ = φ (n₁ + permVec sec124Sigma n₁) := by
    rw [hw₁, sec124_mul_inv_sq_of_comm (hVab x₁ hx₁V a₁ ha₁V), hx₁sq, ha₁φ, hperm₁,
      hφmul n₁ (permVec sec124Sigma n₁) hn₁ (isEvenVec_permVec sec124Sigma hn₁)]
  have hw₂sq : w₂ * w₂ = φ (n₂ + permVec sec124Sigma n₂) := by
    rw [hw₂, sec124_mul_inv_sq_of_comm (hVab x₂ hx₂V a₂ ha₂V), hx₂sq, ha₂φ, hperm₂,
      hφmul n₂ (permVec sec124Sigma n₂) hn₂ (isEvenVec_permVec sec124Sigma hn₂)]
  have hc₁ : φ (n₁ + permVec sec124Sigma n₁) * φ (n₁ + permVec sec124Sigma n₁) = 1 :=
    hB2 _ (hφB _ hm₁e)
  have hc₂ : φ (n₂ + permVec sec124Sigma n₂) * φ (n₂ + permVec sec124Sigma n₂) = 1 :=
    hB2 _ (hφB _ hm₂e)
  have hc₁1 : φ (n₁ + permVec sec124Sigma n₁) ≠ 1 := by
    intro h
    exact hm₁0 (hφinj _ _ hm₁e sec124_isEvenVec_zero (by rw [h, hφ0]))
  have hc₂1 : φ (n₂ + permVec sec124Sigma n₂) ≠ 1 := by
    intro h
    exact hm₂0 (hφinj _ _ hm₂e sec124_isEvenVec_zero (by rw [h, hφ0]))
  have hc₁₂ : φ (n₁ + permVec sec124Sigma n₁) ≠ φ (n₂ + permVec sec124Sigma n₂) := by
    intro h
    exact hm₁₂ (hφinj _ _ hm₁e hm₂e h)
  have hinf : zpowers w₁ ⊓ zpowers w₂ = ⊥ :=
    sec124_inf_zpowers_bot hw₁sq hw₂sq hc₁ hc₂ hc₁1 hc₂1 hc₁₂
  have hord₁ : orderOf w₁ = 4 := sec124_orderOf_eq_four hw₁sq hc₁ hc₁1
  have hord₂ : orderOf w₂ = 4 := sec124_orderOf_eq_four hw₂sq hc₂ hc₂1
  have hcard₁ : Nat.card (zpowers w₁) = 4 := by rw [Nat.card_zpowers, hord₁]
  have hcard₂ : Nat.card (zpowers w₂) = 4 := by rw [Nat.card_zpowers, hord₂]
  have hcommw : w₁ * w₂ = w₂ * w₁ := hVab w₁ hw₁V w₂ hw₂V
  have hcommc : Commute w₁ w₂ := hcommw
  have hcommsub : ∀ a ∈ zpowers w₁, ∀ b ∈ zpowers w₂, a * b = b * a := by
    intro a ha b hb
    rw [Subgroup.mem_zpowers_iff] at ha hb
    obtain ⟨m, rfl⟩ := ha
    obtain ⟨n, rfl⟩ := hb
    exact (hcommc.zpow_zpow m n).eq
  have hcardD : Nat.card ↥(zpowers w₁ ⊔ zpowers w₂) = 16 := by
    rw [sec124_card_sup hcommsub hinf, hcard₁, hcard₂]
  have huw₁ : u * w₁ * u⁻¹ = w₁⁻¹ := by
    rw [hw₁]; exact sec124_conj_mul_inv_self_inv hu2
  have huw₂ : u * w₂ * u⁻¹ = w₂⁻¹ := by
    rw [hw₂]; exact sec124_conj_mul_inv_self_inv hu2
  have htw₁ : t * w₁ * t⁻¹ = w₁⁻¹ := htinv w₁ hw₁V
  have htw₂ : t * w₂ * t⁻¹ = w₂⁻¹ := htinv w₂ hw₂V
  have hs₁ : (t * u) * w₁ * (t * u)⁻¹ = w₁ := by
    rw [show (t * u) * w₁ * (t * u)⁻¹ = t * (u * w₁ * u⁻¹) * t⁻¹ by group, huw₁,
      show t * w₁⁻¹ * t⁻¹ = (t * w₁ * t⁻¹)⁻¹ by group, htw₁, inv_inv]
  have hs₂ : (t * u) * w₂ * (t * u)⁻¹ = w₂ := by
    rw [show (t * u) * w₂ * (t * u)⁻¹ = t * (u * w₂ * u⁻¹) * t⁻¹ by group, huw₂,
      show t * w₂⁻¹ * t⁻¹ = (t * w₂ * t⁻¹)⁻¹ by group, htw₂, inv_inv]
  have hs₁' : (t * u) * w₁ = w₁ * (t * u) := by
    have h := congrArg (fun z => z * (t * u)) hs₁
    simpa [mul_assoc] using h
  have hs₂' : (t * u) * w₂ = w₂ * (t * u) := by
    have h := congrArg (fun z => z * (t * u)) hs₂
    simpa [mul_assoc] using h
  have hcent₁ : w₁ ∈ Subgroup.centralizer ({t * u} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hs₁'
  have hcent₂ : w₂ ∈ Subgroup.centralizer ({t * u} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hs₂'
  have hDV : zpowers w₁ ⊔ zpowers w₂ ≤ V :=
    sup_le (Subgroup.zpowers_le.mpr hw₁V) (Subgroup.zpowers_le.mpr hw₂V)
  have hDcent : zpowers w₁ ⊔ zpowers w₂ ≤ Subgroup.centralizer ({t * u} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hcent₁) (Subgroup.zpowers_le.mpr hcent₂)
  refine ⟨zpowers w₁ ⊔ zpowers w₂, hDV, hcardD, ?_, ?_⟩
  · intro d hd
    have hd' := hDcent hd
    rw [Subgroup.mem_centralizer_iff] at hd'
    have hcommd : (t * u) * d = d * (t * u) := hd' (t * u) (Set.mem_singleton _)
    rw [hcommd]; group
  · exact ⟨w₁, Subgroup.mem_sup_left (Subgroup.mem_zpowers w₁), by rw [hw₁sq]; exact hc₁1⟩

end CFSG.OddStandard.SmallF3.Omega
