module

public import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeCover
public import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeLevi
public import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeSeries
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.CentralExt.PerfectLift
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace

public section

namespace CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

universe u

variable {F : Type} [Field F] [Finite F] [CharP F 3]

local notation "σ₀" => unitaryInvolution F 3 1

theorem gramSU_antidiag_eq (h : UnitaryFieldData 3 1 F)
    (hbar : h.bar = (unitaryInvolution F 3 1).toRingHom) (k : ℕ) :
    gramSU h (antidiag k) = SU σ₀ k := by
  ext g
  rw [mem_gramSU, mem_SU, hbar]
  exact And.comm

theorem pow_factorization_card_SU (hF : Nat.card F = (3 ^ 1) ^ 2) {k : ℕ} (hk : 1 ≤ k) :
    3 ^ (Nat.card (SU σ₀ k)).factorization 3 = 3 ^ (k * (k - 1) / 2) := by
  have h : UnitaryFieldData 3 1 F := ⟨Nat.prime_three, le_rfl, by rw [hF]; norm_num⟩
  have hbar : h.bar = (unitaryInvolution F 3 1).toRingHom :=
    RingHom.ext fun c => (h.bar_apply c).trans (unitaryInvolution_apply F 3 1 c).symm
  have hG : ((antidiag k : Matrix (Fin k) (Fin k) F).map h.bar)ᵀ = antidiag k := by
    ext i j
    simp only [transpose_apply, map_apply, antidiag, of_apply]
    by_cases hij : j = Fin.rev i
    · subst hij
      simp
    · rw [ite_eq_right (fun h' => hij (by rw [h', Fin.rev_rev])), ite_eq_right hij, map_zero]
  have key := (CFSG.LinearGroups.unitary_full_group_order h (gramForm_isSymm h hG)
    (gramForm_separatingLeft h (det_antidiag_ne_zero k)) (Module.finrank_fin_fun F) hk).2.2.2.2.2.2
  rw [← card_gramSU, gramSU_antidiag_eq h hbar] at key
  rw [key, pow_one]

theorem card_sylow_SU (hF : Nat.card F = (3 ^ 1) ^ 2) {k : ℕ} (hk : 1 ≤ k)
    (S : Sylow 3 (SU σ₀ k)) : Nat.card S = 3 ^ (k * (k - 1) / 2) := by
  rw [Sylow.card_eq_multiplicity, pow_factorization_card_SU hF hk]

theorem card_radical_three (hF : Nat.card F = (3 ^ 1) ^ 2) (hσ : ∀ c, σ₀ (σ₀ c) = c) {m : ℕ} :
    Nat.card (radical σ₀ hσ (m := m)) = 3 ^ (2 * m + 1) := by
  rw [card_radical hσ, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin,
    hF, CFSG.LieType.Steinberg.card_traceZero hF, pow_succ 3 (2 * m), pow_mul]
  norm_num

theorem card_center0_three (hF : Nat.card F = (3 ^ 1) ^ 2) (hσ : ∀ c, σ₀ (σ₀ c) = c) {m : ℕ} :
    Nat.card (center0 σ₀ hσ (m := m)) = 3 := by
  rw [card_center0 hσ, CFSG.LieType.Steinberg.card_traceZero hF, pow_one]

theorem exponent_add_two (m : ℕ) : (m + 2) * (m + 2 - 1) / 2 = 2 * m + 1 + m * (m - 1) / 2 := by
  rcases m with _ | j
  · rfl
  · have e1 : j + 1 + 2 - 1 = j + 2 := by omega
    have e2 : j + 1 - 1 = j := by omega
    rw [e1, e2, show (j + 1 + 2) * (j + 2) = (j + 1) * j + 2 * (2 * (j + 1) + 1) by ring,
      Nat.add_mul_div_left _ _ two_pos]
    ring

theorem exists_sylow_le (hF : Nat.card F = (3 ^ 1) ^ 2) (hσ : ∀ c, σ₀ (σ₀ c) = c) {m : ℕ}
    (hm : 1 ≤ m) (S' : Sylow 3 (SU σ₀ m)) :
    ∃ P : Sylow 3 (SU σ₀ (m + 2)), (P : Subgroup (SU σ₀ (m + 2))) ≤
      radical σ₀ hσ ⊔ (S' : Subgroup (SU σ₀ m)).map iotaHom := by
  have hQp : IsPGroup 3 (radical σ₀ hσ (m := m)) := IsPGroup.of_card (card_radical_three hF hσ)
  have hSp : IsPGroup 3 ((S' : Subgroup (SU σ₀ m)).map iotaHom) := S'.isPGroup'.map _
  have hN : (S' : Subgroup (SU σ₀ m)).map iotaHom ≤
      Subgroup.normalizer ((radical σ₀ hσ : Subgroup (SU σ₀ (m + 2))) : Set (SU σ₀ (m + 2))) :=
    (Subgroup.map_le_range _ _).trans (range_iotaHom_le_levi.trans levi_le_normalizer_radical)
  obtain ⟨P, hP⟩ := (IsPGroup.to_sup_of_normal_left' hQp hSp hN).exists_le_sylow
  refine ⟨P, le_of_eq (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
  let H := radical σ₀ hσ ⊔ (S' : Subgroup (SU σ₀ m)).map iotaHom
  let Φ : radical σ₀ hσ (m := m) × (S' : Subgroup (SU σ₀ m)) → H := fun q =>
    ⟨q.1 * iotaHom (q.2 : SU σ₀ m),
      mul_mem (Subgroup.mem_sup_left q.1.2) (Subgroup.mem_sup_right ⟨q.2, q.2.2, rfl⟩)⟩
  have hΦ : Function.Injective Φ := by
    intro q q' hqq
    have h1 : (q.1 : SU σ₀ (m + 2)) * iotaHom (q.2 : SU σ₀ m) =
        q'.1 * iotaHom (q'.2 : SU σ₀ m) := congrArg Subtype.val hqq
    have h2 : (q'.1 : SU σ₀ (m + 2))⁻¹ * q.1 =
        iotaHom ((q'.2 : SU σ₀ m) * (q.2 : SU σ₀ m)⁻¹) := by
      calc (q'.1 : SU σ₀ (m + 2))⁻¹ * q.1 =
          (q'.1 : SU σ₀ (m + 2))⁻¹ * (q.1 * iotaHom (q.2 : SU σ₀ m)) *
            (iotaHom (q.2 : SU σ₀ m))⁻¹ := by group
        _ = (q'.1 : SU σ₀ (m + 2))⁻¹ * (q'.1 * iotaHom (q'.2 : SU σ₀ m)) *
            (iotaHom (q.2 : SU σ₀ m))⁻¹ := by rw [h1]
        _ = iotaHom ((q'.2 : SU σ₀ m) * (q.2 : SU σ₀ m)⁻¹) := by
          rw [map_mul, map_inv]
          group
    have h3 := eq_one_of_mem_radical_of_mem_range (mul_mem (inv_mem q'.1.2) q.1.2) ⟨_, h2.symm⟩
    have h4 : iotaHom ((q'.2 : SU σ₀ m) * (q.2 : SU σ₀ m)⁻¹) = 1 := by rw [← h2, h3]
    rw [← map_one iotaHom] at h4
    exact Prod.ext (Subtype.ext (inv_mul_eq_one.1 h3).symm)
      (Subtype.ext (mul_inv_eq_one.1 (iotaHom_injective h4)).symm)
  have hcard := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_prod, card_radical_three hF hσ, card_sylow_SU hF hm S'] at hcard
  rw [card_sylow_SU hF (by omega) P, exponent_add_two, pow_add]
  exact hcard

theorem exists_torus_data (hF : Nat.card F = (3 ^ 1) ^ 2) (k : ℕ) :
    ∃ a l μ : Fˣ, σ₀ (l : F) * l = 1 ∧ (a : F) * (l : F) ^ (2 * k + 1) * (σ₀ a)⁻¹ = 1 ∧
      σ₀ (a : F) * l = μ ∧ σ₀ (a : F) * a = -1 ∧ (μ : F) ≠ 1 ∧ (μ : F) ^ 2 ≠ 1 ∧
      ∀ t : Fˣ, ∃ n : ℕ, μ ^ n = t := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = 8 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
    norm_num
  have h8 : g ^ 8 = 1 := hord ▸ pow_orderOf_eq_one g
  have hσ3 : ∀ x : Fˣ, σ₀ (x : F) = ((x ^ 3 : Fˣ) : F) := fun x => by
    rw [unitaryInvolution_apply, pow_one, Units.val_pow_eq_pow_val]
  have hne : ∀ j, 0 < j → j < 8 → g ^ j ≠ 1 := fun j hj0 hj8 =>
    pow_ne_one_of_lt_orderOf hj0.ne' (hord ▸ hj8)
  have hpow8 : ∀ q r : ℕ, g ^ (8 * q + r) = g ^ r := fun q r => by
    rw [pow_add, pow_mul, h8, one_pow, one_mul]
  have hval1 : ∀ x : Fˣ, (x : F) = 1 → x = 1 := fun x h => Units.ext h
  have hμ2 : ((g ^ (4 * k + 5)) ^ 2 : Fˣ) = g ^ 2 := by
    rw [← pow_mul, show (4 * k + 5) * 2 = 8 * (k + 1) + 2 by ring, hpow8]
  have hμsq : ((g ^ (4 * k + 5) : Fˣ) : F) ^ 2 ≠ 1 := fun h =>
    hne 2 (by norm_num) (by norm_num)
      (by rw [← hμ2]; exact hval1 _ (by rw [Units.val_pow_eq_pow_val, h]))
  refine ⟨g, g ^ (4 * k + 2), g ^ (4 * k + 5), ?_, ?_, ?_, ?_, ?_, hμsq, ?_⟩
  · rw [hσ3, ← Units.val_mul, ← pow_succ, ← pow_mul,
      show (4 * k + 2) * (3 + 1) = 8 * (2 * k + 1) + 0 by ring, hpow8, pow_zero, Units.val_one]
  · rw [hσ3, ← Units.val_pow_eq_pow_val, ← Units.val_inv_eq_inv_val, ← Units.val_mul,
      ← Units.val_mul, ← pow_mul, show (4 * k + 2) * (2 * k + 1) = 8 * (k * k + k) + 2 by ring,
      hpow8, ← pow_succ', mul_inv_cancel, Units.val_one]
  · rw [hσ3, ← Units.val_mul, ← pow_add, show 3 + (4 * k + 2) = 4 * k + 5 by ring]
  · have hsq : ((g ^ 4 : Fˣ) : F) * ((g ^ 4 : Fˣ) : F) = 1 := by
      rw [← Units.val_mul, ← pow_add, h8, Units.val_one]
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exact absurd (hval1 _ h) (hne 4 (by norm_num) (by norm_num))
    · rw [hσ3, ← Units.val_mul, ← pow_succ, h]
  · intro h
    exact hμsq (by rw [h, one_pow])
  · intro t
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 (hg t))
    refine ⟨(4 * k + 5) * n, ?_⟩
    rw [pow_mul, ← pow_mul g, show (4 * k + 5) * (4 * k + 5) = 8 * (2 * k * k + 5 * k + 3) + 1 by
      ring, hpow8, pow_one]

theorem isPerfect_SU (hF : Nat.card F = (3 ^ 1) ^ 2) {k : ℕ} (hk : 3 ≤ k) :
    Group.IsPerfect (SU σ₀ k) := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF k
  have : Group.IsPerfect (SUid σ₀ k) := CFSG.ClassicalGroups.Unitary.isPerfect_SUid
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF) hk
    fun _ => CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hF (by norm_num)
  exact Group.IsPerfect.ofSurjective (f := (conjEquiv P hP).symm.toMonoidHom)
    (conjEquiv P hP).symm.surjective

omit [Finite F] [CharP F 3] in
theorem eq_one_of_SU_one {σ : F ≃+* F} (A : SU σ 1) : A = 1 := by
  refine mat_injective ?_
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  have h := A.2.1
  rw [det_unique] at h
  rw [map_one, one_apply_eq]
  exact h

omit [Finite F] [CharP F 3] in
theorem ker_eq_bot_SU_one {σ : F ≃+* F} {E : Type u} [Group E] [Group.IsPerfect E]
    (η : E →* SU σ 1) (hC : η.ker ≤ Subgroup.center E) : η.ker = ⊥ := by
  have htop : η.ker = ⊤ := eq_top_iff.2 fun x _ => eq_one_of_SU_one (η x)
  have hcomm : commutator E = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    have hx : x ∈ Subgroup.center E := hC (htop ▸ Subgroup.mem_top x)
    exact (Subgroup.mem_center_iff.1 hx y)
  rw [htop, ← hcomm, Group.IsPerfect.commutator_eq_top]

theorem exists_invariant_lift_radical (hF : Nat.card F = (3 ^ 1) ^ 2)
    (hσ : ∀ c, σ₀ (σ₀ c) = c) {m : ℕ} {E : Type*} [Group E] [Finite E]
    (η : E →* SU σ₀ (m + 2)) (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E)
    (h3 : IsPGroup 3 η.ker) {d : SU σ₀ (m + 2)} (hdL : d ∈ levi σ₀) (hd8 : d ^ 8 = 1) {μ : Fˣ}
    (hdθ : ∀ x ∈ radical σ₀ hσ, qθ σ₀ (d * x * d⁻¹) = (μ : F) • qθ σ₀ x)
    (hdZ : ∀ z ∈ center0 σ₀ hσ, d * z * d⁻¹ = z⁻¹) (hμ1 : (μ : F) ≠ 1)
    (hμ2 : (μ : F) ^ 2 ≠ 1) (hμ : ∀ t : Fˣ, ∃ n : ℕ, μ ^ n = t) :
    ∃ K : Subgroup E, (∀ k ∈ K, η k ∈ radical σ₀ hσ) ∧ (∀ k ∈ K, η k = 1 → k = 1) ∧
      (∀ u ∈ radical σ₀ hσ, ∃ k ∈ K, η k = u) ∧
      ∀ e : E, η e = d → ∀ k ∈ K, e * k * e⁻¹ ∈ K := by
  have hdQ : ∀ x ∈ radical σ₀ hσ, d * x * d⁻¹ ∈ radical σ₀ hσ := fun x hx =>
    conj_mem_radical hdL hx
  have hTL : Subgroup.zpowers d ≤ levi σ₀ := Subgroup.zpowers_le.2 hdL
  have hT : Nat.Coprime 3 (Nat.card (Subgroup.zpowers d)) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hd8) (by norm_num)
  have hF9 : Nat.card F = 3 ^ 2 := by rw [hF]; norm_num
  have hZ3 := card_center0_three hF hσ (m := m)
  let S : ℕ → Subgroup (SU σ₀ (m + 2)) := fun i =>
    if i = 0 then ⊥ else if i = 1 then center0 σ₀ hσ else radical σ₀ hσ
  have hS0 : S 0 = ⊥ := by simp [S]
  have hS1 : S 1 = center0 σ₀ hσ := by simp [S]
  have hS2 : S 2 = radical σ₀ hσ := by simp [S]
  have hdd : (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d) = ⟨d, Subgroup.mem_zpowers d⟩ :=
    rfl
  obtain ⟨K, hKQ, hKC, hKs, hKe⟩ := exists_invariant_lift_of_coprime_series (p := 3) η hη hC h3
    (U := radical σ₀ hσ) (IsPGroup.of_card (card_radical_three hF hσ)) hT
    (Subgroup.zpowers d).subtype (fun t x hx => conj_mem_radical (hTL t.2) hx) 2 S hS0 hS2
    (fun i hi => by
      interval_cases i
      · rw [hS0]
        exact bot_le
      · rw [hS1, hS2]
        exact center0_le_radical)
    (fun i hi t x hx => by
      interval_cases i
      · rw [hS0, Subgroup.mem_bot] at hx ⊢
        rw [hx, mul_one, mul_inv_cancel]
      · rw [hS1] at hx ⊢
        exact (Subgroup.mem_normalizer_iff.1 (levi_le_normalizer_center0 (hTL t.2)) x).1 hx
      · rw [hS2] at hx ⊢
        exact (Subgroup.mem_normalizer_iff.1 (levi_le_normalizer_radical (hTL t.2)) x).1 hx)
    (fun i hi x hx g hg => by
      interval_cases i
      · rw [hS1] at hx
        rw [hS0, Subgroup.mem_bot, mul_assoc, center0_comm hx hg]
        group
      · rw [hS2] at hx
        rw [hS1]
        refine ⟨mul_mem (mul_mem (mul_mem (inv_mem hx) (inv_mem hg)) hx) hg, ?_⟩
        rw [qθ_mul (mul_mem (mul_mem (inv_mem hx) (inv_mem hg)) hx) hg,
          qθ_mul (mul_mem (inv_mem hx) (inv_mem hg)) hx, qθ_mul (inv_mem hx) (inv_mem hg),
          qθ_inv hx, qθ_inv hg]
        abel)
    (fun i hi x hx => by
      interval_cases i
      · rw [hS1] at hx
        rw [hS0, Subgroup.mem_bot]
        exact pow_three_eq_one hσ hx
      · rw [hS2] at hx
        rw [hS1]
        exact pow_three_mem_center0 hσ hx)
    (fun i hi x hx h => by
      interval_cases i
      · rw [hS1] at hx
        rw [hS0, Subgroup.mem_bot]
        have h1 := h ⟨d, Subgroup.mem_zpowers d⟩
        rw [hS0, Subgroup.mem_bot] at h1
        exact hfix_center0 hdZ hx h1
      · rw [hS2] at hx
        rw [hS1]
        have h1 := h ⟨d, Subgroup.mem_zpowers d⟩
        rw [hS1] at h1
        exact hfix_radical hdQ hdθ hμ1 hx h1)
    (fun i hi j hj b h₁ h₂ h₃ h₄ halt h₅ => by
      interval_cases i <;> interval_cases j
      · simp only [zero_add, hS0, hS1, Subgroup.mem_bot, forall_eq] at h₂ h₃ halt ⊢
        exact hbil_center0_center0 hZ3 b h₂ h₃ (halt trivial)
      · simp only [zero_add, Nat.reduceAdd, hS1, hS2] at h₂ h₄ h₅ ⊢
        exact hbil_center0_radical hdQ hdθ hdZ hμ2 b h₂ h₄
          (h₅ ⟨d ^ 2, Subgroup.npow_mem_zpowers d 2⟩)
      · simp only [zero_add, Nat.reduceAdd, hS1, hS2] at h₁ h₃ h₅ ⊢
        exact hbil_radical_center0 hdQ hdθ hdZ hμ2 b h₁ h₃
          (h₅ ⟨d ^ 2, Subgroup.npow_mem_zpowers d 2⟩)
      · simp only [Nat.reduceAdd, hS1, hS2] at h₁ h₂ h₃ h₄ h₅ ⊢
        exact hbil_radical_radical hF9 hdQ hdθ hμ b h₁ h₂ h₃ h₄
          (h₅ ⟨d, Subgroup.mem_zpowers d⟩))
  exact ⟨K, hKQ, hKC, hKs, fun e he => hKe ⟨d, Subgroup.mem_zpowers d⟩ e he⟩

theorem ker_eq_bot_SU_add_two (hF : Nat.card F = (3 ^ 1) ^ 2) {m : ℕ} (hm : Odd m)
    (IH : ∀ (P : Type u) [Group P] [Finite P] [Group.IsPerfect P] (ρ : P →* SU σ₀ m),
      Function.Surjective ρ → ρ.ker ≤ Subgroup.center P → IsPGroup 3 ρ.ker → ρ.ker = ⊥)
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E] (η : E →* SU σ₀ (m + 2))
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h3 : IsPGroup 3 η.ker) :
    η.ker = ⊥ := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨k, hk⟩ := hm
  obtain ⟨a, l, μ, hl, hdet, haμ, ha1, hμ1, hμ2, hμ⟩ := exists_torus_data hF k
  rw [← hk] at hdet
  obtain ⟨d, hdL, hd8, hdθ, hdZ, hdι⟩ : ∃ d : SU σ₀ (m + 2), d ∈ levi σ₀ ∧ d ^ 8 = 1 ∧
      (∀ x ∈ radical σ₀ hσ, qθ σ₀ (d * x * d⁻¹) = (μ : F) • qθ σ₀ x) ∧
      (∀ z ∈ center0 σ₀ hσ, d * z * d⁻¹ = z⁻¹) ∧
      ∀ A : SU σ₀ m, d * iotaHom A = iotaHom A * d := by
    refine ⟨torusElt hσ hl hdet, torusElt_mem_levi, ?_,
      fun x hx => by rw [qθ_torusElt_conj hx, haμ], ?_, torusElt_commute_iotaHom⟩
    · refine mat_injective ?_
      rw [map_pow, mat_torusElt, diagonal_pow, map_one, ← diagonal_one]
      congr 1
      funext t
      rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val,
        show (8 : ℕ) = Nat.card Fˣ by rw [Nat.card_units, hF]; norm_num, pow_card_eq_one',
        Units.val_one]
    · intro z hz
      refine eq_of_qθ_qc (conj_mem_radical torusElt_mem_levi hz.1) (inv_mem hz.1) ?_ ?_
      · rw [qθ_torusElt_conj hz.1, hz.2, smul_zero, qθ_inv hz.1, hz.2, neg_zero]
      · rw [qc_torusElt_conj hz.1, ha1, neg_one_mul]
        have h := qc_mul_of_mem_center0 hz (inv_mem hz.1)
        rw [mul_inv_cancel, qc_one] at h
        exact neg_eq_of_add_eq_zero_right h.symm
  have hdQ : ∀ x ∈ radical σ₀ hσ, d * x * d⁻¹ ∈ radical σ₀ hσ := fun x hx =>
    conj_mem_radical hdL hx
  obtain ⟨K, hKQ, hKC, hKs, hKe⟩ :=
    exists_invariant_lift_radical hF hσ η hη hC h3 hdL hd8 hdθ hdZ hμ1 hμ2 hμ
  obtain ⟨e₀, he₀⟩ := hη d
  obtain ⟨s, hs, hscomm⟩ : ∃ s : SU σ₀ m →* E, (∀ A, η (s A) = iotaHom A) ∧
      ∀ A, e₀ * s A * e₀⁻¹ = s A := by
    by_cases hk0 : k = 0
    · subst hk0
      have hm1 : m = 1 := by omega
      subst hm1
      exact ⟨1, fun A => by simp [eq_one_of_SU_one A], fun A => by simp⟩
    · have : Group.IsPerfect (SU σ₀ m) := isPerfect_SU hF (by omega)
      let H : Subgroup E := (iotaHom (σ := σ₀) (m := m)).range.comap η
      let eι := MonoidHom.ofInjective (iotaHom_injective (σ := σ₀) (m := m))
      let ρ : H →* SU σ₀ m :=
        eι.symm.toMonoidHom.comp ((η.comp H.subtype).codRestrict _ fun x => x.2)
      have hρι : ∀ x : H, iotaHom (ρ x) = η x := fun x => by
        have h := MonoidHom.ofInjective_apply (iotaHom_injective (σ := σ₀) (m := m))
          (x := eι.symm ⟨η x, x.2⟩)
        rw [MulEquiv.apply_symm_apply] at h
        exact h.symm
      have hρ : Function.Surjective ρ := fun A => by
        obtain ⟨x, hx⟩ := hη (iotaHom A)
        refine ⟨⟨x, ⟨A, hx.symm⟩⟩, iotaHom_injective ?_⟩
        rw [hρι]
        exact hx
      have hker : ∀ x : H, x ∈ ρ.ker → (x : E) ∈ η.ker := fun x hx => by
        rw [MonoidHom.mem_ker, ← hρι, (MonoidHom.mem_ker).1 hx, map_one]
      have hρC : ρ.ker ≤ Subgroup.center H := fun x hx =>
        Subgroup.mem_center_iff.2 fun y =>
          Subtype.ext (Subgroup.mem_center_iff.1 (hC (hker x hx)) y)
      have hρp : IsPGroup 3 ρ.ker := by
        let φ : ρ.ker →* η.ker :=
          (H.subtype.comp ρ.ker.subtype).codRestrict η.ker fun x => hker x x.2
        exact h3.of_injective φ fun x y hxy =>
          Subtype.ext (Subtype.ext (congrArg (Subtype.val : η.ker → E) hxy))
      obtain ⟨s₀, hs₀⟩ := exists_section_of_cover_trivial IH ρ hρ hρC hρp
      have hs₀ι : ∀ A, η (s₀ A : E) = iotaHom A := fun A => by rw [← hρι, hs₀]
      refine ⟨H.subtype.comp s₀, hs₀ι, fun A => ?_⟩
      have hβ : η.comp ((MulAut.conj e₀).toMonoidHom.comp (H.subtype.comp s₀)) =
          η.comp (H.subtype.comp s₀) := by
        refine MonoidHom.ext fun A => ?_
        change η (e₀ * (s₀ A : E) * e₀⁻¹) = η (s₀ A : E)
        rw [map_mul, map_mul, map_inv, he₀, hs₀ι, mul_inv_eq_iff_eq_mul]
        exact hdι A
      exact DFunLike.congr_fun (CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect hC hβ) A
  have hsK : ∀ A, ∀ k ∈ K, s A * k * (s A)⁻¹ ∈ K := by
    intro A
    have heq : K = K.map (MulAut.conj (s A)).toMonoidHom := by
      refine invariant_lift_unique η hC (U := radical σ₀ hσ) (e₀ := e₀) ?_ hKQ ?_ hKC ?_ hKs ?_
        (hKe e₀ he₀) ?_
      · intro φ hφC hφmul hφinv
        rw [he₀] at hφinv
        exact eq_one_of_invariant hdQ hdθ hdZ hμ1 φ hφmul hφinv
      · rintro _ ⟨k', hk', rfl⟩
        change η (s A * k' * (s A)⁻¹) ∈ radical σ₀ hσ
        rw [map_mul, map_mul, map_inv, hs]
        exact conj_mem_radical (iotaHom_mem_levi A) (hKQ k' hk')
      · rintro _ ⟨k', hk', rfl⟩ h1
        change η (s A * k' * (s A)⁻¹) = 1 at h1
        change s A * k' * (s A)⁻¹ = 1
        rw [map_mul, map_mul, map_inv, hs, mul_inv_eq_one, mul_eq_left] at h1
        rw [hKC k' hk' h1, mul_one, mul_inv_cancel]
      · intro u hu
        obtain ⟨k', hk', hk'u⟩ := hKs ((iotaHom A)⁻¹ * u * (iotaHom A)⁻¹⁻¹)
          (conj_mem_radical (inv_mem (iotaHom_mem_levi A)) hu)
        refine ⟨s A * k' * (s A)⁻¹, ⟨k', hk', rfl⟩, ?_⟩
        rw [map_mul, map_mul, map_inv, hs, hk'u]
        group
      · rintro _ ⟨k', hk', rfl⟩
        refine ⟨e₀ * k' * e₀⁻¹, hKe e₀ he₀ k' hk', ?_⟩
        change s A * (e₀ * k' * e₀⁻¹) * (s A)⁻¹ = e₀ * (s A * k' * (s A)⁻¹) * e₀⁻¹
        calc s A * (e₀ * k' * e₀⁻¹) * (s A)⁻¹ =
            (e₀ * s A * e₀⁻¹) * (e₀ * k' * e₀⁻¹) * (e₀ * s A * e₀⁻¹)⁻¹ := by rw [hscomm A]
          _ = e₀ * (s A * k' * (s A)⁻¹) * e₀⁻¹ := by group
    intro k hk
    rw [heq]
    exact ⟨k, hk, rfl⟩
  obtain ⟨S'⟩ := (inferInstance : Nonempty (Sylow 3 (SU σ₀ m)))
  obtain ⟨P, hP⟩ := exists_sylow_le hF hσ (by omega) S'
  exact ker_eq_bot_of_levi_lift η hη hC h3 iotaHom iotaHom_injective
    (fun x hx hι => eq_one_of_mem_radical_of_mem_range hx hι) hKQ hKC hKs s hs hsK S' P hP

theorem su_odd_field_three_cover_trivial (hF : Nat.card F = (3 ^ 1) ^ 2) {n : ℕ} (hn : Odd n)
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* SU (unitaryInvolution F 3 1) n) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h3 : IsPGroup 3 η.ker) : η.ker = ⊥ := by
  obtain ⟨k, rfl⟩ := hn
  induction k generalizing E with
  | zero => exact ker_eq_bot_SU_one η hC
  | succ k ih =>
    exact ker_eq_bot_SU_add_two hF ⟨k, rfl⟩ (fun P _ _ _ ρ hρ hρC hρp => ih ρ hρ hρC hρp) η hη
      hC h3

end CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree
