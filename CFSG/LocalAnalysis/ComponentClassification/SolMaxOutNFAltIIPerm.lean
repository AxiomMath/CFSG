module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36E

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem oddCentGen_le_centralizer (σ : Perm α) : oddCentGen σ ≤ centralizer ({σ} : Set (Perm α)) :=
  (closure_le _).mpr fun _ hπ => mem_centralizer_singleton_iff.mpr hπ.2.1

theorem card_support_of_mem_cycleFactorsFinset {σ : Perm α} (hσ : σ * σ = 1) {c : Perm α}
    (hc : c ∈ σ.cycleFactorsFinset) : c.support.card = 2 := by
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    simp at hc
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ) hσ1
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hk
  have h1 : c.support.card ∈ σ.cycleType := by
    rw [Perm.cycleType_def]
    exact Multiset.mem_map_of_mem _ hc
  rw [hk] at h1
  exact Multiset.eq_of_mem_replicate h1

theorem two_mul_card_cycleFactorsFinset {σ : Perm α} (hσ : σ * σ = 1) :
    2 * σ.cycleFactorsFinset.card = σ.support.card := by
  by_cases hσ1 : σ = 1
  · subst hσ1
    simp
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ) hσ1
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hk
  have h1 := Perm.sum_cycleType σ
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at h1
  have h2 : Multiset.card σ.cycleType = σ.cycleFactorsFinset.card := by
    rw [Perm.cycleType_def, Multiset.card_map]
    rfl
  rw [hk, Multiset.card_replicate] at h2
  omega

theorem swap_mem_cycleFactorsFinset {σ : Perm α} (hσ : σ * σ = 1) {v : α} (hv : v ∈ σ.support) :
    swap v (σ v) ∈ σ.cycleFactorsFinset := by
  have hσσ : ∀ w, σ (σ w) = w := fun w => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  have hv' : v ≠ σ v := fun h => Perm.mem_support.mp hv h.symm
  rw [Perm.mem_cycleFactorsFinset_iff]
  refine ⟨Perm.isCycle_swap hv', fun a ha => ?_⟩
  rw [Perm.support_swap hv', Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · rw [swap_apply_left]
  · rw [swap_apply_right, hσσ]

theorem exists_swap_eq_of_mem_cycleFactorsFinset {σ : Perm α} (hσ : σ * σ = 1) {c : Perm α}
    (hc : c ∈ σ.cycleFactorsFinset) : ∃ q ∈ σ.support, c = swap q (σ q) := by
  obtain ⟨q, r, hqr, rfl⟩ := Perm.card_support_eq_two.mp
    (card_support_of_mem_cycleFactorsFinset hσ hc)
  have hc' := (Perm.mem_cycleFactorsFinset_iff.mp hc).2 q
    (by rw [Perm.support_swap hqr]; exact Finset.mem_insert_self _ _)
  rw [swap_apply_left] at hc'
  refine ⟨q, Perm.mem_support.mpr (by rw [← hc']; exact hqr.symm), by rw [hc']⟩

theorem oddCentGen_cycleAction_mem (σ : Perm α) (w : ↥(oddCentGen σ)) :
    (Perm.OnCycleFactors.toPermHom σ) (inclusion (oddCentGen_le_centralizer σ) w) ∈
      alternatingGroup ↥σ.cycleFactorsFinset := by
  obtain ⟨π, hπ⟩ := w
  change π ∈ Subgroup.closure _ at hπ
  induction hπ using closure_induction with
  | mem π hπ' =>
    rw [Perm.mem_alternatingGroup]
    refine sign_eq_one_of_odd_orderOf ?_
    have h1 : Odd (orderOf (inclusion (oddCentGen_le_centralizer σ)
        (⟨π, subset_closure hπ'⟩ : ↥(oddCentGen σ)))) := by
      rw [← Subgroup.orderOf_coe]
      exact hπ'.2.2
    exact h1.of_dvd_nat (orderOf_map_dvd _ _)
  | one =>
    have h1 : inclusion (oddCentGen_le_centralizer σ) (⟨1, one_mem _⟩ : ↥(oddCentGen σ)) = 1 :=
      rfl
    rw [h1, map_one]
    exact one_mem _
  | mul x y hx hy ihx ihy =>
    have h1 : inclusion (oddCentGen_le_centralizer σ) (⟨x * y, mul_mem hx hy⟩ : ↥(oddCentGen σ)) =
        inclusion (oddCentGen_le_centralizer σ) ⟨x, hx⟩ *
          inclusion (oddCentGen_le_centralizer σ) ⟨y, hy⟩ := rfl
    rw [h1, map_mul]
    exact mul_mem ihx ihy
  | inv x hx ihx =>
    have h1 : inclusion (oddCentGen_le_centralizer σ) (⟨x⁻¹, inv_mem hx⟩ : ↥(oddCentGen σ)) =
        (inclusion (oddCentGen_le_centralizer σ) ⟨x, hx⟩)⁻¹ := rfl
    rw [h1, map_inv]
    exact inv_mem ihx

theorem pow_four_pow_eq_of_orderOf_eq_three {G : Type*} [Group G] {τ : G} (hτ : orderOf τ = 3)
    (b : ℕ) : τ ^ (2 ^ b * 2 ^ b) = τ := by
  have h1 : 2 ^ b * 2 ^ b % 3 = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  rw [← pow_mod_orderOf, hτ, h1, pow_one]

theorem exists_oddCentGen_cycleAction_eq {σ : Perm α} (hσ : σ * σ = 1)
    {τ : Perm ↥σ.cycleFactorsFinset} (hτ : τ ∈ alternatingGroup ↥σ.cycleFactorsFinset) :
    ∃ w : ↥(oddCentGen σ),
      (Perm.OnCycleFactors.toPermHom σ) (inclusion (oddCentGen_le_centralizer σ) w) = τ := by
  rw [← Perm.closure_three_cycles_eq_alternating] at hτ
  induction hτ using closure_induction with
  | mem τ h3 =>
    have hrange : τ ∈ (Perm.OnCycleFactors.toPermHom σ).range := by
      rw [Perm.OnCycleFactors.mem_range_toPermHom_iff]
      intro c
      rw [card_support_of_mem_cycleFactorsFinset hσ (τ c).2,
        card_support_of_mem_cycleFactorsFinset hσ c.2]
    obtain ⟨w, hw⟩ := hrange
    obtain ⟨b, d, hd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
    set w₁ := w ^ 2 ^ b with hw₁def
    have hw₁o : Odd (orderOf (w₁ : Perm α)) := by
      rw [Subgroup.orderOf_coe]
      have h1 : w₁ ^ d = 1 := by rw [hw₁def, ← pow_mul, ← hord, pow_orderOf_eq_one]
      exact hd.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
    have hw₁S : (w₁ : Perm α) ∈ oddCentGen σ := by
      refine subset_oddCentGen ?_ ?_ hw₁o
      · rw [Perm.mem_alternatingGroup]
        exact sign_eq_one_of_odd_orderOf hw₁o
      · exact mem_centralizer_singleton_iff.mp w₁.2
    have hτ3 := h3.orderOf
    refine ⟨⟨w₁, hw₁S⟩ ^ 2 ^ b, ?_⟩
    have h1 : inclusion (oddCentGen_le_centralizer σ) (⟨w₁, hw₁S⟩ ^ 2 ^ b : ↥(oddCentGen σ)) =
        w ^ (2 ^ b * 2 ^ b) := by
      rw [map_pow, pow_mul]
      rfl
    rw [h1, map_pow, hw, pow_four_pow_eq_of_orderOf_eq_three hτ3]
  | one => exact ⟨1, map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u * v, by rw [map_mul, map_mul, hu, hv]⟩
  | inv x _ hx =>
    obtain ⟨u, hu⟩ := hx
    exact ⟨u⁻¹, by rw [map_inv, map_inv, hu]⟩

theorem exists_mem_of_normal_oddCentGen {σ : Perm α} (hσ : σ * σ = 1)
    (h10 : 10 ≤ σ.support.card) {N : Subgroup ↥(oddCentGen σ)} (hNn : N.Normal)
    (hN : ∃ w ∈ N, (Perm.OnCycleFactors.toPermHom σ)
      (inclusion (oddCentGen_le_centralizer σ) w) ≠ 1)
    {i₀ i₁ : α} (hi₀ : i₀ ∈ σ.support) (hi₁ : i₁ ∈ σ.support) (h10' : i₁ ≠ i₀)
    (h1σ0 : i₁ ≠ σ i₀) :
    ∃ w ∈ N, (w : Perm α) = swap i₀ (σ i₀) * swap i₁ (σ i₁) := by
  classical
  have hσσ : ∀ v, σ (σ v) = v := fun v => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  set 𝒞 := σ.cycleFactorsFinset with h𝒞def
  set κ : ↥(oddCentGen σ) →* Perm ↥𝒞 :=
    (Perm.OnCycleFactors.toPermHom σ).comp (inclusion (oddCentGen_le_centralizer σ)) with hκdef
  have hκ : ∀ w, κ w = (Perm.OnCycleFactors.toPermHom σ)
      (inclusion (oddCentGen_le_centralizer σ) w) := fun _ => rfl
  have hcard : 5 ≤ Nat.card ↥𝒞 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have := two_mul_card_cycleFactorsFinset hσ
    rw [← h𝒞def] at this
    omega
  set A := alternatingGroup ↥𝒞 with hAdef
  have hκA : ∀ w, κ w ∈ A := fun w => oddCentGen_cycleAction_mem σ w
  set K : Subgroup ↥A := (N.map κ).comap A.subtype with hKdef
  have hKn : K.Normal := by
    refine ⟨fun k hk a => ?_⟩
    obtain ⟨u, hu⟩ := exists_oddCentGen_cycleAction_eq hσ a.2
    obtain ⟨w, hw, hwk⟩ := hk
    refine ⟨u * w * u⁻¹, hNn.conj_mem w hw u, ?_⟩
    change κ (u * w * u⁻¹) = (a : Perm ↥𝒞) * (k : Perm ↥𝒞) * (a : Perm ↥𝒞)⁻¹
    rw [map_mul, map_mul, map_inv, hκ u, hu, hwk]
    rfl
  have hKtop : K = ⊤ := by
    have : IsSimpleGroup ↥A := alternatingGroup.isSimpleGroup hcard
    rcases hKn.eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨w, hwN, hw1⟩ := hN
      have h1 : (⟨κ w, hκA w⟩ : ↥A) ∈ K := ⟨w, hwN, rfl⟩
      rw [h, mem_bot] at h1
      exact hw1 (congrArg Subtype.val h1)
    · exact h
  have hc₀ : swap i₀ (σ i₀) ∈ 𝒞 := swap_mem_cycleFactorsFinset hσ hi₀
  have hc₁ : swap i₁ (σ i₁) ∈ 𝒞 := swap_mem_cycleFactorsFinset hσ hi₁
  set c₀ : ↥𝒞 := ⟨_, hc₀⟩ with hc₀def
  set c₁ : ↥𝒞 := ⟨_, hc₁⟩ with hc₁def
  have hi₀' : i₀ ≠ σ i₀ := fun h => Perm.mem_support.mp hi₀ h.symm
  have hi₁' : i₁ ≠ σ i₁ := fun h => Perm.mem_support.mp hi₁ h.symm
  have hc₀₁ : c₀ ≠ c₁ := by
    intro h
    have h1 := congrArg (fun c : ↥𝒞 => (c : Perm α) i₀) h
    simp only [hc₀def, hc₁def, swap_apply_left] at h1
    rw [swap_apply_of_ne_of_ne (Ne.symm h10') (fun h' => h1σ0 (by rw [h', hσσ]))] at h1
    exact hi₀' h1.symm
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({c₀, c₁} : Finset ↥𝒞)) (t := Finset.univ)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact
      lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({c₀, c₁, p} : Finset ↥𝒞)) (t := Finset.univ)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact
      lt_of_le_of_lt Finset.card_le_three (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  set τ : Perm ↥𝒞 := swap c₀ u * swap c₀ c₁ with hτdef
  have hτA : τ ∈ A :=
    (Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hu.1) hc₀₁ hu.2.1).mem_alternatingGroup
  have hτc₀ : τ c₀ = c₁ := by
    rw [hτdef, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hc₀₁)
      (fun h => hu.2.1 h.symm)]
  have hτp : τ p = p := by
    rw [hτdef, Perm.mul_apply, swap_apply_of_ne_of_ne hp.1 hp.2,
      swap_apply_of_ne_of_ne hp.1 (fun h => hu.2.2 h.symm)]
  obtain ⟨w, hwN, hwτ⟩ : ∃ w ∈ N, κ w = τ := by
    have h1 : (⟨τ, hτA⟩ : ↥A) ∈ K := by rw [hKtop]; exact mem_top _
    obtain ⟨w, hwN, hw⟩ := h1
    exact ⟨w, hwN, hw⟩
  obtain ⟨q, hq, hpq⟩ := exists_swap_eq_of_mem_cycleFactorsFinset hσ p.2
  have hq' : q ≠ σ q := fun h => Perm.mem_support.mp hq h.symm
  have hqi : ∀ {i : α} (hi : i ∈ σ.support),
      (⟨swap i (σ i), swap_mem_cycleFactorsFinset hσ hi⟩ : ↥𝒞) ≠ p → q ≠ i ∧ q ≠ σ i := by
    intro i hi hne
    constructor
    · rintro rfl
      exact hne (Subtype.ext hpq.symm)
    · intro h
      refine hne (Subtype.ext ?_)
      show swap i (σ i) = (p : Perm α)
      rw [hpq, h, hσσ, swap_comm]
  obtain ⟨hq0, hq0'⟩ := hqi hi₀ (Ne.symm hp.1)
  obtain ⟨hq1, hq1'⟩ := hqi hi₁ (Ne.symm hp.2)
  have hb : swap q (σ q) * swap i₀ (σ i₀) ∈ oddCentGen σ :=
    pair_mem_oddCentGen hσ (Perm.mem_support.mp hi₁) (Perm.mem_support.mp hq)
      (Perm.mem_support.mp hi₀) hq1 hq1' h10'.symm (fun h => h1σ0 (by rw [h, hσσ]))
      (Ne.symm hq0) (fun h => hq0' (by rw [h, hσσ]))
  set bP : ↥(oddCentGen σ) := ⟨_, hb⟩ with hbPdef
  refine ⟨bP * w * bP⁻¹ * w⁻¹, mul_mem (hNn.conj_mem w hwN bP) (inv_mem hwN), ?_⟩
  set W : Perm α := (w : Perm α) with hWdef
  have hconj : ∀ c : ↥𝒞, W * (c : Perm α) * W⁻¹ = ((κ w) c : Perm α) := by
    intro c
    rw [hκ w, Perm.OnCycleFactors.coe_toPermHom]
    rfl
  have hWp : W * swap q (σ q) * W⁻¹ = swap q (σ q) := by
    have h1 := hconj p
    rw [hwτ, hτp, hpq] at h1
    exact h1
  have hWc₀ : W * swap i₀ (σ i₀) * W⁻¹ = swap i₁ (σ i₁) := by
    have h1 := hconj c₀
    rw [hwτ, hτc₀] at h1
    exact h1
  have hcomm : ∀ c ∈ 𝒞, c ≠ swap q (σ q) → swap q (σ q) * c = c * swap q (σ q) := by
    intro c hc hne
    exact (Perm.cycleFactorsFinset_mem_commute σ (hpq ▸ p.2) hc (Ne.symm hne)).eq
  have hcq0 := hcomm _ hc₀ (fun h => hp.1 (Subtype.ext (by rw [hpq]; exact h.symm)))
  have hcq1 := hcomm _ hc₁ (fun h => hp.2 (Subtype.ext (by rw [hpq]; exact h.symm)))
  change swap q (σ q) * swap i₀ (σ i₀) * W * (swap q (σ q) * swap i₀ (σ i₀))⁻¹ * W⁻¹ = _
  calc swap q (σ q) * swap i₀ (σ i₀) * W * (swap q (σ q) * swap i₀ (σ i₀))⁻¹ * W⁻¹ =
        swap q (σ q) * swap i₀ (σ i₀) *
          (W * swap q (σ q) * W⁻¹ * (W * swap i₀ (σ i₀) * W⁻¹))⁻¹ := by group
    _ = swap q (σ q) * swap i₀ (σ i₀) * (swap q (σ q) * swap i₁ (σ i₁))⁻¹ := by
          rw [hWp, hWc₀]
    _ = swap q (σ q) * swap i₀ (σ i₀) * (swap i₁ (σ i₁) * swap q (σ q)) := by
          rw [mul_inv_rev, swap_inv, swap_inv]
    _ = swap i₀ (σ i₀) * (swap q (σ q) * swap i₁ (σ i₁)) * swap q (σ q) := by
          rw [hcq0]
          group
    _ = swap i₀ (σ i₀) * (swap i₁ (σ i₁) * swap q (σ q)) * swap q (σ q) := by rw [hcq1]
    _ = swap i₀ (σ i₀) * swap i₁ (σ i₁) := by
          rw [mul_assoc, mul_assoc, swap_mul_self, mul_one]

end CFSG.ComponentClassification.SolMax
