module

public import CFSG.GH74.Uniqueness.SU.SU7Gen
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.GH74.Uniqueness.SU.SU7.Gen

open Subgroup

section LiftThroughOdd

variable {X : Type*} [Group X] [Finite X]

theorem exists_conj_mem_of_two_element {K S₀ : Subgroup X} [K.Normal] (hK : Odd (Nat.card K))
    (hS : IsPGroup 2 S₀) {y : X} (hy : IsPGroup 2 (zpowers y)) (hyS : y ∈ K ⊔ S₀) :
    ∃ k ∈ K, k⁻¹ * y * k ∈ S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ S₀.relIndex (S₀ ⊔ K) := by
    rw [relIndex_sup_odd K hS hK]
    have := Nat.odd_iff.1 hK
    omega
  rw [sup_comm] at hyS
  have hle : zpowers y ≤ S₀ ⊔ K := Subgroup.zpowers_le.2 hyS
  obtain ⟨c, hc, hcy⟩ :=
    CFSG.GH74.GLS.Bg.Thompson.exists_conj_into_sylow (p := 2) hle hy le_sup_left hS hidx
  rw [sup_comm] at hc
  obtain ⟨k, hk, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hc
  refine ⟨k, hk, ?_⟩
  have h1 := hcy y (Subgroup.mem_zpowers y)
  have h2 : k⁻¹ * y * k = s * ((k * s)⁻¹ * y * (k * s)) * s⁻¹ := by group
  rw [h2]
  exact S₀.mul_mem (S₀.mul_mem hs h1) (S₀.inv_mem hs)

omit [Finite X] in
theorem isPGroup_zpowers_of_pow {y : X} {n : ℕ} (hy : y ^ (2 ^ n) = 1) :
    IsPGroup 2 (zpowers y) := by
  have : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hy
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers]; exact hk)

end LiftThroughOdd

theorem ncard_image_of_fibers_two {α β : Type*} (f : α → β) {A : Set α} (hA : A.Finite)
    (σ : α → α) (hσA : ∀ a ∈ A, σ a ∈ A) (hσne : ∀ a ∈ A, σ a ≠ a)
    (hfib : ∀ a ∈ A, ∀ b ∈ A, f a = f b ↔ b = a ∨ b = σ a) :
    A.ncard = 2 * (f '' A).ncard := by
  classical
  have hB : (f '' A).Finite := hA.image f
  have hmaps : Set.MapsTo f hA.toFinset (hB.toFinset : Set β) := by
    intro a ha
    simpa using Set.mem_image_of_mem f (by simpa using ha : a ∈ A)
  have h1 := Finset.card_eq_sum_card_fiberwise hmaps
  have h2 : ∀ b ∈ hB.toFinset, ({a ∈ hA.toFinset | f a = b}).card = 2 := by
    intro b hb
    have hb' : b ∈ f '' A := by simpa using hb
    obtain ⟨a₀, ha₀, rfl⟩ := hb'
    have : ({a ∈ hA.toFinset | f a = f a₀} : Finset α) = {a₀, σ a₀} := by
      ext a
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨haA, hfa⟩
        have := (hfib a₀ ha₀ a haA).1 hfa.symm
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rintro (rfl | rfl)
        · exact ⟨ha₀, rfl⟩
        · exact ⟨hσA _ ha₀, ((hfib a₀ ha₀ _ (hσA _ ha₀)).2 (Or.inr rfl)).symm⟩
    rw [this, Finset.card_pair (hσne a₀ ha₀).symm]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul] at h1
  have e1 : A.ncard = hA.toFinset.card := by rw [Set.ncard_eq_toFinset_card A hA]
  have e2 : (f '' A).ncard = hB.toFinset.card := by rw [Set.ncard_eq_toFinset_card _ hB]
  rw [e1, e2, h1, mul_comm]

theorem zmod5_sq : ∀ a : ZMod 5, a * a = 1 → a = 1 ∨ a = -1 := by decide

theorem false_of_card_twenty
    {Y Ω : Type*} [Group Y] [Finite Y] [MulAction Y Ω] [Finite Ω] [FaithfulSMul Y Ω]
    (hΩ : Nat.card Ω = 5) (h20 : Nat.card Y = 20)
    {P : Subgroup Y} (hP4 : Nat.card P = 4) (hPe : ∀ g ∈ P, g * g = 1) : False := by
  classical
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Y) 5 (by rw [h20]; norm_num)
  have hc1 : c ≠ 1 := by intro h; rw [h, orderOf_one] at hc; omega
  set Q : Subgroup Y := zpowers c with hQ
  have hQcard : Nat.card Q = 5 := by rw [hQ, Nat.card_zpowers, hc]
  have hQidx : Q.index = 4 := by
    have := Subgroup.card_mul_index Q
    rw [hQcard, h20] at this; omega
  have hQp : IsPGroup 5 Q := IsPGroup.of_card (n := 1) (by rw [hQcard]; norm_num)
  let Qs : Sylow 5 Y := hQp.toSylow (by rw [hQidx]; norm_num)
  have hQs : (Qs : Subgroup Y) = Q := rfl
  have hcnt : Nat.card (Sylow 5 Y) = 1 := by
    have h1 := Sylow.card_dvd_index Qs
    have h2 := card_sylow_modEq_one 5 Y
    rw [hQs, hQidx] at h1
    have h3 : Nat.card (Sylow 5 Y) ≤ 4 := Nat.le_of_dvd (by norm_num) h1
    have h4 : 0 < Nat.card (Sylow 5 Y) := Nat.card_pos
    unfold Nat.ModEq at h2
    interval_cases hn : Nat.card (Sylow 5 Y) <;> simp_all
  have : Subsingleton (Sylow 5 Y) := (Nat.card_eq_one_iff_unique.1 hcnt).1
  have hQn : Q.Normal := Sylow.normal_of_subsingleton Qs
  have hinv : ∀ t ∈ P, t * c * t⁻¹ = c ∨ t * c * t⁻¹ = c⁻¹ := by
    intro t ht
    have htt := hPe t ht
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (hQn.conj_mem c (mem_zpowers c) t)
    have hj' : t * c * t⁻¹ = c ^ j := hj.symm
    have hcc : c ^ (j * j) = c := by
      have e1 : c = t * (t * c * t⁻¹) * t⁻¹ := by
        have : t * (t * c * t⁻¹) * t⁻¹ = (t * t) * c * (t * t)⁻¹ := by group
        rw [this, htt]; group
      calc c ^ (j * j) = (c ^ j) ^ j := by rw [zpow_mul]
        _ = (t * c * t⁻¹) ^ j := by rw [hj']
        _ = t * c ^ j * t⁻¹ := by rw [conj_zpow]
        _ = t * (t * c * t⁻¹) * t⁻¹ := by rw [hj']
        _ = c := e1.symm
    have h5dvd : (5 : ℤ) ∣ j * j - 1 := by
      have : (orderOf c : ℤ) ∣ j * j - 1 := by
        apply orderOf_dvd_iff_zpow_eq_one.2
        rw [zpow_sub, zpow_one, hcc]; group
      rw [hc] at this
      exact_mod_cast this
    have hz : ((j : ZMod 5)) * (j : ZMod 5) = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (j * j - 1) 5).2 (by exact_mod_cast h5dvd)
      push_cast at this
      exact sub_eq_zero.1 this
    rcases zmod5_sq _ hz with h | h
    · left
      rw [hj']
      have : c ^ j = c ^ (1 : ℤ) := by
        rw [zpow_eq_zpow_iff_modEq, hc]
        exact (ZMod.intCast_eq_intCast_iff j 1 5).1 (by rw [h]; simp)
      simpa using this
    · right
      rw [hj']
      have : c ^ j = c ^ (-1 : ℤ) := by
        rw [zpow_eq_zpow_iff_modEq, hc]
        exact (ZMod.intCast_eq_intCast_iff j (-1) 5).1 (by rw [h]; simp)
      simpa using this
  have hP1 : ∃ t₁ ∈ P, t₁ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 hcon
    rw [this, Subgroup.card_bot] at hP4; omega
  obtain ⟨t₁, ht₁, ht₁1⟩ := hP1
  have hP2 : ∃ t₂ ∈ P, t₂ ≠ 1 ∧ t₂ ≠ t₁ := by
    by_contra hcon
    push Not at hcon
    have hsub : (P : Set Y) ⊆ ({1, t₁} : Finset Y) := by
      intro g hg
      by_cases h1 : g = 1
      · simp [h1]
      · have := hcon g hg h1
        simp [this]
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at this
    have h3 : ({1, t₁} : Finset Y).card ≤ 2 := Finset.card_le_two
    have : Nat.card P ≤ 2 := by
      calc Nat.card P = Nat.card (P : Set Y) := rfl
        _ ≤ _ := this
        _ ≤ 2 := h3
    omega
  obtain ⟨t₂, ht₂, ht₂1, ht₂₁⟩ := hP2
  have hex : ∃ t ∈ P, t ≠ 1 ∧ t * c * t⁻¹ = c := by
    rcases hinv t₁ ht₁ with h | h
    · exact ⟨t₁, ht₁, ht₁1, h⟩
    · rcases hinv t₂ ht₂ with h' | h'
      · exact ⟨t₂, ht₂, ht₂1, h'⟩
      · refine ⟨t₁ * t₂, P.mul_mem ht₁ ht₂, ?_, ?_⟩
        · intro h1
          apply ht₂₁
          have h11 := hPe t₁ ht₁
          have : t₂ = t₁⁻¹ := by
            have := congrArg (t₁⁻¹ * ·) h1
            simpa using this
          rw [this]
          exact inv_eq_of_mul_eq_one_right h11
        · calc t₁ * t₂ * c * (t₁ * t₂)⁻¹ = t₁ * (t₂ * c * t₂⁻¹) * t₁⁻¹ := by group
            _ = t₁ * c⁻¹ * t₁⁻¹ := by rw [h']
            _ = (t₁ * c * t₁⁻¹)⁻¹ := by group
            _ = c := by rw [h]; group
  obtain ⟨t, htP, ht1, htc⟩ := hex
  have htt := hPe t htP
  obtain ⟨ω₁, hω₁⟩ : ∃ ω₁ : Ω, c • ω₁ ≠ ω₁ := by
    by_contra hcon
    push Not at hcon
    apply hc1
    exact MulAction.toPerm_injective (α := Y) (β := Ω) (by ext ω; simpa using hcon ω)
  have hlt : ∀ i k : ℕ, i < k → k < 5 → c ^ k • ω₁ ≠ c ^ i • ω₁ := by
    intro i k hik hk5 heq
    have hfix : c ^ (k - i) • ω₁ = ω₁ := by
      have e : c ^ k • ω₁ = c ^ i • (c ^ (k - i) • ω₁) := by
        rw [smul_smul, ← pow_add]; congr 2; omega
      rw [e] at heq
      exact MulAction.injective (c ^ i) heq
    apply hω₁
    have hd1 : 0 < k - i := by omega
    have hd2 : k - i < 5 := by omega
    have e4 : (k - i) ^ 4 % 5 = 1 := by
      generalize k - i = d at hd1 hd2
      interval_cases d <;> norm_num
    have hc5 : c = (c ^ (k - i)) ^ ((k - i) ^ 3) := by
      rw [← pow_mul]
      have e : (k - i) * (k - i) ^ 3 = (k - i) ^ 4 := by ring
      rw [e, ← pow_mod_orderOf, hc, e4, pow_one]
    have : ∀ m : ℕ, (c ^ (k - i)) ^ m • ω₁ = ω₁ := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, mul_smul, hfix, ih]
    calc c • ω₁ = ((c ^ (k - i)) ^ ((k - i) ^ 3)) • ω₁ := by rw [← hc5]
      _ = ω₁ := this _
  have hinj : Function.Injective (fun i : Fin 5 => c ^ (i : ℕ) • ω₁) := by
    intro i k hik
    simp only at hik
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : (i : ℕ) ≠ (k : ℕ)) with h | h
    · exact hlt i k h k.2 hik.symm
    · exact hlt k i h i.2 hik
  have hbij : Function.Bijective (fun i : Fin 5 => c ^ (i : ℕ) • ω₁) :=
    hinj.bijective_of_nat_card_le (by rw [hΩ]; simp)
  obtain ⟨j, hj⟩ := hbij.2 (t • ω₁)
  simp only at hj
  have htc' : t * c = c * t := by
    have := htc
    rwa [mul_inv_eq_iff_eq_mul] at this
  have hpow : ∀ i : ℕ, t * c ^ i = c ^ i * t := fun i => (Commute.pow_right htc' i)
  have htact : ∀ ω : Ω, t • ω = c ^ (j : ℕ) • ω := by
    intro ω
    obtain ⟨i, rfl⟩ := hbij.2 ω
    simp only
    calc t • (c ^ (i:ℕ) • ω₁) = (t * c ^ (i:ℕ)) • ω₁ := (mul_smul _ _ _).symm
      _ = (c ^ (i:ℕ) * t) • ω₁ := by rw [hpow]
      _ = c ^ (i:ℕ) • (t • ω₁) := mul_smul _ _ _
      _ = c ^ (i:ℕ) • (c ^ (j:ℕ) • ω₁) := by rw [hj]
      _ = (c ^ (i:ℕ) * c ^ (j:ℕ)) • ω₁ := (mul_smul _ _ _).symm
      _ = (c ^ (j:ℕ) * c ^ (i:ℕ)) • ω₁ := by rw [← pow_add, ← pow_add, add_comm]
      _ = c ^ (j:ℕ) • (c ^ (i:ℕ) • ω₁) := mul_smul _ _ _
  have htj : t = c ^ (j : ℕ) := eq_of_smul_eq_smul htact
  rw [htj, ← pow_add] at htt
  have hdvd : orderOf c ∣ (j : ℕ) + j := orderOf_dvd_of_pow_eq_one htt
  rw [hc] at hdvd
  have hj0 : (j : ℕ) = 0 := by have := j.2; omega
  apply ht1
  rw [htj, hj0, pow_zero]

theorem nonempty_mulEquiv_alternatingGroup_five
    {Y Ω : Type*} [Group Y] [Finite Y] [MulAction Y Ω] [Finite Ω] [FaithfulSMul Y Ω]
    [MulAction.IsPretransitive Y Ω] (hΩ : Nat.card Ω = 5)
    {P : Subgroup Y} (hP4 : Nat.card P = 4) (hPidx : ¬ 2 ∣ P.index)
    (hPe : ∀ g ∈ P, g * g = 1) :
    Nonempty (Y ≃* alternatingGroup (Fin 5)) := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let _ : Fintype Ω := Fintype.ofFinite Ω
  let _ : Fintype Y := Fintype.ofFinite Y
  have hΩf : Fintype.card Ω = 5 := by rw [← Nat.card_eq_fintype_card]; exact hΩ
  let φ : Y →* Equiv.Perm Ω := MulAction.toPermHom Y Ω
  have hinj : Function.Injective φ := MulAction.toPerm_injective
  have hperm : Nat.card (Equiv.Perm Ω) = 120 := by
    rw [Nat.card_perm, hΩ]; decide
  have hY : Nat.card Y = 4 * P.index := by
    rw [← hP4]; exact (Subgroup.card_mul_index P).symm
  have : Nonempty Ω := ⟨(Fintype.equivFinOfCardEq hΩf).symm 0⟩
  obtain ⟨ω₀⟩ : Nonempty Ω := inferInstance
  have h5Y : 5 ∣ Nat.card Y := by
    have := (MulAction.stabilizer Y ω₀).index_dvd_card
    rwa [MulAction.index_stabilizer_of_transitive Y ω₀, hΩ] at this
  have h120 : Nat.card Y ∣ 120 := by
    have := Subgroup.card_dvd_of_injective φ hinj
    rwa [hperm] at this
  have hodd : P.index % 2 = 1 := by
    have := Nat.odd_iff.1 (Nat.odd_iff.2 (by omega : P.index % 2 = 1))
    omega
  have hcases : Nat.card Y = 20 ∨ Nat.card Y = 60 := by
    have hle : Nat.card Y ≤ 120 := Nat.le_of_dvd (by norm_num) h120
    rw [hY] at h5Y h120 hle
    have hm : P.index ≤ 30 := by omega
    interval_cases hm' : P.index <;> omega
  rcases hcases with h20 | h60
  · exact (false_of_card_twenty hΩ h20 hP4 hPe).elim
  · have hrange_index : (φ.range).index = 2 := by
      have := φ.range.card_mul_index
      have hr : Nat.card φ.range = 60 := by
        rw [← h60]; exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      rw [hr, hperm] at this
      omega
    have hA : φ.range = alternatingGroup Ω :=
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two hrange_index
    let e1 : Y ≃* φ.range := MonoidHom.ofInjective hinj
    let e2 : φ.range ≃* alternatingGroup Ω := MulEquiv.subgroupCongr hA
    let σ : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hΩf
    exact ⟨(e1.trans e2).trans (Equiv.altCongrHom σ)⟩

end CFSG.GH74.Uniqueness.SU.SU7.Gen
