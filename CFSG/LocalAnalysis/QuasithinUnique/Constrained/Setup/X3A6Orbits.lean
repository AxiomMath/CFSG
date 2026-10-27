module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.QuasithinUnique.Setup.X3

open Equiv Subgroup

@[expose] def fiveCycle : alternatingGroup (Fin 6) :=
  ⟨c[0, 1, 2, 3, 4], by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def fiveRefl : alternatingGroup (Fin 6) :=
  ⟨swap 1 4 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def dihedralTen : Finset (alternatingGroup (Fin 6)) :=
  (Finset.range 5).image (fun i => fiveCycle ^ i) ∪ (Finset.range 5).image (fun i => fiveCycle ^ i * fiveRefl)

theorem card_dihedralTen : dihedralTen.card = 10 := by decide +kernel

theorem normalizer_fiveCycle_aux :
    ∀ g : alternatingGroup (Fin 6), (∃ i : Fin 5, g * fiveCycle * g⁻¹ = fiveCycle ^ (i : ℕ)) →
      g ∈ dihedralTen := by
  decide +kernel

theorem card_normalizer_fiveCycle_le :
    Nat.card (normalizer (zpowers fiveCycle : Set (alternatingGroup (Fin 6)))) ≤ 10 := by
  have hsub : ((normalizer (zpowers fiveCycle : Set (alternatingGroup (Fin 6))) :
      Subgroup (alternatingGroup (Fin 6))) : Set (alternatingGroup (Fin 6))) ⊆
      ((dihedralTen : Finset (alternatingGroup (Fin 6))) : Set (alternatingGroup (Fin 6))) := by
    intro g hg
    have hmem : g * fiveCycle * g⁻¹ ∈ zpowers fiveCycle := by
      have := (mem_normalizer_iff.mp hg fiveCycle).mp (mem_zpowers fiveCycle)
      simpa using this
    have h5 : fiveCycle ^ 5 = 1 := by decide +kernel
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    have hk' : g * fiveCycle * g⁻¹ = fiveCycle ^ ((k % 5).toNat) := by
      rw [← hk]
      have : (k % 5).toNat = (k % 5 : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
      rw [← zpow_natCast, this]
      conv_lhs => rw [← Int.emod_add_mul_ediv k 5, zpow_add, zpow_mul]
      have h5z : fiveCycle ^ (5 : ℤ) = 1 := by exact_mod_cast h5
      rw [h5z, one_zpow, mul_one]
    refine normalizer_fiveCycle_aux g ⟨⟨(k % 5).toNat, ?_⟩, hk'⟩
    have := Int.emod_lt_of_pos k (show (0 : ℤ) < 5 by norm_num)
    omega
  have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, card_dihedralTen] at h
  calc Nat.card (normalizer (zpowers fiveCycle : Set (alternatingGroup (Fin 6))))
      = ((normalizer (zpowers fiveCycle : Set (alternatingGroup (Fin 6))) :
        Subgroup (alternatingGroup (Fin 6))) : Set (alternatingGroup (Fin 6))).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ 10 := h


theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem factorization_card_alt6 : (Nat.card (alternatingGroup (Fin 6))).factorization 5 = 1 := by
  rw [card_alt6]
  have h := Nat.Prime.factorization_pos_of_dvd Nat.prime_five (by norm_num : (360 : ℕ) ≠ 0)
    (by norm_num)
  have h2 : (360 : ℕ).factorization 5 ≤ 1 := by
    by_contra hc
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five (by norm_num)).mpr
      (by omega : 2 ≤ (360 : ℕ).factorization 5)
    norm_num at this
  omega

theorem orderOf_fiveCycle : orderOf fiveCycle = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem card_normalizer_le_ten {Q : Subgroup (alternatingGroup (Fin 6))} (hQ : Nat.card Q = 5) :
    Nat.card (normalizer (Q : Set (alternatingGroup (Fin 6)))) ≤ 10 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hc : Nat.card (zpowers fiveCycle) = 5 := by
    rw [Nat.card_zpowers, orderOf_fiveCycle]
  let S : Sylow 5 (alternatingGroup (Fin 6)) :=
    Sylow.ofCard Q (by rw [factorization_card_alt6]; simpa using hQ)
  let S0 : Sylow 5 (alternatingGroup (Fin 6)) :=
    Sylow.ofCard (zpowers fiveCycle) (by rw [factorization_card_alt6]; simpa using hc)
  have h1 := S.card_eq_index_normalizer
  have h2 := S0.card_eq_index_normalizer
  have hidx : (normalizer (Q : Set (alternatingGroup (Fin 6)))).index =
      (normalizer (zpowers fiveCycle : Set (alternatingGroup (Fin 6)))).index := h1.symm.trans h2
  have hm := Subgroup.card_mul_index (normalizer (Q : Set (alternatingGroup (Fin 6))))
  have hm0 := Subgroup.card_mul_index
    (normalizer (zpowers fiveCycle : Set (alternatingGroup (Fin 6))))
  rw [hidx] at hm
  have hpos : 0 < (normalizer (zpowers fiveCycle : Set (alternatingGroup (Fin 6)))).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have heq : Nat.card (normalizer (Q : Set (alternatingGroup (Fin 6)))) =
      Nat.card (normalizer (zpowers fiveCycle : Set (alternatingGroup (Fin 6)))) :=
    Nat.eq_of_mul_eq_mul_right hpos (hm.trans hm0.symm)
  rw [heq]
  exact card_normalizer_fiveCycle_le

theorem no_subgroup_order {K : Subgroup (alternatingGroup (Fin 6))}
    (hK : Nat.card K = 20 ∨ Nat.card K = 40 ∨ Nat.card K = 45) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 K) := inferInstance
  have hfac : (Nat.card K).factorization 5 = 1 := by
    have h := Nat.Prime.factorization_pos_of_dvd Nat.prime_five (by omega : Nat.card K ≠ 0)
      (by rcases hK with h | h | h <;> rw [h] <;> norm_num)
    have h2 : (Nat.card K).factorization 5 ≤ 1 := by
      by_contra hc
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five (by omega)).mpr
        (by omega : 2 ≤ (Nat.card K).factorization 5)
      rcases hK with h | h | h <;> rw [h] at this <;> norm_num at this
    omega
  have hP5 : Nat.card (P : Subgroup K) = 5 := by
    rw [P.card_eq_multiplicity, hfac]; norm_num
  have hn : Nat.card (Sylow 5 K) = 1 := by
    have hdvd := P.card_dvd_index
    have hmod := card_sylow_modEq_one 5 K
    have hidx : (P : Subgroup K).index * 5 = Nat.card K := by
      have := Subgroup.card_mul_index (P : Subgroup K)
      rw [hP5] at this
      omega
    have hle : Nat.card (Sylow 5 K) ≤ (P : Subgroup K).index :=
      Nat.le_of_dvd (by rcases hK with h | h | h <;> omega) hdvd
    have hmod' : Nat.card (Sylow 5 K) % 5 = 1 := hmod
    have hpos : 0 < Nat.card (Sylow 5 K) := Nat.card_pos
    rcases hK with h | h | h
    · have : (P : Subgroup K).index = 4 := by omega
      rw [this] at hdvd hle
      interval_cases (Nat.card (Sylow 5 K)) <;> omega
    · have : (P : Subgroup K).index = 8 := by omega
      rw [this] at hdvd hle
      interval_cases (Nat.card (Sylow 5 K)) <;> omega
    · have : (P : Subgroup K).index = 9 := by omega
      rw [this] at hdvd hle
      interval_cases (Nat.card (Sylow 5 K)) <;> omega
  have hsub : Subsingleton (Sylow 5 K) := (Nat.card_eq_one_iff_unique.mp hn).1
  have : (P : Subgroup K).Normal := Sylow.normal_of_subsingleton P
  set Q : Subgroup (alternatingGroup (Fin 6)) := (P : Subgroup K).map K.subtype with hQdef
  have hQ : Nat.card Q = 5 := by
    rw [hQdef, Subgroup.card_map_of_injective K.subtype_injective, hP5]
  have hKN : K ≤ normalizer (Q : Set (alternatingGroup (Fin 6))) := by
    intro k hk
    rw [mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨k, hk⟩ * p * ⟨k, hk⟩⁻¹, (inferInstance : (P : Subgroup K).Normal).conj_mem p hp _, rfl⟩
    · rintro ⟨p, hp, hph⟩
      refine ⟨⟨k, hk⟩⁻¹ * p * ⟨k, hk⟩, ?_, ?_⟩
      · have := (inferInstance : (P : Subgroup K).Normal).conj_mem p hp ⟨k, hk⟩⁻¹
        rwa [inv_inv] at this
      · change k⁻¹ * (p : alternatingGroup (Fin 6)) * k = h
        rw [show (p : alternatingGroup (Fin 6)) = k * h * k⁻¹ from hph]
        group
  have h1 := Subgroup.card_le_of_le hKN
  have h2 := card_normalizer_le_ten hQ
  rcases hK with h | h | h <;> omega


section Orbits

variable {Γ : Type*} [Group Γ]

theorem finite_of_equiv_alt6 (e : Γ ≃* alternatingGroup (Fin 6)) : Finite Γ :=
  Finite.of_equiv _ e.toEquiv.symm

theorem card_of_equiv_alt6 (e : Γ ≃* alternatingGroup (Fin 6)) : Nat.card Γ = 360 := by
  rw [Nat.card_congr e.toEquiv, card_alt6]

theorem isSimpleGroup_alt6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem isSimpleGroup_of_equiv_alt6 (e : Γ ≃* alternatingGroup (Fin 6)) : IsSimpleGroup Γ :=
  haveI := isSimpleGroup_alt6
  e.isSimpleGroup

theorem orbit_card_cases {X : Type*} [MulAction Γ X] (e : Γ ≃* alternatingGroup (Fin 6)) (x : X) :
    (MulAction.orbit Γ x).ncard = 1 ∨
      (6 ≤ (MulAction.orbit Γ x).ncard ∧ (MulAction.orbit Γ x).ncard ∣ 360 ∧
        (MulAction.orbit Γ x).ncard ≠ 8 ∧ (MulAction.orbit Γ x).ncard ≠ 9 ∧
        (MulAction.orbit Γ x).ncard ≠ 18) := by
  have hfin : Finite Γ := finite_of_equiv_alt6 e
  have hsimple : IsSimpleGroup Γ := isSimpleGroup_of_equiv_alt6 e
  rw [← MulAction.index_stabilizer Γ x]
  set K := MulAction.stabilizer Γ x with hK
  by_cases htop : K = ⊤
  · left
    rw [htop, Subgroup.index_top]
  · right
    have hdvd : K.index ∣ 360 := by
      rw [← card_of_equiv_alt6 e]
      exact Subgroup.index_dvd_card K
    have hmul : Nat.card K * K.index = 360 := by
      rw [← card_of_equiv_alt6 e]
      exact Subgroup.card_mul_index K
    have h6 : 6 ≤ K.index := by
      by_contra hlt0
      have hlt : K.index < 6 := not_le.mp hlt0
      let φ := MulAction.toPermHom Γ (Γ ⧸ K)
      have hker : φ.ker = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
        · exact h
        · exfalso
          apply htop
          rw [eq_top_iff]
          intro g _
          have hg : φ g = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
          have h1 : φ g (((1 : Γ) : Γ ⧸ K)) = ((1 : Γ) : Γ ⧸ K) := by rw [hg]; rfl
          have h2 : ((g : Γ) : Γ ⧸ K) = ((1 : Γ) : Γ ⧸ K) := by
            have : φ g (((1 : Γ) : Γ ⧸ K)) = ((g * 1 : Γ) : Γ ⧸ K) := rfl
            rw [this, mul_one] at h1
            exact h1
          have := QuotientGroup.eq.mp h2
          simpa using this
      have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
      have hle := Nat.card_le_card_of_injective φ hinj
      rw [Nat.card_perm, card_of_equiv_alt6 e] at hle
      have hq : Nat.card (Γ ⧸ K) = K.index := rfl
      rw [hq] at hle
      interval_cases (K.index) <;> simp [Nat.factorial] at hle
    have hcases : ∀ n : ℕ, K.index = n → (n = 8 ∨ n = 9 ∨ n = 18) → False := by
      intro n hn hn'
      have hKm : Nat.card (K.map e.toMonoidHom) = Nat.card K :=
        Subgroup.card_map_of_injective e.injective
      refine no_subgroup_order (K := K.map e.toMonoidHom) ?_
      rw [hKm]
      rcases hn' with rfl | rfl | rfl <;> rw [hn] at hmul <;> omega
    refine ⟨h6, hdvd, fun h => hcases 8 h (Or.inl rfl), fun h => hcases 9 h (Or.inr (Or.inl rfl)),
      fun h => hcases 18 h (Or.inr (Or.inr rfl))⟩

theorem orbit_card_cases' {X : Type*} (φ : Γ →* Perm X) (e : Γ ≃* alternatingGroup (Fin 6)) (x : X) :
    {y | ∃ g, φ g x = y}.ncard = 1 ∨
      (6 ≤ {y | ∃ g, φ g x = y}.ncard ∧ {y | ∃ g, φ g x = y}.ncard ∣ 360 ∧
        {y | ∃ g, φ g x = y}.ncard ≠ 8 ∧ {y | ∃ g, φ g x = y}.ncard ≠ 9 ∧
        {y | ∃ g, φ g x = y}.ncard ≠ 18) := by
  let _ : MulAction Γ X := MulAction.compHom X φ
  exact orbit_card_cases e x

end Orbits

end CFSG.QuasithinUnique.Setup.X3
