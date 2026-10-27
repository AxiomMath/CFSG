module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Loc
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.A5.Kc3J
  CFSG.QuasithinUnique.A5.Kc3NSC CFSG.QuasithinUnique.Unc25G2

section Arith

theorem span5 : ∀ j ∈ ({1, 2, 3, 4} : Finset ℕ), ∀ w : Fin 5 → ZMod 2, ∑ i, w i = 0 → w ≠ 0 →
    ∀ u : Fin 5 → ZMod 2, ∑ i, u i = 0 →
      ∃ S : Finset (Fin 5), u = ∑ k ∈ S, Delta5.pact (Delta5.a0 ^ (j * (k : ℕ))) w := by
  decide +kernel

theorem sum5_zero : ∀ j ∈ ({1, 2, 3, 4} : Finset ℕ), ∀ w : Fin 5 → ZMod 2, ∑ i, w i = 0 →
    ∑ k : Fin 5, Delta5.pact (Delta5.a0 ^ (j * (k : ℕ))) w = 0 := by
  decide +kernel

theorem inv_mod5 : ∀ i ∈ ({1, 2, 3, 4} : Finset ℕ),
    ∃ i' ∈ ({1, 2, 3, 4} : Finset ℕ), i * i' % 5 = 1 := by
  decide +kernel

theorem mul_mod5 : ∀ j ∈ ({1, 2, 3, 4} : Finset ℕ), ∀ i' ∈ ({1, 2, 3, 4} : Finset ℕ),
    j * i' % 5 ∈ ({1, 2, 3, 4} : Finset ℕ) := by
  decide +kernel

theorem w0_ne_zero : (⟨Delta5.w0, Delta5.w0_mem⟩ : ↥(evenWeight 5)) ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  revert this
  decide +kernel

theorem five_part {K : Type} [Group K] [Finite K] (h25 : ¬ 25 ∣ Nat.card K) (l : K)
    (h5l : 5 ∣ orderOf l) : ∃ r : ℕ, ¬ 5 ∣ r ∧ orderOf (l ^ r) = 5 := by
  have hl0 : orderOf l ≠ 0 := (orderOf_pos l).ne'
  obtain ⟨e, r, hr5, hr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hl0 5 (by norm_num)
  have hr0 : r ≠ 0 := fun h => hr5 (h ▸ dvd_zero 5)
  have hlpow : orderOf (l ^ r) = 5 ^ e := by
    have hrdvd : r ∣ orderOf l := ⟨5 ^ e, by rw [hr]; ring⟩
    rw [orderOf_pow_of_dvd hr0 hrdvd]
    conv_lhs => rw [hr]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hr0)
  have h5e : e = 1 := by
    have hdvd : 5 ^ e ∣ Nat.card K := hlpow ▸ orderOf_dvd_natCard (l ^ r)
    have he1 : e ≤ 1 := by
      by_contra h
      have h2 : (25 : ℕ) ∣ 5 ^ e := by
        have := pow_dvd_pow 5 (show 2 ≤ e by omega)
        norm_num at this
        exact this
      exact h25 (dvd_trans h2 hdvd)
    have he0 : e ≠ 0 := by
      rintro rfl
      apply hr5
      simpa [hr] using h5l
    omega
  subst h5e
  exact ⟨r, hr5, by simpa using hlpow⟩

theorem exists_conj_pow {K : Type} [Group K] [Finite K] (h25 : ¬ 25 ∣ Nat.card K) {x x₀ : K}
    (hx : orderOf x = 5) (hx₀ : orderOf x₀ = 5) :
    ∃ (c : K) (i : ℕ), i ∈ ({1, 2, 3, 4} : Finset ℕ) ∧ c * x * c⁻¹ = x₀ ^ i := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : ∀ {z : K}, orderOf z = 5 →
      IsPGroup 5 (Subgroup.zpowers z) ∧ ¬ 5 ∣ (Subgroup.zpowers z).index := by
    intro z hz
    refine ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz]; norm_num), ?_⟩
    intro hdvd
    apply h25
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers z)
    rw [Nat.card_zpowers, hz] at h1
    obtain ⟨m, hm⟩ := hdvd
    rw [← h1, hm]
    exact ⟨m, by ring⟩
  obtain ⟨hP, hPi⟩ := hcard hx
  obtain ⟨hP₀, hP₀i⟩ := hcard hx₀
  obtain ⟨c, hc⟩ := exists_conj_map_eq hP hPi hP₀ hP₀i
  have hmem : c * x * c⁻¹ ∈ Subgroup.zpowers x₀ := by
    rw [← hc]
    exact ⟨x, Subgroup.mem_zpowers x, rfl⟩
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hmod : x₀ ^ i = x₀ ^ (i % (5 : ℤ)) := by
    rw [← zpow_mod_orderOf, hx₀]
    simp
  have hnn : 0 ≤ i % (5 : ℤ) := Int.emod_nonneg _ (by norm_num)
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
  have hn5 : n < 5 := by
    have := Int.emod_lt_of_pos i (by norm_num : (0 : ℤ) < 5)
    omega
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hx1
    have : c * x * c⁻¹ = 1 := by
      rw [← hi, hmod, hn]
      simp
    have h2 : x = c⁻¹ * (c * x * c⁻¹) * c := by group
    rw [h2, this]
    group
  refine ⟨c, n, ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · rw [← hi, hmod, hn]
    simp

end Arith

section Five

variable {K : Type} [Group K] {E : Subgroup K}
  (β : ↥E ≃* Multiplicative ↥(evenWeight 5))

theorem toAdd_psi_pow (x : ↥(Subgroup.normalizer (E : Set K))) (τ : Equiv.Perm (Fin 5))
    (hψ : psi β x = permHom τ) (k : ℕ) (y : ↥E) :
    Multiplicative.toAdd (psi β (x ^ k) (β y)) =
      Delta5.vact (τ ^ k) (Multiplicative.toAdd (β y)) := by
  rw [map_pow, hψ, ← map_pow, permHom_apply]
  simp

theorem coe_conj_psi (x : ↥(Subgroup.normalizer (E : Set K))) (y : ↥E) :
    ((β.symm (psi β x (β y)) : ↥E) : K) = (x : K) * (y : K) * (x : K)⁻¹ := by
  have := psi_spec β x (β y)
  rwa [MulEquiv.symm_apply_apply] at this

theorem E_le_closure (x : K) (hx : x ∈ Subgroup.normalizer (E : Set K)) (j : ℕ)
    (hj : j ∈ ({1, 2, 3, 4} : Finset ℕ)) (hψ : psi β ⟨x, hx⟩ = permHom (Delta5.a0 ^ j))
    (y : ↥E) (hy1 : y ≠ 1) (u : ↥E) :
    (u : K) ∈ Subgroup.closure
      {z : K | ∃ k : Fin 5, z = x ^ (k : ℕ) * (y : K) * (x ^ (k : ℕ))⁻¹} := by
  classical
  set X : ↥(Subgroup.normalizer (E : Set K)) := ⟨x, hx⟩ with hX
  set w : ↥(evenWeight 5) := Multiplicative.toAdd (β y) with hw
  have hw0 : (w : Fin 5 → ZMod 2) ≠ 0 := by
    intro h0
    apply hy1
    apply β.injective
    have : w = 0 := Subtype.ext h0
    rw [map_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact this
  obtain ⟨S, hS⟩ := span5 j hj w.1 w.2 hw0 (Multiplicative.toAdd (β u)).1
    (Multiplicative.toAdd (β u)).2
  have hprod : β u = ∏ k ∈ S, psi β (X ^ (k : ℕ)) (β y) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    simp_rw [toAdd_psi_pow β X (Delta5.a0 ^ j) hψ]
    apply Subtype.ext
    rw [hS, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← pow_mul]
    rfl
  have key : ∀ T : Finset (Fin 5), ∃ t : ↥E, (t : K) ∈ Subgroup.closure
      {z : K | ∃ k : Fin 5, z = x ^ (k : ℕ) * (y : K) * (x ^ (k : ℕ))⁻¹} ∧
      β t = ∏ k ∈ T, psi β (X ^ (k : ℕ)) (β y) := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | insert k T hk ih =>
      obtain ⟨t, ht, hβt⟩ := ih
      refine ⟨β.symm (psi β (X ^ (k : ℕ)) (β y)) * t, ?_, ?_⟩
      · rw [Subgroup.coe_mul, coe_conj_psi]
        refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨k, ?_⟩) ht
        simp [hX]
      · rw [Finset.prod_insert hk, map_mul, MulEquiv.apply_symm_apply, hβt]
  obtain ⟨t, ht, hβt⟩ := key S
  have : u = t := β.injective (hprod.trans hβt.symm)
  rw [this]
  exact ht

theorem prod5_eq_one (x : K) (hx : x ∈ Subgroup.normalizer (E : Set K)) (j : ℕ)
    (hj : j ∈ ({1, 2, 3, 4} : Finset ℕ)) (hψ : psi β ⟨x, hx⟩ = permHom (Delta5.a0 ^ j))
    (y : ↥E) :
    (x ^ (0 : ℕ) * (y : K) * (x ^ (0 : ℕ))⁻¹) * (x ^ (1 : ℕ) * (y : K) * (x ^ (1 : ℕ))⁻¹) *
      (x ^ (2 : ℕ) * (y : K) * (x ^ (2 : ℕ))⁻¹) * (x ^ (3 : ℕ) * (y : K) * (x ^ (3 : ℕ))⁻¹) *
      (x ^ (4 : ℕ) * (y : K) * (x ^ (4 : ℕ))⁻¹) = 1 := by
  classical
  set X : ↥(Subgroup.normalizer (E : Set K)) := ⟨x, hx⟩ with hX
  have hu : ∀ k : ℕ, x ^ k * (y : K) * (x ^ k)⁻¹ =
      ((β.symm (psi β (X ^ k) (β y)) : ↥E) : K) := by
    intro k
    rw [coe_conj_psi β (X ^ k) y]
    simp [hX]
  rw [hu 0, hu 1, hu 2, hu 3, hu 4]
  have hD : psi β (X ^ 0) (β y) * psi β (X ^ 1) (β y) * psi β (X ^ 2) (β y) *
      psi β (X ^ 3) (β y) * psi β (X ^ 4) (β y) = 1 := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_one]
    simp only [toAdd_psi_pow β X (Delta5.a0 ^ j) hψ]
    apply Subtype.ext
    have h5 := sum5_zero j hj (Multiplicative.toAdd (β y)).1 (Multiplicative.toAdd (β y)).2
    rw [Fin.sum_univ_five] at h5
    simp only [← pow_mul] at *
    simpa [Delta5.vact] using h5
  have key : β.symm (psi β (X ^ 0) (β y)) * β.symm (psi β (X ^ 1) (β y)) *
      β.symm (psi β (X ^ 2) (β y)) * β.symm (psi β (X ^ 3) (β y)) *
      β.symm (psi β (X ^ 4) (β y)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hD, map_one]
  have := congrArg Subtype.val key
  simpa using this

theorem orderOf_a0 : orderOf (Delta5.a0 : Equiv.Perm (Fin 5)) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem exists_order_five [Finite K] (h25 : ¬ 25 ∣ Nat.card K) (hact : Delta5Norm E β) :
    ∃ (x : K) (hx : x ∈ Subgroup.normalizer (E : Set K)), orderOf x = 5 ∧
      ∃ j ∈ ({1, 2, 3, 4} : Finset ℕ), psi β ⟨x, hx⟩ = permHom (Delta5.a0 ^ j) := by
  have ha := Equiv.Perm.mem_alternatingGroup.1 Delta5.a0_alt
  obtain ⟨l, hlN, hl⟩ := hact _ ha
  have hψ := psi_eq_permHom β hlN hl
  have hoψ : orderOf (permHom Delta5.a0 : MulAut Dm) = 5 := by
    rw [orderOf_injective permHom permHom_injective, orderOf_a0]
  have h5l : 5 ∣ orderOf l := by
    have h1 : orderOf (psi β ⟨l, hlN⟩) ∣ orderOf (⟨l, hlN⟩ : ↥(Subgroup.normalizer (E : Set K))) :=
      orderOf_map_dvd _ _
    rw [hψ, hoψ, Subgroup.orderOf_mk] at h1
    exact h1
  obtain ⟨r, hr5, hr⟩ := five_part h25 l h5l
  refine ⟨l ^ r, pow_mem hlN r, hr, r % 5, ?_, ?_⟩
  · have h1 : r % 5 ≠ 0 := fun h => hr5 (Nat.dvd_of_mod_eq_zero h)
    have h2 : r % 5 < 5 := Nat.mod_lt _ (by norm_num)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · have hxe : (⟨l ^ r, pow_mem hlN r⟩ : ↥(Subgroup.normalizer (E : Set K))) =
        ⟨l, hlN⟩ ^ r := Subtype.ext (by simp)
    rw [hxe, map_pow, hψ, ← map_pow]
    congr 1
    rw [← pow_mod_orderOf, orderOf_a0]

theorem exists_x_conj [Finite K] (x₀ : K) (hx₀ : orderOf x₀ = 5) (h25 : ¬ 25 ∣ Nat.card K)
    (hact : Delta5Norm E β) :
    ∃ (c x : K) (hx : x ∈ Subgroup.normalizer (E : Set K)), orderOf x = 5 ∧ c * x * c⁻¹ = x₀ ∧
      ∃ j ∈ ({1, 2, 3, 4} : Finset ℕ), psi β ⟨x, hx⟩ = permHom (Delta5.a0 ^ j) := by
  obtain ⟨x, hx, hx5, j, hj, hψ⟩ := exists_order_five β h25 hact
  obtain ⟨c, i, hi, hcx⟩ := exists_conj_pow h25 hx5 hx₀
  obtain ⟨i', hi', hii'⟩ := inv_mod5 i hi
  refine ⟨c, x ^ i', pow_mem hx i', ?_, ?_, (j * i') % 5, mul_mod5 j hj i' hi', ?_⟩
  · have hcop : Nat.Coprime (orderOf x) i' := by
      rw [hx5]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
      rcases hi' with rfl | rfl | rfl | rfl <;> decide
    rw [hcop.orderOf_pow, hx5]
  · have h1 : c * x ^ i' * c⁻¹ = (c * x * c⁻¹) ^ i' := (conj_pow).symm
    rw [h1, hcx, ← pow_mul, ← pow_mod_orderOf, hx₀, hii', pow_one]
  · have hxe : (⟨x ^ i', pow_mem hx i'⟩ : ↥(Subgroup.normalizer (E : Set K))) =
        ⟨x, hx⟩ ^ i' := Subtype.ext (by simp)
    rw [hxe, map_pow, hψ, ← map_pow, ← pow_mul]
    congr 1
    rw [← pow_mod_orderOf, orderOf_a0]

end Five

section Gen

theorem closure_conj_gen {K : Type} [Group K] (E : Subgroup K) (x x₀ y₁ c : K)
    (hcx : c * x * c⁻¹ = x₀) (hx : x ∈ Subgroup.normalizer (E : Set K)) (hy₁ : y₁ ∈ E)
    (hgen : ∀ u ∈ E, u ∈ Subgroup.closure
      {z : K | ∃ k : Fin 5, z = x ^ (k : ℕ) * y₁ * (x ^ (k : ℕ))⁻¹}) :
    E.map (MulAut.conj c).toMonoidHom =
      Subgroup.closure
        {z : K | ∃ k : Fin 5, z = x₀ ^ (k : ℕ) * (c * y₁ * c⁻¹) * (x₀ ^ (k : ℕ))⁻¹} ∧
    ∀ k : ℕ, x₀ ^ k * (c * y₁ * c⁻¹) * (x₀ ^ k)⁻¹ ∈ E.map (MulAut.conj c).toMonoidHom := by
  have hy'E : c * y₁ * c⁻¹ ∈ E.map (MulAut.conj c).toMonoidHom := ⟨y₁, hy₁, rfl⟩
  have hx₀N : x₀ ∈ Subgroup.normalizer
      ((E.map (MulAut.conj c).toMonoidHom : Subgroup K) : Set K) := by
    rw [← hcx]
    exact (mem_normalizer_map (MulAut.conj c : K ≃* K) x).2 hx
  have hmem : ∀ k : ℕ, x₀ ^ k * (c * y₁ * c⁻¹) * (x₀ ^ k)⁻¹ ∈
      E.map (MulAut.conj c).toMonoidHom := fun k =>
    (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ hx₀N k) _).1 hy'E
  refine ⟨le_antisymm ?_ ?_, hmem⟩
  · rintro _ ⟨u, hu, rfl⟩
    have h1 := hgen u hu
    have h2 : (MulAut.conj c).toMonoidHom u ∈
        (Subgroup.closure {z : K | ∃ k : Fin 5, z = x ^ (k : ℕ) * y₁ * (x ^ (k : ℕ))⁻¹}).map
          (MulAut.conj c).toMonoidHom := ⟨u, h1, rfl⟩
    rw [MonoidHom.map_closure] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨k, ?_⟩
    have h3 : (c * x * c⁻¹) ^ (k : ℕ) = c * x ^ (k : ℕ) * c⁻¹ := by
      rw [conj_pow]
    rw [← hcx, h3]
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    group
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact hmem k

end Gen

section Main

variable {K : Type} [Group K] {E : Subgroup K}
  (β : ↥E ≃* Multiplicative ↥(evenWeight 5))

theorem exists_conj_closure [Finite K] (x₀ : K) (hx₀ : orderOf x₀ = 5) (h25 : ¬ 25 ∣ Nat.card K)
    (I : Set K) (hI : ∀ t : K, t * t = 1 → t ≠ 1 → t ∈ I) (hact : Delta5Norm E β) :
    ∃ (c y : K), y ∈ I ∧
      E.map (MulAut.conj c).toMonoidHom =
        Subgroup.closure {z : K | ∃ k : Fin 5, z = x₀ ^ (k : ℕ) * y * (x₀ ^ (k : ℕ))⁻¹} ∧
      (∀ k l : ℕ, (x₀ ^ k * y * (x₀ ^ k)⁻¹) * (x₀ ^ l * y * (x₀ ^ l)⁻¹) =
        (x₀ ^ l * y * (x₀ ^ l)⁻¹) * (x₀ ^ k * y * (x₀ ^ k)⁻¹)) ∧
      (x₀ ^ (0 : ℕ) * y * (x₀ ^ (0 : ℕ))⁻¹) * (x₀ ^ (1 : ℕ) * y * (x₀ ^ (1 : ℕ))⁻¹) *
        (x₀ ^ (2 : ℕ) * y * (x₀ ^ (2 : ℕ))⁻¹) * (x₀ ^ (3 : ℕ) * y * (x₀ ^ (3 : ℕ))⁻¹) *
        (x₀ ^ (4 : ℕ) * y * (x₀ ^ (4 : ℕ))⁻¹) = 1 := by
  classical
  obtain ⟨c, x, hx, hx5, hcx, j, hj, hψ⟩ := exists_x_conj β x₀ hx₀ h25 hact
  set w₀ : ↥(evenWeight 5) := ⟨Delta5.w0, Delta5.w0_mem⟩ with hw₀
  set y₁ : ↥E := β.symm (Multiplicative.ofAdd w₀) with hy₁
  have hβy : β y₁ = Multiplicative.ofAdd w₀ := by simp [hy₁]
  have hy₁ne : y₁ ≠ 1 := by
    intro h1
    have h2 : Multiplicative.ofAdd w₀ = 1 := by rw [← hβy, h1, map_one]
    have h3 : w₀ = 0 := by simpa using h2
    exact w0_ne_zero h3
  have hy₁sq : (y₁ : K) * y₁ = 1 := by
    have h1 : y₁ * y₁ = 1 := by
      apply β.injective
      rw [map_mul, map_one, hβy]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_ofAdd, toAdd_one]
      exact Kc3L3.add_self_evenWeight _
    exact congrArg Subtype.val h1
  have hy₁ne' : (y₁ : K) ≠ 1 := fun h => hy₁ne (Subtype.ext h)
  have hy'sq : (c * y₁ * c⁻¹) * (c * y₁ * c⁻¹) = 1 := by
    calc (c * y₁ * c⁻¹) * (c * y₁ * c⁻¹) = c * ((y₁ : K) * y₁) * c⁻¹ := by group
      _ = 1 := by rw [hy₁sq]; group
  have hy'ne : c * (y₁ : K) * c⁻¹ ≠ 1 := by
    intro h
    apply hy₁ne'
    have : (y₁ : K) = c⁻¹ * (c * y₁ * c⁻¹) * c := by group
    rw [this, h]
    group
  obtain ⟨hcl, hmem⟩ := closure_conj_gen E x x₀ y₁ c hcx hx y₁.2
    (fun u hu => E_le_closure β x hx j hj hψ y₁ hy₁ne ⟨u, hu⟩)
  refine ⟨c, c * y₁ * c⁻¹, hI _ hy'sq hy'ne, hcl, ?_, ?_⟩
  · intro k l
    obtain ⟨u₁, hu₁, h₁⟩ := hmem k
    obtain ⟨u₂, hu₂, h₂⟩ := hmem l
    rw [← h₁, ← h₂, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (comm_of_beta β ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩)
  · have h : ∀ k : ℕ, x₀ ^ k * (c * y₁ * c⁻¹) * (x₀ ^ k)⁻¹ =
        c * (x ^ k * y₁ * (x ^ k)⁻¹) * c⁻¹ := by
      intro k
      rw [← hcx, conj_pow]
      group
    rw [h 0, h 1, h 2, h 3, h 4]
    have hp := prod5_eq_one β x hx j hj hψ y₁
    calc _ = c * ((x ^ (0 : ℕ) * (y₁ : K) * (x ^ (0 : ℕ))⁻¹) *
          (x ^ (1 : ℕ) * (y₁ : K) * (x ^ (1 : ℕ))⁻¹) * (x ^ (2 : ℕ) * (y₁ : K) * (x ^ (2 : ℕ))⁻¹) *
          (x ^ (3 : ℕ) * (y₁ : K) * (x ^ (3 : ℕ))⁻¹) *
          (x ^ (4 : ℕ) * (y₁ : K) * (x ^ (4 : ℕ))⁻¹)) * c⁻¹ := by group
      _ = 1 := by rw [hp]; group

end Main

end CFSG.QuasithinUnique.A5
