module

public import CFSG.GH74.M12.HypGroup
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14

open Subgroup

abbrev B3 : Type := Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)

theorem B3_card : Nat.card B3 = 36 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm]; simp [Nat.factorial]

theorem perm_exp : ∀ σ : Equiv.Perm (Fin 3), σ ^ 6 = 1 := by decide

theorem B3_exp (b : B3) : b ^ 6 = 1 := Prod.ext (perm_exp b.1) (perm_exp b.2)

theorem B3_three_card : Nat.card {b : B3 // b ^ 3 = 1} = 9 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; decide

theorem cent_aux : ∀ τ : Equiv.Perm (Fin 3), τ ≠ 1 → τ * τ = 1 → ∀ σ : Equiv.Perm (Fin 3),
    τ * σ = σ * τ → σ 0 = 0 ∨ σ 0 = τ 0 := by decide

theorem noncomm_aux (τ σ₀ σ₁ : Equiv.Perm (Fin 3)) (h1 : τ ≠ 1) (h2 : τ * τ = 1)
    (e₀ : σ₀ 0 = 1) (e₁ : σ₁ 0 = 2) : ¬ (τ * σ₀ = σ₀ * τ ∧ τ * σ₁ = σ₁ * τ) := by
  rintro ⟨c₀, c₁⟩
  have a₀ := cent_aux τ h1 h2 σ₀ c₀
  have a₁ := cent_aux τ h1 h2 σ₁ c₁
  rw [e₀] at a₀
  rw [e₁] at a₁
  revert a₀ a₁
  generalize τ 0 = t
  revert t
  decide

theorem fpf_aux : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 → σ ^ 3 = 1 → ∀ i, σ i ≠ i := by decide

theorem omega_aux : ((finRotate 3 : Equiv.Perm (Fin 3)), (finRotate 3 : Equiv.Perm (Fin 3))⁻¹) ^ 3
    = (1 : B3) ∧ (finRotate 3 : Equiv.Perm (Fin 3)) 2 = 0 ∧
    ((finRotate 3 : Equiv.Perm (Fin 3))⁻¹) 1 = 0 := by decide

theorem order_cases : ∀ m < 19, m ∣ 18 → Odd m → m = 1 ∨ m = 3 ∨ m = 9 := by decide

variable (H : Subgroup B3)

theorem card_eq_six (h2 : ∃ m, Odd m ∧ Nat.card H = 2 * m)
    (ht1 : ∀ i, ∃ h ∈ H, h.1 0 = i)
    (hT2 : ∀ h ∈ H, ¬ (h.1 2 = 0 ∧ h.2 1 = 0)) : Nat.card H = 6 := by
  obtain ⟨m, hm, hcard⟩ := h2
  have hdvd : Nat.card H ∣ 36 := B3_card ▸ H.card_subgroup_dvd_card
  have hm18 : m ∣ 18 := by
    rw [hcard] at hdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 (by simpa using hdvd)
  have hm19 : m < 19 := Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hm18)
  have hsurj : Function.Surjective (fun h : H => h.1.1 0) := by
    intro i
    obtain ⟨h, hh, e⟩ := ht1 i
    exact ⟨⟨h, hh⟩, e⟩
  have h3 : 3 ≤ Nat.card H := by
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa using this
  rcases order_cases m hm19 hm18 hm with rfl | rfl | rfl
  · omega
  · omega
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := 2)
      (by rw [hcard]; norm_num)
    let K' : Subgroup B3 := K.map H.subtype
    have hK' : Nat.card K' = 9 := by
      rw [Subgroup.card_map_of_injective H.subtype_injective, hK]; norm_num
    have hsub : (K' : Set B3) ⊆ {b : B3 | b ^ 3 = 1} := by
      rintro _ ⟨k, hk, rfl⟩
      have h9 : (k : H) ^ 9 = 1 := by
        have := pow_card_eq_one' (G := K) (x := (⟨k, hk⟩ : K))
        rw [hK] at this
        have := congrArg (fun t : K => ((t : H))) this
        simpa using this
      have h6 : ((k : H) : B3) ^ 6 = 1 := B3_exp _
      have h9' : ((k : H) : B3) ^ 9 = 1 := by
        have := congrArg (fun t : H => (t : B3)) h9
        simpa using this
      have := pow_gcd_eq_one.2 ⟨h6, h9'⟩
      have e : Nat.gcd 6 9 = 3 := by norm_num
      rw [e] at this
      exact this
    have hcardle : Set.ncard {b : B3 | b ^ 3 = 1} ≤ Set.ncard (K' : Set B3) := by
      have h1 : Set.ncard {b : B3 | b ^ 3 = 1} = 9 := by
        rw [← Nat.card_coe_set_eq]
        exact B3_three_card
      have h2 : Set.ncard (K' : Set B3) = 9 := by
        rw [← Nat.card_coe_set_eq]
        exact hK'
      omega
    have heq := Set.eq_of_subset_of_ncard_le hsub hcardle (Set.toFinite _)
    obtain ⟨hω3, hω1, hω2⟩ := omega_aux
    have hωmem : ((finRotate 3 : Equiv.Perm (Fin 3)), (finRotate 3 : Equiv.Perm (Fin 3))⁻¹) ∈
        (K' : Set B3) := by
      rw [heq]; exact hω3
    obtain ⟨k, _, hk⟩ := hωmem
    have hk' : (k : B3) = ((finRotate 3 : Equiv.Perm (Fin 3)),
        (finRotate 3 : Equiv.Perm (Fin 3))⁻¹) := hk
    exact hT2 _ k.2 ⟨by rw [hk']; exact hω1, by rw [hk']; exact hω2⟩

theorem exists_noncomm (hdvd : 2 ∣ Nat.card H) (ht1 : ∀ i, ∃ h ∈ H, h.1 0 = i)
    (ht2 : ∀ i, ∃ h ∈ H, h.2 0 = i) : ∃ a b : H, a * b ≠ b * a := by
  by_contra hnc
  have hcomm : ∀ a b : H, a * b = b * a := fun a b => by
    by_contra hne
    exact hnc ⟨a, b, hne⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 hdvd
  have hs2 : s * s = 1 := by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 (hs ▸ dvd_rfl)
  have hs1 : s ≠ 1 := fun e => by rw [e, orderOf_one] at hs; omega
  obtain ⟨h₀, hh₀, e₀⟩ := ht1 1
  obtain ⟨h₁, hh₁, e₁⟩ := ht1 2
  obtain ⟨k₀, hk₀, f₀⟩ := ht2 1
  obtain ⟨k₁, hk₁, f₁⟩ := ht2 2
  have c := fun t : H => congrArg (fun u : H => (u : B3)) (hcomm s t)
  have s1 : (s : B3).1 = 1 := by
    by_contra hne
    have := noncomm_aux (s : B3).1 h₀.1 h₁.1 hne (by
        have := congrArg (fun u : H => ((u : B3)).1) hs2
        simpa using this) e₀ e₁
    apply this
    have c0 := c ⟨h₀, hh₀⟩
    have c1 := c ⟨h₁, hh₁⟩
    exact ⟨by simpa using congrArg Prod.fst c0, by simpa using congrArg Prod.fst c1⟩
  have s2 : (s : B3).2 = 1 := by
    by_contra hne
    have := noncomm_aux (s : B3).2 k₀.2 k₁.2 hne (by
        have := congrArg (fun u : H => ((u : B3)).2) hs2
        simpa using this) f₀ f₁
    apply this
    have c0 := c ⟨k₀, hk₀⟩
    have c1 := c ⟨k₁, hk₁⟩
    exact ⟨by simpa using congrArg Prod.snd c0, by simpa using congrArg Prod.snd c1⟩
  apply hs1
  apply Subtype.ext
  exact Prod.ext s1 s2

theorem fixed_point_free_of_order_three (h6 : Nat.card H = 6) (ht1 : ∀ i, ∃ h ∈ H, h.1 0 = i)
    {u : B3} (hu : u ∈ H) (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1) : ∀ i, u.1 i ≠ i := by
  have hu13 : u.1 ^ 3 = 1 := by simpa using congrArg Prod.fst hu3
  suffices hne : u.1 ≠ 1 from fpf_aux u.1 hne hu13
  intro hu1'
  let φ : H →* Equiv.Perm (Fin 3) := (MonoidHom.fst _ _).comp H.subtype
  let _ : MulAction H (Fin 3) := MulAction.compHom (Fin 3) φ
  have horb : MulAction.orbit H (0 : Fin 3) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    obtain ⟨h, hh, e⟩ := ht1 i
    exact ⟨⟨h, hh⟩, e⟩
  have hcardorb : Nat.card (MulAction.orbit H (0 : Fin 3)) = 3 := by
    rw [horb, Nat.card_univ]; simp
  have hos := Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer H (0 : Fin 3))
  rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H (0 : Fin 3)), hcardorb, h6] at hos
  have hst : Nat.card (MulAction.stabilizer H (0 : Fin 3)) = 2 := by omega
  have hmem : (⟨u, hu⟩ : H) ∈ MulAction.stabilizer H (0 : Fin 3) := by
    show φ ⟨u, hu⟩ 0 = 0
    show u.1 0 = 0
    rw [hu1']; rfl
  have hord := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hst] at hord
  have hsq : (⟨u, hu⟩ : H) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hord
  have hu2 : u ^ 2 = 1 := by
    have := congrArg (fun t : H => (t : B3)) hsq
    simpa using this
  apply hu1
  calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
    _ = 1 := by rw [hu3, hu2]; group

theorem fixed_point_free_of_order_three_snd (h6 : Nat.card H = 6) (ht2 : ∀ i, ∃ h ∈ H, h.2 0 = i)
    {u : B3} (hu : u ∈ H) (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1) : ∀ i, u.2 i ≠ i := by
  have hu13 : u.2 ^ 3 = 1 := by simpa using congrArg Prod.snd hu3
  suffices hne : u.2 ≠ 1 from fpf_aux u.2 hne hu13
  intro hu1'
  let φ : H →* Equiv.Perm (Fin 3) := (MonoidHom.snd _ _).comp H.subtype
  let _ : MulAction H (Fin 3) := MulAction.compHom (Fin 3) φ
  have horb : MulAction.orbit H (0 : Fin 3) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    obtain ⟨h, hh, e⟩ := ht2 i
    exact ⟨⟨h, hh⟩, e⟩
  have hcardorb : Nat.card (MulAction.orbit H (0 : Fin 3)) = 3 := by
    rw [horb, Nat.card_univ]; simp
  have hos := Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer H (0 : Fin 3))
  rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H (0 : Fin 3)), hcardorb, h6] at hos
  have hst : Nat.card (MulAction.stabilizer H (0 : Fin 3)) = 2 := by omega
  have hmem : (⟨u, hu⟩ : H) ∈ MulAction.stabilizer H (0 : Fin 3) := by
    show φ ⟨u, hu⟩ 0 = 0
    show u.2 0 = 0
    rw [hu1']; rfl
  have hord := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hst] at hord
  have hsq : (⟨u, hu⟩ : H) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hord
  have hu2 : u ^ 2 = 1 := by
    have := congrArg (fun t : H => (t : B3)) hsq
    simpa using this
  apply hu1
  calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
    _ = 1 := by rw [hu3, hu2]; group

theorem exists_equiv_perm_three (h2 : ∃ m, Odd m ∧ Nat.card H = 2 * m)
    (ht1 : ∀ i, ∃ h ∈ H, h.1 0 = i) (ht2 : ∀ i, ∃ h ∈ H, h.2 0 = i)
    (hT2 : ∀ h ∈ H, ¬ (h.1 2 = 0 ∧ h.2 1 = 0)) : Nonempty (↥H ≃* Equiv.Perm (Fin 3)) := by
  have h6 := card_eq_six H h2 ht1 hT2
  obtain ⟨a, b, hab⟩ := exists_noncomm H (by rw [h6]; norm_num) ht1 ht2
  exact CFSG.GH74.M12.Hyp.nonempty_mulEquiv_perm_three_of_card_six h6 a b hab

end CFSG.GH74.GLS.Stage1.Thm6.Sec14
