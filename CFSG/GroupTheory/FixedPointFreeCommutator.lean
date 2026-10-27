module

public import Mathlib.GroupTheory.FixedPointFree

public section

open scoped commutatorElement

namespace CFSG

theorem centralizes_of_fixed_of_card_four {G : Type*} [Group G] {T : Subgroup G} {b : G}
    (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hsq : ∀ x ∈ T, x ^ 2 = 1) (hcard : Nat.card ↥T = 4)
    (hN : b ∈ Subgroup.normalizer (T : Set G))
    (hb3 : b ^ 3 ∈ Subgroup.centralizer (T : Set G))
    {t : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hfix : b * t * b⁻¹ = t) :
    ∀ z ∈ T, b * z * b⁻¹ = z := by
  classical
  haveI : Finite ↥T := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  set σ : MulAut ↥T := Subgroup.normalizerMonoidHom T ⟨b, hN⟩ with hσdef
  have hσcoe : ∀ z : ↥T, ((σ z : ↥T) : G) = b * (z : G) * b⁻¹ := fun z =>
    Subgroup.normalizerMonoidHom_apply_apply_coe T ⟨b, hN⟩ z
  have htT : (⟨t, ht⟩ : ↥T) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hσt : σ ⟨t, ht⟩ = ⟨t, ht⟩ := by
    apply Subtype.ext
    rw [hσcoe]
    exact hfix
  set H : Subgroup ↥T := Subgroup.zpowers ⟨t, ht⟩ with hHdef
  have hHfix : ∀ y ∈ H, σ y = y := by
    rintro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [map_zpow, hσt]
  have hHfix_inv : ∀ y ∈ H, σ⁻¹ y = y := by
    intro y hy
    calc σ⁻¹ y = σ⁻¹ (σ y) := by rw [hHfix y hy]
      _ = y := by simp
  have hfixT : ∀ z ∈ T, b * z * b⁻¹ = z := by
    by_cases hHtop : H = ⊤
    ·
      have hσ1 : σ = 1 := by
        refine MulEquiv.ext fun z => ?_
        exact hHfix z (by rw [hHtop]; exact Subgroup.mem_top z)
      intro z hz
      have h := congrArg (fun f : MulAut ↥T => ((f ⟨z, hz⟩ : ↥T) : G)) hσ1
      simpa [hσcoe] using h
    ·
      have hHne : H ≠ ⊥ := by
        intro hbot
        have hmem : (⟨t, ht⟩ : ↥T) ∈ (⊥ : Subgroup ↥T) := by
          rw [← hbot]
          exact Subgroup.mem_zpowers _
        rw [Subgroup.mem_bot] at hmem
        exact htT hmem
      have hHcard2 : 2 ≤ Nat.card ↥H := by
        haveI hnt : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).2 hHne
        exact Finite.one_lt_card
      have hHpos : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hne1 : H.index ≠ 1 := by
        intro hone
        exact hHtop ((Subgroup.index_eq_one).1 hone)
      have hpos : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hcardH : Nat.card ↥H = 2 := by
        have h1 := Subgroup.index_mul_card H
        rw [hcard] at h1
        rcases Nat.lt_or_ge (Nat.card ↥H) 2 with hlt | hge
        · omega
        · by_contra hne
          have h3 : 3 ≤ Nat.card ↥H := by omega
          have hge2 : 2 ≤ H.index := by omega
          have hle := Nat.mul_le_mul hge2 h3
          omega
      have hHindex : H.index = 2 := by
        have h1 := Subgroup.index_mul_card H
        rw [hcard, hcardH] at h1
        omega
      obtain ⟨a, hxor⟩ := Subgroup.index_eq_two_iff.1 hHindex
      have hza_of : ∀ z : ↥T, z ∉ H → z * a ∈ H := by
        intro z hz
        rcases hxor z with ⟨h1, -⟩ | ⟨h2, -⟩
        · exact h1
        · exact absurd h2 hz
      have hkey : ∀ z : ↥T, σ z * z⁻¹ ∈ H := by
        intro z
        by_cases hzH : z ∈ H
        · rw [hHfix z hzH]
          exact H.mul_mem hzH (H.inv_mem hzH)
        · have hza : z * a ∈ H := hza_of z hzH
          have hσzH : σ z ∉ H := by
            intro hcon
            have h1 : σ⁻¹ (σ z) ∈ H := by
              rw [hHfix_inv (σ z) hcon]
              exact hcon
            rw [show σ⁻¹ (σ z) = z from by simp] at h1
            exact hzH h1
          have hσza : σ z * a ∈ H := hza_of (σ z) hσzH
          have heq : σ z * z⁻¹ = (σ z * a) * (z * a)⁻¹ := by group
          rw [heq]
          exact H.mul_mem hσza (H.inv_mem hza)
      have hσ2 : σ ^ 2 = 1 := by
        refine MulEquiv.ext fun z => ?_
        obtain ⟨h, hhH, hh⟩ : ∃ h ∈ H, σ z = h * z := by
          refine ⟨σ z * z⁻¹, hkey z, ?_⟩
          rw [mul_assoc, inv_mul_cancel, mul_one]
        have hh2 : h * h = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
          exact hsq (h : G) h.2
        rw [pow_two, MulAut.mul_apply, hh, map_mul, hHfix h hhH, hh, ← mul_assoc, hh2, one_mul]
        rfl
      have hσ3 : σ ^ 3 = 1 := by
        refine MulEquiv.ext fun z => ?_
        apply Subtype.ext
        have hc := Subgroup.mem_centralizer_iff.1 hb3 (z : G) z.2
        have hb3' : b ^ 3 = b * (b * b) := by rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ,
          pow_two, mul_assoc]
        rw [hb3'] at hc
        have h3 : ((σ ^ 3) z : ↥T) = σ (σ (σ z)) := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_two]
          rfl
        rw [h3, hσcoe, hσcoe, hσcoe]
        change b * (b * (b * (z : G) * b⁻¹) * b⁻¹) * b⁻¹ = (z : G)
        rw [show b * (b * (b * (z : G) * b⁻¹) * b⁻¹) * b⁻¹ =
          (b * (b * b)) * (z : G) * (b * (b * b))⁻¹ from by group]
        rw [← hc]
        group
      have hσ1 : σ = 1 := by
        have h3 : σ ^ 3 = 1 := hσ3
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, hσ2, one_mul] at h3
        exact h3
      intro z hz
      have h := congrArg (fun f : MulAut ↥T => ((f ⟨z, hz⟩ : ↥T) : G)) hσ1
      simpa [hσcoe] using h
  exact hfixT

theorem exists_eq_conj_mul_inv_of_fixedPointFree {G : Type*} [Group G] {T : Subgroup G} {b : G}
    [Finite T] (hN : b ∈ Subgroup.normalizer (T : Set G))
    (hfree : ∀ t ∈ T, b * t * b⁻¹ = t → t = 1) :
    ∀ t ∈ T, ∃ s ∈ T, t = b * s * b⁻¹ * s⁻¹ := by
  classical
  set φ : T →* T := (Subgroup.normalizerMonoidHom T ⟨b, hN⟩).toMonoidHom with hφdef
  have hφcoe : ∀ t : T, (φ t : G) = b * (t : G) * b⁻¹ := fun t =>
    Subgroup.normalizerMonoidHom_apply_apply_coe T ⟨b, hN⟩ t
  have hφ : MonoidHom.FixedPointFree φ := by
    intro t ht
    apply Subtype.ext
    have hfix : b * (t : G) * b⁻¹ = (t : G) := by
      rw [← hφcoe]
      exact congrArg Subtype.val ht
    have ht1 : (t : G) = 1 := hfree (t : G) t.2 hfix
    rw [ht1, Subgroup.coe_one]
  have hsurj : Function.Surjective (MonoidHom.commutatorMap φ) :=
    MonoidHom.FixedPointFree.commutatorMap_surjective hφ
  intro t ht
  obtain ⟨s, hs⟩ := hsurj (⟨t, ht⟩ : ↥T)⁻¹
  refine ⟨s, s.2, ?_⟩
  have hval : (s : G) * (b * (s : G) * b⁻¹)⁻¹ = (t : G)⁻¹ := by
    have h := congrArg (Subtype.val) hs
    simpa only [MonoidHom.commutatorMap_apply, div_eq_mul_inv, Subgroup.coe_mul,
      Subgroup.coe_inv, hφcoe] using h
  have ht_eq : (t : G) = ((s : G) * (b * (s : G) * b⁻¹)⁻¹)⁻¹ := by
    rw [hval, inv_inv]
  rw [ht_eq]
  group

theorem commutator_zpowers_eq_of_fixedPointFree {G : Type*} [Group G] (T : Subgroup G) (u : G)
    [Finite T] (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (huN : u ∈ Subgroup.normalizer (T : Set G))
    (hfree : ∀ t ∈ T, u * t * u⁻¹ = t → t = 1) :
    ⁅T, Subgroup.zpowers u⁆ = T := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have hyN : y ∈ Subgroup.normalizer (T : Set G) := (Subgroup.zpowers_le.2 huN) hy
    have hconj : y * x⁻¹ * y⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.1 hyN x⁻¹).1 (T.inv_mem hx)
    have h1 : x * (y * x⁻¹ * y⁻¹) ∈ T := T.mul_mem hx hconj
    have h2 : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [commutatorElement_def, h2]
    exact h1
  · intro t ht
    obtain ⟨s, hs, hse⟩ := exists_eq_conj_mul_inv_of_fixedPointFree huN hfree t ht
    have hmem : ⁅(s : G), u⁆ ∈ ⁅T, Subgroup.zpowers u⁆ :=
      Subgroup.commutator_mem_commutator hs (Subgroup.mem_zpowers u)
    have h2 : t = ⁅(s : G), u⁆⁻¹ := by
      rw [hse, commutatorElement_def]
      group
    rw [h2]
    exact inv_mem hmem

theorem fixedPointFree_of_commutator_zpowers_eq_top {G : Type*} [Group G] {T : Subgroup G} {b : G}
    (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hsq : ∀ x ∈ T, x ^ 2 = 1) (hcard : Nat.card ↥T = 4)
    (hN : b ∈ Subgroup.normalizer (T : Set G))
    (hb3 : b ^ 3 ∈ Subgroup.centralizer (T : Set G))
    (h : ⁅T, Subgroup.zpowers b⁆ = T) :
    ∀ t ∈ T, b * t * b⁻¹ = t → t = 1 := by
  intro t ht hfix
  by_contra ht1
  have hcent : ∀ z ∈ T, b * z * b⁻¹ = z :=
    centralizes_of_fixed_of_card_four hT hsq hcard hN hb3 ht ht1 hfix
  have hbot : ⁅T, Subgroup.zpowers b⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hcomm : Commute b x := by
      show b * x = x * b
      calc b * x = (b * x * b⁻¹) * b := by simp [mul_assoc]
        _ = x * b := by rw [hcent x hx]
    exact hcomm.zpow_left n
  rw [h] at hbot
  have h1 : Nat.card ↥T = 1 := by rw [hbot, Subgroup.card_bot]
  omega

theorem exists_eq_conj_mul_inv_of_commutator_zpowers_eq_top {G : Type*} [Group G]
    {T : Subgroup G} {b : G}
    (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hsq : ∀ x ∈ T, x ^ 2 = 1) (hcard : Nat.card ↥T = 4)
    (hN : b ∈ Subgroup.normalizer (T : Set G))
    (hb3 : b ^ 3 ∈ Subgroup.centralizer (T : Set G))
    (h : ⁅T, Subgroup.zpowers b⁆ = T) :
    ∀ t ∈ T, ∃ s ∈ T, t = b * s * b⁻¹ * s⁻¹ := by
  haveI : Finite ↥T := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact exists_eq_conj_mul_inv_of_fixedPointFree hN
    (fixedPointFree_of_commutator_zpowers_eq_top hT hsq hcard hN hb3 h)

end CFSG

end
