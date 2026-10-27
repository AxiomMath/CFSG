module

public import CFSG.GH74.GLS.SP.Local.SPLSL2Input
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GH74.GLS.IVK.L2.TorusCentralizer
public import CFSG.GH74.GLS.IVK.L2.TorusMatrices

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74.GLS
open scoped MatrixGroups

namespace SL2One

theorem mem_sup_zpowers_cases {G : Type*} [Group G] {T : Subgroup G} {w₀ : G}
    (hinv : ∀ x ∈ T, w₀ * x * w₀⁻¹ = x⁻¹) (hsq : w₀ * w₀ ∈ T) {x : G}
    (hx : x ∈ T ⊔ zpowers w₀) : x ∈ T ∨ ∃ t ∈ T, x = t * w₀ := by
  have hconj : ∀ t ∈ T, w₀ * t = t⁻¹ * w₀ := fun t ht => by
    have := hinv t ht
    rwa [mul_inv_eq_iff_eq_mul] at this
  let S : Subgroup G :=
    { carrier := {x | x ∈ T ∨ ∃ t ∈ T, x = t * w₀}
      mul_mem' := by
        rintro x y (hx | ⟨t, ht, rfl⟩) (hy | ⟨s, hs, rfl⟩)
        · exact Or.inl (mul_mem hx hy)
        · exact Or.inr ⟨x * s, mul_mem hx hs, by rw [mul_assoc]⟩
        · refine Or.inr ⟨t * y⁻¹, mul_mem ht (inv_mem hy), ?_⟩
          rw [mul_assoc t w₀ y, hconj y hy, ← mul_assoc]
        · refine Or.inl ?_
          have h : t * w₀ * (s * w₀) = (t * s⁻¹) * (w₀ * w₀) :=
            calc t * w₀ * (s * w₀) = t * (w₀ * s) * w₀ := by group
              _ = t * (s⁻¹ * w₀) * w₀ := by rw [hconj s hs]
              _ = (t * s⁻¹) * (w₀ * w₀) := by group
          rw [h]
          exact mul_mem (mul_mem ht (inv_mem hs)) hsq
      one_mem' := Or.inl (one_mem T)
      inv_mem' := by
        rintro x (hx | ⟨t, ht, rfl⟩)
        · exact Or.inl (inv_mem hx)
        · refine Or.inr ⟨(w₀ * w₀)⁻¹ * t, mul_mem (inv_mem hsq) ht, ?_⟩
          have h3 : w₀ * t⁻¹ = t * w₀ := by simpa using hconj t⁻¹ (inv_mem ht)
          calc (t * w₀)⁻¹ = w₀⁻¹ * t⁻¹ := by group
            _ = (w₀ * w₀)⁻¹ * (w₀ * t⁻¹) := by group
            _ = (w₀ * w₀)⁻¹ * (t * w₀) := by rw [h3]
            _ = (w₀ * w₀)⁻¹ * t * w₀ := by group }
  have h1 : T ⊔ zpowers w₀ ≤ S :=
    sup_le (fun x hx => Or.inl hx) (zpowers_le.2 (Or.inr ⟨1, one_mem T, (one_mul _).symm⟩))
  exact h1 hx

theorem sup_zpowers_swap {G : Type*} [Group G] {T : Subgroup G} {w₀ w : G}
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hinv : ∀ x ∈ T, w₀ * x * w₀⁻¹ = x⁻¹) (hsq : w₀ * w₀ ∈ T)
    (hw : w ∈ T ⊔ zpowers w₀) (hwT : w ∉ T) :
    (∀ k ∈ T, w * k * w⁻¹ = k⁻¹) ∧ w * w = w₀ * w₀ ∧ T ⊔ zpowers w = T ⊔ zpowers w₀ := by
  rcases mem_sup_zpowers_cases hinv hsq hw with h | ⟨t, ht, rfl⟩
  · exact absurd h hwT
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · calc t * w₀ * k * (t * w₀)⁻¹ = t * (w₀ * k * w₀⁻¹) * t⁻¹ := by group
      _ = t * k⁻¹ * t⁻¹ := by rw [hinv k hk]
      _ = k⁻¹ := by rw [hcomm t ht k⁻¹ (inv_mem hk), mul_inv_cancel_right]
  · calc t * w₀ * (t * w₀) = t * (w₀ * t * w₀⁻¹) * (w₀ * w₀) := by group
      _ = w₀ * w₀ := by rw [hinv t ht]; group
  · apply le_antisymm
    · exact sup_le le_sup_left (zpowers_le.2 (mul_mem_sup ht (mem_zpowers w₀)))
    · refine sup_le le_sup_left (zpowers_le.2 ?_)
      have h : t⁻¹ * (t * w₀) ∈ T ⊔ zpowers (t * w₀) :=
        mul_mem_sup (inv_mem ht) (mem_zpowers _)
      simpa using h

theorem mul_mem_of_not_mem {G : Type*} [Group G] {T : Subgroup G} {w₀ b w : G}
    (hinv : ∀ x ∈ T, w₀ * x * w₀⁻¹ = x⁻¹) (hsq : w₀ * w₀ ∈ T)
    (hb : b ∈ T ⊔ zpowers w₀) (hbT : b ∉ T) (hw : w ∈ T ⊔ zpowers w₀) (hwT : w ∉ T) :
    b * w ∈ T := by
  rcases mem_sup_zpowers_cases hinv hsq hb with h | ⟨t, ht, rfl⟩
  · exact absurd h hbT
  rcases mem_sup_zpowers_cases hinv hsq hw with h | ⟨s, hs, rfl⟩
  · exact absurd h hwT
  have hconj : w₀ * s = s⁻¹ * w₀ := by
    have := hinv s hs
    rwa [mul_inv_eq_iff_eq_mul] at this
  have h : t * w₀ * (s * w₀) = (t * s⁻¹) * (w₀ * w₀) :=
    calc t * w₀ * (s * w₀) = t * (w₀ * s) * w₀ := by group
      _ = t * (s⁻¹ * w₀) * w₀ := by rw [hconj]
      _ = (t * s⁻¹) * (w₀ * w₀) := by group
  rw [h]
  exact mul_mem (mul_mem ht (inv_mem hs)) hsq

theorem conj_mem_centralizer {G : Type*} [Group G] {a y t : G}
    (hy : y⁻¹ * a * y ∈ zpowers a) (ht : t ∈ centralizer ({a} : Set G)) :
    y * t * y⁻¹ ∈ centralizer ({a} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at ht ⊢
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hc : t * (y⁻¹ * a * y) = (y⁻¹ * a * y) * t := by
    rw [← hk]
    exact (Commute.zpow_right (show Commute t a from ht) k).eq
  calc y * t * y⁻¹ * a = y * (t * (y⁻¹ * a * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * a * y) * t) * y⁻¹ := by rw [hc]
    _ = a * (y * t * y⁻¹) := by group

theorem mem_normalizer_centralizer {G : Type*} [Group G] {a y : G}
    (hy : y⁻¹ * a * y ∈ zpowers a) (hy' : y * a * y⁻¹ ∈ zpowers a) :
    y ∈ normalizer (centralizer ({a} : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨fun ht => conj_mem_centralizer hy ht, fun ht => ?_⟩
  have h := conj_mem_centralizer (a := a) (y := y⁻¹) (by simpa using hy') ht
  have e : y⁻¹ * (y * t * y⁻¹) * y⁻¹⁻¹ = t := by group
  rwa [e] at h

theorem card_sylow_two_SL2 {F : Type*} [Field F] [Finite F] (h5 : 5 ≤ Nat.card F)
    (hmod : Nat.card F % 4 = 1) (Q : Sylow 2 SL(2, F)) :
    Nat.card (Q : Subgroup SL(2, F)) = 2 ^ ((Nat.card F - 1).factorization 2 + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Sylow.card_eq_multiplicity Q).trans ?_
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  congr 1
  obtain ⟨r, hr⟩ : ∃ r, Nat.card F = 4 * r + 1 := ⟨Nat.card F / 4, by omega⟩
  have hr1 : 1 ≤ r := by omega
  have e1 : (4 * r + 1) ^ 2 - 1 = 2 ^ 3 * r * (2 * r + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  have e2 : 4 * r + 1 - 1 = 2 ^ 2 * r := by omega
  have key : ∀ k m : ℕ, m ≠ 0 → (2 ^ k * m).factorization 2 = k + m.factorization 2 := by
    intro k m hm
    rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm]
    simp [Nat.Prime.factorization_self Nat.prime_two]
  have hodd1 : ¬ 2 ∣ 4 * r + 1 := by omega
  have hodd2 : ¬ 2 ∣ 2 * r + 1 := by omega
  rw [hr, e1, e2, key 2 r (by omega)]
  have hne1 : 4 * r + 1 ≠ 0 := by omega
  have hne2 : 2 ^ 3 * r * (2 * r + 1) ≠ 0 := by positivity
  rw [Nat.factorization_mul hne1 hne2, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd1, Nat.factorization_mul (by positivity) (by omega),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd2, key 3 r (by omega)]
  omega

theorem exists_order_four_normalized {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (Q : Sylow 2 SL(2, F)) (h4 : 4 ∣ Nat.card (Q : Subgroup SL(2, F))) :
    ∃ a ∈ (Q : Subgroup SL(2, F)), orderOf a = 4 ∧
      ∀ y ∈ (Q : Subgroup SL(2, F)), y * a * y⁻¹ ∈ zpowers a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(Q : Subgroup SL(2, F)) := Q.isPGroup'.isNilpotent
  obtain ⟨H, hHcard, hHn⟩ :=
    Group.IsNilpotent.exists_normal_card_eq_of_dvd_card (G := ↥(Q : Subgroup SL(2, F))) h4
  set H' : Subgroup SL(2, F) := H.map (Q : Subgroup SL(2, F)).subtype with hH'
  have hH'card : Nat.card H' = 4 := by
    rw [hH', Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hHcard]
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  obtain ⟨a, haH', ha4⟩ : ∃ a ∈ H', orderOf a = 4 := by
    by_contra hcon
    push Not at hcon
    have hsub : (H' : Set SL(2, F)) ⊆ {1, CFSG.Semidihedral.OddFieldSL2.minusIdentity F} := by
      intro x hx
      have hdvd : orderOf x ∣ 4 := hH'card ▸ Subgroup.orderOf_dvd_natCard H' hx
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).1 (by simpa using hdvd)
      interval_cases k
      · simp [orderOf_eq_one_iff.1 (by simpa using hk')]
      · right
        exact (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff F h2 x).1 (by simpa using hk')
      · exact absurd (by simpa using hk') (hcon x hx)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair (CFSG.Semidihedral.OddFieldSL2.minusIdentity_ne_one F h2).symm] at hle
    change Nat.card H' ≤ 2 at hle
    omega
  have hzp : zpowers a = H' := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.2 haH')
    rw [hH'card, Nat.card_zpowers, ha4]
  have hHQ : H' ≤ (Q : Subgroup SL(2, F)) := Subgroup.map_subtype_le H
  refine ⟨a, hHQ haH', ha4, fun y hy => ?_⟩
  rw [hzp]
  obtain ⟨a', ha', haa'⟩ := Subgroup.mem_map.1 haH'
  let y' : ↥(Q : Subgroup SL(2, F)) := ⟨y, hy⟩
  have hy' : (Q : Subgroup SL(2, F)).subtype y' = y := rfl
  have hc : y' * a' * y'⁻¹ ∈ H := hHn.conj_mem a' ha' y'
  have hm := Subgroup.mem_map_of_mem (Q : Subgroup SL(2, F)).subtype hc
  rw [map_mul, map_mul, map_inv, haa', hy'] at hm
  exact hm

end SL2One

theorem sl2OddAutTorusSL2_one : SL2OddAutTorusSL2 1 := by
  intro F _ _ hodd h5 hmod Q Φ hfix _
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hsq : IsSquare (-1 : F) := by
    have := Fintype.ofFinite F
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    omega
  have hQcard := SL2One.card_sylow_two_SL2 h5 hmod Q
  have hν1 : 0 < (Nat.card F - 1).factorization 2 :=
    Nat.prime_two.factorization_pos_of_dvd (by omega) (by omega)
  have h4 : 4 ∣ Nat.card (Q : Subgroup SL(2, F)) := by
    rw [hQcard]
    exact (pow_dvd_pow 2 (by omega : 2 ≤ (Nat.card F - 1).factorization 2 + 1) : 2 ^ 2 ∣ _)
  obtain ⟨a, haQ, ha4, hnorm⟩ := SL2One.exists_order_four_normalized hodd Q h4
  have ha2 : a * a = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
    have : orderOf (a ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [ha4]; norm_num), ha4]
    rw [CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff F h2] at this
    rwa [← pow_two]
  obtain ⟨hcyc, hTcard, -⟩ := CFSG.GH74.GLS.IVK.L2Torus.centralizer_cyclic_card hodd a ha2
  obtain ⟨T, hT⟩ : ∃ T : Subgroup SL(2, F), T = centralizer ({a} : Set SL(2, F)) := ⟨_, rfl⟩
  rw [← hT] at hcyc hTcard
  have hTc : Nat.card T = Nat.card F - 1 := hTcard hsq
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hTh : zpowers (g : SL(2, F)) = T := by
    apply le_antisymm
    · exact zpowers_le.2 g.2
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  have hord : orderOf (g : SL(2, F)) = Nat.card F - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hTc]
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    rw [← hTh] at hx hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self _ i j).eq
  obtain ⟨w₀, hN, -, hw₀c, hw₀ne, hw₀inv⟩ :=
    CFSG.GH74.GLS.IVK.L2Torus.exists_inverting_normalizer (MulEquiv.refl SL(2, F)) hodd
      (by omega) T hcyc hTc
  have hsq0 : w₀ * w₀ ∈ T := by
    rw [hT]
    exact Subgroup.center_le_centralizer _ (by rwa [pow_two] at hw₀c)
  have hQN : ∀ y ∈ (Q : Subgroup SL(2, F)), y ∈ T ⊔ zpowers w₀ := by
    intro y hy
    rw [← hN, hT]
    exact SL2One.mem_normalizer_centralizer (by simpa using hnorm y⁻¹ (inv_mem hy)) (hnorm y hy)
  obtain ⟨w, hwQ, hwT⟩ : ∃ w ∈ (Q : Subgroup SL(2, F)), w ∉ T := by
    by_contra hcon
    push Not at hcon
    have hle : (Q : Subgroup SL(2, F)) ≤ T := hcon
    have := Subgroup.card_dvd_of_le hle
    rw [hQcard, hTc] at this
    exact Nat.pow_succ_factorization_not_dvd (by omega) Nat.prime_two this
  obtain ⟨hwinv, hww, hsup⟩ := SL2One.sup_zpowers_swap hcomm hw₀inv hsq0 (hQN w hwQ) hwT
  have hrel2 : T.relIndex (Q : Subgroup SL(2, F)) ∣ 2 := by
    refine Subgroup.relIndex_dvd_two_iff.2 ⟨w, hwQ, fun b hb => ?_⟩
    by_cases hbT : b ∈ T
    · exact Or.inr hbT
    · exact Or.inl (SL2One.mul_mem_of_not_mem hw₀inv hsq0 (hQN b hb) hbT (hQN w hwQ) hwT)
  have hrel : T.relIndex (Q : Subgroup SL(2, F)) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hrel2 with h1 | h1
    · exact absurd ((Subgroup.relIndex_eq_one.1 h1) hwQ) hwT
    · exact h1
  have hTQ : Nat.card ↥(T ⊓ (Q : Subgroup SL(2, F))) = 2 ^ (Nat.card F - 1).factorization 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := T) (K := (Q : Subgroup SL(2, F)))
    rw [hrel, hQcard, pow_succ] at h1
    omega
  have hidx : ¬ 2 ∣ (T ⊓ (Q : Subgroup SL(2, F))).relIndex T := by
    intro hdvd
    have h1 := Subgroup.relIndex_mul_card (H := T ⊓ (Q : Subgroup SL(2, F))) (K := T)
    rw [inf_eq_left.2 inf_le_left, hTQ, hTc] at h1
    obtain ⟨r, hr⟩ := hdvd
    refine Nat.pow_succ_factorization_not_dvd (n := Nat.card F - 1) (by omega) Nat.prime_two
      ⟨r, ?_⟩
    calc Nat.card F - 1 = (T ⊓ (Q : Subgroup SL(2, F))).relIndex T *
          2 ^ (Nat.card F - 1).factorization 2 := h1.symm
      _ = 2 ^ ((Nat.card F - 1).factorization 2 + 1) * r := by rw [hr]; ring
  refine ⟨(g : SL(2, F)), w, hord, hwQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hww, ← pow_two]
    exact hw₀c
  · rw [hww, ← pow_two]
    exact hw₀ne
  · rw [hTh]
    exact hwinv
  · rw [hTh]
    exact hN.trans hsup.symm
  · rw [hTh]
    exact hidx
  · intro φ hφ k hk
    rw [hTh, hT] at hk ⊢
    rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
    have hφa : φ a = a := hfix φ hφ a haQ
    calc φ k * a = φ k * φ a := by rw [hφa]
      _ = φ (k * a) := (map_mul φ k a).symm
      _ = φ (a * k) := by rw [hk]
      _ = a * φ k := by rw [map_mul, hφa]

end CFSG.GH74.GLS.SP.Local
