module

public import CFSG.CharacterTheory.Semidihedral.StructureTransport
public import CFSG.CharacterTheory.Semidihedral.Conjugacy
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicSylowComplement

public section

namespace CFSG.Semidihedral.Principal

open CFSG.Open
open scoped Pointwise

section Presentation

theorem rotationFusion_conj_r_cases (n : ℕ) (hn : 3 ≤ n) (w : SemidihedralGroup n) :
    w * r n * w⁻¹ = r n ∨ w * r n * w⁻¹ = r n ^ (2 ^ (n - 2) - 1) := by
  have hr : r n = element n hn 1 0 := by
    simpa only [pow_one, Nat.cast_one] using r_pow_eq_element n hn 1
  have hconj : IsConj (element n hn 1 0) (w * r n * w⁻¹) := by
    rw [← hr]
    exact isConj_iff.mpr ⟨w, rfl⟩
  rcases (rotation_conjugacy_iff n hn 1 _).mp hconj with h | h
  · left
    rw [h, hr]
  · right
    rw [h, mul_one, r_pow_eq_element n hn, twist_eq_natCast]

theorem rotationFusion_twist_int {n : ℕ} (hn : 3 ≤ n) :
    ((modulus n / 2 : ℕ) : ℤ) - 1 = ((2 ^ (n - 2) - 1 : ℕ) : ℤ) := by
  rw [modulus_div_two n hn, half, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one]

theorem rotationFusion_half_cast {n : ℕ} (hn : 3 ≤ n) :
    (((modulus n / 2 : ℕ) : ℤ) : ZMod (modulus n)) = (half n : ZMod (modulus n)) := by
  rw [Int.cast_natCast, modulus_div_two n hn]

theorem rotationFusion_noncentral_zmod {n : ℕ} (hn : 3 ≤ n) (i : ℤ) :
    (i ≡ 0 [ZMOD modulus n] ↔ (i : ZMod (modulus n)) = 0) ∧
      (i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] ↔
        (i : ZMod (modulus n)) = (half n : ZMod (modulus n))) := by
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff, Int.cast_zero]
  · rw [← ZMod.intCast_eq_intCast_iff, rotationFusion_half_cast hn]

theorem rotationFusion_twist_noncentral {n : ℕ} (hn : 4 ≤ n) (k : ℤ)
    (hk0 : ¬ k ≡ 0 [ZMOD modulus n]) (hk1 : ¬ k ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    ¬ (((modulus n / 2 : ℕ) : ℤ) - 1) * k ≡ 0 [ZMOD modulus n] ∧
      ¬ (((modulus n / 2 : ℕ) : ℤ) - 1) * k ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] ∧
      ¬ (((modulus n / 2 : ℕ) : ℤ) - 1) * k ≡ k [ZMOD modulus n] := by
  have hcast : (((((modulus n / 2 : ℕ) : ℤ) - 1) * k : ℤ) : ZMod (modulus n)) =
      twist n * (k : ZMod (modulus n)) := by
    rw [Int.cast_mul, Int.cast_sub, rotationFusion_half_cast (by omega), Int.cast_one, twist]
  rw [(rotationFusion_noncentral_zmod (by omega) k).1] at hk0
  rw [(rotationFusion_noncentral_zmod (by omega) k).2] at hk1
  rw [(rotationFusion_noncentral_zmod (by omega) _).1,
    (rotationFusion_noncentral_zmod (by omega) _).2, ← ZMod.intCast_eq_intCast_iff, hcast]
  have hinv : twist n * (twist n * (k : ZMod (modulus n))) = k := by
    rw [← mul_assoc, ← sq, twist_sq (by omega), one_mul]
  have hhalf : twist n * (half n : ZMod (modulus n)) = half n :=
    (twist_fixed_iff n hn _).mpr (Or.inr rfl)
  refine ⟨fun h => hk0 ?_, fun h => hk1 ?_, fun h => ?_⟩
  · rw [← hinv, h, mul_zero]
  · rw [← hinv, h, hhalf]
  · rcases (twist_fixed_iff n hn _).mp h with h' | h'
    · exact hk0 h'
    · exact hk1 h'

end Presentation

theorem rotationFusion_ncard_image_mul_two {α β : Type*} {X : Set α} (hX : X.Finite)
    (f : α → β) (hfib : ∀ x ∈ X, (X ∩ {y | f y = f x}).ncard = 2) :
    (f '' X).ncard * 2 = X.ncard := by
  classical
  have hsum := Finset.card_eq_sum_card_image f hX.toFinset
  have hconst : ∀ b ∈ hX.toFinset.image f,
      (hX.toFinset.filter (fun a => f a = b)).card = 2 := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    rw [← hfib x ((Set.Finite.mem_toFinset hX).mp hx), ← Set.ncard_coe_finset]
    congr 1
    ext y
    simp
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul] at hsum
  rw [Set.ncard_eq_toFinset_card X hX, hsum]
  conv_lhs => rw [← hX.coe_toFinset, ← Finset.coe_image, Set.ncard_coe_finset]

variable {G : Type*} [Group G] {n : ℕ} {S : Sylow 2 G}

theorem suppliedRotation_orderOf (hn : 3 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G)) :
    orderOf (e (r n) : G) = modulus n := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_r n hn]

theorem suppliedRotation_zpow_eq_iff (hn : 3 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G))
    (i j : ℤ) : (e (r n) : G) ^ i = (e (r n) : G) ^ j ↔ i ≡ j [ZMOD modulus n] := by
  rw [zpow_eq_zpow_iff_modEq, suppliedRotation_orderOf hn e]

theorem suppliedReflection_conj_rotation (e : SemidihedralGroup n ≃* (S : Subgroup G)) :
    (e (s n) : G) * (e (r n) : G) * (e (s n) : G)⁻¹ = (e (r n) : G) ^ (2 ^ (n - 2) - 1) := by
  have h := congrArg (fun x => (e x : G)) (s_conj_r n)
  simpa only [map_mul, map_inv, map_pow, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.coe_pow] using h

theorem suppliedSylow_conj_rotation (hn : 3 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G))
    (σ : G) (hσ : σ ∈ (S : Subgroup G)) :
    σ * (e (r n) : G) * σ⁻¹ = (e (r n) : G) ∨
      σ * (e (r n) : G) * σ⁻¹ = (e (r n) : G) ^ (2 ^ (n - 2) - 1) := by
  obtain ⟨w, hw⟩ := e.surjective ⟨σ, hσ⟩
  have hσw : σ = (e w : G) := by rw [hw]
  rcases rotationFusion_conj_r_cases n hn w with h | h
  · left
    have h' := congrArg (fun x => (e x : G)) h
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h'
    rw [hσw, h']
  · right
    have h' := congrArg (fun x => (e x : G)) h
    simp only [map_mul, map_inv, map_pow, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_pow] at h'
    rw [hσw, h']

theorem suppliedSylow_conj_rotation_zpow (hn : 3 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (σ : G) (hσ : σ ∈ (S : Subgroup G)) (i : ℤ) :
    σ * (e (r n) : G) ^ i * σ⁻¹ = (e (r n) : G) ^ i ∨
      σ * (e (r n) : G) ^ i * σ⁻¹ = (e (r n) : G) ^ (((2 ^ (n - 2) - 1 : ℕ) : ℤ) * i) := by
  rw [← conj_zpow]
  rcases suppliedSylow_conj_rotation hn e σ hσ with h | h
  · left
    rw [h]
  · right
    rw [h, ← zpow_natCast, ← zpow_mul]

theorem suppliedSylow_conj_mem_rotation (hn : 3 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (σ : G) (hσ : σ ∈ (S : Subgroup G)) (x : G)
    (hx : x ∈ Subgroup.zpowers (e (r n) : G)) :
    σ * x * σ⁻¹ ∈ Subgroup.zpowers (e (r n) : G) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow]
  apply Subgroup.zpow_mem
  rcases suppliedSylow_conj_rotation hn e σ hσ with h | h
  · rw [h]
    exact Subgroup.mem_zpowers _
  · rw [h]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem suppliedSylow_le_normalizer_rotation (hn : 3 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) :
    (S : Subgroup G) ≤ Subgroup.normalizer (Subgroup.zpowers (e (r n) : G) : Set G) := by
  intro σ hσ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact suppliedSylow_conj_mem_rotation hn e σ hσ x
  · intro hx
    have h := suppliedSylow_conj_mem_rotation hn e σ⁻¹ ((S : Subgroup G).inv_mem hσ) _ hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h

theorem suppliedRotation_le_centralizer (e : SemidihedralGroup n ≃* (S : Subgroup G)) (i : ℤ) :
    Subgroup.zpowers (e (r n) : G) ≤ Subgroup.centralizer {(e (r n) : G) ^ i} := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
  exact (Commute.self_zpow (e (r n) : G) i).eq

theorem noncentralRotation_sq_ne_one (hn : 3 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G))
    (i : ℤ) (hi0 : ¬ i ≡ 0 [ZMOD modulus n])
    (hi1 : ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    ((e (r n) : G) ^ i) ^ 2 ≠ 1 := by
  rw [(rotationFusion_noncentral_zmod hn i).1] at hi0
  rw [(rotationFusion_noncentral_zmod hn i).2] at hi1
  intro h
  rw [← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one,
    suppliedRotation_orderOf hn e, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  push_cast at h
  rw [mul_comm, two_mul_eq_zero_iff n hn] at h
  rcases h with h | h
  · exact hi0 h
  · exact hi1 h

theorem suppliedRotation_zpow_not_mem_iff (hn : 3 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (k : ℤ) :
    (e (r n) : G) ^ k ∉ ({1, (e (r n) : G) ^ (modulus n / 2)} : Set G) ↔
      ¬ k ≡ 0 [ZMOD modulus n] ∧ ¬ k ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] := by
  have h1 : (e (r n) : G) ^ k = 1 ↔ k ≡ 0 [ZMOD modulus n] := by
    rw [← zpow_zero (e (r n) : G), suppliedRotation_zpow_eq_iff hn e]
  have h2 : (e (r n) : G) ^ k = (e (r n) : G) ^ (modulus n / 2) ↔
      k ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] := by
    rw [← zpow_natCast, suppliedRotation_zpow_eq_iff hn e]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, h1, h2]

theorem suppliedRotation_centralizer_zpowers (e : SemidihedralGroup n ≃* (S : Subgroup G))
    (i : ℤ) :
    Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G) =
      Subgroup.centralizer {(e (r n) : G) ^ i} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem suppliedSylow_natCard (hn : 3 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G)) :
    Nat.card (S : Subgroup G) = 2 ^ n := by
  rw [← Nat.card_congr e.toEquiv, card n hn]

theorem suppliedRotation_natCard (hn : 3 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G)) :
    Nat.card (Subgroup.zpowers (e (r n) : G)) = 2 ^ (n - 1) := by
  rw [Nat.card_zpowers, suppliedRotation_orderOf hn e, modulus]

variable [Finite G]

theorem suppliedRotation_card_mulAut (hn : 3 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G)) :
    Nat.card (MulAut (Subgroup.zpowers (e (r n) : G))) = 2 ^ (n - 2) := by
  rw [IsCyclic.card_mulAut, suppliedRotation_natCard hn e,
    Nat.totient_prime_pow Nat.prime_two (by omega)]
  have h : n - 1 - 1 = n - 2 := by omega
  rw [h]
  norm_num

theorem noncentralRotation_twoSubgroup_eq (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (i : ℤ) (hi0 : ¬ i ≡ 0 [ZMOD modulus n])
    (hi1 : ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n])
    (P : Subgroup G) (hP : IsPGroup 2 P) (hAP : Subgroup.zpowers (e (r n) : G) ≤ P)
    (hPC : P ≤ Subgroup.centralizer {(e (r n) : G) ^ i}) :
    P = Subgroup.zpowers (e (r n) : G) := by
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup G) = 2 ^ n := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity S,
      suppliedSylow_natCard (by omega) e]
  have hAcard := suppliedRotation_natCard (by omega) e
  have hPdvd : Nat.card P ∣ 2 ^ n := hQcard ▸ Subgroup.card_dvd_of_le hPQ
  have hAdvd : 2 ^ (n - 1) ∣ Nat.card P := hAcard ▸ Subgroup.card_dvd_of_le hAP
  obtain ⟨k, hkn, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hPdvd
  rw [hk] at hAdvd
  have hk1 : n - 1 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hAdvd
  rcases (show k = n - 1 ∨ k = n by omega) with hk' | hk'
  · rw [hk'] at hk
    exact (Subgroup.eq_of_le_of_card_ge hAP (by rw [hk, hAcard])).symm
  · rw [hk'] at hk
    exfalso
    have hPQ' : P = Q := Subgroup.eq_of_le_of_card_ge hPQ (by rw [hQcard, hk])
    have hcenter : Nat.card (Subgroup.center (Q : Subgroup G)) = 2 :=
      (supplied_center n hn (e.trans (Sylow.equiv S Q))).2
    have hu : (e (r n) : G) ^ i ∈ (Q : Subgroup G) :=
      hPQ (hAP (Subgroup.zpow_mem_zpowers _ _))
    have hmem : (⟨_, hu⟩ : (Q : Subgroup G)) ∈ Subgroup.center (Q : Subgroup G) := by
      rw [Subgroup.mem_center_iff]
      intro q
      apply Subtype.ext
      have hq : (q : G) ∈ Subgroup.centralizer {(e (r n) : G) ^ i} := hPC (hPQ' ▸ q.2)
      rw [Subgroup.mem_centralizer_singleton_iff] at hq
      exact hq
    have hord := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hcenter, Subgroup.orderOf_mk] at hord
    exact noncentralRotation_sq_ne_one (by omega) e i hi0 hi1
      (orderOf_dvd_iff_pow_eq_one.mp hord)

@[expose] def noncentralRotationSylow (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (i : ℤ) (hi0 : ¬ i ≡ 0 [ZMOD modulus n])
    (hi1 : ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    Sylow 2 (Subgroup.centralizer {(e (r n) : G) ^ i}) where
  toSubgroup := (Subgroup.zpowers (e (r n) : G)).subgroupOf
    (Subgroup.centralizer {(e (r n) : G) ^ i})
  isPGroup' := (IsPGroup.of_card (suppliedRotation_natCard (by omega) e)).of_equiv
    (Subgroup.subgroupOfEquivOfLe (suppliedRotation_le_centralizer e i)).symm
  is_maximal' := by
    intro Q hQ hle
    have hmap := noncentralRotation_twoSubgroup_eq hn e i hi0 hi1
      (Q.map (Subgroup.centralizer {(e (r n) : G) ^ i}).subtype) (hQ.map _)
      (fun x hx => ⟨⟨x, suppliedRotation_le_centralizer e i hx⟩, hle hx, rfl⟩)
      (Subgroup.map_subtype_le Q)
    rw [← hmap]
    exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) Q).symm

theorem noncentralRotationSylow_coe (hn : 4 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G))
    (i : ℤ) (hi0 : ¬ i ≡ 0 [ZMOD modulus n])
    (hi1 : ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    (noncentralRotationSylow hn e i hi0 hi1 :
        Subgroup (Subgroup.centralizer {(e (r n) : G) ^ i})) =
      (Subgroup.zpowers (e (r n) : G)).subgroupOf
        (Subgroup.centralizer {(e (r n) : G) ^ i}) := rfl

theorem noncentralRotation_sylow (hn : 4 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G))
    (i : ℤ) (hi0 : ¬ i ≡ 0 [ZMOD modulus n])
    (hi1 : ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    ∃ P : Sylow 2 (Subgroup.centralizer {(e (r n) : G) ^ i}),
      (P : Subgroup (Subgroup.centralizer {(e (r n) : G) ^ i})).map
        (Subgroup.centralizer {(e (r n) : G) ^ i}).subtype = Subgroup.zpowers (e (r n) : G) :=
  ⟨noncentralRotationSylow hn e i hi0 hi1,
    Subgroup.map_subgroupOf_eq_of_le (suppliedRotation_le_centralizer e i)⟩

theorem noncentralRotation_normal_odd_complement (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (i : ℤ) (hi0 : ¬ i ≡ 0 [ZMOD modulus n])
    (hi1 : ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    ∃ (R : Subgroup (Subgroup.centralizer {(e (r n) : G) ^ i})) (_ : R.Normal),
      (Odd (Nat.card R) ∧ ∃ k : ℕ, R.index = 2 ^ k) ∧
      (∀ R' : Subgroup (Subgroup.centralizer {(e (r n) : G) ^ i}), R'.Normal →
        Odd (Nat.card R') → (∃ k : ℕ, R'.index = 2 ^ k) → R' = R) ∧
      R.Characteristic ∧ (∀ x, x ∈ R ↔ Odd (orderOf x)) ∧
      (R : Set (Subgroup.centralizer {(e (r n) : G) ^ i})) *
          ((Subgroup.zpowers (e (r n) : G)).subgroupOf
            (Subgroup.centralizer {(e (r n) : G) ^ i}) : Set _) = Set.univ ∧
      R ⊓ (Subgroup.zpowers (e (r n) : G)).subgroupOf
          (Subgroup.centralizer {(e (r n) : G) ^ i}) = ⊥ ∧
      Function.Bijective ((QuotientGroup.mk' R).comp
        ((Subgroup.zpowers (e (r n) : G)).subgroupOf
          (Subgroup.centralizer {(e (r n) : G) ^ i})).subtype) := by
  have hcyc : IsCyclic (noncentralRotationSylow hn e i hi0 hi1 :
      Subgroup (Subgroup.centralizer {(e (r n) : G) ^ i})) :=
    (Subgroup.subgroupOfEquivOfLe (suppliedRotation_le_centralizer e i)).isCyclic.mpr
      (Subgroup.isCyclic_zpowers _)
  exact cyclicSylowTwo_normal_odd_complement (noncentralRotationSylow hn e i hi0 hi1) hcyc

theorem noncentralRotation_sylow_zpowers (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (i : ℤ) (hi0 : ¬ i ≡ 0 [ZMOD modulus n])
    (hi1 : ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    ∃ P : Sylow 2 (Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G)),
      (P : Subgroup (Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G))).map
        (Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G)).subtype =
          Subgroup.zpowers (e (r n) : G) := by
  rw [suppliedRotation_centralizer_zpowers]
  exact noncentralRotation_sylow hn e i hi0 hi1

theorem noncentralRotation_normal_odd_complement_zpowers (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (i : ℤ) (hi0 : ¬ i ≡ 0 [ZMOD modulus n])
    (hi1 : ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    ∃ (R : Subgroup (Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G)))
      (_ : R.Normal),
      (Odd (Nat.card R) ∧ ∃ k : ℕ, R.index = 2 ^ k) ∧
      (∀ R' : Subgroup (Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G)),
        R'.Normal → Odd (Nat.card R') → (∃ k : ℕ, R'.index = 2 ^ k) → R' = R) ∧
      R.Characteristic ∧ (∀ x, x ∈ R ↔ Odd (orderOf x)) ∧
      (R : Set (Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G))) *
          ((Subgroup.zpowers (e (r n) : G)).subgroupOf
            (Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G)) : Set _) =
        Set.univ ∧
      R ⊓ (Subgroup.zpowers (e (r n) : G)).subgroupOf
          (Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G)) = ⊥ ∧
      Function.Bijective ((QuotientGroup.mk' R).comp
        ((Subgroup.zpowers (e (r n) : G)).subgroupOf
          (Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G))).subtype) := by
  rw [suppliedRotation_centralizer_zpowers]
  exact noncentralRotation_normal_odd_complement hn e i hi0 hi1

theorem rotationNormalizer_acts_as_suppliedSylow (hn : 3 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (h : G)
    (hh : h ∈ Subgroup.normalizer (Subgroup.zpowers (e (r n) : G) : Set G)) :
    ∃ σ ∈ (S : Subgroup G), h * (e (r n) : G) * h⁻¹ = σ * (e (r n) : G) * σ⁻¹ := by
  set A := Subgroup.zpowers (e (r n) : G)
  set NA := Subgroup.normalizer (A : Set G)
  have hSN : (S : Subgroup G) ≤ NA := suppliedSylow_le_normalizer_rotation hn e
  let ψ := A.normalizerMonoidHom
  let f := ψ.rangeRestrict
  have hf : Function.Surjective f := ψ.rangeRestrict_surjective
  let S' := S.subtype hSN
  have hodd : ¬ 2 ∣ ((S' : Subgroup NA).map f).index :=
    fun h2 => S'.not_dvd_index (h2.trans (Subgroup.index_map_dvd _ hf))
  have hdvd : ((S' : Subgroup NA).map f).index ∣ 2 ^ (n - 2) := by
    rw [← suppliedRotation_card_mulAut hn e]
    exact (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card ψ.range)
  have hone : ((S' : Subgroup NA).map f).index = 1 := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hm] at hodd ⊢
    rcases m with _ | m
    · rfl
    · exact absurd (dvd_pow_self 2 (Nat.succ_ne_zero m)) hodd
  have hmem : f ⟨h, hh⟩ ∈ (S' : Subgroup NA).map f :=
    Subgroup.index_eq_one.mp hone ▸ Subgroup.mem_top _
  obtain ⟨σ', hσ', hfσ⟩ := hmem
  have hψ : ψ σ' = ψ ⟨h, hh⟩ := congrArg Subtype.val hfσ
  have hval :=
    congrArg (fun φ : MulAut A => ((φ ⟨e (r n), Subgroup.mem_zpowers _⟩ : A) : G)) hψ
  simp only [ψ, Subgroup.normalizerMonoidHom_apply_apply_coe] at hval
  exact ⟨σ', hσ', hval.symm⟩

theorem noncentralRotation_exists_normalizer_conj (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (j : ℤ) (hj0 : ¬ j ≡ 0 [ZMOD modulus n])
    (hj1 : ¬ j ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) (x g : G)
    (hx : x ∈ Subgroup.zpowers (e (r n) : G)) (hg : g * x * g⁻¹ = (e (r n) : G) ^ j) :
    ∃ h ∈ Subgroup.normalizer (Subgroup.zpowers (e (r n) : G) : Set G),
      h * x * h⁻¹ = (e (r n) : G) ^ j := by
  set ρ : G := (e (r n) : G)
  set A := Subgroup.zpowers ρ
  set C := Subgroup.centralizer {ρ ^ j} with hCdef
  have hAC : A ≤ C := suppliedRotation_le_centralizer e j
  let P₁ := noncentralRotationSylow hn e j hj0 hj1
  have hP₁ : (P₁ : Subgroup C) = A.subgroupOf C := rfl
  let Ag := A.map (MulAut.conj g).toMonoidHom
  have hAgC : Ag ≤ C := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    have hxa : x * a = a * x := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_zpow_self ρ k l).eq
    change g * a * g⁻¹ * (ρ ^ j) = ρ ^ j * (g * a * g⁻¹)
    rw [← hg]
    simp only [mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc a x, hxa.symm, mul_assoc]
  have hcard : Nat.card (Ag.subgroupOf C) = 2 ^ (Nat.card C).factorization 2 := by
    rw [← Sylow.card_eq_multiplicity P₁, hP₁,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAgC).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  let P₂ := Sylow.ofCard (Ag.subgroupOf C) hcard
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P₂ P₁
  have hcA : ∀ a ∈ A, (c : G) * (g * a * g⁻¹) * (c : G)⁻¹ ∈ A := by
    intro a ha
    have hga : (⟨g * a * g⁻¹, hAgC ⟨a, ha, rfl⟩⟩ : C) ∈ (P₂ : Subgroup C) :=
      ⟨a, ha, rfl⟩
    have hc' : MulAut.conj c • (P₂ : Set C) = (P₁ : Set C) := by
      rw [← hc]
      exact (Sylow.coe_smul (g := c) (P := P₂)).symm
    have hmem : MulAut.conj c • (⟨g * a * g⁻¹, hAgC ⟨a, ha, rfl⟩⟩ : C) ∈
        MulAut.conj c • (P₂ : Set C) := Set.smul_mem_smul_set hga
    rw [hc'] at hmem
    exact hmem
  refine ⟨(c : G) * g, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨a, ha, rfl⟩
      have h := hcA a ha
      change (c : G) * g * a * ((c : G) * g)⁻¹ ∈ A
      convert h using 1
      group
    · rw [Subgroup.card_map_of_injective (MulAut.conj ((c : G) * g)).injective]
  · have hcy : (c : G) * ρ ^ j = ρ ^ j * (c : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp c.2
    calc (c : G) * g * x * ((c : G) * g)⁻¹ = (c : G) * (g * x * g⁻¹) * (c : G)⁻¹ := by group
      _ = ρ ^ j := by rw [hg, hcy, mul_inv_cancel_right]

theorem noncentralRotation_isConj_iff (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (i j : ℤ) (hj0 : ¬ j ≡ 0 [ZMOD modulus n])
    (hj1 : ¬ j ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    IsConj ((e (r n) : G) ^ i) ((e (r n) : G) ^ j) ↔
      j ≡ i [ZMOD modulus n] ∨ j ≡ (((modulus n / 2 : ℕ) : ℤ) - 1) * i [ZMOD modulus n] := by
  rw [rotationFusion_twist_int (by omega), ← suppliedRotation_zpow_eq_iff (by omega) e,
    ← suppliedRotation_zpow_eq_iff (by omega) e]
  constructor
  · intro hconj
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    obtain ⟨h, hh, hhx⟩ := noncentralRotation_exists_normalizer_conj hn e j hj0 hj1 _ g
      (Subgroup.zpow_mem_zpowers _ _) hg
    obtain ⟨σ, hσ, hσh⟩ := rotationNormalizer_acts_as_suppliedSylow (by omega) e h hh
    have hσj : σ * (e (r n) : G) ^ i * σ⁻¹ = (e (r n) : G) ^ j := by
      rw [← conj_zpow, ← hσh, conj_zpow, hhx]
    rcases suppliedSylow_conj_rotation_zpow (by omega) e σ hσ i with h1 | h1
    · exact Or.inl (hσj.symm.trans h1)
    · exact Or.inr (hσj.symm.trans h1)
  · rintro (h | h)
    · rw [h]
    · rw [h]
      refine isConj_iff.mpr ⟨(e (s n) : G), ?_⟩
      rw [← conj_zpow, suppliedReflection_conj_rotation, ← zpow_natCast, ← zpow_mul]

theorem noncentralRotation_conjClasses (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) :
    {c : ConjClasses G | (c.carrier ∩ ((Subgroup.zpowers (e (r n) : G) : Set G) \
        {1, (e (r n) : G) ^ (modulus n / 2)})).Nonempty}.ncard = modulus n / 2 - 1 ∧
      ∀ c : ConjClasses G, (c.carrier ∩ ((Subgroup.zpowers (e (r n) : G) : Set G) \
        {1, (e (r n) : G) ^ (modulus n / 2)})).Nonempty →
        (c.carrier ∩ ((Subgroup.zpowers (e (r n) : G) : Set G) \
          {1, (e (r n) : G) ^ (modulus n / 2)})).ncard = 2 := by
  set ρ : G := (e (r n) : G) with hρ
  set X : Set G := (Subgroup.zpowers ρ : Set G) \ {1, ρ ^ (modulus n / 2)} with hX
  have hmemX : ∀ x, x ∈ X ↔ ∃ k : ℤ, x = ρ ^ k ∧ ¬ k ≡ 0 [ZMOD modulus n] ∧
      ¬ k ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] := by
    intro x
    constructor
    · rintro ⟨hx, hx'⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ⟨k, rfl, (suppliedRotation_zpow_not_mem_iff (by omega) e k).mp hx'⟩
    · rintro ⟨k, rfl, hk⟩
      exact ⟨Subgroup.zpow_mem_zpowers _ _,
        (suppliedRotation_zpow_not_mem_iff (by omega) e k).mpr hk⟩
  have hfib : ∀ x ∈ X, (X ∩ {y | ConjClasses.mk y = ConjClasses.mk x}).ncard = 2 := by
    intro x hx
    obtain ⟨k, rfl, hk0, hk1⟩ := (hmemX x).mp hx
    obtain ⟨ha0, ha1, hak⟩ := rotationFusion_twist_noncentral hn k hk0 hk1
    have hset : X ∩ {y | ConjClasses.mk y = ConjClasses.mk (ρ ^ k)} =
        {ρ ^ k, ρ ^ ((((modulus n / 2 : ℕ) : ℤ) - 1) * k)} := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, ConjClasses.mk_eq_mk_iff_isConj]
      constructor
      · rintro ⟨hy, hconj⟩
        obtain ⟨l, rfl, hl0, hl1⟩ := (hmemX y).mp hy
        rcases (noncentralRotation_isConj_iff hn e k l hl0 hl1).mp hconj.symm with h | h
        · exact Or.inl ((suppliedRotation_zpow_eq_iff (by omega) e l k).mpr h)
        · exact Or.inr ((suppliedRotation_zpow_eq_iff (by omega) e _ _).mpr h)
      · rintro (rfl | rfl)
        · exact ⟨hx, IsConj.refl _⟩
        · refine ⟨(hmemX _).mpr ⟨_, rfl, ha0, ha1⟩, ?_⟩
          exact ((noncentralRotation_isConj_iff hn e k _ ha0 ha1).mpr
            (Or.inr (Int.ModEq.refl _))).symm
    rw [hset, Set.ncard_pair]
    intro h
    exact hak ((suppliedRotation_zpow_eq_iff (by omega) e _ _).mp h).symm
  have himage : {c : ConjClasses G | (c.carrier ∩ X).Nonempty} = ConjClasses.mk '' X := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨x, hxc, hxX⟩
      exact ⟨x, hxX, ConjClasses.mem_carrier_iff_mk_eq.mp hxc⟩
    · rintro ⟨x, hxX, rfl⟩
      exact ⟨x, ConjClasses.mem_carrier_mk, hxX⟩
  have hhalf_pos : 0 < modulus n / 2 := by
    rw [modulus_div_two n (by omega), half]
    exact Nat.two_pow_pos _
  have hmod : modulus n = 2 * (modulus n / 2) := by
    rw [modulus_div_two n (by omega)]
    exact modulus_eq_two_mul_half (by omega)
  have hne : (1 : G) ≠ ρ ^ (modulus n / 2) := by
    refine (pow_ne_one_of_lt_orderOf hhalf_pos.ne' ?_).symm
    rw [hρ, suppliedRotation_orderOf (by omega) e]
    omega
  have hXcard : X.ncard = modulus n - 2 := by
    have hsub : ({1, ρ ^ (modulus n / 2)} : Set G) ⊆ (Subgroup.zpowers ρ : Set G) := by
      intro y hy
      rcases hy with rfl | hy
      · exact (Subgroup.zpowers ρ).one_mem
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers ρ) _
    have hA : (Subgroup.zpowers ρ : Set G).ncard = modulus n := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_zpowers, hρ,
        suppliedRotation_orderOf (by omega) e]
    rw [hX, Set.ncard_sdiff hsub, Set.ncard_pair hne, hA]
  have hcount := rotationFusion_ncard_image_mul_two (Set.toFinite X) ConjClasses.mk hfib
  refine ⟨?_, ?_⟩
  · rw [himage]
    omega
  · rintro c ⟨x, hxc, hxX⟩
    have hc : c = ConjClasses.mk x := (ConjClasses.mem_carrier_iff_mk_eq.mp hxc).symm
    have hset : c.carrier ∩ X = X ∩ {y | ConjClasses.mk y = ConjClasses.mk x} := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ConjClasses.mem_carrier_iff_mk_eq, hc]
      exact and_comm
    rw [hset, hfib x hxX]

theorem noncentral_rotation_centralizers_and_fusion (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) :
    let r : G := (e (CFSG.Semidihedral.r n) : G)
    let M : ℕ := modulus n
    let a : ℤ := ((M / 2 : ℕ) : ℤ) - 1
    let A : Subgroup G := Subgroup.zpowers r
    let t : G := r ^ (M / 2)
    (∀ i : ℤ, ¬ i ≡ 0 [ZMOD M] → ¬ i ≡ (M / 2 : ℕ) [ZMOD M] →
      (∃ P : Sylow 2 (Subgroup.centralizer {r ^ i}),
        (P : Subgroup (Subgroup.centralizer {r ^ i})).map
          (Subgroup.centralizer {r ^ i}).subtype = A) ∧
      ∃ (R : Subgroup (Subgroup.centralizer {r ^ i})) (_ : R.Normal),
        (Odd (Nat.card R) ∧ ∃ k : ℕ, R.index = 2 ^ k) ∧
        (∀ R' : Subgroup (Subgroup.centralizer {r ^ i}), R'.Normal → Odd (Nat.card R') →
          (∃ k : ℕ, R'.index = 2 ^ k) → R' = R) ∧
        R.Characteristic ∧ (∀ x, x ∈ R ↔ Odd (orderOf x)) ∧
        (R : Set (Subgroup.centralizer {r ^ i})) *
            (A.subgroupOf (Subgroup.centralizer {r ^ i}) : Set _) = Set.univ ∧
        R ⊓ A.subgroupOf (Subgroup.centralizer {r ^ i}) = ⊥ ∧
        Function.Bijective ((QuotientGroup.mk' R).comp
          (A.subgroupOf (Subgroup.centralizer {r ^ i})).subtype)) ∧
    (∀ i j : ℤ, ¬ i ≡ 0 [ZMOD M] → ¬ i ≡ (M / 2 : ℕ) [ZMOD M] →
      ¬ j ≡ 0 [ZMOD M] → ¬ j ≡ (M / 2 : ℕ) [ZMOD M] →
      (IsConj (r ^ i) (r ^ j) ↔ j ≡ i [ZMOD M] ∨ j ≡ a * i [ZMOD M])) ∧
    {c : ConjClasses G | (c.carrier ∩ ((A : Set G) \ {1, t})).Nonempty}.ncard = M / 2 - 1 ∧
    ∀ c : ConjClasses G, (c.carrier ∩ ((A : Set G) \ {1, t})).Nonempty →
      (c.carrier ∩ ((A : Set G) \ {1, t})).ncard = 2 := by
  intro r M a A t
  refine ⟨fun i hi0 hi1 => ⟨noncentralRotation_sylow hn e i hi0 hi1,
      noncentralRotation_normal_odd_complement hn e i hi0 hi1⟩,
    fun i j _ _ hj0 hj1 => noncentralRotation_isConj_iff hn e i j hj0 hj1,
    (noncentralRotation_conjClasses hn e).1, (noncentralRotation_conjClasses hn e).2⟩

end CFSG.Semidihedral.Principal
