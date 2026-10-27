module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapReps
public import CFSG.LocalAnalysis.OddStandard.AltStdSmallSylowSym

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm
open scoped Pointwise

structure GoodQ (Q : Subgroup (Perm (Fin 10))) : Prop where
  pgroup : IsPGroup 2 Q
  card : Nat.card Q = 2 ^ 8
  τ₀_mem : τ₀ ∈ Q
  ρ₄_mem : ρ₄ ∈ Q
  τ₀_comm : ∀ q ∈ Q, τ₀ * q = q * τ₀
  ρ₄_comm : ∀ q ∈ Q, ρ₄ * q = q * ρ₄
  center : ∀ q ∈ Q, (∀ p ∈ Q, q * p = p * q) → q = 1 ∨ q = τ₀ ∨ q = ρ₄ ∨ q = τ₀ * ρ₄

theorem exists_mul_zpowers_of_mem_sup {G : Type*} [Group G] [Finite G] [DecidableEq G]
    {H : Subgroup G}
    {a : G} (ha : orderOf a = 2) (hHa : H ≤ Subgroup.normalizer (Subgroup.zpowers a)) {q : G}
    (hq : q ∈ H ⊔ Subgroup.zpowers a) :
    ∃ h ∈ H, ∃ i : Fin 2, q = h * a ^ (i : ℕ) := by
  classical
  have hcoe : (↑(H ⊔ Subgroup.zpowers a) : Set G) =
      (↑H : Set G) * (↑(Subgroup.zpowers a) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right H (Subgroup.zpowers a) hHa
  have hq' : q ∈ (↑H : Set G) * (↑(Subgroup.zpowers a) : Set G) := by
    rw [← hcoe]; exact hq
  obtain ⟨h, hh, t, ht, hht⟩ := hq'
  have ht' : t ∈ (Finset.range (orderOf a)).image (a ^ ·) := by
    change t ∈ Subgroup.zpowers a at ht
    rwa [mem_zpowers_iff_mem_range_orderOf] at ht
  simp only [Finset.mem_image, Finset.mem_range] at ht'
  obtain ⟨i, hi, hit⟩ := ht'
  exact ⟨h, hh, ⟨i, by rwa [ha] at hi⟩, by rw [← hht, ← hit]⟩

theorem card_sup_zpowers_of_notMem {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {H : Subgroup G} {a : G} (ha : orderOf a = 2)
    (hHa : H ≤ Subgroup.normalizer (Subgroup.zpowers a)) (haH : a ∉ H) :
    Nat.card (H ⊔ Subgroup.zpowers a : Subgroup G) = 2 * Nat.card H := by
  classical
  let F : H × Fin 2 → (H ⊔ Subgroup.zpowers a : Subgroup G) := fun x =>
    ⟨x.1.1 * a ^ (x.2 : ℕ), (H ⊔ Subgroup.zpowers a : Subgroup G).mul_mem
      (Subgroup.mem_sup_left (S := H) (T := Subgroup.zpowers a) x.1.2)
      ((H ⊔ Subgroup.zpowers a : Subgroup G).pow_mem
        (Subgroup.mem_sup_right (S := H) (T := Subgroup.zpowers a) (Subgroup.mem_zpowers a)) _)⟩
  have hbij : Function.Bijective F := by
    constructor
    · intro x y hxy
      have hval : x.1.1 * a ^ (x.2 : ℕ) = y.1.1 * a ^ (y.2 : ℕ) := by
        have h := congrArg (fun z : (H ⊔ Subgroup.zpowers a : Subgroup G) => (z : G)) hxy
        simpa [F] using h
      obtain ⟨⟨h₁, hh₁⟩, i₁⟩ := x
      obtain ⟨⟨h₂, hh₂⟩, i₂⟩ := y
      fin_cases i₁ <;> fin_cases i₂
      · simp only [Fin.val_zero, pow_zero, mul_one] at hval
        exact Prod.ext (Subtype.ext hval) rfl
      · simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one] at hval
        exfalso
        exact haH ((show h₂⁻¹ * h₁ = a from by rw [hval]; group) ▸
          H.mul_mem (H.inv_mem hh₂) hh₁)
      · simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one] at hval
        exfalso
        exact haH ((show h₁⁻¹ * h₂ = a from by rw [← hval]; group) ▸
          H.mul_mem (H.inv_mem hh₁) hh₂)
      · simp only [Fin.val_one, pow_one] at hval
        exact Prod.ext (Subtype.ext (mul_right_cancel hval)) rfl
    · intro y
      obtain ⟨h, hh, i, hy⟩ := exists_mul_zpowers_of_mem_sup ha hHa y.2
      exact ⟨(⟨h, hh⟩, i), Subtype.ext hy.symm⟩
  calc Nat.card (H ⊔ Subgroup.zpowers a : Subgroup G) = Nat.card (H × Fin 2) :=
        (Nat.card_congr (Equiv.ofBijective F hbij)).symm
    _ = Nat.card H * Nat.card (Fin 2) := Nat.card_prod _ _
    _ = 2 * Nat.card H := by rw [Nat.card_fin, Nat.mul_comm]

theorem center_sup_zpowers {G : Type*} [Group G] [Finite G] [DecidableEq G] {H : Subgroup G}
    {a z : G}
    (ha : orderOf a = 2) (hHa : H ≤ Subgroup.normalizer (Subgroup.zpowers a)) (haH : a ∉ H)
    (hza : z * a = a * z) (ha_comm : ∀ h ∈ H, h * a = a * h)
    (hH_center : ∀ q ∈ H, (∀ h ∈ H, q * h = h * q) → q = 1 ∨ q = z) :
    ∀ q ∈ H ⊔ Subgroup.zpowers a,
      (∀ p ∈ H ⊔ Subgroup.zpowers a, q * p = p * q) →
      q = 1 ∨ q = a ∨ q = z ∨ q = a * z := by
  classical
  intro q hq hqcomm
  obtain ⟨h, hh, i, hq_eq⟩ := exists_mul_zpowers_of_mem_sup ha hHa hq
  have ha_central : ∀ x ∈ H ⊔ Subgroup.zpowers a, a * x = x * a := by
    intro x hx
    obtain ⟨k, hk, j, hx_eq⟩ := exists_mul_zpowers_of_mem_sup ha hHa hx
    have hka : Commute a k := (ha_comm k hk).symm
    have hcomm : Commute a (k * a ^ (j : ℕ)) :=
      hka.mul_right ((Commute.refl a).pow_right j)
    rw [hx_eq]
    exact hcomm
  have h_central : ∀ x ∈ H ⊔ Subgroup.zpowers a, h * x = x * h := by
    intro x hx
    have hcomm_x : Commute a x := ha_central x hx
    have h_inv : (a ^ (i : ℕ))⁻¹ * x = x * (a ^ (i : ℕ))⁻¹ :=
      (hcomm_x.pow_left (i : ℕ)).inv_left
    have hh_eq : h = q * (a ^ (i : ℕ))⁻¹ := by rw [hq_eq]; group
    calc h * x = q * (a ^ (i : ℕ))⁻¹ * x := by rw [hh_eq]
      _ = q * ((a ^ (i : ℕ))⁻¹ * x) := by group
      _ = q * (x * (a ^ (i : ℕ))⁻¹) := by rw [h_inv]
      _ = q * x * (a ^ (i : ℕ))⁻¹ := by group
      _ = x * q * (a ^ (i : ℕ))⁻¹ := by rw [hqcomm x hx]
      _ = x * (q * (a ^ (i : ℕ))⁻¹) := by group
      _ = x * h := by rw [← hh_eq]
  have hh_central : ∀ k ∈ H, h * k = k * h := fun k hk => h_central k (Subgroup.mem_sup_left hk)
  rcases hH_center h hh hh_central with h1 | hz
  · subst h1
    fin_cases i
    · left; simpa only [Fin.val_zero, pow_zero, mul_one] using hq_eq
    · right; left; simpa only [Fin.val_one, pow_one, one_mul] using hq_eq
  · subst hz
    fin_cases i
    · right; right; left; simpa only [Fin.val_zero, pow_zero, mul_one] using hq_eq
    · right; right; right
      simp only [Fin.val_one, pow_one] at hq_eq
      rw [hq_eq, hza]

theorem exists_sylow_eight :
    ∃ P : Subgroup (Perm (Fin 8)), IsPGroup 2 P ∧ Nat.card P = 2 ^ 7 ∧ ρ₄' ∈ P ∧
      (∀ p ∈ P, ρ₄' * p = p * ρ₄') ∧
      (∀ q ∈ P, (∀ p ∈ P, q * p = p * q) → q = 1 ∨ q = ρ₄') := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup (Perm (Fin 8)) := centralizer ({ρ₄'} : Set (Perm (Fin 8)))
  have hcardC : Nat.card C = 2 ^ 7 * 3 := by
    dsimp only [C]
    rw [CFSG.OddStandard.AltStdSec.nat_card_centralizer_of_mul_self ρ₄'_mul_self,
      card_cycleType_ρ₄']
    norm_num [Nat.factorial]
  have hρC : ρ₄' ∈ C := by
    dsimp only [C]
    rw [mem_centralizer_singleton_iff]
  have hHpg : IsPGroup 2 ((zpowers ρ₄').subgroupOf C) := by
    apply IsPGroup.comap_subtype
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers]
    have h : orderOf ρ₄' = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact ρ₄'_mul_self) (by decide)
    rw [h]; norm_num
  obtain ⟨S, hHS⟩ := hHpg.exists_le_sylow
  have hcardS : Nat.card S = 2 ^ 7 := by
    rw [Sylow.card_eq_multiplicity]
    congr 1
    rw [show Nat.card (↥C) = Nat.card C from rfl, hcardC]
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), add_zero]
  let P : Subgroup (Perm (Fin 8)) := (S : Subgroup ↥C).map C.subtype
  have hPpg : IsPGroup 2 P := by
    dsimp only [P]
    exact S.isPGroup'.map C.subtype
  have hcardP : Nat.card P = 2 ^ 7 := by
    dsimp only [P]
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hcardS
  have hρP : ρ₄' ∈ P := by
    dsimp only [P]
    refine ⟨⟨ρ₄', hρC⟩, hHS ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers ρ₄'
  have hcomm_of_mem : ∀ p ∈ P, p ∈ C := by
    intro p hp
    dsimp only [P] at hp
    obtain ⟨s, -, rfl⟩ := hp
    exact s.2
  have hρcommP : ∀ p ∈ P, ρ₄' * p = p * ρ₄' := by
    intro p hp
    exact (mem_centralizer_singleton_iff.1 (hcomm_of_mem p hp)).symm
  have hcenterP : ∀ q ∈ P, (∀ p ∈ P, q * p = p * q) → q = 1 ∨ q = ρ₄' := by
    intro q hq hqcomm
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    · right
      have hρ1 : ρ₄' ≠ 1 := by
        intro h
        have hc := card_cycleType_ρ₄'
        rw [h] at hc
        simpa using hc
      exact (CFSG.OddStandard.AltStdSmall.eq_of_mem_center_sylow_sym (n := 8)
        (by norm_num) (by norm_num) hPpg (hcardP ▸ dvd_refl _) hρP hq hρcommP hqcomm
        hρ1 hq1).symm
  exact ⟨P, hPpg, hcardP, hρP, hρcommP, hcenterP⟩

theorem exists_goodQ : ∃ Q : Subgroup (Perm (Fin 10)), GoodQ Q := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPpg, hcardP, hρ'P, hρ'commP, hcenterP⟩ := exists_sylow_eight
  let P' : Subgroup (Perm (Fin 10)) := P.map liftS8
  set Q : Subgroup (Perm (Fin 10)) := P' ⊔ zpowers τ₀ with hQdef
  have hcardP' : Nat.card P' = 2 ^ 7 := by
    dsimp only [P']
    rw [Subgroup.card_map_of_injective liftS8_injective]
    exact hcardP
  have hτ0order : orderOf τ₀ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact τ₀_mul_self) (by decide)
  have hρ4_mem_P' : ρ₄ ∈ P' := Subgroup.mem_map.2 ⟨ρ₄', hρ'P, liftS8_ρ₄'⟩
  have hρ4_commP' : ∀ h ∈ P', ρ₄ * h = h * ρ₄ := by
    intro h hh
    dsimp only [P'] at hh
    rw [Subgroup.mem_map] at hh
    obtain ⟨p₀, hp₀P, rfl⟩ := hh
    have h := congrArg liftS8 (hρ'commP p₀ hp₀P)
    simp only [map_mul, liftS8_ρ₄'] at h
    exact h
  have hρ4_τ0 : Commute ρ₄ τ₀ := by
    rw [← liftS8_ρ₄']; exact liftS8_mul_τ₀ ρ₄'
  have hτ0_commP' : ∀ h ∈ P', h * τ₀ = τ₀ * h := by
    intro h hh
    dsimp only [P'] at hh
    rw [Subgroup.mem_map] at hh
    obtain ⟨p₀, -, rfl⟩ := hh
    exact liftS8_mul_τ₀ p₀
  have hP'norm : P' ≤ Subgroup.normalizer (zpowers τ₀ : Subgroup (Perm (Fin 10))) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    have hkcomm : Commute h k := by
      have hmem : τ₀ ∈ Subgroup.centralizer ({h} : Set (Perm (Fin 10))) :=
        mem_centralizer_singleton_iff.2 (hτ0_commP' h hh).symm
      have hk' : k ∈ Subgroup.centralizer ({h} : Set (Perm (Fin 10))) :=
        Subgroup.zpowers_le.2 hmem hk
      exact (mem_centralizer_singleton_iff.1 hk').symm
    rw [hkcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hk
  have hτ0_not_mem_P' : τ₀ ∉ P' := by
    intro h
    dsimp only [P'] at h
    rw [Subgroup.mem_map] at h
    obtain ⟨p₀, -, hp₀⟩ := h
    have h8 := liftS8_apply_eight p₀
    rw [hp₀, τ₀_apply_eight] at h8
    exact absurd h8 (by decide)
  have hcenterP' : ∀ q ∈ P', (∀ p ∈ P', q * p = p * q) → q = 1 ∨ q = ρ₄ := by
    intro q hq hqcomm
    dsimp only [P'] at hq
    rw [Subgroup.mem_map] at hq
    obtain ⟨p₀, hp₀P, rfl⟩ := hq
    have hp₀_central : ∀ a ∈ P, p₀ * a = a * p₀ := by
      intro a ha
      have h := hqcomm (liftS8 a) (Subgroup.mem_map.2 ⟨a, ha, rfl⟩)
      rw [← map_mul, ← map_mul] at h
      exact liftS8_injective h
    rcases hcenterP p₀ hp₀P hp₀_central with h1 | hρ
    · left; rw [h1, map_one]
    · right; rw [hρ, liftS8_ρ₄']
  have hcardQ : Nat.card Q = 2 ^ 8 := by
    rw [hQdef, card_sup_zpowers_of_notMem hτ0order hP'norm hτ0_not_mem_P', hcardP']
    norm_num
  have hτ0_mem_Q : τ₀ ∈ Q := by
    rw [hQdef]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers τ₀)
  have hρ4_mem_Q : ρ₄ ∈ Q := by
    rw [hQdef]; exact Subgroup.mem_sup_left hρ4_mem_P'
  refine ⟨Q, ?_, hcardQ, hτ0_mem_Q, hρ4_mem_Q, ?_, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 8) hcardQ
  · intro q hq
    rw [hQdef] at hq
    obtain ⟨p, hp, i, hq_eq⟩ := exists_mul_zpowers_of_mem_sup hτ0order hP'norm hq
    have hcomm_p : Commute τ₀ p := (hτ0_commP' p hp).symm
    have hcomm' : Commute τ₀ (p * τ₀ ^ (i : ℕ)) :=
      hcomm_p.mul_right ((Commute.refl τ₀).pow_right i)
    rw [hq_eq]; exact hcomm'
  · intro q hq
    rw [hQdef] at hq
    obtain ⟨p, hp, i, hq_eq⟩ := exists_mul_zpowers_of_mem_sup hτ0order hP'norm hq
    have hcomm_p : Commute ρ₄ p := hρ4_commP' p hp
    have hcomm' : Commute ρ₄ (p * τ₀ ^ (i : ℕ)) :=
      hcomm_p.mul_right (hρ4_τ0.pow_right i)
    rw [hq_eq]; exact hcomm'
  · exact center_sup_zpowers hτ0order hP'norm hτ0_not_mem_P' hρ4_τ0 hτ0_commP' hcenterP'

end CFSG.OddStandard.AltStdSec.SwapPattern
