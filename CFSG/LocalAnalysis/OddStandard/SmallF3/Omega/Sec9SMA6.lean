module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMGrp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SNorm

import CFSG.Mathlib.GroupTheory.PermCenter

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem center_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxc : e x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, hx z, map_mul]
  have hx1 : e x = 1 := Subgroup.mem_bot.mp (h ▸ hxc)
  exact e.injective (by rw [hx1, map_one])

private theorem mem_center_closure_pair {G : Type*} [Group G] {K : Subgroup G} {φ : G}
    (hφ : ∀ k ∈ K, φ * k = k * φ) :
    (⟨φ, Subgroup.subset_closure (Or.inr rfl)⟩ :
      ↥(Subgroup.closure ((K : Set G) ∪ {φ}))) ∈
      Subgroup.center ↥(Subgroup.closure ((K : Set G) ∪ {φ})) := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  change (h : G) * φ = φ * (h : G)
  refine Subgroup.closure_induction (p := fun z _ => z * φ = φ * z) ?_ ?_ ?_ ?_ h.2
  · intro x hx
    rcases hx with hx | hx
    · exact (hφ x hx).symm
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
  · rw [one_mul, mul_one]
  · intro x y hx hy ihx ihy
    calc (x * y) * φ = x * (y * φ) := by group
      _ = x * (φ * y) := by rw [ihy]
      _ = (x * φ) * y := by group
      _ = (φ * x) * y := by rw [ihx]
      _ = φ * (x * y) := by group
  · intro x hx ih
    calc x⁻¹ * φ = x⁻¹ * (φ * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * φ) * x⁻¹ := by rw [← ih]
      _ = φ * x⁻¹ := by group

theorem sec9m_closure_two {K : Type*} [Group K] [Finite K]
    (hK : Nonempty (K ≃* alternatingGroup (Fin 6))) :
    Subgroup.closure {k : K | ∃ m : ℕ, k ^ (2 ^ m) = 1} = ⊤ := by
  obtain ⟨e⟩ := hK
  have hcard : Nat.card K = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by norm_num)
  have : IsSimpleGroup K := e.isSimpleGroup
  set S : Set K := {k : K | ∃ m : ℕ, k ^ (2 ^ m) = 1} with hS
  have hinv : ∀ g k : K, k ∈ S → g * k * g⁻¹ ∈ S := by
    rintro g k ⟨m, hm⟩
    exact ⟨m, by rw [conj_pow, hm]; simp⟩
  have hnormal : (Subgroup.closure S).Normal :=
    ⟨fun k hk g => by
      refine Subgroup.closure_induction (p := fun z _ => g * z * g⁻¹ ∈ Subgroup.closure S)
        (fun x hx => Subgroup.subset_closure (hinv g x hx)) ?_ ?_ ?_ hk
      · simp
      · intro x y hx hy ihx ihy
        rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
        exact (Subgroup.closure S).mul_mem ihx ihy
      · intro x hx ih
        rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
        exact (Subgroup.closure S).inv_mem ih⟩
  have : (Subgroup.closure S).Normal := hnormal
  have h2dvd : 2 ∣ Nat.card K := by rw [hcard]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hxS : x ∈ S := ⟨1, by rw [pow_one, ← hx, pow_orderOf_eq_one]⟩
  have hxne : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    norm_num at hx
  have hne : Subgroup.closure S ≠ ⊥ := by
    intro hbot
    have : x ∈ (⊥ : Subgroup K) := by
      rw [← hbot]
      exact Subgroup.subset_closure hxS
    rw [Subgroup.mem_bot] at this
    exact hxne this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure S) with h | h
  · exact absurd h hne
  · exact h

theorem sec9m_not_comm {K : Type*} [Group K] (hK : Nonempty (K ≃* alternatingGroup (Fin 6))) :
    ∃ a b : K, a * b ≠ b * a := by
  obtain ⟨e⟩ := hK
  let a0 : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap',
        Equiv.Perm.sign_swap']
      decide⟩
  let b0 : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap',
        Equiv.Perm.sign_swap']
      decide⟩
  have h : a0 * b0 ≠ b0 * a0 := by decide
  exact ⟨e.symm a0, e.symm b0, fun hc => h (by simpa using congrArg e hc)⟩

theorem sec9m_card_A6 {K : Type*} [Group K] (hK : Nonempty (K ≃* alternatingGroup (Fin 6))) :
    Nat.card K = 360 := by
  obtain ⟨e⟩ := hK
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

theorem sec9m_centralizer_trivial (hN : Asc82NormA6) {G : Type} [Group G] [Finite G]
    {B : Subgroup G} (hB : IsElemAb2 B 4) {K : Subgroup (MulAut ↥B)}
    (hK : Nonempty (↥K ≃* alternatingGroup (Fin 6))) :
    ∀ φ : MulAut ↥B, (∀ k ∈ K, φ * k = k * φ) → φ = 1 := by
  intro φ hφ
  let H₂ : Subgroup (MulAut ↥B) := Subgroup.closure ((K : Set (MulAut ↥B)) ∪ {φ})
  have hK_le : K ≤ H₂ := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hφ_mem : φ ∈ H₂ := Subgroup.subset_closure (Or.inr rfl)
  have hnormK : ∀ h ∈ H₂, ∀ a ∈ K, h * a * h⁻¹ ∈ K := by
    have hle : H₂ ≤ Subgroup.normalizer (K : Set (MulAut ↥B)) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · exact Subgroup.le_normalizer hx
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Subgroup.mem_normalizer_iff.mpr (by
          intro a
          constructor
          · intro ha
            rwa [hφ a ha, mul_assoc, mul_inv_cancel, mul_one]
          · intro ha
            have hb := hφ (φ * a * φ⁻¹) ha
            have hone : φ * a * φ⁻¹ = a := by
              have h2 : φ⁻¹ * (φ * (φ * a * φ⁻¹)) = φ⁻¹ * ((φ * a * φ⁻¹) * φ) :=
                congrArg (fun t => φ⁻¹ * t) hb
              calc φ * a * φ⁻¹ = φ⁻¹ * (φ * (φ * a * φ⁻¹)) := by group
                _ = φ⁻¹ * ((φ * a * φ⁻¹) * φ) := h2
                _ = a := by group
            rwa [hone] at ha)
    intro h hh a ha
    exact (Subgroup.mem_normalizer_iff.mp (hle hh) a).mp ha
  have hφcen : (⟨φ, hφ_mem⟩ : ↥H₂) ∈ Subgroup.center ↥H₂ := mem_center_closure_pair hφ
  have key : Subgroup.center ↥H₂ = ⊥ → φ = 1 := by
    intro hc
    have hmem : (⟨φ, hφ_mem⟩ : ↥H₂) ∈ Subgroup.center ↥H₂ := hφcen
    rw [hc, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  rcases hN G B hB K H₂ hK_le hK hnormK with hcase | hcase
  · obtain ⟨e⟩ := hcase
    exact key (center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot (by norm_num)))
  · obtain ⟨e⟩ := hcase
    exact key (center_eq_bot_of_mulEquiv e
      (CFSG.center_perm_eq_bot_of_three_le_card (α := Fin 6) (by simp)))

theorem sec9m_normal_trivial {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 16)
    (hAut : Nat.card (MulAut V) = 20160) {H K R : Subgroup (MulAut V)} (hKH : K ≤ H)
    (hK : Nonempty (↥K ≃* alternatingGroup (Fin 6)))
    (htrans : ∀ b b' : V, b ≠ 1 → b' ≠ 1 → ∃ h ∈ H, h b = b')
    (hRH : R ≤ H) (hnorm : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hnotK : ¬ K ≤ R) :
    ∀ r ∈ R, ∀ b : V, r b = b := by
  obtain ⟨e⟩ := hK
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by norm_num)
  have hsimpleK : IsSimpleGroup ↥K := e.isSimpleGroup
  have hnorm_inf : ((K ⊓ R).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    exact ⟨K.mul_mem (K.mul_mem hk hh.1) (K.inv_mem hk),
      hnorm k (hKH hk) h hh.2⟩
  have hkey : K ⊓ R = ⊥ ∨ K ⊓ R = K := by
    have := (Subgroup.isSimpleGroup_iff (H := K)).mp hsimpleK
    exact this.2 (K ⊓ R) inf_le_left hnorm_inf
  have hinf : K ⊓ R = ⊥ := by
    rcases hkey with h | h
    · exact h
    · exact absurd (le_trans (le_of_eq h.symm) inf_le_right) hnotK
  have hcardK : Nat.card ↥K = 360 := sec9m_card_A6 ⟨e⟩
  have hdvd : Nat.card ↥K * Nat.card ↥R ∣ Nat.card ↥H :=
    sec9m_card_mul_dvd hKH hRH hnorm hinf
  have hdvd_aut : Nat.card ↥H ∣ Nat.card (MulAut V) := Subgroup.card_subgroup_dvd_card H
  have hR56 : Nat.card ↥R ∣ 56 := by
    have h1 : Nat.card ↥K * Nat.card ↥R ∣ 20160 := by
      rw [← hAut]
      exact dvd_trans hdvd hdvd_aut
    rw [hcardK] at h1
    rwa [show (20160 : ℕ) = 360 * 56 by norm_num,
      Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 360)] at h1
  have hV' : Nat.card V - 1 = 15 := by rw [hV]
  have hcop : Nat.Coprime (Nat.card ↥R) (Nat.card V - 1) := by
    rw [hV']
    exact Nat.Coprime.coprime_dvd_left hR56 (by norm_num : Nat.Coprime 56 15)
  exact sec9m_normal_fixes hRH hnorm htrans hcop

end CFSG.OddStandard.SmallF3.Omega
