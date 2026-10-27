module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetup

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.ABGLocalTools

theorem card_eq_card_map_mul_card_ker_inf {N Γ : Type*} [Group N] [Group Γ] (ρ : N →* Γ)
    (X : Subgroup N) :
    Nat.card X = Nat.card (X.map ρ) * Nat.card (ρ.ker ⊓ X : Subgroup N) := by
  rw [← Subgroup.relIndex_ker, Subgroup.relIndex_mul_card]

theorem exists_card_zpowers_eq_two_pow {G : Type*} [Group G] {g : G} (h : g * g = 1) :
    ∃ a : ℕ, Nat.card (Subgroup.zpowers g) = 2 ^ a := by
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 1)).mp (by simpa using hdvd)
  exact ⟨a, by rw [Nat.card_zpowers, ha]⟩

theorem isSylowOf_inf_comap_zpowers {N Γ : Type*} [Group N] [Finite N] [Group Γ]
    (ρ : N →* Γ) (P : Sylow 2 N) {y : N} (hy : y ∈ (P : Subgroup N))
    (hsq : ρ y * ρ y = 1) :
    IsSylowOf 2 ((P : Subgroup N) ⊓ (Subgroup.zpowers (ρ y)).comap ρ)
      ((Subgroup.zpowers (ρ y)).comap ρ) := by
  have hKH : ρ.ker ≤ (Subgroup.zpowers (ρ y)).comap ρ := fun k hk => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hk]
    exact Subgroup.one_mem _
  have hP : IsSylowOf 2 (P : Subgroup N) ⊤ := by
    rw [isSylowOf_iff]
    exact ⟨le_top, P.isPGroup', by simpa using P.not_dvd_index⟩
  have hS : IsSylowOf 2 ((P : Subgroup N) ⊓ ρ.ker) ρ.ker :=
    hP.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  have hle : Subgroup.zpowers (ρ y) ≤ ρ.range := Subgroup.zpowers_le.mpr ⟨y, rfl⟩
  have hHmap : ((Subgroup.zpowers (ρ y)).comap ρ).map ρ = Subgroup.zpowers (ρ y) := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hle]
  have hRmap : ((P : Subgroup N) ⊓ (Subgroup.zpowers (ρ y)).comap ρ).map ρ =
      Subgroup.zpowers (ρ y) := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨-, hxH⟩, rfl⟩
      exact hxH
    · rw [Subgroup.zpowers_le]
      exact ⟨y, ⟨hy, Subgroup.mem_zpowers _⟩, rfl⟩
  have hinf : ρ.ker ⊓ ((P : Subgroup N) ⊓ (Subgroup.zpowers (ρ y)).comap ρ) =
      (P : Subgroup N) ⊓ ρ.ker := by
    ext x
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_comap]
    constructor
    · rintro ⟨hk, hxP, -⟩
      exact ⟨hxP, hk⟩
    · rintro ⟨hxP, hk⟩
      exact ⟨hk, hxP, by rw [hk]; exact Subgroup.one_mem _⟩
  have hHcard : Nat.card ((Subgroup.zpowers (ρ y)).comap ρ) =
      Nat.card (Subgroup.zpowers (ρ y)) * Nat.card ρ.ker := by
    rw [card_eq_card_map_mul_card_ker_inf ρ, hHmap, inf_eq_left.mpr hKH]
  have hRcard : Nat.card ((P : Subgroup N) ⊓ (Subgroup.zpowers (ρ y)).comap ρ :
      Subgroup N) = Nat.card (Subgroup.zpowers (ρ y)) *
        Nat.card ((P : Subgroup N) ⊓ ρ.ker : Subgroup N) := by
    rw [card_eq_card_map_mul_card_ker_inf ρ, hRmap, hinf]
  obtain ⟨a, ha⟩ := exists_card_zpowers_eq_two_pow hsq
  refine isSylowOf_of_card inf_le_right ?_
  rw [hRcard, hHcard, hS.card_eq, ha, Nat.factorization_mul (by positivity) Nat.card_pos.ne']
  simp [pow_add, Nat.Prime.factorization_pow Nat.prime_two]

theorem exists_involution_of_map_eq {N Γ : Type*} [Group N] [Finite N] [Group Γ]
    (ρ : N →* Γ) (P : Sylow 2 N) {y ι : N} (hy : y ∈ (P : Subgroup N)) (hι : ι * ι = 1)
    (hρ : ρ ι = ρ y) : ∃ ι' ∈ (P : Subgroup N), ι' * ι' = 1 ∧ ρ ι' = ρ y := by
  have hsq : ρ y * ρ y = 1 := by rw [← hρ, ← map_mul, hι, map_one]
  have hR := isSylowOf_inf_comap_zpowers ρ P hy hsq
  set H : Subgroup N := (Subgroup.zpowers (ρ y)).comap ρ with hH
  have hιH : ι ∈ H := by
    rw [hH, Subgroup.mem_comap, hρ]
    exact Subgroup.mem_zpowers _
  have hzι : IsPGroup 2 (Subgroup.zpowers (⟨ι, hιH⟩ : H)) := by
    obtain ⟨a, ha⟩ := exists_card_zpowers_eq_two_pow
      (g := (⟨ι, hιH⟩ : H)) (Subtype.ext (by simpa using hι))
    exact IsPGroup.of_card ha
  obtain ⟨Q, hQ⟩ := hzι.exists_le_sylow
  have hQs : IsSylowOf 2 ((Q : Subgroup H).map H.subtype) H := ⟨Q, rfl⟩
  obtain ⟨k, hkH, hk⟩ := hR.exists_mem_conj hQs
  have hιQ : ι ∈ (Q : Subgroup H).map H.subtype :=
    ⟨⟨ι, hιH⟩, hQ (Subgroup.mem_zpowers _), rfl⟩
  obtain ⟨hιP, -⟩ := (hk ι).mp hιQ
  refine ⟨k⁻¹ * ι * k, hιP, ?_, ?_⟩
  · calc k⁻¹ * ι * k * (k⁻¹ * ι * k) = k⁻¹ * (ι * ι) * k := by group
      _ = 1 := by rw [hι]; group
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hkH)
    have hc : Commute (ρ y) (ρ k) := by
      rw [← hm]
      exact (Commute.refl _).zpow_right m
    rw [map_mul, map_mul, map_inv, hρ]
    exact hc.symm.inv_mul_cancel

section Centralizer

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_centralizer (W : Subgroup G) :
    normalizer (W : Set G) ≤ normalizer (centralizer (W : Set G) : Set G) := by
  have key : ∀ m ∈ normalizer (W : Set G), ∀ c ∈ centralizer (W : Set G),
      m * c * m⁻¹ ∈ centralizer (W : Set G) := by
    intro m hm c hc
    rw [mem_centralizer_iff]
    intro w hw
    have hw' : m⁻¹ * w * m ∈ W := (mem_normalizer_iff''.1 hm w).1 hw
    have h1 := mem_centralizer_iff.1 hc _ hw'
    calc w * (m * c * m⁻¹) = m * ((m⁻¹ * w * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * w * m)) * m⁻¹ := by rw [h1]
      _ = m * c * m⁻¹ * w := by group
  intro n hn
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key n hn c, fun hc => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hc
  simpa [mul_assoc] using this

theorem exists_conj_mem_of_centralizer [Finite G] {X W : Subgroup G}
    (hX : IsSylowOf 2 X (⊤ : Subgroup G)) (hXW : X ≤ normalizer (W : Set G)) {u : G}
    (hu : u ∈ centralizer (W : Set G)) (hu2 : IsPGroup 2 (zpowers u)) :
    ∃ k ∈ centralizer (W : Set G), k⁻¹ * u * k ∈ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXN : IsSylowOf 2 X (normalizer (W : Set G)) := hX.of_le hXW le_top
  have hXC : IsSylowOf 2 (X ⊓ centralizer (W : Set G)) (centralizer (W : Set G)) :=
    hXN.inf_of_le_normalizer (centralizer_le_normalizer _) (normalizer_le_normalizer_centralizer W)
  obtain ⟨P', hP', hle⟩ := exists_isSylowOf_of_le hu2 (zpowers_le.2 hu)
  obtain ⟨k, hk, hconj⟩ := hXC.exists_mem_conj hP'
  exact ⟨k, hk, ((hconj u).1 (hle (mem_zpowers u))).1⟩

end Centralizer

end CFSG.OddStandard.ChengHeld
