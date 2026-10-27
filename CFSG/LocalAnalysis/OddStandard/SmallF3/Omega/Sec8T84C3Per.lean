module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

private theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem alt6_not_comm : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  letI : CommGroup (alternatingGroup (Fin 6)) :=
    { (inferInstance : Group (alternatingGroup (Fin 6))) with mul_comm := hcon }
  have hp := IsSimpleGroup.prime_card (α := alternatingGroup (Fin 6))
  rw [card_alt6] at hp
  have h2 := hp.eq_one_or_self_of_dvd 2 ⟨180, rfl⟩
  omega

theorem ker_dichotomy {K L : Type} [Group K] [Group L] (φ : K →* alternatingGroup (Fin 6))
    (hφ : Function.Surjective φ) (ρ : K →* L) :
    (∀ k : K, ∃ n ∈ φ.ker, ρ k = ρ n) ∨ ρ.ker ≤ φ.ker := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : (Subgroup.map φ ρ.ker).Normal :=
    Subgroup.Normal.map (inferInstance : ρ.ker.Normal) φ hφ
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.map φ ρ.ker) with h | h
  · right
    intro k hk
    have hmem : φ k ∈ Subgroup.map φ ρ.ker := ⟨k, hk, rfl⟩
    rw [h] at hmem
    simpa only [Subgroup.mem_bot, MonoidHom.mem_ker] using hmem
  · left
    intro k
    have hmem : φ k ∈ Subgroup.map φ ρ.ker := by
      rw [h]; exact Subgroup.mem_top _
    obtain ⟨k', hk', hk'eq⟩ := hmem
    refine ⟨k'⁻¹ * k, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hk'eq]
      simp
    · have hk'1 : ρ k' = 1 := MonoidHom.mem_ker.mp hk'
      rw [map_mul, map_inv, hk'1, inv_one, one_mul]

theorem exists_eq_of_card_lt {K L : Type} [Group K] [Finite K] [Group L] [Finite L]
    (φ : K →* alternatingGroup (Fin 6)) (hφ : Function.Surjective φ) (ρ : K →* L)
    (hL : Nat.card L < 360) (k : K) : ∃ n ∈ φ.ker, ρ k = ρ n := by
  rcases ker_dichotomy φ hφ ρ with h | h
  · exact h k
  · exfalso
    haveI : Nonempty ↥φ.ker := ⟨1⟩
    haveI : Finite ↥φ.ker := inferInstance
    have hφcard := Subgroup.card_ker_mul_card_of_surjective (f := φ) hφ
    have hρcard := Subgroup.card_ker_mul_card_range (f := ρ)
    have hL' : Nat.card L < Nat.card (alternatingGroup (Fin 6)) := by
      rw [card_alt6]; exact hL
    have hlt : Nat.card φ.ker * Nat.card L <
        Nat.card φ.ker * Nat.card (alternatingGroup (Fin 6)) :=
      Nat.mul_lt_mul_of_pos_left hL' Nat.card_pos
    have hker_le : Nat.card ρ.ker ≤ Nat.card φ.ker := Subgroup.card_le_of_le h
    have hrange_le : Nat.card ρ.range ≤ Nat.card L :=
      Nat.card_le_card_of_injective (fun x : ρ.range => (x : L))
        (fun a b hab => Subtype.ext hab)
    have hle : Nat.card ρ.ker * Nat.card ρ.range ≤ Nat.card φ.ker * Nat.card L :=
      Nat.mul_le_mul hker_le hrange_le
    have heq : Nat.card φ.ker * Nat.card (alternatingGroup (Fin 6)) =
        Nat.card ρ.ker * Nat.card ρ.range := by rw [hφcard, hρcard]
    omega

theorem exists_eq_of_comm {K L : Type} [Group K] [Group L]
    (φ : K →* alternatingGroup (Fin 6)) (hφ : Function.Surjective φ) (ρ : K →* L)
    (hL : ∀ a b : L, a * b = b * a) (k : K) : ∃ n ∈ φ.ker, ρ k = ρ n := by
  rcases ker_dichotomy φ hφ ρ with h | h
  · exact h k
  · exfalso
    have hcomm : ∀ a b : alternatingGroup (Fin 6), a * b = b * a := by
      intro a b
      obtain ⟨x, rfl⟩ := hφ a
      obtain ⟨y, rfl⟩ := hφ b
      have hxy : x * y * x⁻¹ * y⁻¹ ∈ ρ.ker := by
        rw [MonoidHom.mem_ker]
        calc ρ (x * y * x⁻¹ * y⁻¹)
            = ρ x * ρ y * (ρ x)⁻¹ * (ρ y)⁻¹ := by simp only [map_mul, map_inv]
          _ = ρ y * ρ x * (ρ x)⁻¹ * (ρ y)⁻¹ := by rw [hL (ρ x) (ρ y)]
          _ = 1 := by group
      have hxy1 : φ x * φ y * (φ x)⁻¹ * (φ y)⁻¹ = 1 := by
        have hmem := h hxy
        simpa only [MonoidHom.mem_ker, map_mul, map_inv] using hmem
      have h2 : (φ x * φ y) * (φ y * φ x)⁻¹ = 1 := by
        rw [← hxy1]; group
      exact mul_inv_eq_one.mp h2
    obtain ⟨a, b, hab⟩ := alt6_not_comm
    exact hab (hcomm a b)

theorem card_eq_of_quotEquivTo {Γ : Type} [Group Γ] [Finite Γ] {M N : Subgroup Γ}
    (h : QuotEquivTo M N (alternatingGroup (Fin 6))) (hNM : N ≤ M) :
    Nat.card M = 360 * Nat.card N := by
  obtain ⟨φ, hφ, hk⟩ := h
  have hcard := Subgroup.card_ker_mul_card_of_surjective (f := φ) hφ
  have hker : Nat.card φ.ker = Nat.card N := by
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]
  rw [card_alt6, hker] at hcard
  rw [mul_comm] at hcard
  exact hcard.symm

theorem exists_eq_of_quotEquivTo_card_lt {Γ : Type} [Group Γ] [Finite Γ] {M N : Subgroup Γ}
    (h : QuotEquivTo M N (alternatingGroup (Fin 6))) {L : Type} [Group L] [Finite L]
    (ρ : ↥M →* L) (hL : Nat.card L < 360) (m : ↥M) :
    ∃ n : ↥M, (n : Γ) ∈ N ∧ ρ m = ρ n := by
  obtain ⟨φ, hφ, hk⟩ := h
  haveI : Finite ↥M := inferInstance
  obtain ⟨n, hn, heq⟩ := exists_eq_of_card_lt φ hφ ρ hL m
  refine ⟨n, ?_, heq⟩
  rw [← Subgroup.mem_subgroupOf, ← hk]
  exact hn

theorem exists_eq_of_quotEquivTo_comm {Γ : Type} [Group Γ] {M N : Subgroup Γ}
    (h : QuotEquivTo M N (alternatingGroup (Fin 6))) {L : Type} [Group L]
    (ρ : ↥M →* L) (hL : ∀ a b : L, a * b = b * a) (m : ↥M) :
    ∃ n : ↥M, (n : Γ) ∈ N ∧ ρ m = ρ n := by
  obtain ⟨φ, hφ, hk⟩ := h
  obtain ⟨n, hn, heq⟩ := exists_eq_of_comm φ hφ ρ hL m
  refine ⟨n, ?_, heq⟩
  rw [← Subgroup.mem_subgroupOf, ← hk]
  exact hn

end C10

end CFSG.OddStandard.SmallF3.Omega
