module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenRootQ
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGen

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup

section Invol

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem cycleType_eq_replicate_of_mul_self {σ : Perm α} (h2 : σ * σ = 1) :
    σ.cycleType = Multiset.replicate (σ.support.card / 2) 2 := by
  have hall : ∀ x ∈ σ.cycleType, x = 2 := by
    intro x hx
    have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h2])
    have h2le := two_le_of_mem_cycleType hx
    have hle := Nat.le_of_dvd (by norm_num) ((dvd_of_mem_cycleType hx).trans hord)
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.mpr hall
  have hsum := sum_cycleType σ
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hrep]
  congr 1
  omega

theorem exists_cycleType_eq_replicate {σ : Perm α} (h1 : σ ≠ 1) (h2 : σ * σ = 1)
    (hs : sign σ = 1) : ∃ j : ℕ, 1 ≤ j ∧ σ.cycleType = Multiset.replicate (2 * j) 2 ∧
      4 * j ≤ Fintype.card α := by
  have hrep := cycleType_eq_replicate_of_mul_self h2
  set k := σ.support.card / 2 with hk
  have hsign := sign_of_cycleType σ
  rw [hs, hrep, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  have hev : (k * 2 + k) % 2 = 0 := by
    by_contra hodd
    have hodd' : Odd (k * 2 + k) := Nat.odd_iff.mpr (by omega)
    rw [hodd'.neg_one_pow] at hsign
    exact absurd hsign (by decide)
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, Multiset.replicate_zero] at hrep
    exact h1 (cycleType_eq_zero.mp hrep)
  have hsum := sum_cycleType σ
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hcard : σ.support.card ≤ Fintype.card α := Finset.card_le_univ _
  refine ⟨k / 2, by omega, ?_, by omega⟩
  rw [hrep]
  congr 1
  omega

end Invol

section Pair

variable {m : ℕ}

theorem card_support_zPair : (zPair m).support.card = 2 * m := by
  have h : (zPair m).support = Finset.univ := by
    ext ⟨k, b⟩
    simp only [mem_support, Finset.mem_univ, iff_true, zPair_apply, ne_eq, Prod.mk.injEq,
      true_and]
    fin_cases b <;> simp
  rw [h, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]

theorem cycleType_zPair : (zPair m).cycleType = Multiset.replicate m 2 := by
  have h2 : zPair m * zPair m = 1 := by
    refine Equiv.ext fun ⟨k, b⟩ => ?_
    rw [Perm.mul_apply, zPair_apply, zPair_apply, swap_apply_self]
    rfl
  rw [cycleType_eq_replicate_of_mul_self h2, card_support_zPair]
  congr 1
  omega

end Pair

theorem AltGenSetting.rootFusionAt_of_four {G : Type} [Group G] [Finite G] {A R T : Subgroup G}
    {g : G} {n : ℕ} {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenSetting A R T g n Φ)
    (h7 : 7 ≤ n)
    (h4 : ∀ (h8 : 2 * 4 ≤ n + 4) (x : G),
      x * Φ (pairAlt h8 (zAlt (m := 4) ⟨2, rfl⟩)) * x⁻¹ ∈ centralizer (A : Set G) → False) :
    RootFusionAt A Φ := by
  intro π x hπ2 hπ1 hx
  have hπ2' : (π : Perm (Fin (n + 4))) * π = 1 := by
    rw [← Subgroup.coe_mul, hπ2]
    rfl
  have hπ1' : (π : Perm (Fin (n + 4))) ≠ 1 := fun h => hπ1 (Subtype.ext h)
  obtain ⟨j, hj1, hct, hj4⟩ := exists_cycleType_eq_replicate hπ1' hπ2' π.2
  rw [Fintype.card_fin] at hj4
  rcases (by omega : j = 1 ∨ j = 2 ∨ 3 ≤ j) with rfl | rfl | hj3
  · rw [hct]
    rfl
  · exfalso
    have h8 : 2 * 4 ≤ n + 4 := by omega
    set z := pairAlt h8 (zAlt (m := 4) ⟨2, rfl⟩) with hz
    have hzc : (z : Perm (Fin (n + 4))).cycleType = (π : Perm (Fin (n + 4))).cycleType := by
      rw [hz, coe_pairAlt, cycleType_viaEmbeddingHom', hct]
      exact cycleType_zPair
    have hzz : zAlt (m := 4) ⟨2, rfl⟩ * zAlt (m := 4) ⟨2, rfl⟩ = 1 := zAlt_mul_self _
    have hz2 : z * z = 1 := by rw [hz, ← map_mul, hzz, map_one]
    have hz1 : z ≠ 1 := fun h =>
      zAlt_ne_one _ (by norm_num) (pairAlt_injective h8 (h.trans (map_one _).symm))
    obtain ⟨β, hβ⟩ := exists_conj_eq_of_cycleType_eq hzc hz2 hz1
    refine h4 h8 (x * Φ β) ?_
    have h1 : x * Φ β * Φ z * (x * Φ β)⁻¹ = x * Φ π * x⁻¹ := by
      rw [← hβ, map_mul, map_mul, map_inv]
      group
    rw [← hz, h1]
    exact hx
  · exfalso
    have hm : Even (2 * j) := ⟨j, by ring⟩
    have h2m : 2 * (2 * j) ≤ n + 4 := by omega
    set z := pairAlt h2m (zAlt (m := 2 * j) hm) with hz
    have hzc : (z : Perm (Fin (n + 4))).cycleType = (π : Perm (Fin (n + 4))).cycleType := by
      rw [hz, coe_pairAlt, cycleType_viaEmbeddingHom', hct]
      exact cycleType_zPair
    have hzz : zAlt (m := 2 * j) hm * zAlt (m := 2 * j) hm = 1 := zAlt_mul_self _
    have hz2 : z * z = 1 := by rw [hz, ← map_mul, hzz, map_one]
    have hz1 : z ≠ 1 := fun h =>
      zAlt_ne_one _ (by omega) (pairAlt_injective h2m (h.trans (map_one _).symm))
    obtain ⟨β, hβ⟩ := exists_conj_eq_of_cycleType_eq hzc hz2 hz1
    refine s.false_of_conj_mem_of_six_le h7 (by omega) hm h2m (x := x * Φ β) ?_
    have h1 : x * Φ β * Φ z * (x * Φ β)⁻¹ = x * Φ π * x⁻¹ := by
      rw [← hβ, map_mul, map_mul, map_inv]
      group
    rw [← hz, h1]
    exact hx

theorem altRootFusion : AltRootFusion := by
  intro G _ _ A R T g n Φ s hn _ π x hπ2 hπ1 hx
  exact s.rootFusionAt_of_four (by omega) (fun h8 _ hx' => s.false_of_conj_mem_four hn h8 hx')
    π x hπ2 hπ1 hx

end CFSG.ComponentClassification.RankTwoAlt
