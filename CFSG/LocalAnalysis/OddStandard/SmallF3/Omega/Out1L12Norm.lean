module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1L12LA
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {S : Type} [Group S]

private lemma aor_l12_mem_normalizer_zpowers_iff [Finite S] {u x : S} :
    x ∈ Subgroup.normalizer (Subgroup.zpowers u : Set S) ↔
      x * u * x⁻¹ ∈ Subgroup.zpowers u := by
  constructor
  · intro hx
    exact (Subgroup.mem_normalizer_iff.mp hx u).mp (Subgroup.mem_zpowers u)
  · intro hx
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hn
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx
    change x * n * x⁻¹ ∈ Subgroup.zpowers u
    refine Subgroup.mem_zpowers_iff.mpr ⟨j * m, ?_⟩
    calc u ^ (j * m) = (u ^ j) ^ m := zpow_mul u j m
      _ = (x * u * x⁻¹) ^ m := by rw [hj]
      _ = x * u ^ m * x⁻¹ := conj_zpow
      _ = x * n * x⁻¹ := by rw [hm]

theorem aor_l12_normal [Finite S] (hS : IsPGroup 2 S) {t u : S} (h : L12Main S t u) :
    (Subgroup.zpowers u).Normal := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Subgroup.normalizer_eq_top_iff]
  let M : Subgroup S := Subgroup.normalizer (Subgroup.zpowers u : Set S)
  change M = ⊤
  by_contra hMne
  have hM_iff : ∀ x : S, x ∈ M ↔ x * u * x⁻¹ ∈ Subgroup.zpowers u :=
    fun x => aor_l12_mem_normalizer_zpowers_iff
  have hMlt : M < ⊤ := lt_top_iff_ne_top.mpr hMne
  haveI : Group.IsNilpotent S := hS.isNilpotent
  have hMlt' : M < Subgroup.normalizer (M : Set S) :=
    Group.normalizerCondition_of_isNilpotent M hMlt
  obtain ⟨s, hs_norm, hs_notM⟩ := SetLike.exists_of_lt hMlt'
  have hN_le_M : L12N t ≤ M := by
    intro n hn
    rw [hM_iff]
    have hc := h.N_comm n hn
    simpa [hc] using Subgroup.mem_zpowers u
  have htM : t ∈ M := by
    rw [hM_iff]
    have hu : t * u * t⁻¹ = u := by rw [← h.coord.comm]; group
    rw [hu]
    exact Subgroup.mem_zpowers u
  let u₁ : S := s * u * s⁻¹
  have hu₁_notU : u₁ ∉ Subgroup.zpowers u := by
    intro hmem
    exact hs_notM ((hM_iff s).mpr hmem)
  have hu₁_ord : orderOf u₁ = 4 := by
    have hsem : SemiconjBy s u u₁ := by
      change s * u = (s * u * s⁻¹) * s
      group
    rw [← SemiconjBy.orderOf_eq s hsem]
    exact h.coord.ord_u
  have h_a : ∀ m ∈ M, m * u₁ * m⁻¹ ∈ Subgroup.zpowers u₁ := by
    intro m hm
    have hm' : s⁻¹ * m * s ∈ M := by
      have hiff := (Subgroup.mem_set_normalizer_iff.mp hs_norm) (s⁻¹ * m * s)
      rw [show s * (s⁻¹ * m * s) * s⁻¹ = m by group] at hiff
      exact hiff.mpr hm
    have hmu : (s⁻¹ * m * s) * u * (s⁻¹ * m * s)⁻¹ ∈ Subgroup.zpowers u :=
      (hM_iff (s⁻¹ * m * s)).mp hm'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmu
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    change (s * u * s⁻¹) ^ k = m * (s * u * s⁻¹) * m⁻¹
    rw [conj_zpow, hk]
    group
  have htu₁_ord : orderOf (t * u₁ * t⁻¹) = 4 := by
    have hsem : SemiconjBy t u₁ (t * u₁ * t⁻¹) := by
      show t * u₁ = (t * u₁ * t⁻¹) * t
      group
    rw [← SemiconjBy.orderOf_eq t hsem]
    exact hu₁_ord
  rcases aor_l12_zpowers_four hu₁_ord (h_a t htM) htu₁_ord with htu | htu
  ·
    exfalso
    have hu₁_comm : u₁ * t = t * u₁ := by
      have h2 : t * u₁ = u₁ * t := by
        have := congrArg (fun z => z * t) htu
        simpa [mul_assoc] using this
      exact h2.symm
    have hu₁R : u₁ ∈ L12R t := Subgroup.mem_centralizer_singleton_iff.mpr hu₁_comm
    have huR : u ∈ L12R t := Subgroup.mem_centralizer_singleton_iff.mpr h.coord.comm
    have hM_le_N : M ≤ L12N t := by
      rw [Subgroup.le_normalizer_iff]
      intro m hm y hyR
      obtain ⟨i, j, hy⟩ := L12Coord.R_gen h.coord hu₁_comm hu₁_ord hu₁_notU
        (Subgroup.mem_centralizer_singleton_iff.mp hyR)
      have hmu : (m * u * m⁻¹) ^ i ∈ L12R t :=
        (L12R t).pow_mem (Subgroup.zpowers_le.mpr huR ((hM_iff m).mp hm)) i
      have hmu₁ : (m * u₁ * m⁻¹) ^ j ∈ L12R t :=
        (L12R t).pow_mem (Subgroup.zpowers_le.mpr hu₁R (h_a m hm)) j
      have heq : m * (u ^ i * u₁ ^ j) * m⁻¹
          = (m * u * m⁻¹) ^ i * (m * u₁ * m⁻¹) ^ j := by
        calc m * (u ^ i * u₁ ^ j) * m⁻¹
            = (m * u ^ i * m⁻¹) * (m * u₁ ^ j * m⁻¹) := by group
          _ = (m * u * m⁻¹) ^ i * (m * u₁ * m⁻¹) ^ j := by rw [← conj_pow, ← conj_pow]
      rw [hy, heq]
      exact (L12R t).mul_mem hmu hmu₁
    have hNM_eq : L12N t = M := le_antisymm hN_le_M hM_le_N
    have hs_normN : s ∈ Subgroup.normalizer (L12N t : Set S) := by
      rw [hNM_eq]
      exact hs_norm
    have huN : u ∈ L12N t := Subgroup.le_normalizer huR
    have hsu_N : s * u * s⁻¹ ∈ L12N t :=
      (Subgroup.mem_normalizer_iff.mp hs_normN u).mp huN
    have hsu_central : ∀ n ∈ L12N t, n * (s * u * s⁻¹) = (s * u * s⁻¹) * n := by
      intro n hn
      have hn' : s⁻¹ * n * s ∈ L12N t :=
        (Subgroup.mem_normalizer_iff''.mp hs_normN n).mp hn
      have hc := h.N_comm (s⁻¹ * n * s) hn'
      calc n * (s * u * s⁻¹)
          = s * ((s⁻¹ * n * s) * u) * s⁻¹ := by group
        _ = s * (u * (s⁻¹ * n * s)) * s⁻¹ := by rw [hc]
        _ = (s * u * s⁻¹) * n := by group
    have hsu_U : s * u * s⁻¹ ∈ Subgroup.zpowers u :=
      h.center_N (s * u * s⁻¹) hsu_N hsu_central
    exact hs_notM ((hM_iff s).mpr hsu_U)
  ·
    exfalso
    have hcu : (s⁻¹ * t * s) * u * (s⁻¹ * t * s)⁻¹ = u⁻¹ := by
      have h1 : (s⁻¹ * t * s) * u * (s⁻¹ * t * s)⁻¹
          = s⁻¹ * (t * u₁ * t⁻¹) * s := by
        change (s⁻¹ * t * s) * u * (s⁻¹ * t * s)⁻¹
          = s⁻¹ * (t * (s * u * s⁻¹) * t⁻¹) * s
        group
      rw [h1, htu]
      have h2 : s⁻¹ * u₁⁻¹ * s = u⁻¹ := by
        change s⁻¹ * (s * u * s⁻¹)⁻¹ * s = u⁻¹
        group
      exact h2
    have hmemU : (s⁻¹ * t * s) * u * (s⁻¹ * t * s)⁻¹ ∈ Subgroup.zpowers u := by
      rw [hcu]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers u)
    have hLA : (s⁻¹ * t * s) * u = u * (s⁻¹ * t * s) := by
      have hmemU' : (s⁻¹ * t * (s⁻¹)⁻¹) * u * (s⁻¹ * t * (s⁻¹)⁻¹)⁻¹
          ∈ Subgroup.zpowers u := by
        simpa using hmemU
      simpa using aor_l12_LA hS h s⁻¹ hmemU'
    have hcu_mult : (s⁻¹ * t * s) * u = u⁻¹ * (s⁻¹ * t * s) := by
      have := congrArg (fun z => z * (s⁻¹ * t * s)) hcu
      simpa [mul_assoc] using this
    have huu : u⁻¹ = u := by
      have h1 : u⁻¹ * (s⁻¹ * t * s) = u * (s⁻¹ * t * s) := by
        rw [← hcu_mult]
        exact hLA
      exact mul_right_cancel h1
    exact h.coord.z_ne_one (by
      have : u * u = 1 := by
        calc u * u = u * u⁻¹ := by rw [huu]
          _ = 1 := mul_inv_cancel u
      simpa [pow_two] using this)

end CFSG.OddStandard.SmallF3.Omega
