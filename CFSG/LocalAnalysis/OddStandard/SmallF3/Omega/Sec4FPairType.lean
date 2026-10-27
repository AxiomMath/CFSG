module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FTrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.pair_type (h : Sec4FSetup t L S z A B φ) {k : G} {c₀ c : Option (Fin 7)}
    (hcc : c ≠ c₀) (hk : k⁻¹ * sec4MPt t φ c₀ * k = t) :
    InducesTypeSome L (k⁻¹ * sec4MPt t φ c * k) 7 1 6 (-1) := by
  obtain ⟨n, ν, hnN, hν, hν0⟩ := h.exists_move_pt c₀
  have hnt : n * t * n⁻¹ = sec4MPt t φ c₀ := by
    have h1 := hν none
    rwa [h.pt_none, hν0] at h1
  have hc₁t : (k⁻¹ * n) * t = t * (k⁻¹ * n) := by
    calc (k⁻¹ * n) * t = (k⁻¹ * (n * t * n⁻¹) * k) * (k⁻¹ * n) := by group
      _ = t * (k⁻¹ * n) := by rw [hnt, hk]
  have hc₁N : k⁻¹ * n ∈ normalizer (L : Set G) :=
    h.cent_le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hc₁t)
  have hq : ν⁻¹ c ≠ none := by
    intro h0
    apply hcc
    have h1 : c = ν none := by
      rw [← h0]
      simp
    rw [h1, hν0]
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hq
  have hcν : ν (some i) = c := by
    rw [← hi]
    simp
  have hptc : sec4MPt t φ c = n * sec4MPt t φ (some i) * n⁻¹ := by
    rw [hν (some i), hcν]
  have hv : IsEvenVec (sec4MW i) := sec4MW_even i
  have hv0 : sec4MW i ≠ 0 := by
    intro h0
    have hw : vecWeight (sec4MW i) = 0 := by rw [h0]; simp [vecWeight]
    rw [sec4MW_weight i] at hw
    exact absurd hw (by decide)
  have h6 : InducesTypeSome L (φ (sec4MW i)) 7 1 6 (-1) :=
    (h.data.bdata.type6 _ hv hv0).mp (sec4MW_weight i)
  have hφL : φ (sec4MW i) ∈ L := h.B_le_L (h.data.bdata.perm.mem hv)
  have h6t : InducesTypeSome L (φ (sec4MW i) * t) 7 1 6 (-1) :=
    (sec4F_type_mul_cent_iff h.omega7 h.t_mem_cent (Or.inr (Or.inr rfl))).mpr h6
  have hptφ : sec4MPt t φ (some i) = φ (sec4MW i) * t := h.t_cent_L hφL
  have hconj : k⁻¹ * sec4MPt t φ c * k =
      (k⁻¹ * n) * sec4MPt t φ (some i) * (k⁻¹ * n)⁻¹ := by
    rw [hptc]
    group
  rw [hconj, hptφ]
  exact sec4F_type_conj_norm h.omega7 hc₁N (Or.inr (Or.inr rfl)) h6t

end CFSG.OddStandard.SmallF3.Omega
