module

public import CFSG.CGT.Stroth77.Arch76Lemma2Cases

public section

namespace CFSG.CGT.Stroth77

namespace Arch76.Config

variable {X : Type*} [Group X] (C : Config X) [C.A.Normal]

theorem lemma2 (hρodd : Odd (orderOf C.ρ)) (hCA : Subgroup.centralizer (C.A : Set X) = C.A)
    (P : Sylow 2 X) (hTP : C.A ⊔ Subgroup.closure {C.uv, C.t, C.u} ≤ P)
    (hE : ∀ g ∈ (P : Subgroup X),
      g ∈ Subgroup.normalizer (Subgroup.closure {C.x ^ 2, C.y ^ 2, C.uv, C.t} : Set X) →
        g ∈ C.A ⊔ Subgroup.closure {C.uv, C.t, C.u}) :
    (P : Subgroup X) = C.A ⊔ Subgroup.closure {C.uv, C.t, C.u} ∨
      ∃ s ∈ (P : Subgroup X), (P : Subgroup X) = C.A ⊔ Subgroup.closure {C.uv, C.t, C.u, s} ∧
        s ^ 2 = 1 ∧ s⁻¹ * C.w * s = C.w ∧ s⁻¹ * C.x * s = C.x⁻¹ ∧ s⁻¹ * C.y * s = C.y⁻¹ ∧
        ((s⁻¹ * C.uv * s = C.x * C.y * C.uv ∧ s⁻¹ * C.t * s = C.x⁻¹ * C.t ∧
            s⁻¹ * C.u * s = C.u) ∨
          (s⁻¹ * C.uv * s = C.x⁻¹ * C.y * C.uv ∧ s⁻¹ * C.t * s = C.x⁻¹ * C.y ^ 2 * C.t ∧
            s⁻¹ * C.u * s = C.w * C.u)) := by
  have hρ3 := C.ρ_cube hCA hρodd
  have hPTK := C.sylow_eq hCA P hTP
  by_cases h1 : ∃ k ∈ C.K, Lρ (C.kap k) ≠ C.kap k
  · obtain ⟨k, hk, hρk⟩ := h1
    obtain ⟨s, hs, hκ⟩ := C.exists_gam1 hk hρk
    exact (C.compIII_false hCA P hE hs hκ).elim
  push Not at h1
  by_cases h2 : ∃ k ∈ C.K, C.kap k ≠ 0 ∧ C.kap k ≠ al0
  · obtain ⟨k, hk, h0, ha⟩ := h2
    obtain ⟨r, hr, hκ⟩ := C.exists_bet hk (h1 k hk) h0 ha
    exact (C.compII_false hCA hρ3 P hE hr hκ).elim
  push Not at h2
  by_cases h3 : ∃ s ∈ C.K, C.kap s = al0
  · right
    obtain ⟨s0, hs0, hκ0⟩ := h3
    obtain ⟨s, hs, hκ, hrel⟩ := C.compI hCA hρ3 P hE hs0 hκ0
    have hK : C.K = C.A ⊔ Subgroup.closure {s} := by
      refine le_antisymm (fun k hk => ?_)
        (sup_le C.A_le_K ((Subgroup.closure_le _).mpr (by simpa using hs)))
      by_cases hk0 : C.kap k = 0
      · exact Subgroup.mem_sup_left ((C.kap_eq_zero_iff hCA hk).mp hk0)
      · obtain ⟨v, hv⟩ := C.exists_ev_of_kap_eq hCA hs hk (by rw [h2 k hk hk0, hκ])
        rw [hv]
        exact mul_mem (Subgroup.mem_sup_right (Subgroup.subset_closure rfl))
          (Subgroup.mem_sup_left (C.ev_mem v))
    refine ⟨s, C.K_le hCA P hs, ?_, hrel⟩
    rw [hPTK, hK, sup_sup_sup_comm, sup_idem, ← Subgroup.closure_union]
    congr 2
    ext z
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]
  · left
    push Not at h3
    have hK : C.K = C.A := le_antisymm
      (fun k hk => (C.kap_eq_zero_iff hCA hk).mp (by_contra fun h => h3 k hk (h2 k hk h)))
      C.A_le_K
    rw [hPTK, hK]
    exact sup_eq_left.mpr le_sup_left

end Arch76.Config

end CFSG.CGT.Stroth77
