module

public import CFSG.ClassicalInvolution.Q3.Q3T6DC3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace Std20Three

variable (d : Std20Three K K' J S R R' W V z t)
include d

theorem sec20X_le_normalizers :
    sec20X (CoreAssembly.conjClass K) z K K' ≤
      Subgroup.normalizer (K : Set G) ⊓ Subgroup.normalizer (K' : Set G) := by
  unfold sec20X
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup₂_le fun U hU => ?_
    obtain ⟨hUU, hUC⟩ := hU
    obtain ⟨L₀, hL₀, hUL₀⟩ := Sec6Gen.exists_member_of_mem_USet d.late_hΩ hUU
    have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ hUU
    obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet d.late_hΩ hUU
    refine le_inf ?_ ?_
    · by_cases h : L₀ = K
      · subst h
        exact hUL₀.trans Subgroup.le_normalizer
      · exact Sec6Gen.le_normalizer_of_le_centralizer d.late_hΩ d.late_mem_K hL₀ (Ne.symm h)
          d.viol.hzK hUL₀ hU2 (by omega) hUC
    · by_cases h : L₀ = K'
      · subst h
        exact hUL₀.trans Subgroup.le_normalizer
      · exact Sec6Gen.le_normalizer_of_le_centralizer d.late_hΩ d.late_mem_K' hL₀ (Ne.symm h)
          d.late_hzK' hUL₀ hU2 (by omega) hUC
  · exact le_inf Subgroup.le_normalizer d.late_K_le
  · exact le_inf d.late_K'_le Subgroup.le_normalizer

theorem sec20X_le_C :
    sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.centralizer ({z} : Set G) :=
  sec20X_le_centralizer (le_sup_left.trans d.sup_le_centralizer_z)
    (le_sup_right.trans d.sup_le_centralizer_z)

theorem concl20_3_of_res_pt (hH : Hex20 (CoreAssembly.conjClass K) K J W)
    (hres : ∀ c ∈ Subgroup.centralizer ({z} : Set G),
      conjSub c V ≤ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K'))) :
    Concl20_3 K K' V z := by
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  show sec20X (CoreAssembly.conjClass K) z K K' =
    oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K'))
  have hNX : oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K')) ≤
      sec20X (CoreAssembly.conjClass K) z K K' :=
    sup_le (oddCoreOf_le_self _) (sup_le (tw.hVX) le_sec20X_pair)
  refine le_antisymm ?_ hNX
  set N := oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K')) with hN
  have hMN : K ⊔ K' ≤ N := le_trans le_sup_right le_sup_right
  have hKconj : ∀ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c K ≤ K ⊔ K' := fun c hc => by
    rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inl rfl) hc with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right
  have hK'conj : ∀ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c K' ≤ K ⊔ K' := fun c hc => by
    rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inr rfl) hc with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right
  unfold sec20X
  refine sup_le (sup_le ?_ (le_trans le_sup_left hMN)) (le_trans le_sup_right hMN)
  refine iSup₂_le fun U hU => ?_
  obtain ⟨hUU, hUC⟩ := hU
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ hUU
  obtain ⟨c, hc, hcU⟩ := d.exists_conj_le_S hU2 hUC
  have hU1 : conjSub c U ∈ USet (CoreAssembly.conjClass K) := USet.conj d.hyp.conjInvariant hUU c
  have hc' : c⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := (Subgroup.centralizer _).inv_mem hc
  have hback : U = conjSub c⁻¹ (conjSub c U) := (conjSub_inv_conjSub c U).symm
  rcases d.U_cases hU1 hcU with h | h | h
  · have h1 : conjSub c U ≤ V ⊔ K :=
      h.trans ((d.W_le_V_sup_K hH).trans (sup_le_sup_left inf_le_right V))
    have h2 := conjSub_mono (n := c⁻¹) h1
    rw [conjSub_inv_conjSub, conjSub_sup'] at h2
    exact h2.trans (sup_le (hres c⁻¹ hc') ((hKconj c⁻¹ hc').trans hMN))
  · have h2 := conjSub_mono (n := c⁻¹) h
    rw [conjSub_inv_conjSub] at h2
    exact h2.trans ((hKconj c⁻¹ hc').trans hMN)
  · have h2 := conjSub_mono (n := c⁻¹) h
    rw [conjSub_inv_conjSub] at h2
    exact h2.trans ((hK'conj c⁻¹ hc').trans hMN)

end Std20Three

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
