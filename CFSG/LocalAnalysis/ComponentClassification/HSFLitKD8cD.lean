module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cPi

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem nfBits_head_of_R1 : ∀ x : MC, inR1 x = true → (MC.nfBits x).headI = false := by
  decide +kernel

theorem nfBits_ne_nil : ∀ x : MC, MC.nfBits x ≠ [] := by decide +kernel

theorem inE_tu : ∀ j : Fin 8, inE j (MC.t * MC.u) = true → j = 1 ∨ j = 7 := by decide +kernel

theorem inE_ztu : ∀ j : Fin 8, inE j (MC.z * (MC.t * MC.u)) = true → j = 1 ∨ j = 7 := by
  decide +kernel

theorem fpf_of_triple : ∀ i a : Fin 8, interCard a 1 = interCard i 0 →
    interCard a 0 = interCard i 1 → interCard a 7 = interCard i 6 → a ≠ i := by
  decide

namespace Conf

variable (K : Conf S T₁)

theorem R1_le {H : Subgroup X}
    (h : ∀ g ∈ [MC.u, MC.w₁, MC.v, MC.z, MC.y, MC.t, MC.k], K.ι g ∈ H) : K.R1 ≤ H := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' := MC.nf_spec x
  have hb := nfBits_head_of_R1 x hx
  have hne := nfBits_ne_nil x
  obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hne
  rw [hbs, List.headI_cons] at hb
  rw [hx', map_nfProd, hbs, hb]
  simp only [MC.gens, List.map_cons, List.map_nil, nfProd, Bool.false_eq_true, ↓reduceIte,
    one_mul]
  have hc := nfProd_mem_closure (S := (H : Set X))
    [K.ι MC.u, K.ι MC.w₁, K.ι MC.v, K.ι MC.z, K.ι MC.y, K.ι MC.t, K.ι MC.k] (by simpa using h) bs
  rwa [closure_eq] at hc

theorem cN_mem_T : K.P.cN ∈ A.T := B_le_T S K.P.cN_mem_B

theorem R1_le_T₁ : K.R1 ≤ T₁ := by
  have hT : A.T ≤ T₁ := K.h4.le
  refine K.R1_le fun g hg => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [K.ι_u]; exact hT (mul_mem A.t_mem_T (mul_mem (x_mem_T S) (y_mem_T S)))
  · rw [Conf.ι_w₁, CPair.w₁N_eq]; exact mul_mem K.P.V.w₁_mem_T₁ (hT K.cN_mem_T)
  · rw [CPair.ι_v]; exact K.P.V.vN_mem_T₁
  · rw [K.ι_z]; exact hT (z_mem_T S)
  · rw [K.ι_y]; exact hT (y_mem_T S)
  · have := hT A.t_mem_T
    rwa [← K.ι_t] at this
  · rw [K.ι_k]; exact hT C.k_mem

include K in
theorem d_mem_T₁ : C.d ∈ T₁ := K.h4.le C.d_mem

theorem d_conj_Ex0 {e : X} (he : e ∈ K.Ex 0) : C.d * e * C.d⁻¹ ∈ K.Ex 1 := by
  rw [← K.E₁_eq] at he
  rw [← K.E₂_eq]
  exact d_conj_E₁ S he

theorem d_conj_Ex1 {e : X} (he : e ∈ K.Ex 1) : C.d * e * C.d⁻¹ ∈ K.Ex 0 := by
  rw [← K.E₂_eq] at he
  rw [← K.E₁_eq]
  exact (KD46.conj_E_of_not_mem_TE S (KD46.d_mem_T S) (KD46.d_not_mem_TE S)).2 he

theorem d_not_mem_R1 : C.d ∉ K.R1 := by
  intro hd
  apply KD46.E_y_ne S
  rw [K.E₁_eq, K.E₂_eq]
  refine (K.conj_Ex_of_le (n := C.d) (fun e he => K.R1_conj_Ex hd he)).symm.trans ?_
  exact K.conj_Ex_of_le fun e he => K.d_conj_Ex0 he

theorem relIndex_R1 : K.R1.relIndex T₁ = 2 := by
  have h1 := K.h4.card
  have h2 := card_T_le C
  have hdvd : Nat.card K.R1 ∣ Nat.card T₁ := Subgroup.card_dvd_of_le K.R1_le_T₁
  rw [K.card_R1] at hdvd
  have hne : Nat.card T₁ ≠ 128 := by
    intro h
    have heq : K.R1 = T₁ := eq_of_le_of_card_ge K.R1_le_T₁ (by rw [h, K.card_R1])
    exact K.d_not_mem_R1 (by rw [heq]; exact d_mem_T₁ K)
  have hpos : 0 < Nat.card T₁ := Nat.card_pos
  obtain ⟨m, hm⟩ := hdvd
  have hm2 : m = 2 := by
    rcases m with _ | _ | _ | m
    · omega
    · omega
    · rfl
    · omega
  have := relIndex_mul_card K.R1 T₁
  rw [inf_of_le_left K.R1_le_T₁, K.card_R1, hm, hm2] at this
  omega

theorem normR1_d : K.NormR1 C.d := by
  intro g hg
  have hn : (K.R1.subgroupOf T₁).Normal := Subgroup.normal_of_index_eq_two K.relIndex_R1
  have := hn.conj_mem ⟨g, K.R1_le_T₁ hg⟩ (mem_subgroupOf.mpr hg) ⟨C.d, d_mem_T₁ K⟩
  exact mem_subgroupOf.mp this

theorem pi_d_0 : K.pi K.normR1_d 0 = 1 := K.pi_eq_of _ fun _ he => K.d_conj_Ex0 he

theorem pi_d_1 : K.pi K.normR1_d 1 = 0 := K.pi_eq_of _ fun _ he => K.d_conj_Ex1 he

theorem pi_d_6 : K.pi K.normR1_d 6 = 7 := by
  have hy : S.y ∈ K.Ex 6 := by rw [← K.ι_y]; exact K.ι_mem_Ex (by decide +kernel)
  have h := K.conj_mem_pi K.normR1_d hy
  obtain ⟨m, hm, hι⟩ := K.mem_Ex.mp h
  have key : K.pi K.normR1_d 6 = 1 ∨ K.pi K.normR1_d 6 = 7 := by
    rcases conj_refl_of_ψ (KD46.d_mem_T S) (KD46.ψ_d S) (isRefl_y S) with h1 | h1
    · rw [show S.d = C.d from rfl] at h1
      rw [h1, ← K.ι_tu] at hι
      rw [K.ι_injective hι] at hm
      exact inE_tu _ hm
    · rw [show S.d = C.d from rfl] at h1
      rw [h1, x_inv_eq S, mul_assoc, ← K.ι_tu, ← K.ι_z, ← map_mul] at hι
      rw [K.ι_injective hι] at hm
      exact inE_ztu _ hm
  rcases key with h1 | h1
  · exfalso
    have := K.pi_injective K.normR1_d (h1.trans K.pi_d_0.symm)
    exact absurd this (by decide)
  · exact h1

theorem pi_d_ne (i : Fin 8) : K.pi K.normR1_d i ≠ i := by
  refine fpf_of_triple i _ ?_ ?_ ?_
  · rw [← K.pi_d_0, K.interCard_pi]
  · rw [← K.pi_d_1, K.interCard_pi]
  · rw [← K.pi_d_6, K.interCard_pi]

end Conf

end KD8c

end CFSG.ComponentClassification.HSFLit
