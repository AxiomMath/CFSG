module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18L
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18N
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18F

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem z18_V1_dec (h : L41GPh16 t L S x₁ x₂ lam rho) {v : G}
    (hv : v ∈ l41V1 t x₁ x₂ rho lam) :
    ∃ q ∈ l41Q1 t x₁ x₂ rho, ∃ k : G,
      (k = 1 ∨ k = t ∨ k = lam ∨ k = t * lam) ∧ v = q * k := by
  have hKn : closure ({t, lam} : Set G) ≤
      normalizer ((l41Q1 t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    intro k hk
    have hkM : k ∈ l41M t x₁ x₂ rho :=
      z18_V1_le_M h.toL41GPh15 (Subgroup.mem_sup_right (Subgroup.subset_closure hk))
    exact mem_normalizer_of_conj_mem fun q hq => h.q1facts.normal_Q1.2 k hkM q hq
  have hv' : v ∈ ((l41Q1 t x₁ x₂ rho ⊔ closure ({t, lam} : Set G) : Subgroup G) : Set G) := hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hKn] at hv'
  obtain ⟨q, hq, k, hk, rfl⟩ := Set.mem_mul.mp hv'
  exact ⟨q, hq, k, (m11_mem_K_iff h.toL41GPh5).mp hk, rfl⟩

theorem z18_exists_M (h : L41GPh17 t L S x₁ x₂ lam rho) {V₂ : Subgroup G}
    (hV₂ : IsPGroup 2 V₂) (hV₁ : l41V1 t x₁ x₂ rho lam ≤ V₂)
    (hN : V₂ ≤ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G))
    (hbig : ¬ V₂ ≤ l41V1 t x₁ x₂ rho lam) :
    ∃ M : Subgroup G, M ≤ V₂ ∧ M.relIndex V₂ = 2 ∧ t ∉ M ∧
      ∀ u ∈ M, u * u = 1 → u ∈ l41Q1 t x₁ x₂ rho ∨
        ∃ k ∈ l41Q1 t x₁ x₂ rho, u = lam * k := by
  have hY16 := h.yfacts.Y_elem.2
  have htl : t * lam = lam * t := m13_t_comm_L h.toL41GPh5 (generators_mem_L h.toCtx0).2.2
  refine z18_exists_M_abs hV₂ hN (fun a ha b hb => z18_Y_comm h.toL41GPh11 ha hb)
    (fun y hy => z18_Y_sq h.toL41GPh11 hy) hY16 (z18_cent_V2_Y' h hV₂ hV₁ hN)
    le_sup_left hV₁ ?_ ?_ (t_mul_self h.hyp) (n4_lam_sq h.toCtx0) htl h.q1facts.t_not_mem ?_ ?_
    (fun v hv => z18_V1_dec h.toL41GPh16 hv)
    (fun x hx hxt => z18_mem_V1_of_comm h hV₂ hV₁ hx hxt) hbig (z18_hlam h)
  · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  · exact fun hc => z18_not_cent h.yfacts.card_cent_Y_lam hY16 hc
  · intro hc
    refine z18_not_cent (k := t * lam) ?_ hY16 hc
    rw [htl]
    exact h.yfacts.card_cent_Y_lamt

theorem l41_final_of (h : L41GPh17 t L S x₁ x₂ lam rho) (hs : IsSimpleGroup G) : False := by
  obtain ⟨V₂, hV₂, hV₁, hN, hodd⟩ := z18_exists_V2 h.toL41GPh15
  have hbig : ¬ V₂ ≤ l41V1 t x₁ x₂ rho lam := by
    intro hle
    apply hodd
    rw [← le_antisymm hV₁ hle]
    exact h.q1facts.V1_not_sylow
  obtain ⟨M, hMV, hMidx, htM, hMu⟩ := z18_exists_M h hV₂ hV₁ hN hbig
  have htV₂ : t ∈ V₂ := hV₁ (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have h4 : 4 ∣ Nat.card G := by
    have hV1 := Subgroup.card_subgroup_dvd_card (l41V1 t x₁ x₂ rho lam)
    rw [h.q1facts.card_V1] at hV1
    exact Nat.dvd_trans (by norm_num : 4 ∣ 2 ^ 10) hV1
  exact z18_final_of_index_two hs h4 hV₂ hodd hMV hMidx (t_mul_self h.hyp) htV₂ htM
    hMu (fun g u hu => z18_tG_Q1 h.toL41GPh16 g hu) (z18_hlam h)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l41_final_holds : L41FinalStmt :=
  fun h => S4A.l41_final_of h.toG h.glob.simple

end CFSG.OddStandard.SmallF3.HarrisU33
