module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutHS29
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAmbient

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem mem_normalizer_of_normalIn {H K : Subgroup G} (hK : NormalIn H K) {g : G}
    (hg : g ∈ K) : g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => hK.2 g hg x hx, fun hx => by
    have h1 := hK.2 g⁻¹ (K.inv_mem hg) (g * x * g⁻¹) hx
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [h2] at h1⟩

private theorem l12_x₁_ne_one (hc : Ctx11 t L S x₁ x₂ lam rho tau) : x₁ ≠ 1 := by
  intro h
  have h4 := hc.wreath.ord_x₁
  rw [h, orderOf_one] at h4
  exact absurd h4 (by norm_num)

private theorem l12_x₂_ne_x₁ (hc : Ctx11 t L S x₁ x₂ lam rho tau) : x₂ ≠ x₁ := by
  intro h
  have hmem : x₁ ∈ (⊥ : Subgroup G) := by
    rw [← hc.wreath.inf_eq_bot]
    exact ⟨Subgroup.mem_zpowers x₁, by rw [← h]; exact Subgroup.mem_zpowers x₂⟩
  exact l12_x₁_ne_one hc (by simpa using hmem)

private theorem l12_x₂_eq_x₁_of_comm (hc : Ctx11 t L S x₁ x₂ lam rho tau)
    (h : lam * x₁ = x₁ * lam) : x₂ = x₁ := by
  have hconj := hc.wreath.conj_x₁
  rw [h] at hconj
  rw [mul_assoc, mul_inv_cancel, mul_one] at hconj
  exact hconj.symm

private theorem l12_dichotomy_nonabelian (hc : Ctx11 t L S x₁ x₂ lam rho tau)
    (hcomm : ¬ ∀ a ∈ ctxQ t tau x₁ x₂ rho, ∀ b ∈ ctxQ t tau x₁ x₂ rho, a * b = b * a) :
    IsSylSL34 (ctxQ t tau x₁ x₂ rho) := by
  set Q : Subgroup G := ctxQ t tau x₁ x₂ rho with hQ
  have hNQ : NormalIn Q (ctxM t tau x₁ x₂) := by rw [hQ]; exact hc.normal_Q
  have hρ : rho ∈ normalizer (Q : Set G) :=
    mem_normalizer_of_normalIn hNQ (l12_rho_lam_mem_M hc).1
  have hlam : lam ∈ normalizer (Q : Set G) :=
    mem_normalizer_of_normalIn hNQ (l12_rho_lam_mem_M hc).2
  have hx₁Q' : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q (Subgroup.subset_closure (by simp))
  have hx₁Q : x₁ ∈ Q := by rw [hQ]; exact hx₁Q'
  have hx₁ne : x₁ ≠ 1 := l12_x₁_ne_one hc
  have hfρ : ∃ h ∈ Q, rho * h ≠ h * rho := by
    refine ⟨x₁, hx₁Q, fun hconj => ?_⟩
    exact hx₁ne (l12_cent_Q_rho hc x₁ hx₁Q' hconj.symm)
  have hfx : ∃ h ∈ Q, lam * h ≠ h * lam := by
    refine ⟨x₁, hx₁Q, fun hconj => ?_⟩
    exact l12_x₂_ne_x₁ hc (l12_x₂_eq_x₁_of_comm hc hconj)
  have hs : Outside.Sigma3Rel (Outside.conjAut Q rho hρ) (Outside.conjAut Q lam hlam) :=
    Outside.sigma3Rel_conjAut Q hρ hlam hc.ord_rho hc.wreath.ord_lam hc.lam_rho hfρ hfx
  have hfpf : ∀ g : ↥Q, Outside.conjAut Q rho hρ g = g → g = 1 := by
    intro g hg
    have h1 : rho * (g : G) * rho⁻¹ = (g : G) := by
      have := congrArg (fun x : ↥Q => (x : G)) hg
      simpa [Outside.conjAut_coe] using this
    have h2 : rho * (g : G) = (g : G) * rho := (mul_inv_eq_iff_eq_mul).mp h1
    exact Subtype.ext (l12_cent_Q_rho hc (g : G) (hQ ▸ g.2) h2.symm)
  have hnab : ∃ a b : ↥Q, a * b ≠ b * a := by
    have hcomm' := hcomm
    push Not at hcomm'
    obtain ⟨a, ha, b, hb, hab⟩ := hcomm'
    exact ⟨⟨a, hQ.symm ▸ ha⟩, ⟨b, hQ.symm ▸ hb⟩,
      fun h => hab (congrArg Subtype.val h)⟩
  have hcard : Nat.card ↥Q = 64 := by
    rw [hQ, l12_card_Q hc]
    norm_num
  exact (Outside.HS29 hcard hnab hs hfpf).1

theorem l12_dichotomy (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho) ∨ IsSylSL34 (ctxQ t tau x₁ x₂ rho) := by
  by_cases hcomm : ∀ a ∈ ctxQ t tau x₁ x₂ rho, ∀ b ∈ ctxQ t tau x₁ x₂ rho, a * b = b * a
  · left
    have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
      hc.base_le_Q (Subgroup.subset_closure (by simp))
    have hx₂Q : x₂ ∈ ctxQ t tau x₁ x₂ rho :=
      hc.base_le_Q (Subgroup.subset_closure (by simp))
    refine isZ4Z4E4_of_abelian hc.wreath hx₁Q hx₂Q hcomm ?_ ?_
    · rw [l12_card_Q hc]; norm_num
    · intro a ha
      exact l12_sq_mem_V hc (l12_Q_le_R hc ha)
  · right
    exact l12_dichotomy_nonabelian hc hcomm

theorem l12_b (hc : Ctx11 t L S x₁ x₂ lam rho tau) : Lemma4_12bConcl t tau x₁ x₂ lam rho := by
  unfold Lemma4_12bConcl
  generalize hM : ctxM t tau x₁ x₂ = M
  generalize hQ : ctxQ t tau x₁ x₂ rho = Q
  generalize hC : ctxCO t tau x₁ x₂ rho = C
  generalize hR : ctxR t tau x₁ x₂ = R
  generalize hO : ctxO t tau x₁ x₂ = O
  generalize hB : closure {t, tau} = B
  generalize hD : closure {rho, lam} = D
  have hR_le_O : R ≤ O := by rw [← hR, ← hO]; exact hc.R_le_O
  have hO_le_M : O ≤ M := by
    rw [← hO, ← hM]
    exact Subgroup.map_subtype_le (H := ctxM t tau x₁ x₂) (CFSG.pCore 2 (ctxM t tau x₁ x₂))
  have hQ_le_R : Q ≤ R := by rw [← hQ, ← hR]; exact l12_Q_le_R hc
  have hQ_le_M : Q ≤ M := (hQ_le_R.trans hR_le_O).trans hO_le_M
  have hC_le_O : C ≤ O := by
    rw [← hC, ← hO]
    change ctxO t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) ≤ ctxO t tau x₁ x₂
    exact inf_le_left
  have hC_le_M : C ≤ M := hC_le_O.trans hO_le_M
  have hP_le_M : zpowers rho ≤ M := by
    rw [← hM]; exact Subgroup.zpowers_le.mpr (l12_rho_lam_mem_M hc).1
  have hL_le_M : zpowers lam ≤ M := by
    rw [← hM]; exact Subgroup.zpowers_le.mpr (l12_rho_lam_mem_M hc).2
  have hB_le_C : B ≤ C := by
    have h : B ≤ ctxCO t tau x₁ x₂ rho := by
      change B ≤ ctxO t tau x₁ x₂ ⊓ centralizer ({rho} : Set G)
      rw [← hB, ← hc.CR_rho]
      exact inf_le_inf_right _ hc.R_le_O
    rwa [hC] at h
  have hR_eq : R = Q ⊔ B := by rw [← hR, l12_R_eq hc, hQ, hB]
  have hR_le : R ≤ Q ⊔ (C ⊔ zpowers rho) := by
    rw [hR_eq]
    apply sup_le
    · exact le_sup_left
    · exact (hB_le_C.trans le_sup_left).trans le_sup_right
  have hO_eq : O = R ⊔ C := by rw [← hO, hc.O_eq, hR, hC]
  have hO_le : O ≤ (Q ⊔ (C ⊔ zpowers rho)) ⊔ zpowers lam := by
    rw [hO_eq]
    apply sup_le
    · exact hR_le.trans le_sup_left
    · exact (le_sup_left.trans le_sup_right).trans le_sup_left
  have hD_le : D ≤ (Q ⊔ (C ⊔ zpowers rho)) ⊔ zpowers lam := by
    rw [← hD, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      have hP : zpowers rho ≤ (Q ⊔ (C ⊔ zpowers rho)) ⊔ zpowers lam :=
        (le_sup_right.trans (le_sup_right.trans le_sup_left))
      exact hP (Subgroup.mem_zpowers rho)
    · rw [hx]
      have hL : zpowers lam ≤ (Q ⊔ (C ⊔ zpowers rho)) ⊔ zpowers lam := le_sup_right
      exact hL (Subgroup.mem_zpowers lam)
  have hM_eq : M = O ⊔ D := by rw [← hM, hc.M_eq, hO, hD]
  apply le_antisymm
  · rw [hM_eq]
    apply sup_le
    · exact hO_le
    · exact hD_le
  · refine sup_le (sup_le ?_ (sup_le ?_ ?_)) ?_
    · exact hQ_le_M
    · exact hC_le_M
    · exact hP_le_M
    · exact hL_le_M

theorem l12_a (hc : Ctx11 t L S x₁ x₂ lam rho tau) : Lemma4_12aConcl t tau x₁ x₂ rho := by
  unfold Lemma4_12aConcl
  exact ⟨l12_phi_R hc, l12_B_normal hc, l12_CQ_t hc, l12_card_Q hc, l12_R_eq hc,
    l12_Q_eq_comm_R hc, l12_dichotomy hc⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
