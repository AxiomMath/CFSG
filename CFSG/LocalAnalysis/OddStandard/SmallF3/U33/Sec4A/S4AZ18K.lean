module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18G
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AN4C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem z18_rho_mem_M (h : L41GPh14 t L S x₁ x₂ lam rho) : rho ∈ l41M t x₁ x₂ rho := by
  rw [h.qfacts.M_eq]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem z18_lam_mem_M (h : L41GPh14 t L S x₁ x₂ lam rho) : lam ∈ l41M t x₁ x₂ rho := by
  rw [h.qfacts.M_eq]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem z18_t_mem_M (t x₁ x₂ rho : G) : t ∈ l41M t x₁ x₂ rho :=
  Subgroup.le_normalizer (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

theorem z18_conj_Q1 (h : L41GPh15 t L S x₁ x₂ lam rho) {g : G} (hg : g ∈ l41M t x₁ x₂ rho)
    {q : G} (hq : q ∈ l41Q1 t x₁ x₂ rho) : g * q * g⁻¹ ∈ l41Q1 t x₁ x₂ rho :=
  h.q1facts.normal_Q1.2 g hg q hq

theorem z18_conj_Y (h : L41GPh13 t L S x₁ x₂ lam rho) {g : G} (hg : g ∈ l41M t x₁ x₂ rho)
    {y : G} (hy : y ∈ l41Y t x₁ x₂ rho) : g * y * g⁻¹ ∈ l41Y t x₁ x₂ rho :=
  h.mbasic.normal_Y.2 g hg y hy

theorem z18_Y_sq (h : L41GPh11 t L S x₁ x₂ lam rho) {y : G} (hy : y ∈ l41Y t x₁ x₂ rho) :
    y * y = 1 :=
  h.yfacts.Y_elem.1.mul_self_eq_one hy

theorem z18_Y_comm (h : L41GPh11 t L S x₁ x₂ lam rho) {a b : G} (ha : a ∈ l41Y t x₁ x₂ rho)
    (hb : b ∈ l41Y t x₁ x₂ rho) : a * b = b * a :=
  h.yfacts.Y_elem.1.comm ha hb

theorem z18_Y_central (h : L41GPh16 t L S x₁ x₂ lam rho) {y : G}
    (hy : y ∈ l41Y t x₁ x₂ rho) {k : G} (hk : k ∈ l41Q1 t x₁ x₂ rho) : y * k = k * y := by
  have : k ∈ l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [h.centQ1]
    exact hk
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp this).2 y hy

theorem z18_Q1_comm (h : L41GPh15 t L S x₁ x₂ lam rho) {a b : G}
    (ha : a ∈ l41Q1 t x₁ x₂ rho) (hb : b ∈ l41Q1 t x₁ x₂ rho) :
    a * b * a⁻¹ * b⁻¹ ∈ l41Y t x₁ x₂ rho := by
  have := h.q1facts.comm_le (Subgroup.commutator_mem_commutator ha hb)
  simpa [commutatorElement_def] using this

theorem z18_fix_Q1 (h : L41GPh15 t L S x₁ x₂ lam rho) {k : G} (hk : k ∈ l41Q1 t x₁ x₂ rho)
    (hc : rho * k * rho⁻¹ * k⁻¹ ∈ l41Y t x₁ x₂ rho) : k ∈ l41Y t x₁ x₂ rho := by
  have hkQ : k ∈ l41Q t x₁ x₂ rho := by
    rw [h.q1facts.Q_eq]
    exact Subgroup.mem_sup_left hk
  have hcomm : ⁅k, rho⁆ ∈ l41Y t x₁ x₂ rho := by
    have : ⁅k, rho⁆ = (rho * k * rho⁻¹ * k⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact Subgroup.inv_mem _ hc
  have hmem : k ∈ ((zpowers t ⊔ l41Y t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [← h.qfacts.cent_Qbar_rho]
    exact ⟨hkQ, hcomm⟩
  have htN : zpowers t ≤ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_conj_mem fun y hy =>
      z18_conj_Y h.toL41GPh13 (z18_t_mem_M t x₁ x₂ rho) hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ htN] at hmem
  obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_mul.mp hmem
  rcases pt_eq_one_or_of_mem_zpowers h.hyp.ord_t ha with h1 | h1
  · rw [h1, one_mul] at hk ⊢
    exact hy
  · exfalso
    apply h.q1facts.t_not_mem
    rw [h1] at hk
    simpa using Subgroup.mul_mem _ hk (Subgroup.inv_mem _ (h.q1facts.Y_le hy))

theorem z18_cent_Q1_rho (h : L41GPh15 t L S x₁ x₂ lam rho) {k : G}
    (hk : k ∈ l41Q1 t x₁ x₂ rho) (hρ : rho * k = k * rho) : k = 1 := by
  have hkQ : k ∈ l41Q t x₁ x₂ rho := by
    rw [h.q1facts.Q_eq]
    exact Subgroup.mem_sup_left hk
  have hmem : k ∈ l41Q t x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hkQ, Subgroup.mem_centralizer_singleton_iff.mpr hρ.symm⟩
  rw [h.qfacts.cent_Q_rho] at hmem
  rcases pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hmem with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hk) h.q1facts.t_not_mem

theorem z18_hlam (h : L41GPh17 t L S x₁ x₂ lam rho) :
    ∀ g : G, ∀ k ∈ l41Q1 t x₁ x₂ rho, g⁻¹ * t * g ≠ lam * k := by
  intro g k hk hgk
  have hρM := z18_rho_mem_M h.toL41GPh14
  have hlM := z18_lam_mem_M h.toL41GPh14
  have hinv : (lam * k) * (lam * k) = 1 := by
    rw [← hgk]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [t_mul_self h.hyp]; group
  have hcard : Nat.card ↥(l41Y t x₁ x₂ rho) = Nat.card ↥(l41Y t x₁ x₂ rho ⊓
      centralizer ({lam} : Set G)) * Nat.card ↥(l41Y t x₁ x₂ rho ⊓
      centralizer ({lam} : Set G)) := by
    rw [h.yfacts.Y_elem.2, h.yfacts.card_cent_Y_lam]
  obtain ⟨w, -, hw⟩ := z18_coh h.q1facts.Y_le
    (fun y hy k hk => z18_Y_central h.toL41GPh16 hy hk)
    (fun y hy => z18_Y_sq h.toL41GPh11 hy) h.q1elem
    (fun a ha b hb => z18_Q1_comm h.toL41GPh15 ha hb)
    (fun k hk => z18_conj_Q1 h.toL41GPh15 hρM hk) (fun y hy => z18_conj_Y h.toL41GPh13 hρM hy)
    (fun k hk => z18_conj_Q1 h.toL41GPh15 hlM hk) (fun y hy => z18_conj_Y h.toL41GPh13 hlM hy)
    (n4_rho_cube h.toCtx0) (n4_lam_sq h.toCtx0) h.lam_rho
    (fun k hk hc => z18_fix_Q1 h.toL41GPh15 hk hc) hcard k hk hinv
  have hlam1 : lam ≠ 1 := by
    intro h1
    have := h.wreath.ord_lam
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨c, -, hc⟩ := h.invol_L lam (generators_mem_L h.toCtx0).2.2 (n4_lam_sq h.toCtx0) hlam1
  refine h.fusion.not_conj_z ((g * w * c)⁻¹) ?_
  have e1 : t = g * (w * lam * w⁻¹) * g⁻¹ := by
    rw [hw, ← hgk]
    group
  rw [e1, ← hc]
  group

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
