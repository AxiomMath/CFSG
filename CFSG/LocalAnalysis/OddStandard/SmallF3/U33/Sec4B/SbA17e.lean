module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbA17d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private theorem fourGrp_le_baseGrp (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [fourGrp, baseGrp, Subgroup.closure_le]
  rintro g (hg : g ∈ ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G))
  rcases hg with rfl | rfl
  · exact pow_mem (Subgroup.subset_closure (by simp)) 2
  · exact pow_mem (mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2

private theorem lam_sq (hc : Ctx13 t L S x₁ x₂ lam rho tau om) : lam * lam = 1 := by
  have h := pow_orderOf_eq_one lam
  rw [hc.wreath.ord_lam] at h
  simpa [pow_two] using h

theorem l17_g_facts (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    (t * lam) * (t * lam) = 1 ∧ t * lam ∈ ctxK t tau x₁ x₂ rho ∧
      (t * lam) * x₁ ^ 2 * (t * lam)⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 ∧
      (t * lam) * (x₁ * x₂) ^ 2 * (t * lam)⁻¹ = (x₁ * x₂) ^ 2 := by
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have hl2 : lam * lam = 1 := lam_sq hc
  have hlt : lam * t = t * lam := (l17_lam_comm hc).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (t * lam) * (t * lam) = t * (lam * t) * lam := by group
      _ = t * (t * lam) * lam := by rw [hlt]
      _ = (t * t) * (lam * lam) := by group
      _ = 1 := by rw [ht2, hl2, one_mul]
  · exact (ctxK t tau x₁ x₂ rho).mul_mem (l17_mem_K hc).1 (l17_mem_K hc).2.2.2.1
  · have hy := (l17_cent_V hc (x₁ ^ 2) (Subgroup.subset_closure (by simp))).1
    have hz := (l17_cent_V hc ((x₁ * x₂) ^ 2) (Subgroup.subset_closure (by simp))).1
    have hy' : t * x₁ ^ 2 * t⁻¹ = x₁ ^ 2 := by rw [hy]; group
    have hz' : t * (x₁ * x₂) ^ 2 * t⁻¹ = (x₁ * x₂) ^ 2 := by rw [hz]; group
    calc (t * lam) * x₁ ^ 2 * (t * lam)⁻¹
        = t * (lam * x₁ ^ 2 * lam⁻¹) * t⁻¹ := by group
      _ = t * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * t⁻¹ := by rw [l17_lam_y hc]
      _ = (t * x₁ ^ 2 * t⁻¹) * (t * (x₁ * x₂) ^ 2 * t⁻¹) := by group
      _ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by rw [hy', hz']
  · have hz := (l17_cent_V hc ((x₁ * x₂) ^ 2) (Subgroup.subset_closure (by simp))).1
    have hz' : t * (x₁ * x₂) ^ 2 * t⁻¹ = (x₁ * x₂) ^ 2 := by rw [hz]; group
    calc (t * lam) * (x₁ * x₂) ^ 2 * (t * lam)⁻¹
        = t * (lam * (x₁ * x₂) ^ 2 * lam⁻¹) * t⁻¹ := by group
      _ = t * (x₁ * x₂) ^ 2 * t⁻¹ := by rw [l17_lam_z hc]
      _ = (x₁ * x₂) ^ 2 := hz'

theorem l17_v1 (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∃ v₁ : G, v₁ ∈ ctxQ t tau x₁ x₂ rho ∧ v₁ ^ 2 = 1 ∧ v₁ ∉ fourGrp x₁ x₂ ∧
      (t * lam) * v₁ * (t * lam)⁻¹ = v₁ := by
  obtain ⟨V', v₁, v₂, hV'⟩ := hc.data_V
  obtain ⟨hVab, hVcard, hVQ, hVbot, hVrho, hVlt, hVY, hVcent, hv₁V, hv₁ne,
    htv₁, hv₂V, hv₂not, hVgen, htv₂, hltv₂, hQt, homx₁, homx₂⟩ := hV'
  refine ⟨v₁, ?_, hVab.2 v₁ hv₁V, ?_, ?_⟩
  · rw [hVQ]; exact Subgroup.mem_sup_right hv₁V
  · intro hv
    have hbase : v₁ ∈ baseGrp x₁ x₂ := fourGrp_le_baseGrp x₁ x₂ hv
    have hmem : v₁ ∈ baseGrp x₁ x₂ ⊓ V' := ⟨hbase, hv₁V⟩
    rw [hVbot] at hmem
    exact hv₁ne (Subgroup.mem_bot.mp hmem)
  · have hcent : v₁ ∈ centralizer ({lam * t} : Set G) := by
      have hmem : v₁ ∈ (zpowers v₁ : Subgroup G) := Subgroup.mem_zpowers v₁
      rw [← hVcent] at hmem
      exact hmem.2
    have hcomm : (lam * t) * v₁ = v₁ * (lam * t) :=
      Subgroup.mem_centralizer_iff.mp hcent (lam * t) (by simp)
    rw [show t * lam = lam * t from (l17_lam_comm hc).1.symm, hcomm]
    group

theorem l17_exists_w (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮)
    (hx : ∃ x ∈ ctxP t tau x₁ x₂ rho, x ^ 4 ≠ 1) :
    ∃ w ∈ ctxP t tau x₁ x₂ rho, w ^ 4 = (x₁ * x₂) ^ 2 ∧ (t * lam) * w * (t * lam)⁻¹ = w := by
  obtain ⟨x, hxP, hx4⟩ := hx
  have hρ3 : rho ^ 3 = 1 := by
    rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
  have hρP : ∀ y ∈ ctxP t tau x₁ x₂ rho, rho * y * rho⁻¹ ∈ ctxP t tau x₁ x₂ rho := by
    intro y hy
    exact (l17_P_normal hc.toCtx13).2 rho (l17_mem_K hc.toCtx13).2.2.2.2 y hy
  have hVρ : ∀ v ∈ fourGrp x₁ x₂, rho * v * rho⁻¹ ∈ fourGrp x₁ x₂ := by
    intro v hv
    have hρM : rho ∈ ctxM t tau x₁ x₂ := by
      rw [hc.M_eq]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    exact hc.normal_V.2 rho hρM v hv
  have hfix : ∀ v ∈ fourGrp x₁ x₂, rho * v * rho⁻¹ = v → v = 1 := by
    intro v hv hconj
    have hvP : v ∈ ctxP t tau x₁ x₂ rho :=
      l17_Q_le_P hc.toCtx13 (ctxYq_le_ctxQ (l17_V_le_Y hc.toCtx13 hv))
    have hcomm : v * rho = rho * v := by
      have h : rho * v = v * rho := by
        calc rho * v = rho * v * rho⁻¹ * rho := by group
          _ = v * rho := by rw [hconj]
      exact h.symm
    exact l17_CP_rho hc.toCtx13 v hvP hcomm
  have hpow : ∀ y ∈ fourGrp x₁ x₂, ∃ w ∈ ctxP t tau x₁ x₂ rho, w ^ 4 = y :=
    exists_pow_four_eq (P := ctxP t tau x₁ x₂ rho) (V := fourGrp x₁ x₂) (ρ := rho)
      (l17_P_comm hc) hρ3 hρP (l17_card_V hc.toCtx13) hVρ hfix
      (l17_pow_four_mem_V hc) hxP hx4
  obtain ⟨w₀, hw₀P, hw₀4⟩ := hpow (x₁ ^ 2) (Subgroup.subset_closure (by simp))
  let g : G := t * lam
  let c : G := g * w₀ * g⁻¹
  have hgf : (t * lam) * (t * lam) = 1 ∧ t * lam ∈ ctxK t tau x₁ x₂ rho ∧
      (t * lam) * x₁ ^ 2 * (t * lam)⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 ∧
      (t * lam) * (x₁ * x₂) ^ 2 * (t * lam)⁻¹ = (x₁ * x₂) ^ 2 :=
    l17_g_facts hc.toCtx13
  have hgK : g ∈ ctxK t tau x₁ x₂ rho := hgf.2.1
  have hgg : g * g = 1 := hgf.1
  have hgy : g * x₁ ^ 2 * g⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := hgf.2.2.1
  have hcP : c ∈ ctxP t tau x₁ x₂ rho :=
    (l17_P_normal hc.toCtx13).2 g hgK w₀ hw₀P
  have hcomm : w₀ * c = c * w₀ := l17_P_comm hc w₀ hw₀P c hcP
  refine ⟨w₀ * c, (ctxP t tau x₁ x₂ rho).mul_mem hw₀P hcP, ?_, ?_⟩
  · have hc4 : c ^ 4 = g * w₀ ^ 4 * g⁻¹ := by
      dsimp [c]; rw [conj_pow]
    have hw4 : (w₀ * c) ^ 4 = w₀ ^ 4 * c ^ 4 := Commute.mul_pow hcomm 4
    rw [hw4, hc4, hw₀4, hgy]
    have hx₁4 : x₁ ^ 4 = 1 := by
      have h := pow_orderOf_eq_one x₁
      rw [hc.wreath.ord_x₁] at h
      exact h
    have hx₁sq : x₁ ^ 2 * x₁ ^ 2 = 1 := by
      rw [← pow_add]; simpa using hx₁4
    rw [← mul_assoc, hx₁sq, one_mul]
  · have hgcg : g * c * g⁻¹ = w₀ := by
      have hginv : g⁻¹ * g⁻¹ = 1 := by rw [← mul_inv_rev, hgg, inv_one]
      dsimp [c]
      calc g * (g * w₀ * g⁻¹) * g⁻¹ = (g * g) * w₀ * (g⁻¹ * g⁻¹) := by group
        _ = w₀ := by rw [hgg, hginv, one_mul, mul_one]
    calc g * (w₀ * c) * g⁻¹ = (g * w₀ * g⁻¹) * (g * c * g⁻¹) := by group
      _ = c * w₀ := by rw [hgcg]
      _ = w₀ * c := hcomm.symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
