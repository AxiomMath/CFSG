module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ18
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma fourGrp_le_baseGrp_e (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [fourGrp, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · have h₁ : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    simpa [pow_two] using (baseGrp x₁ x₂).mul_mem h₁ h₁
  · have h₁ : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have h₂ : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have h₁₂ : x₁ * x₂ ∈ baseGrp x₁ x₂ := (baseGrp x₁ x₂).mul_mem h₁ h₂
    simpa [pow_two] using (baseGrp x₁ x₂).mul_mem h₁₂ h₁₂

theorem l18_Xi_special (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    (∀ x ∈ ctxXi t tau x₁ x₂ rho, x * x ∈ ctxYq t tau x₁ x₂ rho) ∧
      ∀ x ∈ ctxXi t tau x₁ x₂ rho, ∀ x' ∈ ctxXi t tau x₁ x₂ rho,
        x * x' * x⁻¹ * x'⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  obtain ⟨V', v₁, v₂, hV⟩ := hc.data_V
  have hV'card : Nat.card V' = 4 := hV.2.1
  have hbaseV' : baseGrp x₁ x₂ ⊓ V' = ⊥ := hV.2.2.2.1
  have hVrho : rho ∈ Subgroup.normalizer (V' : Set G) := hV.2.2.2.2.1
  have hVY : ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ ⊔ V' := hV.2.2.2.2.2.2.1
  have hρ3 : rho ^ 3 = 1 := by
    rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
  have hρΞ : ∀ x ∈ ctxXi t tau x₁ x₂ rho, rho * x * rho⁻¹ ∈ ctxXi t tau x₁ x₂ rho :=
    fun x hx => (l18_Xi_normal hc.toCtx13).2 rho (l17_mem_K hc.toCtx13).2.2.2.2 x hx
  have hρV : ∀ v ∈ V', rho * v * rho⁻¹ ∈ V' := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hVrho v).mp hv
  have hV'Y : V' ≤ ctxYq t tau x₁ x₂ rho := by
    rw [hVY]; exact le_sup_right
  have hYΞ : ctxYq t tau x₁ x₂ rho ≤ ctxXi t tau x₁ x₂ rho :=
    ctxYq_le_ctxQ.trans (l18_Q_le_Xi hc.toCtx13)
  have hYc : ∀ y ∈ ctxYq t tau x₁ x₂ rho, ∀ x ∈ ctxXi t tau x₁ x₂ rho, x * y = y * x := by
    intro y hy x hx
    have hxC : x ∈ ctxCY t tau x₁ x₂ rho := l18_Xi_le_C hc hx
    have hxcent : x ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hxC).2
    exact ((Subgroup.mem_centralizer_iff.mp hxcent) y hy).symm
  have hΞcard : Nat.card (ctxXi t tau x₁ x₂ rho) = 256 := by
    rw [l18_card_Xi hc]; norm_num
  have hYcard : Nat.card (ctxYq t tau x₁ x₂ rho) = 16 := l17_card_Y hc.toCtx13
  have hfpf : ∀ x ∈ ctxXi t tau x₁ x₂ rho, x * rho = rho * x → x = 1 := by
    intro x hx hcomm
    have hxcent : x ∈ centralizer ({rho} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hmem : x ∈ ctxXi t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := ⟨hx, hxcent⟩
    rw [l18_Xi_cap_cent_rho hc] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hfourV' : fourGrp x₁ x₂ ⊓ V' = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro a ha
    have h1 : a ∈ baseGrp x₁ x₂ := fourGrp_le_baseGrp_e x₁ x₂ ha.1
    have h2 : a ∈ V' := ha.2
    have hmem : a ∈ baseGrp x₁ x₂ ⊓ V' := ⟨h1, h2⟩
    rw [hbaseV'] at hmem
    exact hmem
  have hnab : ∃ a ∈ ctxXi t tau x₁ x₂ rho, ∃ b ∈ ctxXi t tau x₁ x₂ rho,
      a * b * a⁻¹ * b⁻¹ ∉ V' := by
    have hex : ∃ m, m ∈ ctxXi t tau x₁ x₂ rho ∧ m ∉ ctxQ t tau x₁ x₂ rho := by
      by_contra h
      push_neg at h
      have hle : ctxXi t tau x₁ x₂ rho ≤ ctxQ t tau x₁ x₂ rho := fun x hx => h x hx
      have hcard := Subgroup.card_le_of_le hle
      rw [l18_card_Xi hc, IsZ4Z4E4.card hc.q_iso] at hcard
      norm_num at hcard
    obtain ⟨m, hmΞ, hmQ⟩ := hex
    have hmOK : m ∈ ctxOK t tau x₁ x₂ rho := l18_Xi_le_OK hc.toCtx13 hmΞ
    have hmK : m ∈ ctxK t tau x₁ x₂ rho := (l18_OK_normal).1 hmOK
    have hmP : m ∉ ctxP t tau x₁ x₂ rho := by
      rw [hc.P_eq]; exact hmQ
    have hmcent : m ∉ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      intro hc'
      exact hmP (by rw [ctxP]; exact ⟨hmK, hc'⟩)
    rw [Subgroup.mem_centralizer_iff] at hmcent
    push_neg at hmcent
    obtain ⟨q, hqQ, hqm⟩ := hmcent
    have hqΞ : q ∈ ctxXi t tau x₁ x₂ rho := l18_Q_le_Xi hc.toCtx13 hqQ
    have hcommV : m * q * m⁻¹ * q⁻¹ ∈ fourGrp x₁ x₂ := l18_comm_Xi_Q_mem_V hc hmΞ hqQ
    have hne : m * q * m⁻¹ * q⁻¹ ≠ 1 := by
      intro h1
      apply hqm
      have h2 : (m * q) * (q * m)⁻¹ = 1 := by
        rw [mul_inv_rev]; rw [← mul_assoc]; exact h1
      exact (mul_inv_eq_one.mp h2).symm
    refine ⟨m, hmΞ, q, hqΞ, ?_⟩
    intro hmemV'
    have hmem_bot : m * q * m⁻¹ * q⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hfourV']
      exact ⟨hcommV, hmemV'⟩
    exact hne (Subgroup.mem_bot.mp hmem_bot)
  exact sq_comm_mem_of_fpf_quot (Ξ := ctxXi t tau x₁ x₂ rho)
    (Y := ctxYq t tau x₁ x₂ rho) (V' := V') (ρ := rho)
    hρ3 hρΞ hρV hV'Y hYΞ hYc hΞcard hYcard hV'card hfpf hnab

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
