module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Una
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private theorem fourGrp_le_baseGrp_aux (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [fourGrp, baseGrp]
  refine (Subgroup.closure_le _).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact pow_mem (Subgroup.subset_closure (by simp)) 2
  · exact pow_mem (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2

private theorem k18e_unipotent (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮)
    {m n : G} (hm : m ∈ ctxXi t tau x₁ x₂ rho) (hn : n ∈ ctxXi t tau x₁ x₂ rho) :
    (∀ q ∈ ctxQ t tau x₁ x₂ rho,
        (m * n * m⁻¹ * n⁻¹) * q = q * (m * n * m⁻¹ * n⁻¹)) ∧
      ∀ q ∈ ctxQ t tau x₁ x₂ rho, (m * m) * q = q * (m * m) := by
  obtain ⟨V', v₁, v₂, hV'⟩ := hc.data_V
  have hQ_eq : ctxQ t tau x₁ x₂ rho = baseGrp x₁ x₂ ⊔ V' := hV'.2.2.1
  have hBinf : baseGrp x₁ x₂ ⊓ V' = ⊥ := hV'.2.2.2.1
  have hY_eq : ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ ⊔ V' := hV'.2.2.2.2.2.2.1
  have hV'Q : V' ≤ ctxQ t tau x₁ x₂ rho := by rw [hQ_eq]; exact le_sup_right
  have hV'Y : V' ≤ ctxYq t tau x₁ x₂ rho := by rw [hY_eq]; exact le_sup_right
  have hVQ : fourGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho :=
    (fourGrp_le_baseGrp_aux x₁ x₂).trans hc.base_le_Q
  have hV'normB : ∀ k ∈ V', ∀ h ∈ baseGrp x₁ x₂, k * h * k⁻¹ ∈ baseGrp x₁ x₂ := by
    intro k hk h hh
    rw [IsZ4Z4E4.comm hc.q_iso (hV'Q hk) (hc.base_le_Q hh)]
    simpa using hh
  have hV'normV : ∀ k ∈ V', ∀ h ∈ fourGrp x₁ x₂, k * h * k⁻¹ ∈ fourGrp x₁ x₂ := by
    intro k hk h hh
    rw [IsZ4Z4E4.comm hc.q_iso (hV'Q hk) (hVQ hh)]
    simpa using hh
  have hQBY : ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      ∃ b ∈ baseGrp x₁ x₂, ∃ y ∈ ctxYq t tau x₁ x₂ rho, q = b * y := by
    intro q hq
    have hq' : q ∈ baseGrp x₁ x₂ ⊔ V' := by rw [← hQ_eq]; exact hq
    obtain ⟨b, hb, w, hw, rfl⟩ :=
      (mem_sup_iff_of_normalizes (H := baseGrp x₁ x₂) (K := V') hV'normB).mp hq'
    exact ⟨b, hb, w, hV'Y hw, rfl⟩
  have hBY : ∀ x ∈ baseGrp x₁ x₂, x ∈ ctxYq t tau x₁ x₂ rho → x ∈ fourGrp x₁ x₂ := by
    intro x hxB hxY
    have hxY' : x ∈ fourGrp x₁ x₂ ⊔ V' := by rw [← hY_eq]; exact hxY
    obtain ⟨v, hv, w, hw, rfl⟩ :=
      (mem_sup_iff_of_normalizes (H := fourGrp x₁ x₂) (K := V') hV'normV).mp hxY'
    have hwB : w ∈ baseGrp x₁ x₂ := by
      have hw_eq : w = v⁻¹ * (v * w) := by group
      rw [hw_eq]
      exact mul_mem (inv_mem ((fourGrp_le_baseGrp_aux x₁ x₂) hv)) hxB
    have hwbot : w ∈ (⊥ : Subgroup G) := by
      rw [← hBinf]
      exact ⟨hwB, hw⟩
    have hw1 : w = 1 := Subgroup.mem_bot.mp hwbot
    simpa [hw1] using hv
  have hV2 : ∀ v ∈ fourGrp x₁ x₂, v * v = 1 := by
    intro v hv
    have h := (l17_Y_elem hc.toCtx13).2 v (l17_V_le_Y hc.toCtx13 hv)
    simpa [pow_two] using h
  have hmOK : m ∈ ctxOK t tau x₁ x₂ rho := l18_Xi_le_OK hc.toCtx13 hm
  have hnOK : n ∈ ctxOK t tau x₁ x₂ rho := l18_Xi_le_OK hc.toCtx13 hn
  have hmK : m ∈ ctxK t tau x₁ x₂ rho :=
    (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).1 hmOK
  have hnK : n ∈ ctxK t tau x₁ x₂ rho :=
    (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).1 hnOK
  have hmQ : ∀ q ∈ ctxQ t tau x₁ x₂ rho, m * q * m⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    fun q hq => hc.normal_Q_K.2 m hmK q hq
  have hnQ : ∀ q ∈ ctxQ t tau x₁ x₂ rho, n * q * n⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    fun q hq => hc.normal_Q_K.2 n hnK q hq
  have hmB : ∀ b ∈ baseGrp x₁ x₂, m * b * m⁻¹ ∈ baseGrp x₁ x₂ :=
    fun b hb => k18_Xi_norm_B hc.toCtx13 m hm b hb
  have hnB : ∀ b ∈ baseGrp x₁ x₂, n * b * n⁻¹ ∈ baseGrp x₁ x₂ :=
    fun b hb => k18_Xi_norm_B hc.toCtx13 n hn b hb
  have hmQY : ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      m * q * m⁻¹ * q⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
    fun q hq => k18_OK_comm_Q hc.toCtx13 m hmOK q hq
  have hnQY : ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      n * q * n⁻¹ * q⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
    fun q hq => k18_OK_comm_Q hc.toCtx13 n hnOK q hq
  have hmYV : ∀ y ∈ ctxYq t tau x₁ x₂ rho,
      m * y * m⁻¹ * y⁻¹ ∈ fourGrp x₁ x₂ :=
    fun y hy => k18_OK_comm_Y hc.toCtx13 m hmOK y hy
  have hnYV : ∀ y ∈ ctxYq t tau x₁ x₂ rho,
      n * y * n⁻¹ * y⁻¹ ∈ fourGrp x₁ x₂ :=
    fun y hy => k18_OK_comm_Y hc.toCtx13 n hnOK y hy
  have hmV : ∀ v ∈ fourGrp x₁ x₂, m * v * m⁻¹ = v :=
    fun v hv => k18_OK_cent_V hc.toCtx13 m hmOK v hv
  have hnV : ∀ v ∈ fourGrp x₁ x₂, n * v * n⁻¹ = v :=
    fun v hv => k18_OK_cent_V hc.toCtx13 n hnOK v hv
  exact comm_sq_centralize_of_unipotent (Q := ctxQ t tau x₁ x₂ rho)
    (Y := ctxYq t tau x₁ x₂ rho) (V := fourGrp x₁ x₂) (B := baseGrp x₁ x₂)
    (fun a ha b hb => IsZ4Z4E4.comm hc.q_iso ha hb) hc.base_le_Q ctxYq_le_ctxQ
    (l17_V_le_Y hc.toCtx13) hQBY hBY hV2 hmQ hnQ hmB hnB hmQY hnQY hmYV hnYV hmV hnV

theorem k18_Xi_quot_elem (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮) :
    (∀ m ∈ ctxXi t tau x₁ x₂ rho, ∀ n ∈ ctxXi t tau x₁ x₂ rho,
        m * n * m⁻¹ * n⁻¹ ∈ ctxQ t tau x₁ x₂ rho) ∧
      ∀ m ∈ ctxXi t tau x₁ x₂ rho, m * m ∈ ctxQ t tau x₁ x₂ rho := by
  have key : ∀ {g : G}, g ∈ ctxK t tau x₁ x₂ rho →
      (∀ q ∈ ctxQ t tau x₁ x₂ rho, g * q = q * g) →
      g ∈ ctxQ t tau x₁ x₂ rho := by
    intro g hgK hg
    rw [← hc.P_eq]
    unfold ctxP
    refine ⟨hgK, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun q hq => (hg q hq).symm)
  constructor
  · intro m hm n hn
    have hmOK : m ∈ ctxOK t tau x₁ x₂ rho := l18_Xi_le_OK hc.toCtx13 hm
    have hnOK : n ∈ ctxOK t tau x₁ x₂ rho := l18_Xi_le_OK hc.toCtx13 hn
    have hmK : m ∈ ctxK t tau x₁ x₂ rho :=
      (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).1 hmOK
    have hnK : n ∈ ctxK t tau x₁ x₂ rho :=
      (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).1 hnOK
    have hcomm := (k18e_unipotent hc hm hn).1
    exact key (mul_mem (mul_mem (mul_mem hmK hnK) (inv_mem hmK)) (inv_mem hnK)) hcomm
  · intro m hm
    have hmOK : m ∈ ctxOK t tau x₁ x₂ rho := l18_Xi_le_OK hc.toCtx13 hm
    have hmK : m ∈ ctxK t tau x₁ x₂ rho :=
      (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).1 hmOK
    have hsq := (k18e_unipotent hc hm hm).2
    exact key (mul_mem hmK hmK) hsq

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
