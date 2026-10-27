module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Sub

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace L246C127

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_sup_of_commute' {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G}
    (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, K.one_mem, (mul_one x).symm⟩
    · exact ⟨1, H.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := hx
    obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := hy
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
    have := hc h₂ hh₂ k₁ hk₁
    calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
      _ = h₁ * (h₂ * k₁) * k₂ := by rw [← this]
      _ = h₁ * h₂ * (k₁ * k₂) := by group
  | inv x _ hx =>
    obtain ⟨h, hh, k, hk, rfl⟩ := hx
    refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
    have hcm : Commute h k := hc h hh k hk
    rw [mul_inv_rev]
    exact (Commute.inv_inv hcm).eq.symm

theorem commutator_le_blockU {K P N : Subgroup G} (hK : IsShort2 K) (hKP : IsSubnormal K P)
    (hNP : N ≤ P) (hNn : (N.subgroupOf P).Normal) (hN2 : IsPGroup 2 N) : ⁅N, K⁆ ≤ blockU K := by
  have hgen := le_closure_oddPPow hK.1
  have hKP' : K ≤ P := A3.subnormal_le hKP
  have hPN : P ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).1 hNn
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := hKP'.trans hPN
  have h1 : ⁅K, N⁆ ≤ K ⊓ N := commutator_le_inf_of_isSubnormal hKP hNP hNn hN2 hgen
  have hKNK : K ≤ Subgroup.normalizer ((K ⊓ N : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hk1 : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
    have hk2 := hKN hk
    rw [Subgroup.mem_normalizer_iff] at hk1 hk2
    simp only [Subgroup.mem_inf]
    rw [hk1 x, hk2 x]
  have h2 : K ⊓ N ≤ blockQ K :=
    C1.le_pCoreOf_of_normalized inf_le_left hKNK (hN2.to_le inf_le_right)
  have h3 : ⁅N, K⁆ ≤ blockQ K := by
    rw [Subgroup.commutator_comm]
    exact h1.trans h2
  have h4 : ⁅N, K⁆ ≤ ⁅⁅N, K⁆, K⁆ := commutator_le_commutator_commutator_two hN2 hKN hgen
  exact h4.trans (Subgroup.commutator_mono h3 le_rfl)

theorem blockU_le_of_sup_eq {K W₁ : Subgroup G} (hK : IsShort2 K) (hKW₁ : K ≤ Subgroup.normalizer (W₁ : Set G))
    (hW₁U : W₁ ≤ blockU K) (h : W₁ ⊔ blockZ K = blockU K) : blockU K ≤ W₁ := by
  have hZU : blockZ K ≤ blockU K := inf_le_left
  have hU : blockU K = ⁅blockU K, K⁆ := (C1.commutator_blockU hK).symm
  have hUab : ∀ a ∈ blockU K, ∀ b ∈ blockU K, a * b = b * a := (C1.elemAb2_blockU hK).1
  rw [hU]
  conv_lhs => rw [← h]
  rw [Subgroup.commutator_le]
  intro u hu k hk
  obtain ⟨w, hw, z, hz, rfl⟩ :=
    mem_sup_of_commute' (fun a ha b hb => hUab a (hW₁U ha) b (hZU hb)) hu
  have hzc : z * k = k * z := (Subgroup.mem_centralizer_iff.1 hz.2 k hk).symm
  have e : ⁅w * z, k⁆ = w * (k * w⁻¹ * k⁻¹) := by
    simp only [commutatorElement_def]
    have : z * k * z⁻¹ = k := by rw [hzc]; group
    calc w * z * k * (w * z)⁻¹ * k⁻¹ = w * (z * k * z⁻¹) * w⁻¹ * k⁻¹ := by group
      _ = w * k * w⁻¹ * k⁻¹ := by rw [this]
      _ = w * (k * w⁻¹ * k⁻¹) := by group
  rw [e]
  exact W₁.mul_mem hw ((Subgroup.mem_normalizer_iff.1 (hKW₁ hk) w⁻¹).1 (W₁.inv_mem hw))

theorem blockU_le_commutator_of_ne_bot {K V : Subgroup G} (hK : IsShort2 K)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hV2 : IsPGroup 2 V) (hle : ⁅V, K⁆ ≤ blockU K)
    (hne : ⁅V, K⁆ ≠ ⊥) : blockU K ≤ ⁅V, K⁆ := by
  have hgen := le_closure_oddPPow hK.1
  set W : Subgroup G := ⁅V, K⁆ with hW
  have hKW : K ≤ Subgroup.normalizer (W : Set G) :=
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized K V hKV
  have hWK : ⁅W, K⁆ ≠ ⊥ := by
    intro h
    apply hne
    have := commutator_le_commutator_commutator_two hV2 hKV hgen
    rw [← hW, h] at this
    exact le_bot_iff.1 this
  have hZnorm : K ≤ Subgroup.normalizer (blockZ K : Set G) := fun g hg =>
    C1.mem_normalizer_blockZ (Subgroup.le_normalizer hg)
  have hW'norm : K ≤ Subgroup.normalizer ((W ⊔ blockZ K : Subgroup G) : Set G) := fun g hg =>
    C1.mem_normalizer_sup (hKW hg) (hZnorm hg)
  have hZU : blockZ K ≤ blockU K := inf_le_left
  have hcases := hK.2.2.2.2.2 (W ⊔ blockZ K) le_sup_right (sup_le hle hZU) hW'norm
  rcases hcases with h | h
  · exfalso
    apply hWK
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    have : W ≤ blockZ K := le_sup_left.trans h.le
    exact this.trans inf_le_right
  · exact blockU_le_of_sup_eq hK hKW hle h

structure Setting (X T P K : Subgroup G) : Prop where
  charTwo : CharTwo X
  sylow : IsSylowTwoOf T X
  PX : P ≤ X
  TP : T ≤ P
  block : IsBlock2 P K

namespace Setting

variable {X T P K : Subgroup G} (S : Setting X T P K)

include S

theorem hred : IsTwoReducedIn X (VZ T X) := C1GN.isTwoReducedIn_VZ S.charTwo S.sylow

theorem V_le_T : VZ T X ≤ T :=
  (le_pCoreOf_of_isTwoReducedIn S.hred).trans (pCoreOf_le_of_isSylowTwoOf S.sylow)

theorem V_isPGroup : IsPGroup 2 (VZ T X) := S.sylow.2.1.to_le S.V_le_T

theorem Q_le_T : pCoreOf 2 X ≤ T := pCoreOf_le_of_isSylowTwoOf S.sylow

omit [Finite G] in
theorem subnormal : IsSubnormal K P := C1GN.isSubnormal_of_isBlock2 S.block

omit [Finite G] in
theorem KP : K ≤ P := S.block.2.1

omit [Finite G] in
theorem short : IsShort2 K := S.block.1

theorem normal_V : ((VZ T X).subgroupOf P).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (S.V_le_T.trans S.TP)]
  exact S.PX.trans S.hred.2.1

theorem normal_Q : ((pCoreOf 2 X).subgroupOf P).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (S.Q_le_T.trans S.TP)]
  exact S.PX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)

theorem comm_V_le : ⁅VZ T X, K⁆ ≤ blockU K := by
  rw [Subgroup.commutator_comm]
  rw [Subgroup.commutator_comm]
  exact commutator_le_blockU S.short S.subnormal (S.V_le_T.trans S.TP) S.normal_V S.V_isPGroup

theorem comm_Q_le : ⁅pCoreOf 2 X, K⁆ ≤ blockU K :=
  commutator_le_blockU S.short S.subnormal (S.Q_le_T.trans S.TP) S.normal_Q (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)

theorem blockU_le_commutator_VZ
    (hKZ : ¬ K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    blockU K ≤ ⁅VZ T X, K⁆ := by
  have hZV : quasithinOmegaOneCenter T ≤ VZ T X := le_conjClosure _ _
  have hne : ⁅VZ T X, K⁆ ≠ ⊥ := by
    intro h
    apply hKZ
    have h1 : ⁅quasithinOmegaOneCenter T, K⁆ = ⊥ :=
      le_bot_iff.1 ((Subgroup.commutator_mono hZV le_rfl).trans h.le)
    rw [Subgroup.commutator_comm] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1
  have hKV : K ≤ Subgroup.normalizer (VZ T X : Set G) := S.KP.trans (S.PX.trans S.hred.2.1)
  exact blockU_le_commutator_of_ne_bot S.short hKV S.V_isPGroup S.comm_V_le hne

theorem blockU_le_VZ (hKZ : ¬ K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    blockU K ≤ VZ T X := by
  refine (S.blockU_le_commutator_VZ hKZ).trans ?_
  have hKV : K ≤ Subgroup.normalizer (VZ T X : Set G) := S.KP.trans (S.PX.trans S.hred.2.1)
  exact CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing (VZ T X) K hKV

end Setting

end L246C127

end CFSG.QuasithinUnique
