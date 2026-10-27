module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux13
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux12

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8 CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false


section Lemmas

variable {L : Type} [Field L]

theorem single_smul_mem {U : Submodule L (Fn L)} {β : Fin Tag.E8.rank → ℤ}
    (h : (Pi.single β (1 : L) : Fn L) ∈ U) (s : L) : (Pi.single β s : Fn L) ∈ U := by
  have : (Pi.single β s : Fn L) = s • (Pi.single β (1 : L) : Fn L) := by
    funext ν
    by_cases hν : ν = β
    · subst hν
      simp
    · simp [Pi.single_eq_of_ne hν]
  rw [this]
  exact U.smul_mem _ h

theorem mRoots_deg1 {β : Fin Tag.E8.rank → ℤ} (h : β ∈ mRoots) : β ∈ Deg1 Tag.E8 :=
  CoordAux.mem_Deg1.2 ⟨(mem_mRoots.1 h).1, (mem_mRoots.1 h).2.1⟩

theorem sgn_ne_zero' (w : WeylGroup Tag.E8) {μ : Fin Tag.E8.rank → ℤ} (hμ : IsRoot Tag.E8 μ) :
    (sgn w μ : L) ≠ 0 := by
  intro h
  have := (sgn_spec (L := L) w hμ).1
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem aE8_cast_ne_zero {δ μ : Fin Tag.E8.rank → ℤ} (hδ : δ ∈ rootFinset Tag.E8) (hδ0 : δ 7 = 0)
    (hμ : μ ∈ deg1Roots) (h : δ + μ ∈ rootFinset Tag.E8) : (aE8 δ μ : L) ≠ 0 := by
  have h1 := ((adm_aE8 δ hδ hδ0 μ hμ).1 h)
  rcases abs_eq (zero_le_one' ℤ) |>.1 h1 with h1 | h1 <;> rw [h1] <;> simp

theorem coeff_pair {δ₀ δ₁ : Fin Tag.E8.rank → ℤ} (hδ₀ : δ₀ ≠ 0) (hδ₁ : δ₁ ≠ 0) (hne : δ₀ ≠ δ₁)
    (μ : Fin Tag.E8.rank → ℤ) (s d : L) :
    ((actOp aE8 δ₀ s ∘ₗ actOp aE8 δ₁ d) (Pi.single μ (1 : L) : Fn L) : Fn L) (μ + δ₀) =
      s * (aE8 δ₀ μ : L) := by
  have h1 : (actOp aE8 δ₁ d) (Pi.single μ (1 : L) : Fn L) =
      (Pi.single μ (1 : L) : Fn L) + d • (Pi.single (μ + δ₁) ((aE8 δ₁ μ : L) * 1) : Fn L) := by
    rw [actOp, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, Eop_single]
  rw [LinearMap.comp_apply, h1, actOp, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_add, map_smul, Eop_single, Eop_single]
  have e1 : μ + δ₀ ≠ μ := fun h => hδ₀ (by
    have : δ₀ = (μ + δ₀) - μ := by abel
    rw [h, sub_self] at this
    exact this)
  have e2 : μ + δ₀ ≠ μ + δ₁ := fun h => hne (add_left_cancel h)
  have e3 : μ + δ₀ ≠ μ + δ₁ + δ₀ := fun h => hδ₁ (by
    have : δ₁ = (μ + δ₁ + δ₀) - (μ + δ₀) := by abel
    rw [← h, sub_self] at this
    exact this)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne e1,
    Pi.single_eq_of_ne e2, Pi.single_eq_of_ne e3, Pi.single_eq_same]
  ring

end Lemmas

structure StepData (kP kQ : ℤ) where
  β₀ : Fin Tag.E8.rank → ℤ
  β₁ : Fin Tag.E8.rank → ℤ
  u₀ : Fin Tag.E8.rank → ℤ
  u₁ : Fin Tag.E8.rank → ℤ
  δ₀ : Fin Tag.E8.rank → ℤ
  δ₁ : Fin Tag.E8.rank → ℤ
  v₀ : Fin Tag.E8.rank → ℤ
  v₁ : Fin Tag.E8.rank → ℤ
  μ₀ : Fin Tag.E8.rank → ℤ
  hβ₀ : β₀ ∈ mRoots
  hβ₁ : β₁ ∈ mRoots
  hcβ₀ : cls β₀ = kP ∨ cls β₀ = 5 - kP
  hcβ₁ : cls β₁ = kP ∨ cls β₁ = 5 - kP
  hwβ₀ : wm.mulVec β₀ = β₁
  hwβ₁ : wm.mulVec β₁ = β₀
  hβne : β₀ ≠ β₁
  hβsum : β₀ + β₁ ∉ rootFinset Tag.E8
  hu₀ : u₀ ∈ mRoots
  hu₁ : u₁ ∈ mRoots
  hcu₀ : cls u₀ = kQ ∨ cls u₀ = 5 - kQ
  hcu₁ : cls u₁ = kQ ∨ cls u₁ = 5 - kQ
  hνu₀ : νm.mulVec u₀ = β₀
  hνu₁ : νm.mulVec u₁ = β₁
  hune : u₀ ≠ u₁
  hδ₀ : δ₀ ∈ rootFinset Tag.E8
  hδ₀7 : δ₀ 7 = 0
  hδ₁ : δ₁ ∈ rootFinset Tag.E8
  hδ₁7 : δ₁ 7 = 0
  hwδ₀ : wm.mulVec δ₀ = δ₁
  hwδ₁ : wm.mulVec δ₁ = δ₀
  hδne : δ₀ ≠ δ₁
  hδneg : δ₀ ≠ -δ₁
  hδsum : δ₀ + δ₁ ∉ rootFinset Tag.E8
  hδ0 : δ₀ ≠ 0
  hδ1 : δ₁ ≠ 0
  hv₀ : v₀ ∈ mRoots
  hv₁ : v₁ ∈ mRoots
  hcv₀ : cls v₀ = kQ ∨ cls v₀ = 5 - kQ
  hcv₁ : cls v₁ = kQ ∨ cls v₁ = 5 - kQ
  hνv₀ : νm.mulVec v₀ = δ₀
  hνv₁ : νm.mulVec v₁ = δ₁
  hvne : v₀ ≠ v₁
  hμ₀ : μ₀ ∈ mRoots
  hcμ₀ : cls μ₀ = kP ∨ cls μ₀ = 5 - kP
  hμδ : μ₀ + δ₀ ∈ rootFinset Tag.E8
  hμδm : μ₀ + δ₀ ∈ mRoots
  hcμδ : cls (μ₀ + δ₀) = kQ ∨ cls (μ₀ + δ₀) = 5 - kQ

section Step

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)
  (H : Subgroup (ModGL Tag.E8 K))

theorem pair_pos1 {β₀ β₁ : Fin Tag.E8.rank → ℤ} (h₀ : β₀ ∈ Deg1 Tag.E8) (h₁ : β₁ ∈ Deg1 Tag.E8)
    {s d : D.L} {l : ModGL Tag.E8 K}
    (hl : baseChangeGL (algebraMap K D.L) l =
      gE D * (pinnedX Tag.E8 D.L β₀ s * pinnedX Tag.E8 D.L β₁ d) * (gE D)⁻¹) :
    l ∈ Qrat (K := K) (toSetup D H).h ∧
      Cc (toSetup D H).h l = Pi.single β₀ s + Pi.single β₁ d := by
  have e : (toSetup D H).h⁻¹ * baseChangeGL (algebraMap K D.L) l * (toSetup D H).h =
      pinnedX Tag.E8 D.L β₀ s * pinnedX Tag.E8 D.L β₁ d := by
    rw [hl]
    change (gE D)⁻¹ * (gE D * (pinnedX Tag.E8 D.L β₀ s * pinnedX Tag.E8 D.L β₁ d) *
      (gE D)⁻¹) * gE D = _
    group
  have hQ0 := pinnedX_mem_Qθ_of_mem_Deg1 h₀ s
  have hQ1 := pinnedX_mem_Qθ_of_mem_Deg1 h₁ d
  refine ⟨?_, ?_⟩
  · show (toSetup D H).h⁻¹ * baseChangeGL (algebraMap K D.L) l * (toSetup D H).h ∈ Qθ Tag.E8 D.L
    rw [e]
    exact mul_mem hQ0 hQ1
  · unfold Cc
    rw [e, (heisCoord_spec Tag.E8 D.L).mul _ hQ0 _ hQ1, (heisCoord_spec Tag.E8 D.L).pinnedX_deg1 β₀ h₀,
      (heisCoord_spec Tag.E8 D.L).pinnedX_deg1 β₁ h₁]

variable [IsAlgClosed D.L]

theorem second_step (hHG : H ≤ adjointGroup Tag.E8 K) (h1 : D.frame TwClass.e8Ten.S₁ ≤ H)
    (h2 : D.frame TwClass.e8Ten.S₂ ≤ H) {kP kQ : ℤ} (T : StepData kP kQ)
    (hP : ∀ ν ∈ mRoots, (cls ν = kP ∨ cls ν = 5 - kP) →
      (Pi.single ν (1 : D.L) : Fn D.L) ∈ Uspace D.g H) :
    ∀ ν ∈ mRoots, (cls ν = kQ ∨ cls ν = 5 - kQ) →
      (Pi.single ν (1 : D.L) : Fn D.L) ∈ Uspace D.g H := by
  classical
  have hsc1 := scalClosed₁ D H h1
  have hsc2 := scalClosed₂ D H h2
  have hk1 := hker₁ D H h1
  have hk2 := hker₂ D H h2
  have hw1 := toSetup_hw D H
  have hw2 := toSetup2_hw D H
  have hrβ₀ : IsRoot Tag.E8 T.β₀ := (mem_mRoots.1 T.hβ₀).1
  have hrβ₁ : IsRoot Tag.E8 T.β₁ := (mem_mRoots.1 T.hβ₁).1
  have hβneg : T.β₀ ≠ -T.β₁ := by
    intro h
    have := congrFun h 7
    rw [Pi.neg_apply, (mem_mRoots.1 T.hβ₀).2.1, (mem_mRoots.1 T.hβ₁).2.1] at this
    omega
  have hδ₀r : IsRoot Tag.E8 T.δ₀ := mem_rootFinset.1 T.hδ₀
  have hδ₁r : IsRoot Tag.E8 T.δ₁ := mem_rootFinset.1 T.hδ₁
  have hu₀D : T.u₀ ∈ Deg1 Tag.E8 := mRoots_deg1 T.hu₀
  have hu₁D : T.u₁ ∈ Deg1 Tag.E8 := mRoots_deg1 T.hu₁
  have hv₀D : T.v₀ ∈ Deg1 Tag.E8 := mRoots_deg1 T.hv₀
  have hv₁D : T.v₁ ∈ Deg1 Tag.E8 := mRoots_deg1 T.hv₁
  have hβ₀D : T.β₀ ∈ Deg1 Tag.E8 := mRoots_deg1 T.hβ₀
  have hβ₁D : T.β₁ ∈ Deg1 Tag.E8 := mRoots_deg1 T.hβ₁
  have hQ2 : ∀ {u : Fn D.L}, u ∈ Uspace (toSetup2 D H).h (toSetup2 D H).H →
      ∀ {μ : Fin Tag.E8.rank → ℤ}, μ ∈ mRoots → u μ ≠ 0 →
      ∀ ν ∈ mRoots, (cls ν = cls μ ∨ cls ν = 5 - cls μ) →
        (Pi.single ν (1 : D.L) : Fn D.L) ∈ Uspace (toSetup2 D H).h (toSetup2 D H).H :=
    fun {u} hu {μ} hμ h0 =>
      (toSetup2 D H).block_pos hw2 (Xc D TwClass.e8Ten.S₁) (Xc D TwClass.e8Ten.S₂)
        (xlink2 D H _ h1) (xlink2 D H _ h2) (listA_mem_Xc D) (listB_mem_Xc D) hu hμ h0
  obtain ⟨s, d, hs0, hsd, hds⟩ := (toSetup D H).exists_pair hrβ₀ hrβ₁
  have hcommβ : ∀ a b : D.L, pinnedX Tag.E8 D.L T.β₀ a * pinnedX Tag.E8 D.L T.β₁ b =
      pinnedX Tag.E8 D.L T.β₁ b * pinnedX Tag.E8 D.L T.β₀ a := fun a b =>
    pinnedX_commute_of_not_root (mem_rootFinset.2 hrβ₀) (mem_rootFinset.2 hrβ₁) T.hβne hβneg
      T.hβsum a b
  have hσ6 := (toSetup D H).pair_sfixed hrβ₀ hrβ₁ (by rw [hw1, T.hwβ₀]) (by rw [hw1, T.hwβ₁])
    hcommβ hsd hds
  have hxA6 : pinnedX Tag.E8 D.L T.β₀ s * pinnedX Tag.E8 D.L T.β₁ d ∈ adjointGroup Tag.E8 D.L :=
    mul_mem (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨s, rfl⟩))
      (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨d, rfl⟩))
  obtain ⟨l₀, hl₀A, hl₀⟩ := (toSetup D H).rat_of_sfixed hxA6 hσ6
  have hl₀' : baseChangeGL (algebraMap K D.L) l₀ =
      gE D * (pinnedX Tag.E8 D.L T.β₀ s * pinnedX Tag.E8 D.L T.β₁ d) * (gE D)⁻¹ := hl₀
  obtain ⟨hl₀Q, hl₀c⟩ := pair_pos1 D H hβ₀D hβ₁D hl₀'
  have hl₀U : Cc (toSetup D H).h l₀ ∈ Uspace (toSetup D H).h (toSetup D H).H := by
    rw [hl₀c]
    exact add_mem (single_smul_mem (hP _ T.hβ₀ T.hcβ₀) s) (single_smul_mem (hP _ T.hβ₁ T.hcβ₁) d)
  have hl₀H : l₀ ∈ H := (toSetup D H).mem_H_of_Uspace hsc1 hHG hk1 hl₀Q hl₀A hl₀U
  obtain ⟨hl₀Q2, hl₀c2⟩ := pair_pos2 D H hu₀D hu₁D (by rw [νW_smul]; exact T.hνu₀)
    (by rw [νW_smul]; exact T.hνu₁) T.hune hl₀'
  have hl₀U2 : Cc (toSetup2 D H).h l₀ ∈ Uspace (toSetup2 D H).h (toSetup2 D H).H :=
    Cc_mem_Uspace (h := (toSetup2 D H).h) (H := H) hl₀H hl₀Q2
  have hcoord0 : Cc (toSetup2 D H).h l₀ T.u₀ ≠ 0 := by
    rw [hl₀c2, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne T.hune, add_zero]
    exact mul_ne_zero (sgn_ne_zero' νW (mem_mRoots.1 T.hu₀).1) hs0
  have hB2 := hQ2 hl₀U2 T.hu₀ hcoord0
  have hB2' : ∀ ν ∈ mRoots, (cls ν = kQ ∨ cls ν = 5 - kQ) →
      (Pi.single ν (1 : D.L) : Fn D.L) ∈ Uspace (toSetup2 D H).h (toSetup2 D H).H := by
    intro ν hν hc
    refine hB2 ν hν ?_
    rcases T.hcu₀ with h | h <;> omega
  obtain ⟨s', d', hs'0, hs'd, hd's⟩ := (toSetup D H).exists_pair hδ₀r hδ₁r
  have hcommδ : ∀ a b : D.L, pinnedX Tag.E8 D.L T.δ₀ a * pinnedX Tag.E8 D.L T.δ₁ b =
      pinnedX Tag.E8 D.L T.δ₁ b * pinnedX Tag.E8 D.L T.δ₀ a := fun a b =>
    pinnedX_commute_of_not_root T.hδ₀ T.hδ₁ T.hδne T.hδneg T.hδsum a b
  have hσD := (toSetup D H).pair_sfixed hδ₀r hδ₁r (by rw [hw1, T.hwδ₀]) (by rw [hw1, T.hwδ₁])
    hcommδ hs'd hd's
  have hxAD : pinnedX Tag.E8 D.L T.δ₀ s' * pinnedX Tag.E8 D.L T.δ₁ d' ∈ adjointGroup Tag.E8 D.L :=
    mul_mem (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨s', rfl⟩))
      (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨d', rfl⟩))
  obtain ⟨l₁, hl₁A, hl₁⟩ := (toSetup D H).rat_of_sfixed hxAD hσD
  have hl₁' : baseChangeGL (algebraMap K D.L) l₁ =
      gE D * (pinnedX Tag.E8 D.L T.δ₀ s' * pinnedX Tag.E8 D.L T.δ₁ d') * (gE D)⁻¹ := hl₁
  obtain ⟨hl₁Q2, hl₁c2⟩ := pair_pos2 D H hv₀D hv₁D (by rw [νW_smul]; exact T.hνv₀)
    (by rw [νW_smul]; exact T.hνv₁) T.hvne hl₁'
  have hl₁U2 : Cc (toSetup2 D H).h l₁ ∈ Uspace (toSetup2 D H).h (toSetup2 D H).H := by
    rw [hl₁c2]
    exact add_mem (single_smul_mem (hB2' _ T.hv₀ T.hcv₀) _) (single_smul_mem (hB2' _ T.hv₁ T.hcv₁) _)
  have hl₁H : l₁ ∈ H := (toSetup2 D H).mem_H_of_Uspace hsc2 hHG hk2 hl₁Q2 hl₁A hl₁U2
  have hact : ActsBy (pinnedX Tag.E8 D.L T.δ₀ s' * pinnedX Tag.E8 D.L T.δ₁ d')
      (actOp aE8 T.δ₀ s' ∘ₗ actOp aE8 T.δ₁ d') :=
    (actsBy_pinnedX T.hδ₀ T.hδ₀7 s').mul (actsBy_pinnedX T.hδ₁ T.hδ₁7 d')
  have hinv := Uspace_inv D.g H hact hl₁H hl₁
  have hmu := hinv _ (hP T.μ₀ T.hμ₀ T.hcμ₀)
  have hcoef : ((actOp aE8 T.δ₀ s' ∘ₗ actOp aE8 T.δ₁ d') (Pi.single T.μ₀ (1 : D.L) : Fn D.L) :
      Fn D.L) (T.μ₀ + T.δ₀) ≠ 0 := by
    rw [coeff_pair T.hδ0 T.hδ1 T.hδne]
    exact mul_ne_zero hs'0 (aE8_cast_ne_zero T.hδ₀ T.hδ₀7 (mem_deg1Roots.2
      ⟨(mem_mRoots.1 T.hμ₀).1, (mem_mRoots.1 T.hμ₀).2.1⟩) (add_comm T.μ₀ T.δ₀ ▸ T.hμδ))
  have hB1 := block_e8Ten D H h1 h2 hmu T.hμδm hcoef
  intro ν hν hc
  refine hB1 ν hν ?_
  rcases T.hcμδ with h | h <;> omega

end Step


end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
