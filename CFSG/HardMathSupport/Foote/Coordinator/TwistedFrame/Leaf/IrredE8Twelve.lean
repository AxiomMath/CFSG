module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Hyp
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE8TwelveAux4
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Leaf.Action

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8

set_option linter.unusedSectionVars false


namespace IrredE8TwelveAux

theorem VM_le_HeisSpace {τ : Tag} {K : Type} [Field K] (X : Subgroup (ModGL τ K)) :
    VM X ≤ HeisSpace τ K := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨q, hq, rfl⟩ β hβ
  exact (heisCoord_spec τ K).support q (Subgroup.mem_inf.1 hq).1 β hβ

theorem irred_main (K : Type) [Field K] [Finite K] (hK : 2 ≤ Nat.card K)
    (D : LangLevi Tag.E8 K wE8) :
    TwIrred (D.frame TwClass.e8Twelve.S₁) (D.frame TwClass.e8Twelve.S₂) := by
  classical
  unfold TwIrred
  intro W hWM hstab
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  refine Or.inr (le_antisymm hWM ?_)
  have hS₁ : D.frame TwClass.e8Twelve.S₁ ≤ D.frame TwClass.e8Twelve.S₁ ⊔ D.frame TwClass.e8Twelve.S₂ :=
    le_sup_left
  have hS₂ : D.frame TwClass.e8Twelve.S₂ ≤ D.frame TwClass.e8Twelve.S₁ ⊔ D.frame TwClass.e8Twelve.S₂ :=
    le_sup_right
  have hw : wE8 • highRoot Tag.E8 = highRoot Tag.E8 := by
    rw [w_smul]
    decide +kernel
  obtain ⟨T⟩ := exists_linData D hw
  obtain ⟨a, ha, hact⟩ := exists_action_data D.L
  have hWH : ∀ v ∈ W, ∀ ν, ν ∉ Deg1 Tag.E8 → v ν = 0 := fun v hv ν hν =>
    VM_le_HeisSpace _ (hWM hv) ν hν
  have hVM : ∀ v ∈ VM (D.frame TwClass.e8Twelve.S₁ ⊔ D.frame TwClass.e8Twelve.S₂),
      ∀ β ∈ sig1, T.Gi (iotaV D v) β = 0 := by
    let P : Submodule K (V8 → K) :=
      { carrier := {v | ∀ β ∈ sig1, T.Gi (iotaV D v) β = 0}
        add_mem' := fun {x y} hx hy β hβ => by
          rw [map_add, map_add, Pi.add_apply, hx β hβ, hy β hβ, add_zero]
        zero_mem' := fun β _ => by simp
        smul_mem' := fun c {x} hx β hβ => by
          rw [map_smul, ← algebraMap_smul D.L c (iotaV D x), map_smul, Pi.smul_apply, hx β hβ,
            smul_zero] }
    have hle : VM (D.frame TwClass.e8Twelve.S₁ ⊔ D.frame TwClass.e8Twelve.S₂) ≤ P := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨hqQ, hqC⟩ := Subgroup.mem_inf.1 hq
      exact propA T hS₁ hK hqQ fun r hr => (Subgroup.mem_centralizer_iff.1 hqC r hr).symm
    exact fun v hv => hle hv
  have hZsupp := Zsp_support T (W := W) fun v hv => hVM v (hWM hv)
  have hZne : Zsp T W ≠ ⊥ := by
    intro hZ0
    obtain ⟨v₀, hv₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have h1 : T.Gi (iotaV D v₀) ∈ Zsp T W := mem_Zsp_of_mem T hv₀
    rw [hZ0, Submodule.mem_bot] at h1
    have h2 := T.G_Gi (v := iotaV D v₀) fun ν hν => by simp [iotaV_apply, hWH v₀ hv₀ ν hν]
    rw [h1, map_zero] at h2
    exact hne (iotaV_injective D (by rw [← h2, map_zero]))
  obtain ⟨Sa, hA⟩ := stab_Apos T hWH hstab hact hS₁
  obtain ⟨Sb, hB⟩ := stab_Aneg T hWH hstab hact hS₁
  obtain ⟨Sc, hC⟩ := stab_Lpos T hWH hstab hact hS₂
  obtain ⟨Sd, hD'⟩ := stab_Lneg T hWH hstab hact hS₂
  obtain ⟨εe, hεe, hE⟩ := stab_Cpos T hWH hstab hact hS₂
  obtain ⟨εf, hεf, hF⟩ := stab_Cneg T hWH hstab hact hS₂
  have hσ : ∀ μ ∈ dl, (Pi.single μ (1 : D.L) : V8 → D.L) ∈ Zsp T W →
      (Pi.single (wp μ) (1 : D.L) : V8 → D.L) ∈ Zsp T W := by
    intro μ hμ hmem
    have hμD : μ ∈ Deg1 Tag.E8 := (mem_Deg1_iff_deg1Roots μ).2 (Finset.mem_sdiff.1 hμ).1
    have hwD : wE8 • μ ∈ Deg1 Tag.E8 := by
      rw [w_smul]
      exact (mem_Deg1_iff_deg1Roots _).2 (wp_mem_deg1 μ hμ)
    obtain ⟨ε, hε, hN⟩ := N_single T hμD hwD
    have h1 := Zsp_sigma T hWH _ hmem
    have h3 : (fun ν => D.Fr ((Pi.single μ (1 : D.L) : V8 → D.L) ν)) = Pi.single μ 1 := by
      funext ν
      by_cases h : ν = μ <;> simp [Pi.single_apply, h]
    rw [h3, hN] at h1
    have h2 := Submodule.smul_mem (Zsp T W) ε h1
    have h4 : ε • (Pi.single (wE8 • μ) ε : V8 → D.L) = Pi.single (wp μ) 1 := by
      rw [w_smul]
      funext ν
      by_cases h : ν = wp μ
      · subst h
        simp [hε]
      · simp [Pi.single_apply, h]
    rwa [h4] at h2
  have hcore := core ha (Nat.card K) hK (card_cast_zero (D := D)) (Zsp T W) hZsupp hZne Sa Sb Sc
    Sd εe εf hεe hεf hA hB hC hD' hE hF hσ
  intro v hv
  have hvsupp : ∀ ν, ν ∉ dl → T.Gi (iotaV D v) ν = 0 := by
    intro ν hν
    by_cases h1 : ν ∈ sig1
    · exact hVM v hv ν h1
    · apply T.Gi_supp
      intro hD
      exact hν (Finset.mem_sdiff.2 ⟨(mem_Deg1_iff_deg1Roots ν).1 hD, h1⟩)
  have hmemZ : T.Gi (iotaV D v) ∈ Zsp T W := by
    rw [eq_sum_single_of_supp hvsupp]
    exact Submodule.sum_mem _ fun μ hμ => Submodule.smul_mem _ _ (hcore μ hμ)
  have hZ : Zsp T W = Submodule.map T.Gi (Submodule.span D.L (iotaV D '' (W : Set (V8 → K)))) := by
    unfold Zsp genSet
    rw [Submodule.map_span, Set.image_image]
  have hspan : ∀ y ∈ Submodule.span D.L (iotaV D '' (W : Set (V8 → K))),
      ∀ ν, ν ∉ Deg1 Tag.E8 → y ν = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w₁, hw₁, rfl⟩ := hx
      intro ν hν
      simp [iotaV_apply, hWH w₁ hw₁ ν hν]
    | zero => intro ν _; rfl
    | add x z _ _ hx hz => intro ν hν; simp [hx ν hν, hz ν hν]
    | smul c x _ hx => intro ν hν; simp [hx ν hν]
  rw [hZ] at hmemZ
  obtain ⟨y, hy, hyeq⟩ := hmemZ
  have hysupp : ∀ ν, ν ∉ Deg1 Tag.E8 → y ν = 0 := hspan y hy
  have hvH : ∀ ν, ν ∉ Deg1 Tag.E8 → iotaV D v ν = 0 := fun ν hν => by
    simp [iotaV_apply, VM_le_HeisSpace _ hv ν hν]
  have hι : iotaV D v = y := by
    have h1 := T.G_Gi (v := y) hysupp
    have h2 := T.G_Gi (v := iotaV D v) hvH
    rw [hyeq] at h1
    rw [← h1, h2]
  exact mem_of_iotaV_mem_span D W (hι ▸ hy)

end IrredE8TwelveAux

theorem twIrred_e8Twelve (K : Type) [Field K] [Finite K] (hK : 2 ≤ Nat.card K)
    (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) :
    TwIrred (TwClass.e8Twelve.X₁ D) (TwClass.e8Twelve.X₂ D) :=
  IrredE8TwelveAux.irred_main K hK D

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
