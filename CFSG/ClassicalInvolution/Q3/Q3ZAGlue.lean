module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPair
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.Q3.Q3ZFraFrame
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.Timmesfeld.ARS.FrameSL3
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Q3.Q3Z
open scoped MatrixGroups commutatorElement

section Family

variable {F : Type} [Field F] {G : Type} [Group G]

structure SteinbergFamily (a b c a' b' c' : F → G) : Prop where
  add_a : ∀ s t, a (s + t) = a s * a t
  add_b : ∀ s t, b (s + t) = b s * b t
  add_c : ∀ s t, c (s + t) = c s * c t
  add_a' : ∀ s t, a' (s + t) = a' s * a' t
  add_b' : ∀ s t, b' (s + t) = b' s * b' t
  add_c' : ∀ s t, c' (s + t) = c' s * c' t
  comm_ac : ∀ s t, Commute (a s) (c t)
  comm_ab' : ∀ s t, Commute (a s) (b' t)
  comm_bc : ∀ s t, Commute (b s) (c t)
  comm_ba' : ∀ s t, Commute (b s) (a' t)
  comm_a'c' : ∀ s t, Commute (a' s) (c' t)
  comm_b'c' : ∀ s t, Commute (b' s) (c' t)
  rel₁ : ∀ s t, ⁅a s, b t⁆ = c (s * t)
  rel₂ : ∀ s t, ⁅a' s, c t⁆ = b (s * t)
  rel₃ : ∀ s t, ⁅a s, c' t⁆ = b' (-(s * t))
  rel₄ : ∀ s t, ⁅a' s, b' t⁆ = c' (-(s * t))
  rel₅ : ∀ s t, ⁅b' s, c t⁆ = a (-(s * t))
  rel₆ : ∀ s t, ⁅b s, c' t⁆ = a' (s * t)

variable {a b c a' b' c' : F → G}

theorem SteinbergFamily.exists_hom [Finite F] (h : SteinbergFamily a b c a' b' c') :
    ∃ ρ : SL(3, F) →* G, ∀ s, ρ (tv 0 1 s) = a s ∧ ρ (tv 1 0 s) = a' s ∧ ρ (tv 1 2 s) = b s ∧
      ρ (tv 2 1 s) = b' s := by
  have hadd := fam_add h.add_a h.add_b h.add_c h.add_a' h.add_b' h.add_c'
  have hcomm := fam_comm_signed h.add_a h.add_b h.add_c h.add_a' h.add_b' h.add_c' h.comm_ac
    h.comm_ab' h.comm_bc h.comm_ba' h.comm_a'c' h.comm_b'c' h.rel₁ h.rel₂ h.rel₃ h.rel₄ h.rel₅
    h.rel₆
  obtain ⟨ρ, hρ⟩ := exists_hom_of_steinberg hadd hcomm
  refine ⟨ρ, fun s => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [tv_of_ne (by decide : (0 : Fin 3) ≠ 1)]
    exact hρ 0 1 (by decide) s
  · rw [tv_of_ne (by decide : (1 : Fin 3) ≠ 0)]
    exact hρ 1 0 (by decide) s
  · rw [tv_of_ne (by decide : (1 : Fin 3) ≠ 2)]
    exact hρ 1 2 (by decide) s
  · rw [tv_of_ne (by decide : (2 : Fin 3) ≠ 1)]
    exact hρ 2 1 (by decide) s

@[expose] def rootGroup (a : F → G) (ha : ∀ s t, a (s + t) = a s * a t) : Subgroup G where
  carrier := Set.range a
  one_mem' := ⟨0, by
    have h := ha 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm⟩
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, ha s t⟩
  inv_mem' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨-s, map_neg_of_add ha s⟩

theorem coe_rootGroup (a : F → G) (ha : ∀ s t, a (s + t) = a s * a t) :
    (rootGroup a ha : Set G) = Set.range a :=
  rfl

theorem SteinbergFamily.linearBlockStandardPair [Finite F]
    (h : SteinbergFamily a b c a' b' c') (hnt : ∃ s, a s ≠ 1) :
    ∃ W, LinearBlockStandardPair F W (Subgroup.closure (Set.range a ∪ Set.range a'))
      (Subgroup.closure (Set.range b ∪ Set.range b')) := by
  obtain ⟨ρ, hρ⟩ := h.exists_hom
  have hker : ρ.ker ≤ Subgroup.center SL(3, F) := by
    refine CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl) ?_
    obtain ⟨s, hs⟩ := hnt
    exact ⟨tv 0 1 s, by rw [(hρ s).1]; exact hs⟩
  have hsup := CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_sup
    (coe_rootGroup a h.add_a) (coe_rootGroup a' h.add_a') (coe_rootGroup b h.add_b)
    (coe_rootGroup b' h.add_b') ρ hker (fun s => ⟨(hρ s).1, (hρ s).2.1, (hρ s).2.2.1,
      (hρ s).2.2.2⟩)
  refine ⟨ρ.range, ?_⟩
  rw [← CFSG.ClassicalInvolution.ModelFacts.closure_range_eq_sup (coe_rootGroup a h.add_a)
    (coe_rootGroup a' h.add_a'), ← CFSG.ClassicalInvolution.ModelFacts.closure_range_eq_sup
    (coe_rootGroup b h.add_b) (coe_rootGroup b' h.add_b')] at hsup
  exact hsup

end Family

section Frame

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] def SteinbergA2 (fr : C3Frame G Ω) : Prop :=
  ∃ a b c a' b' c' : GaloisField 3 1 → G, SteinbergFamily a b c a' b' c' ∧ (∃ s, a s ≠ 1) ∧
    Subgroup.closure (Set.range a ∪ Set.range a') ∈ shortNodes fr.Θ₀₁ ∧
    Subgroup.closure (Set.range b ∪ Set.range b') ∈ shortNodes fr.Θ₁₂

theorem exists_a2_of_steinbergA2 {fr : C3Frame G Ω} (h : SteinbergA2 fr) :
    ∃ T₀ ∈ shortNodes fr.Θ₀₁, ∃ T₁ ∈ shortNodes fr.Θ₁₂,
      ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W T₀ T₁ := by
  obtain ⟨a, b, c, a', b', c', hF, hnt, h₀, h₁⟩ := h
  obtain ⟨W, hW⟩ := hF.linearBlockStandardPair hnt
  exact ⟨_, h₀, _, h₁, W, hW⟩

end Frame

end CFSG.ClassicalInvolution.Q3.Q3ZA
