module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux20

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open scoped commutatorElement

set_option linter.unusedSectionVars false


section Rat

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

theorem sg_eq_one (hK : Nat.card K = 2) {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β) :
    (toSetup D ⊥).sg β = 1 := by
  haveI := charP_L D hK
  exact E8TwoD.eq_one_of_mul_self_eq_one ((toSetup D ⊥).hm β hβ).1

theorem ΨE_comm (a b : ModGL Tag.E8 K) : ΨE D ⁅a, b⁆ = ⁅ΨE D a, ΨE D b⁆ := by
  simp only [commutatorElement_def, ΨE_mul, ΨE_inv]

theorem exists_rho (hK : Nat.card K = 2) {β₀ β₁ : Fin Tag.E8.rank → ℤ} (hA : PairData β₀ β₁)
    {s : D.L} (hs : s ^ 4 = s) :
    ∃ ρ : ModGL Tag.E8 K, ρ ∈ Rθ (TwClass.e8Ten.X₁ D) ∧
      ΨE D ρ = pinnedX Tag.E8 D.L β₀ s * pinnedX Tag.E8 D.L β₁ (s ^ 2) := by
  haveI hcL : CharP D.L 2 := charP_L D hK
  haveI hAC : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set S := toSetup D ⊥ with hS
  have hr₀ : IsRoot Tag.E8 β₀ := mem_rootFinset.1 hA.h₀
  have hr₁ : IsRoot Tag.E8 β₁ := mem_rootFinset.1 hA.h₁
  have hsg₀ : S.sg β₀ = 1 := sg_eq_one D hK hr₀
  have hsg₁ : S.sg β₁ = 1 := sg_eq_one D hK hr₁
  have hFr : ∀ c : D.L, S.Fr c = c ^ 2 := fun c => Fr_sq D hK c
  have hcomm : ∀ a b : D.L, pinnedX Tag.E8 D.L β₀ a * pinnedX Tag.E8 D.L β₁ b =
      pinnedX Tag.E8 D.L β₁ b * pinnedX Tag.E8 D.L β₀ a := fun a b =>
    pinnedX_commute_of_not_root hA.h₀ hA.h₁ hA.ne hA.ne' hA.sum a b
  have hσ := S.pair_sfixed hr₀ hr₁ (by rw [toSetup_hw, hA.w₀]) (by rw [toSetup_hw, hA.w₁]) hcomm
    (s := s) (d := s ^ 2) (by rw [hsg₀, one_mul, hFr]) (by
      rw [hsg₁, one_mul, hFr, ← pow_mul]
      exact hs)
  have hxA : pinnedX Tag.E8 D.L β₀ s * pinnedX Tag.E8 D.L β₁ (s ^ 2) ∈ adjointGroup Tag.E8 D.L :=
    mul_mem (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨s, rfl⟩))
      (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨s ^ 2, rfl⟩))
  obtain ⟨l, hlA, hl⟩ := S.rat_of_sfixed hxA hσ
  have hl' : baseChangeGL (algebraMap K D.L) l =
      gE D * (pinnedX Tag.E8 D.L β₀ s * pinnedX Tag.E8 D.L β₁ (s ^ 2)) * (gE D)⁻¹ := hl
  have hΨ : ΨE D l = pinnedX Tag.E8 D.L β₀ s * pinnedX Tag.E8 D.L β₁ (s ^ 2) := by
    unfold ΨE
    rw [hl']
    group
  have hβ₀D : β₀ ∈ Deg1 Tag.E8 := CoordAux.mem_Deg1.2 ⟨hr₀, hA.d₀⟩
  have hβ₁D : β₁ ∈ Deg1 Tag.E8 := CoordAux.mem_Deg1.2 ⟨hr₁, hA.d₁⟩
  have hQ : pinnedX Tag.E8 D.L β₀ s * pinnedX Tag.E8 D.L β₁ (s ^ 2) ∈ Qθ Tag.E8 D.L :=
    mul_mem (pinnedX_mem_Qθ_of_mem_Deg1 hβ₀D _) (pinnedX_mem_Qθ_of_mem_Deg1 hβ₁D _)
  refine ⟨l, ⟨?_, ?_⟩, hΨ⟩
  · refine (mem_frame_iff' D TwClass.e8Ten.S₁ l).2 ⟨hlA, ?_⟩
    have h1 : ΨE D l ∈ rootSpan Tag.E8 D.L TwClass.e8Ten.S₁ := by
      rw [hΨ]
      exact mul_mem (pinnedX_mem_S₁ D hA.h₀ (sRoots1_S₁ β₀ hA.s₀).2 s)
        (pinnedX_mem_S₁ D hA.h₁ (sRoots1_S₁ β₁ hA.s₁).2 (s ^ 2))
    exact h1
  · refine mem_Qθ_of_bc D hK hlA ?_
    rw [hl']
    exact Lθ_conj_mem_Qθ (gE_mem_Lθ D) hQ

theorem exists_aneg :
    ∃ t : D.L, t ≠ 0 ∧ ΨE D (pinnedX Tag.E8 K (-highRoot Tag.E8) 1) =
      pinnedX Tag.E8 D.L (-highRoot Tag.E8) t := by
  set a' := pinnedX Tag.E8 K (-highRoot Tag.E8) 1 with ha'
  have hbc : baseChangeGL (algebraMap K D.L) a' = pinnedX Tag.E8 D.L (-highRoot Tag.E8) 1 := by
    rw [ha', baseChangeGL_pinnedX, map_one]
  have hx : pinnedX Tag.E8 D.L (-highRoot Tag.E8) 1 ∈ Heis.Uneg Tag.E8 D.L :=
    mem_rootSubgroup.2 ⟨1, rfl⟩
  have hinv : (gE D)⁻¹ ∈ Lθ Tag.E8 D.L := inv_mem (gE_mem_Lθ D)
  have hmem := (Subgroup.mem_normalizer_iff.1 (Lθ_le_normalizer_Uneg Tag.E8 D.L hinv)
    (pinnedX Tag.E8 D.L (-highRoot Tag.E8) 1)).1 hx
  rw [inv_inv] at hmem
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 hmem
  have hΨ : ΨE D a' = pinnedX Tag.E8 D.L (-highRoot Tag.E8) t := by
    unfold ΨE
    rw [hbc, ht]
  refine ⟨t, ?_, hΨ⟩
  intro h0
  rw [h0, pinnedX_zero] at hΨ
  have h1 : a' = 1 := ΨE_injective D (by rw [hΨ, ΨE_one])
  exact one_ne_zero ((E8TwoD.pinnedX_eq_one_iff (τ := Tag.E8) (-highRoot Tag.E8) (1 : K)).1 h1)

theorem exists_Zroot (hK : Nat.card K = 2) {β₀ β₁ : Fin Tag.E8.rank → ℤ} (hA : PairData β₀ β₁) :
    ∃ Z ∈ Agp D, ∃ ζ : D.L, ζ ≠ 0 ∧
      ΨE D Z = pinnedX Tag.E8 D.L (β₀ + (-highRoot Tag.E8 + β₁)) ζ := by
  haveI hcL : CharP D.L 2 := charP_L D hK
  haveI hAC : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨t, ht0, hat⟩ := exists_aneg D
  set a' := pinnedX Tag.E8 K (-highRoot Tag.E8) 1 with ha'
  have ha'U : a' ∈ Heis.Uneg Tag.E8 K := mem_rootSubgroup.2 ⟨1, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω : D.L, ω ^ 2 + ω + 1 = 0 := by
    have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial D.L).degree ≠ 0 := by
      have : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial D.L).degree = 2 := by
        compute_degree!
      rw [this]
      norm_num
    obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨ω, ?_⟩
    simpa [Polynomial.IsRoot] using hω
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hs1 : (1 : D.L) ^ 4 = 1 := one_pow _
  have hsω : ω ^ 4 = ω := by linear_combination ω * hω3
  have hsω2 : (ω ^ 2) ^ 4 = ω ^ 2 := by
    linear_combination ω ^ 2 * (ω ^ 3 + 1) * hω3 + ω ^ 2 * hω3 - ω ^ 2 * hω3
  obtain ⟨ρ₁, hρ₁, hΨ₁⟩ := exists_rho D hK hA hs1
  obtain ⟨ρ₂, hρ₂, hΨ₂⟩ := exists_rho D hK hA hsω
  obtain ⟨ρ₃, hρ₃, hΨ₃⟩ := exists_rho D hK hA hsω2
  have hc : ∀ ρ : ModGL Tag.E8 K, ρ ∈ Rθ (TwClass.e8Ten.X₁ D) → ⁅a', ρ⁆ ∈ Agp D := by
    intro ρ hρ
    have h1 : a' ∈ Agp D := Subgroup.subset_closure (Or.inr ha'U)
    have h2 : ρ ∈ Agp D := Subgroup.subset_closure (Or.inl hρ)
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h1 h2) (inv_mem h1)) (inv_mem h2)
  refine ⟨(⁅a', ρ₁⁆ * ⁅a', ρ₂⁆⁻¹)⁻¹ * ⁅a', ρ₃⁆, ?_, t, ht0, ?_⟩
  · exact mul_mem (inv_mem (mul_mem (hc _ hρ₁) (inv_mem (hc _ hρ₂)))) (hc _ hρ₃)
  · simp only [ΨE_mul, ΨE_inv, ΨE_comm, hat, hΨ₁, hΨ₂, hΨ₃]
    exact Z_extract hA hω t

end Rat

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
