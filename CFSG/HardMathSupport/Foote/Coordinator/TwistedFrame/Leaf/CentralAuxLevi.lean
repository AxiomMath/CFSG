module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.LeviCompare
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.RootSpanInter

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K]

@[expose] def RootClosed (τ : Tag) (S : Set (Fin τ.rank → ℤ)) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) → a • α + b • β ∈ S

theorem rootClosed_inter {S T : Set (Fin τ.rank → ℤ)} (hS : RootClosed τ S) (hT : RootClosed τ T) :
    RootClosed τ (S ∩ T) :=
  fun _ hα _ hβ a b ha hb hr => ⟨hS _ hα.1 _ hβ.1 a b ha hb hr, hT _ hα.2 _ hβ.2 a b ha hb hr⟩

theorem rootClosed_parabolicPosRoots (J : Set (Fin τ.rank)) :
    RootClosed τ (parabolicPosRoots τ J) :=
  fun _ hα _ hβ _ _ ha hb hr => add_mem_parabolicPosRoots hα hβ ha hb hr

theorem rootClosed_image_smul (w : WeylGroup τ) {S : Set (Fin τ.rank → ℤ)} (hS : RootClosed τ S) :
    RootClosed τ ((fun β => w • β) '' S) :=
  closed_image_smul w hS

@[expose] def Ipre {k : ℕ} (ω : Fin k → WeylGroup τ) (n : ℕ) : Set (Fin τ.rank → ℤ) :=
  parabolicPosRoots τ (Jθ τ) ∩
    {β | ∀ i : Fin k, i.val < n → β ∈ (fun γ => ω i • γ) '' parabolicPosRoots τ (Jθ τ)}

theorem Ipre_zero {k : ℕ} (ω : Fin k → WeylGroup τ) :
    Ipre ω 0 = parabolicPosRoots τ (Jθ τ) := by
  ext β
  simp [Ipre]

theorem Ipre_succ_of_lt {k n : ℕ} (ω : Fin k → WeylGroup τ) (hn : n < k) :
    Ipre ω (n + 1) = Ipre ω n ∩ (fun γ => ω ⟨n, hn⟩ • γ) '' parabolicPosRoots τ (Jθ τ) := by
  ext β
  simp only [Ipre, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hA, hall⟩
    exact ⟨⟨hA, fun i hi => hall i (by omega)⟩, hall ⟨n, hn⟩ (by simp)⟩
  · rintro ⟨⟨hA, hall⟩, hB⟩
    refine ⟨hA, fun i hi => ?_⟩
    by_cases hin : i.val < n
    · exact hall i hin
    · have : i = ⟨n, hn⟩ := Fin.ext (by show i.val = n; omega)
      subst this
      exact hB

theorem Ipre_succ_of_le {k n : ℕ} (ω : Fin k → WeylGroup τ) (hn : k ≤ n) :
    Ipre ω (n + 1) = Ipre ω n := by
  ext β
  simp only [Ipre, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hA, hall⟩
    exact ⟨hA, fun i hi => hall i (by omega)⟩
  · rintro ⟨hA, hall⟩
    exact ⟨hA, fun i hi => hall i (by have := i.2; omega)⟩

theorem Ipre_k {k : ℕ} (ω : Fin k → WeylGroup τ) :
    Ipre ω k = parabolicPosRoots τ (Jθ τ) ∩
      {β | ∀ i : Fin k, β ∈ (fun γ => ω i • γ) '' parabolicPosRoots τ (Jθ τ)} := by
  ext β
  simp only [Ipre, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact and_congr_right fun _ => ⟨fun h i => h i i.2, fun h i _ => h i⟩

theorem rootClosed_Ipre {k : ℕ} (ω : Fin k → WeylGroup τ) (n : ℕ) : RootClosed τ (Ipre ω n) := by
  induction n with
  | zero => rw [Ipre_zero]; exact rootClosed_parabolicPosRoots _
  | succ n ih =>
    by_cases hn : n < k
    · rw [Ipre_succ_of_lt ω hn]
      exact rootClosed_inter ih
        (rootClosed_image_smul _ (rootClosed_parabolicPosRoots (τ := τ) (Jθ τ)))
    · rw [Ipre_succ_of_le ω (by omega)]
      exact ih

theorem Ipre_pos {k : ℕ} (ω : Fin k → WeylGroup τ) (n : ℕ) :
    ∀ α ∈ Ipre ω n, IsRoot τ α ∧ 0 < height α :=
  fun α hα => Heis.parabolicPosRoots_pos hα.1

theorem mem_rootSpan_Ipre {k : ℕ} (ω : Fin k → WeylGroup τ)
    (hmin : ∀ i, ∀ β ∈ parabolicPosRoots τ (Jθ τ), 0 < height (ω i • β)) {u : ModGL τ K}
    (hA : u ∈ rootSpan τ K (parabolicPosRoots τ (Jθ τ)))
    (hB : ∀ i, u ∈ rootSpan τ K ((fun γ => ω i • γ) '' parabolicPosRoots τ (Jθ τ))) :
    u ∈ rootSpan τ K (Ipre ω k) := by
  have key : ∀ n : ℕ, u ∈ rootSpan τ K (Ipre ω n) := by
    intro n
    induction n with
    | zero => rw [Ipre_zero]; exact hA
    | succ n ih =>
      by_cases hn : n < k
      · rw [Ipre_succ_of_lt ω hn]
        exact rootSpan_inf_rootSpan_le_rootSpan_inter K (Ipre_pos ω n)
          (image_parabolicPosRoots_pos (hmin ⟨n, hn⟩)) (rootClosed_Ipre ω n)
          (rootClosed_image_smul _ (rootClosed_parabolicPosRoots (τ := τ) (Jθ τ)))
          (Subgroup.mem_inf.2 ⟨ih, hB ⟨n, hn⟩⟩)
      · rw [Ipre_succ_of_le ω (by omega)]
        exact ih
  exact key k

theorem levi_intersection {k : ℕ} (ω : Fin k → WeylGroup τ) (J₂ : Set (Fin τ.rank))
    (hmin : ∀ i, ∀ β ∈ parabolicPosRoots τ (Jθ τ), 0 < height (ω i • β))
    (hperp : ∀ β ∈ Ipre ω k, β ∈ parabolicRoots τ J₂)
    (hfix : ∀ w : WeylGroup τ, w • highRoot τ = highRoot τ →
      (∀ i, w • (ω i • highRoot τ) = ω i • highRoot τ) → w ∈ parabolicWeylGroup τ J₂)
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hcθ : ∀ x ∈ Uθ τ K, g * x = x * g) (hcn : ∀ x ∈ Heis.Uneg τ K, g * x = x * g)
    (hc : ∀ i, (∀ x ∈ conjSub (canonicalRep (coxeterSystem τ) K (ω i)) (Uθ τ K), g * x = x * g) ∧
      (∀ x ∈ conjSub (canonicalRep (coxeterSystem τ) K (ω i)) (Heis.Uneg τ K), g * x = x * g)) :
    ∃ h ∈ torusGroup τ K, ∃ x ∈ rootSpan τ K (parabolicRoots τ J₂), g = h * x := by
  classical
  have hL1 : g ∈ Lθ τ K := centralizer_Uθ_inf_centralizer_Uneg_le_Lθ τ K hg hcθ hcn
  have hmin1 : ∀ β ∈ parabolicPosRoots τ (Jθ τ), 0 < height ((1 : WeylGroup τ) • β) := by
    intro β hβ
    rw [one_smul]
    exact (Heis.parabolicPosRoots_pos hβ).2
  obtain ⟨wa, ha, ua, va, hha, hua, hva, hwa, hga⟩ :=
    normalForm_conj_Lθ τ K hmin1 (g := g)
      (by rw [canonicalRep_one, conjSub_one]; exact hL1)
  have himg1 : (fun β => (1 : WeylGroup τ) • β) '' parabolicPosRoots τ (Jθ τ) =
      parabolicPosRoots τ (Jθ τ) := by
    ext x
    simp
  rw [himg1] at hua hva
  have hcmp : ∀ i, wa • (ω i • highRoot τ) = ω i • highRoot τ ∧
      ua ∈ rootSpan τ K ((fun γ => ω i • γ) '' parabolicPosRoots τ (Jθ τ)) ∧
      va ∈ rootSpan τ K ((fun γ => ω i • γ) '' parabolicPosRoots τ (Jθ τ)) := fun i =>
    normalForm_compare hha hua hva hga (hmin i)
      (mem_conjSub_Lθ_of_centralizes (ω i) hg (hc i).1 (hc i).2)
  have hvA : va ∈ rootSpan τ K (parabolicPosRoots τ (Jθ τ)) :=
    rootSpan_mono_of_subset Set.inter_subset_left hva
  have hu : ua ∈ rootSpan τ K (parabolicRoots τ J₂) :=
    rootSpan_mono_of_subset hperp
      (mem_rootSpan_Ipre ω hmin hua fun i => (hcmp i).2.1)
  have hv : va ∈ rootSpan τ K (parabolicRoots τ J₂) :=
    rootSpan_mono_of_subset hperp
      (mem_rootSpan_Ipre ω hmin hvA fun i => (hcmp i).2.2)
  have hwθ : wa • highRoot τ = highRoot τ := by
    simpa only [one_smul] using hwa
  have hwJ := hfix wa hwθ fun i => (hcmp i).1
  have hn : canonicalRep (coxeterSystem τ) K wa ∈ rootSpan τ K (parabolicRoots τ J₂) := by
    rw [← subsystemGroup_eq_rootSpan]
    exact canonicalRep_mem_subsystemGroup hwJ
  exact ⟨ha, hha, ua * canonicalRep (coxeterSystem τ) K wa * va,
    mul_mem (mul_mem hu hn) hv, by rw [hga]; group⟩

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux
