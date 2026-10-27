module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RConj
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDual
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDualFrob

public section

namespace CFSG.KC.TcRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes
open CFSG.Assembly (LargeEvenLabel LargeEvenSplit LargeEvenHalfSplit)
open CFSG.StandardType (GGLabelIso)

@[expose] def SurvHyp {τ : Tag} {p : ℕ} (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (F : ℕ)
    (P : Submodule (ZMod p) (Fin τ.rank → ZMod p)) (iJ : KernelComponent (tcChiPl τ p P))
    (x : Fin τ.rank → ZMod p) (ix : KernelComponent (tcChiLn τ p x)) : Prop :=
  2 ≤ componentOrbitLength ρ (componentRoots (tcChiPl τ p P) iJ) ∧ x ∈ P ∧ x ≠ 0 ∧
  componentRoots (tcChiPl τ p P) iJ ⊆ componentRoots (tcChiLn τ p x) ix ∧
  componentRoots (tcChiLn τ p x) ix ≠ componentRoots (tcChiPl τ p P) iJ ∧
  (∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn τ p x) ix)) ∧
    LargeEvenSplit p lab') ∧
  (∀ d ∈ P, d ≠ 0 → (∀ c : ZMod p, d ≠ c • x) → ∀ i : KernelComponent (tcChiLn τ p d),
    componentRoots (tcChiPl τ p P) iJ ⊆ componentRoots (tcChiLn τ p d) i →
    GGLabelIso (LabAt ρ F (componentRoots (tcChiLn τ p d) i))
      (LabAt ρ F (componentRoots (tcChiPl τ p P) iJ)) ∨
    ∃ (c : Prop) (lab' : LargeEvenLabel),
      GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn τ p d) i)) ∧
      LargeEvenHalfSplit p lab' c)

theorem SurvHyp.conj {τ : Tag}
    {p : ℕ} (h : WeylGroup τ) {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {F : ℕ}
    {P : Submodule (ZMod p) (Fin τ.rank → ZMod p)} {iJ : KernelComponent (tcChiPl τ p P)}
    {x : Fin τ.rank → ZMod p} {ix : KernelComponent (tcChiLn τ p x)}
    (hS : SurvHyp ρ F P iJ x ix) :
    ∃ (iJ' : KernelComponent (tcChiPl τ p (P.map (tcrDualLin h p))))
      (ix' : KernelComponent (tcChiLn τ p (tcrDualVec h p x))),
      componentRoots (tcChiPl τ p (P.map (tcrDualLin h p))) iJ' =
        (fun γ => h • γ) '' componentRoots (tcChiPl τ p P) iJ ∧
      componentRoots (tcChiLn τ p (tcrDualVec h p x)) ix' =
        (fun γ => h • γ) '' componentRoots (tcChiLn τ p x) ix ∧
      SurvHyp (tcrConjPerm h ρ) F (P.map (tcrDualLin h p)) iJ' (tcrDualVec h p x) ix' := by
  obtain ⟨hJ2, hxP, hx0, hJx, hne, hsplit, hoth⟩ := hS
  have hkerP : kernelRoots (tcChiPl τ p (P.map (tcrDualLin h p))) =
      (fun γ => h • γ) '' kernelRoots (tcChiPl τ p P) := by
    have := kernelRoots_tcChiQ_dual h (p := p) (P : Set (Fin τ.rank → ZMod p))
    have hcoe : ((P.map (tcrDualLin h p) : Submodule (ZMod p) (Fin τ.rank → ZMod p)) :
        Set (Fin τ.rank → ZMod p)) = tcrDualVec h p '' (P : Set (Fin τ.rank → ZMod p)) :=
      Submodule.map_coe _ _
    unfold tcChiPl
    rw [hcoe]
    exact this
  obtain ⟨iJ', hiJ'⟩ := exists_componentRoots_image h hkerP iJ
  have hinj : Function.Injective (fun γ : Fin τ.rank → ℤ => h • γ) := MulAction.injective h
  have hkerLn : ∀ d : Fin τ.rank → ZMod p, kernelRoots (tcChiLn τ p (tcrDualVec h p d)) =
      (fun γ => h • γ) '' kernelRoots (tcChiLn τ p d) := by
    intro d
    have := kernelRoots_tcChiQ_dual h (p := p) ({d} : Set (Fin τ.rank → ZMod p))
    have himg : tcrDualVec h p '' ({d} : Set (Fin τ.rank → ZMod p)) = {tcrDualVec h p d} :=
      Set.image_singleton
    unfold tcChiLn
    rw [← himg]
    exact this
  have hmapzero : ∀ d : Fin τ.rank → ZMod p, tcrDualVec h p d = 0 → d = 0 := fun d hd =>
    tcrDualVec_injective h (hd.trans (map_zero (tcrDualLin h p)).symm)
  obtain ⟨ix', hix'⟩ := exists_componentRoots_image h (hkerLn x) ix
  refine ⟨iJ', ix', hiJ', hix', ?_, Submodule.mem_map.2 ⟨x, hxP, rfl⟩,
    fun h0 => hx0 (hmapzero x h0), ?_, ?_, ?_, ?_⟩
  · rw [hiJ', componentOrbitLength_conj]
    exact hJ2
  · rw [hiJ', hix']
    exact Set.image_mono hJx
  · rw [hiJ', hix']
    intro h'
    exact hne (Set.image_injective.2 hinj h')
  · obtain ⟨lab', hl, hs⟩ := hsplit
    refine ⟨lab', ?_, hs⟩
    rw [hix', labAt_conj]
    exact hl
  · intro d' hd' hd0 hdx i' hi'
    obtain ⟨d, hd, hdd'⟩ := Submodule.mem_map.1 hd'
    have hdd'' : tcrDualVec h p d = d' := hdd'
    subst hdd''
    have hd0' : d ≠ 0 := fun h0 => hd0 (by rw [h0]; exact map_zero (tcrDualLin h p))
    have hdx' : ∀ c : ZMod p, d ≠ c • x := fun c hc => hdx c (by
      rw [hc]
      exact tcrDualVec_smul h c x)
    obtain ⟨i, hi⟩ := exists_componentRoots_preimage h (hkerLn d) i'
    have hsub : componentRoots (tcChiPl τ p P) iJ ⊆ componentRoots (tcChiLn τ p d) i := by
      rw [hiJ', hi] at hi'
      exact (Set.image_subset_image_iff hinj).1 hi'
    have := hoth d hd hd0' hdx' i hsub
    rw [hi, hiJ', labAt_conj, labAt_conj]
    exact this

end CFSG.KC.TcRes

end
