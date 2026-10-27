module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleCycle
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Linear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving
open scoped Pointwise commutatorElement


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
  {i : KernelComponent χ}

theorem iterHom_eq_self_of_mem_centralizer
    {F : ModGL τ L →* ModGL τ L} {Z : Subgroup (ModGL τ L)}
    (hZ : Subgroup.center (rootSpan τ L (componentRoots χ i)) = ⊥)
    (hFmem : ∀ x ∈ rootSpan τ L (componentRoots χ i),
      F x ∈ rootSpan τ L (componentRoots χ i))
    (hZA : Z ≤ Subgroup.centralizer
      (rootSpan τ L (componentRoots χ i) : Set (ModGL τ L)))
    {g : ModGL τ L} (hg : g ∈ rootSpan τ L (componentRoots χ i))
    (hz : F g * g⁻¹ ∈ Z) :
    F g = g := by
  have hmem : F g * g⁻¹ ∈ rootSpan τ L (componentRoots χ i) :=
    mul_mem (hFmem g hg) (inv_mem hg)
  have hcenter : (⟨F g * g⁻¹, hmem⟩ : ↥(rootSpan τ L (componentRoots χ i))) ∈
      Subgroup.center (rootSpan τ L (componentRoots χ i)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (hZA hz) x x.2
  rw [hZ, Subgroup.mem_bot] at hcenter
  exact mul_inv_eq_one.mp (congrArg Subtype.val hcenter)

theorem commutator_mem_of_twist_mem_centralizer
    {F : ModGL τ L →* ModGL τ L} {Z : Subgroup (ModGL τ L)}
    (hZ : Subgroup.center (rootSpan τ L (componentRoots χ i)) = ⊥)
    (hFmem : ∀ x ∈ rootSpan τ L (componentRoots χ i),
      F x ∈ rootSpan τ L (componentRoots χ i))
    (hZA : Z ≤ Subgroup.centralizer
      (rootSpan τ L (componentRoots χ i) : Set (ModGL τ L)))
    {C : Subgroup (ModGL τ L)}
    (hCfull : ∀ x ∈ rootSpan τ L (componentRoots χ i), F x = x → x ∈ C)
    {g₁ g₁' : ModGL τ L}
    (hg₁ : g₁ ∈ rootSpan τ L (componentRoots χ i))
    (hg₁' : g₁' ∈ rootSpan τ L (componentRoots χ i))
    (hz₁ : F g₁ * g₁⁻¹ ∈ Z) (hz₁' : F g₁' * g₁'⁻¹ ∈ Z) :
    ⁅g₁, g₁'⁆ ∈ C := by
  have hfix₁ : F g₁ = g₁ :=
    iterHom_eq_self_of_mem_centralizer hZ hFmem hZA hg₁ hz₁
  have hfix₁' : F g₁' = g₁' :=
    iterHom_eq_self_of_mem_centralizer hZ hFmem hZA hg₁' hz₁'
  have hmem : ⁅g₁, g₁'⁆ ∈ rootSpan τ L (componentRoots χ i) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₁ hg₁') (inv_mem hg₁)) (inv_mem hg₁')
  have hfix : F ⁅g₁, g₁'⁆ = ⁅g₁, g₁'⁆ := by
    rw [map_commutatorElement, hfix₁, hfix₁']
  exact hCfull _ hmem hfix

structure TwoDExcFixedData {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a))
    (s : ℕ) where
  C : Subgroup (ModGL τ L)
  le : C ≤ rootSpan τ L (componentRoots (rootCharHom a) i)
  fix : ∀ x ∈ C, iterHom S.D.step s x = x
  perf : Group.IsPerfect ↥C
  full : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
    iterHom S.D.step s x = x → x ∈ C

@[expose] def fixedPointSubgroup {G : Type*} [Group G] (F : G →* G) (H : Subgroup G) :
    Subgroup G where
  carrier := {x | x ∈ H ∧ F x = x}
  one_mem' := ⟨H.one_mem, map_one F⟩
  mul_mem' hx hy := ⟨H.mul_mem hx.1 hy.1, by rw [map_mul, hx.2, hy.2]⟩
  inv_mem' hx := ⟨H.inv_mem hx.1, by rw [map_inv, hx.2]⟩

@[expose] def TwoDExcFixedPointsPerfect {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a))
    (s : ℕ) : Prop :=
  Group.IsPerfect ↥(fixedPointSubgroup (iterHom S.D.step s)
    (rootSpan τ L (componentRoots (rootCharHom a) i)))

noncomputable def twoDExcFixedData_of_perfect {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    {S : LangSetup τ L p} {a : Fin τ.rank → Lˣ} {i : KernelComponent (rootCharHom a)}
    {s : ℕ} (h : TwoDExcFixedPointsPerfect S a i s) :
    TwoDExcFixedData S a i s where
  C := fixedPointSubgroup (iterHom S.D.step s)
    (rootSpan τ L (componentRoots (rootCharHom a) i))
  le := fun _ hx => hx.1
  fix := fun _ hx => hx.2
  perf := h
  full := fun _ hx hfix => ⟨hx, hfix⟩


end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
