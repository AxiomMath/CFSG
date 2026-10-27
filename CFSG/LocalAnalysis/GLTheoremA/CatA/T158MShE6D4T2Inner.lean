module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6D4T2Lang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6D4T2Asm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.GroupActions (subgroupStabAut subgroupStabRestrict)

section Inner

theorem e6d4t2_inner_of_assembly
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hshape : E6ShapeSetup S) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (hn : (kernelRoots (rootCharHom a)).ncard = 24) {i : KernelComponent (rootCharHom a)}
    (hin : twistInner (componentRoots (rootCharHom a) i) ⇑S.ρ) {y : ModGL Tag.E6 L}
    (hyC : y ∈ toralCentralizer Tag.E6 L a)
    (hyStab : MulAut.conj y ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hAsm : ∀ g : ModGL Tag.E6 L, S.D.step g = g →
      MulAut.conj g ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
      g * y * g⁻¹ * y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) →
      y ^ 3 ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) →
      centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
          (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
            ⟨MulAut.conj y, hyStab⟩) ∈
        innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj y, hyStab⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨t, z0, ht, hz0, hFg⟩ := e6d4t2_exists_g S hshape hT hap hn hin
  obtain ⟨std⟩ := e6d4t2_exists_std S hT hap hn i
  have htK : ∀ γ ∈ kernelRoots (rootCharHom a), t • γ ∈ kernelRoots (rootCharHom a) :=
    fun γ hγ => e6d4t2_mem_kernel_of_inverting ht hγ
  have ht'K : ∀ γ ∈ kernelRoots (rootCharHom a), t⁻¹ • γ ∈ kernelRoots (rootCharHom a) :=
    fun γ hγ => e6d4t2_mem_kernel_of_inverting (e6d4t2_inverting_inv ht) hγ
  set g := z0 * canonicalRep (coxeterSystem Tag.E6) L t with hg
  have hgadj : g ∈ adjointGroup Tag.E6 L :=
    mul_mem (torus_sup_rootSpan_le_adjointGroup _ hz0) (canonicalRep_mem_adjointGroup _ L t)
  have hgmodel : g ∈ S.D.model := ⟨hgadj, hFg⟩
  have hgA := e6d4t2_map_rootSpan_g htK ht'K hz0
  have hgStab := e6d4t2_conj_stab_R S std hgmodel hgA
  exact hAsm g hFg hgStab (e6d4t2_g_conj_mem hap ht hz0 hyC) (e6d4t2_cube_mem_M hap hyC)

theorem e6d4t2_inner_holds
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hshape : E6ShapeSetup S) (a : Fin Tag.E6.rank → Lˣ)
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (hn : (kernelRoots (rootCharHom a)).ncard = 24) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hin : twistInner (componentRoots (rootCharHom a) i) ⇑S.ρ) (y : ModGL Tag.E6 L)
    (hyC : y ∈ toralCentralizer Tag.E6 L a) (hyF : S.D.step y = y)
    (hyStab : MulAut.conj y ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj y, hyStab⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  obtain ⟨std⟩ := e6d4t2_exists_std S hT hap hn i
  have hbig : 2 < (componentRoots (rootCharHom a) i).ncard := by
    rw [std.hker, hn]
    norm_num
  exact e6d4t2_inner_of_assembly S hshape hT hap hn hin hyC hyStab
    (fun g hgF hgStab hgy hy3 =>
      e6d4t2_innAutDerived_of_inverting S hT hap i hqs hρ hbig hin hyF hgF hyStab hgStab hgy hy3)

end Inner

end CFSG.LocalAnalysis.GLTheoremA.T158

end
