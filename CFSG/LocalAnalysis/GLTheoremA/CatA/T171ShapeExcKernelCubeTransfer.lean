module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelCubeHyps

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.GroupActions
  CFSG.ComponentClassification.PerfectAutomorphisms
open scoped Pointwise commutatorElement


theorem centerQuotientHom_pow_three_mem_innAutDerived
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (hD : TwoDExcFixedData S a i s) (hH : CubeTransferHyps S hT i hs hmin hD)
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hyStab : MulAut.conj y ∈ subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {g : ModGL τ L} (hgS : g ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hgconj : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      y * x * y⁻¹ = g * x * g⁻¹)
    (hg3C : g ^ 3 ∈ hD.C)
    (hy3Stab : MulAut.conj (y ^ 3) ∈ subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj (y ^ 3), hy3Stab⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  have hy3Z : y ^ 3 ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    pow_mem hyZ 3
  have hy3F : S.D.step (y ^ 3) = y ^ 3 := by rw [map_pow, hyF]
  let g3C : ↥hD.C := ⟨g ^ 3, hg3C⟩
  let α3 : MulAut ↥hD.C := MulAut.conj g3C
  have hα3 : α3 ∈ innAutDerived ↥hD.C := inner_le_innAutDerived _ ⟨g3C, rfl⟩
  have hθα3 : ∀ c : ↥hD.C, (α3 c : ModGL τ L) =
      y ^ 3 * (c : ModGL τ L) * (y ^ 3)⁻¹ := by
    intro c
    have h := conj_pow_subtype_apply_eq (P := rootSpan τ L (componentRoots (rootCharHom a) i))
      (C := hD.C) hD.le hgS hgconj 3 hg3C c
    simpa [α3, g3C] using h
  exact centerQuotientHom_subgroupStabRestrict_mem_innAutDerived_of_norm S hT i hs hmin
    hD.C.subtype hH.θS hH.θfix hH.θY hH.θZ hD.perf hy3Z hy3F hy3Stab α3 hα3 hθα3

theorem centerQuotientHom_mul_frob_mem_innAutDerived
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (hD : TwoDExcFixedData S a i s) (hH : CubeTransferHyps S hT i hs hmin hD)
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hyStab : MulAut.conj y ∈ subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {g : ModGL τ L} (hgS : g ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hgconj : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      y * x * y⁻¹ = g * x * g⁻¹)
    (hhhC : g * frobGL (τ := τ) (frobeniusEquiv L 2) g ∈ hD.C)
    (hyfyStab : MulAut.conj (y * frobGL (τ := τ) (frobeniusEquiv L 2) y) ∈
      subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj (y * frobGL (τ := τ) (frobeniusEquiv L 2) y), hyfyStab⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  have hyφyZ : y * frobGL (τ := τ) (frobeniusEquiv L 2) y ∈
      torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    mul_mem hyZ (frobGL_mem_sup_torus_rootSpan hyZ)
  have hyφyF : S.D.step (y * frobGL (τ := τ) (frobeniusEquiv L 2) y) =
      y * frobGL (τ := τ) (frobeniusEquiv L 2) y :=
    step_mul_frobGL_fixed S hyF
  let hhh : ↥hD.C := ⟨g * frobGL (τ := τ) (frobeniusEquiv L 2) g, hhhC⟩
  let α : MulAut ↥hD.C := MulAut.conj hhh
  have hα : α ∈ innAutDerived ↥hD.C := inner_le_innAutDerived _ ⟨hhh, rfl⟩
  have hθα : ∀ c : ↥hD.C, (α c : ModGL τ L) =
      (y * frobGL (τ := τ) (frobeniusEquiv L 2) y) * (c : ModGL τ L) *
        (y * frobGL (τ := τ) (frobeniusEquiv L 2) y)⁻¹ := by
    intro c
    have h := mul_frob_conj_eq_on_fixed (P := rootSpan τ L (componentRoots (rootCharHom a) i))
      hgS hgconj (fun x hx => frobGL_mem_rootSpan (frobeniusEquiv L 2) hx)
      (le_map_componentRootSpan_frobGL i) (hD.le c.2)
    simpa [α, hhh, MulAut.conj_apply] using h
  exact centerQuotientHom_subgroupStabRestrict_mem_innAutDerived_of_norm S hT i hs hmin
    hD.C.subtype hH.θS hH.θfix hH.θY hH.θZ hD.perf hyφyZ hyφyF hyfyStab α hα hθα

theorem centerQuotientHom_mem_innAutDerived_excHighRank_cube
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hExp : ∀ z : ↥(componentRootSpan L (rootCharHom a) i),
      z ∈ Subgroup.center (componentRootSpan L (rootCharHom a) i) →
      ((z : ModGL τ L) ^ 3 = 1))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (hD : TwoDExcFixedData S a i s)
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hyStab : MulAut.conj y ∈ subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj y, hyStab⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  let R := rationalComponent S.ρ S.Γ (rootCharHom a) i
  haveI hRfin : Finite ↥R := finite_rationalComponent S i
  have hH := cubeTransferHyps_of S hT i hs hmin hD
  obtain ⟨g, hgS, hgconj, hg3C, hhhC⟩ := exists_cubeConjData S hT i hExp hs hmin hD hyZ hyF
  have hy3Stab : MulAut.conj (y ^ 3) ∈ subgroupStabAut R := by
    rw [show MulAut.conj (y ^ 3) = (MulAut.conj y) ^ 3 by rw [map_pow]]
    exact pow_mem hyStab 3
  have hfyStab : MulAut.conj (frobGL (τ := τ) (frobeniusEquiv L 2) y) ∈ subgroupStabAut R :=
    frobGL_stab_of_stab S hT i hyStab
  have hyfyStab : MulAut.conj (y * frobGL (τ := τ) (frobeniusEquiv L 2) y) ∈
      subgroupStabAut R := by
    rw [map_mul]
    exact mul_mem hyStab hfyStab
  have h3 := centerQuotientHom_pow_three_mem_innAutDerived S hT i hs hmin hD hH hyZ hyF
    hyStab hgS hgconj hg3C hy3Stab
  have h2 := centerQuotientHom_mul_frob_mem_innAutDerived S hT i hs hmin hD hH hyZ hyF
    hyStab hgS hgconj hhhC hyfyStab
  exact centerQuotientHom_mem_innAutDerived_of_cube
    (R := R) (f := frobGL (τ := τ) (frobeniusEquiv L 2)) (frobGL_injective _)
    (by rintro _ ⟨x, hx, rfl⟩; exact frobGL_mem_rationalComponent S i hx)
    hyStab hfyStab hy3Stab hyfyStab h3 h2

theorem excHighRankCubeTransfer_holds : ExcHighRankCubeTransfer := by
  intro τ L _ _ _ p S a hT i hExp s _ hs hmin hD y hyZ hyF hyStab
  exact centerQuotientHom_mem_innAutDerived_excHighRank_cube S hT i hExp hs hmin hD hyZ hyF hyStab

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
