module

import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelSmall
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCtx
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActInnerCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived commutator_le_innAutDerived)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.GroupActions (subgroupStabAut subgroupStabRestrict)
open scoped commutatorElement

section Abstract

theorem mem_of_inverting_of_pow_three {G : Type*} [Group G] (N : Subgroup G)
    (hcomm : ∀ x y : G, ⁅x, y⁆ ∈ N) {a b : G} (h₁ : a * b * a⁻¹ * b ∈ N) (h₃ : b ^ 3 ∈ N) :
    b ∈ N := by
  have hb2 : b * b ∈ N := by
    have e : b * b = ⁅a, b⁆⁻¹ * (a * b * a⁻¹ * b) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem (N.inv_mem (hcomm a b)) h₁
  have h := N.mul_mem h₃ (N.inv_mem hb2)
  rwa [pow_three, mul_inv_cancel_right] at h

theorem mem_innAutDerived_of_inverting_of_pow_three {Y : Type*} [Group Y] {a b : MulAut Y}
    (h₁ : a * b * a⁻¹ * b ∈ innAutDerived Y) (h₃ : b ^ 3 ∈ innAutDerived Y) :
    b ∈ innAutDerived Y := by
  refine mem_of_inverting_of_pow_three (innAutDerived Y) (fun x y => ?_) h₁ h₃
  refine commutator_le_innAutDerived Y ?_
  rw [commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem actionOnCenterQuotient_mem_innAutDerived {G : Type*} [Group G] {R : Subgroup G}
    {g y : G} (hg : MulAut.conj g ∈ subgroupStabAut R) (hy : MulAut.conj y ∈ subgroupStabAut R)
    (h₁ : ∀ hm : MulAut.conj (g * y * g⁻¹ * y) ∈ subgroupStabAut R,
      centerQuotientHom ↥R (subgroupStabRestrict R ⟨MulAut.conj (g * y * g⁻¹ * y), hm⟩) ∈
        innAutDerived (↥R ⧸ Subgroup.center ↥R))
    (h₃ : ∀ hm : MulAut.conj (y ^ 3) ∈ subgroupStabAut R,
      centerQuotientHom ↥R (subgroupStabRestrict R ⟨MulAut.conj (y ^ 3), hm⟩) ∈
        innAutDerived (↥R ⧸ Subgroup.center ↥R)) :
    centerQuotientHom ↥R (subgroupStabRestrict R ⟨MulAut.conj y, hy⟩) ∈
      innAutDerived (↥R ⧸ Subgroup.center ↥R) := by
  have hm₁ : MulAut.conj (g * y * g⁻¹ * y) ∈ subgroupStabAut R := by
    rw [map_mul, map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem (mul_mem hg hy) (inv_mem hg)) hy
  have hm₃ : MulAut.conj (y ^ 3) ∈ subgroupStabAut R := by
    rw [map_pow]
    exact pow_mem hy 3
  have e₁ : (⟨MulAut.conj (g * y * g⁻¹ * y), hm₁⟩ : ↥(subgroupStabAut R)) =
      ⟨MulAut.conj g, hg⟩ * ⟨MulAut.conj y, hy⟩ * ⟨MulAut.conj g, hg⟩⁻¹ * ⟨MulAut.conj y, hy⟩ :=
    Subtype.ext (by simp)
  have e₃ : (⟨MulAut.conj (y ^ 3), hm₃⟩ : ↥(subgroupStabAut R)) =
      (⟨MulAut.conj y, hy⟩ : ↥(subgroupStabAut R)) ^ 3 :=
    Subtype.ext (by simp)
  have h₁' := h₁ hm₁
  have h₃' := h₃ hm₃
  rw [e₁] at h₁'
  rw [e₃] at h₃'
  exact mem_innAutDerived_of_inverting_of_pow_three
    (a := centerQuotientHom ↥R (subgroupStabRestrict R ⟨MulAut.conj g, hg⟩))
    (b := centerQuotientHom ↥R (subgroupStabRestrict R ⟨MulAut.conj y, hy⟩))
    (by simpa only [map_mul, map_inv] using h₁') (by simpa only [map_pow] using h₃')

theorem exists_ne_neg_of_two_lt_ncard {X : Type*} [Neg X] {s : Set X} (h : 2 < s.ncard) :
    ∃ α ∈ s, ∃ δ ∈ s, δ ≠ α ∧ δ ≠ -α := by
  by_contra hcon
  push Not at hcon
  obtain ⟨α, hα⟩ : s.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hsub : s ⊆ {α, -α} := fun δ hδ => by
    by_cases hδα : δ = α
    · exact Or.inl hδα
    · exact Or.inr (hcon α hα δ hδ hδα)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({α, -α} : Set X).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  omega

theorem image_eq_of_mapsTo_perm {X : Type*} (ρ : Equiv.Perm X) {s : Set X} (hfin : s.Finite)
    (hρ : ∀ γ ∈ s, ρ γ ∈ s) : (ρ : X → X) '' s = s :=
  ((hfin.injOn_iff_bijOn_of_mapsTo hρ).1 ρ.injective.injOn).image_eq

end Abstract

section Assembly

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem e6d4t2_action_forall (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hbig : 2 < (componentRoots (rootCharHom a) i).ncard)
    (hin : twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) :
    ∀ ⦃y : ModGL Tag.E6 L⦄,
      y ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) →
      S.D.step y = y →
      ∀ hyStab : MulAut.conj y ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i),
      centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
          (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
            ⟨MulAut.conj y, hyStab⟩) ∈
        innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  have hfin : (componentRoots (rootCharHom a) i).Finite := Set.finite_of_ncard_pos (by omega)
  have hs : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[1] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
    rw [Function.iterate_one]
    exact image_eq_of_mapsTo_perm S.ρ hfin hρ
  have hmin : ∀ k, 0 < k → k < 1 →
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i :=
    fun k hk hk1 => absurd hk1 (by omega)
  obtain ⟨σ, z, hσ, hzZ, hnorm, hz⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_untwistT_Z S hT i (s := 1) one_pos
      (by rwa [Function.iterate_one])
  have hperf : Group.IsPerfect ↥(CQ σ i) :=
    T171Sh.isPerfect_CQ_of_isPerfect_componentRootSpan i σ
      (isPerfect_componentRootSpan_simplyLaced (K := fixSubfield σ) (Or.inr (Or.inl rfl)) i
        (exists_ne_neg_of_two_lt_ncard hbig))
  intro y hyZ hyF hyStab
  exact T171Sh.centerQuotientHom_mem_innAutDerived_inner_of_untwist S hT i hs hmin σ hσ hzZ hnorm
    hz hperf hyZ hyF hyStab

theorem e6d4t2_innAutDerived_of_inverting (S : LangSetup Tag.E6 L p₀)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (_hap : ∀ j, a j ^ 3 = 1) (i : KernelComponent (rootCharHom a))
    (_hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hbig : 2 < (componentRoots (rootCharHom a) i).ncard)
    (hin : twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)))
    {y g : ModGL Tag.E6 L} (hyF : S.D.step y = y) (hgF : S.D.step g = g)
    (hyStab : MulAut.conj y ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hgStab : MulAut.conj g ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hgy : g * y * g⁻¹ * y ∈ torusGroup Tag.E6 L ⊔
      rootSpan Tag.E6 L (kernelRoots (rootCharHom a)))
    (hy3 : y ^ 3 ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a))) :
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj y, hyStab⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  have key := e6d4t2_action_forall S hT i hρ hbig hin
  have hF₁ : S.D.step (g * y * g⁻¹ * y) = g * y * g⁻¹ * y := by
    simp only [map_mul, map_inv, hgF, hyF]
  have hF₃ : S.D.step (y ^ 3) = y ^ 3 := by
    rw [map_pow, hyF]
  exact actionOnCenterQuotient_mem_innAutDerived hgStab hyStab (fun hm => key hgy hF₁ hm)
    (fun hm => key hy3 hF₃ hm)

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.T158

end
