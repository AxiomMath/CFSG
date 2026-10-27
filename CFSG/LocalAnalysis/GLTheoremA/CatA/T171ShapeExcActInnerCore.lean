module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActCQ
public import CFSG.LocalAnalysis.StandardType.GGExcSmallCompOrderCard
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.AlgebraicGroups CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.ComponentClassification.PerfectCentralQuotient CFSG.GroupActions
open scoped Pointwise commutatorElement


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem centerQuotientHom_mem_innAutDerived_inner_of_untwist
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {Q : ℕ} (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ Q)
    {z : ModGL τ L} (hzZ : z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hperf : Group.IsPerfect ↥(CQ σ i))
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
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  set y₁ : ModGL τ L := z⁻¹ * y * z with hy₁def
  have hy₁Z : y₁ ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    mul_mem (mul_mem (inv_mem hzZ) hyZ) hzZ
  obtain ⟨g, hgU, hgconj⟩ := exists_mem_rootSpan_conj_eq_of_mem_Z (a := a) i hy₁Z
  have hgS : g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    have h := hgU
    rwa [CFSG.StandardType.SmallCompOrder.unionRootSpan_singleton_eq (K := L)
      (χ := rootCharHom a) i] at h
  have hcancel : ∀ u : ModGL τ L, frobGL σ (frobGL σ.symm u) = u := by
    intro u
    have h := units_map_entrywiseHom_mul_ringEquiv σ σ.symm u
    have hinv : σ * σ.symm = 1 := mul_inv_cancel σ
    rw [hinv, units_map_entrywiseHom_one_ringEquiv] at h
    exact h.symm
  have hcomm : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      g * frobGL σ x * g⁻¹ = frobGL σ (g * x * g⁻¹) := by
    intro x hx
    set H : ModGL τ L := iterHom S.D.step s (z * x * z⁻¹) with hHdef
    have hzx : z * x * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
      (hnorm i x).1 hx
    have hH : H ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
      rw [hHdef, hz x hx]
      exact (hnorm i _).1 (frobGL_mem_rootSpan σ hx)
    have hHconj : z⁻¹ * H * z ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
      (hnorm i (z⁻¹ * H * z)).2 (by
        rw [show z * (z⁻¹ * H * z) * z⁻¹ = H by group]
        exact hH)
    have hfx : frobGL σ x = z⁻¹ * H * z := by
      rw [hHdef, hz x hx]
      group
    have hx' : g * x * g⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
      mul_mem (mul_mem hgS hx) (inv_mem hgS)
    have hfu : frobGL σ (g * x * g⁻¹) =
        z⁻¹ * iterHom S.D.step s (z * (g * x * g⁻¹) * z⁻¹) * z := by
      rw [hz _ hx']
      group
    have hzconj : z * (g * x * g⁻¹) * z⁻¹ = y * (z * x * z⁻¹) * y⁻¹ := by
      rw [← hgconj x hx]
      rw [hy₁def]
      group
    have hstep : iterHom S.D.step s (y * (z * x * z⁻¹) * y⁻¹) =
        y * iterHom S.D.step s (z * x * z⁻¹) * y⁻¹ := by
      rw [map_mul, map_mul, map_inv, iterHom_eq_self_of_fixed hyF s]
    calc g * frobGL σ x * g⁻¹
        = g * (z⁻¹ * H * z) * g⁻¹ := by rw [hfx]
      _ = y₁ * (z⁻¹ * H * z) * y₁⁻¹ := (hgconj _ hHconj).symm
      _ = z⁻¹ * y * H * y⁻¹ * z := by rw [hy₁def]; group
      _ = z⁻¹ * iterHom S.D.step s (y * (z * x * z⁻¹) * y⁻¹) * z := by
        rw [hstep, hHdef]
        group
      _ = z⁻¹ * iterHom S.D.step s (z * (g * x * g⁻¹) * z⁻¹) * z := by rw [← hzconj]
      _ = frobGL σ (g * x * g⁻¹) := by rw [hfu]
  have hgc : ∀ x ∈ unionRootSpan L (rootCharHom a)
      ({i} : Set (KernelComponent (rootCharHom a))),
      x * (frobGL σ g * g⁻¹) = (frobGL σ g * g⁻¹) * x := by
    intro x hx
    have hxS : x ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
      have h := hx
      rwa [CFSG.StandardType.SmallCompOrder.unionRootSpan_singleton_eq (K := L)
        (χ := rootCharHom a) i] at h
    have hdcent : ∀ u ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
        (g * (frobGL σ g)⁻¹) * frobGL σ u * (g * (frobGL σ g)⁻¹)⁻¹ = frobGL σ u := by
      intro u hu
      have hy : g⁻¹ * u * g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
        mul_mem (mul_mem (inv_mem hgS) hu) hgS
      have h1 := hcomm (g⁻¹ * u * g) hy
      have e1 : g * frobGL σ (g⁻¹ * u * g) * g⁻¹ =
          (g * (frobGL σ g)⁻¹) * frobGL σ u * (g * (frobGL σ g)⁻¹)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        group
      have e2 : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
      rw [e1, e2] at h1
      exact h1
    have hdcomm : ∀ u ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
        (g * (frobGL σ g)⁻¹) * u = u * (g * (frobGL σ g)⁻¹) := by
      intro u hu
      have hu' := frobGL_mem_rootSpan σ.symm hu
      have h := hdcent (frobGL σ.symm u) hu'
      rw [hcancel u] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    have hc : (frobGL σ g * g⁻¹) * x = x * (frobGL σ g * g⁻¹) := by
      have h := hdcomm x hxS
      have hinv : frobGL σ g * g⁻¹ = (g * (frobGL σ g)⁻¹)⁻¹ := by group
      rw [hinv]
      calc (g * (frobGL σ g)⁻¹)⁻¹ * x
          = (g * (frobGL σ g)⁻¹)⁻¹ * (x * (g * (frobGL σ g)⁻¹)) *
              (g * (frobGL σ g)⁻¹)⁻¹ := by group
        _ = (g * (frobGL σ g)⁻¹)⁻¹ * ((g * (frobGL σ g)⁻¹) * x) *
              (g * (frobGL σ g)⁻¹)⁻¹ := by rw [h]
        _ = x * (g * (frobGL σ g)⁻¹)⁻¹ := by group
    exact hc.symm
  obtain ⟨hgC, hgrest⟩ := exists_conj_mem_innAutDerived_CQ (σ := σ) (Q := Q) hσ i hgU hgc
  let θ : ↥(CQ σ i) →* ModGL τ L :=
    (MulAut.conj z).toMonoidHom.comp (CQ σ i).subtype
  have hθ : ∀ c : ↥(CQ σ i), θ c = z * (c : ModGL τ L) * z⁻¹ := fun _ => rfl
  have hθS : ∀ c : ↥(CQ σ i),
      θ c ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    intro c
    rw [hθ]
    exact (hnorm i _).1 (CQ_le_rootSpan σ i c.2)
  have hθfix : ∀ c : ↥(CQ σ i), iterHom S.D.step s (θ c) = θ c := by
    intro c
    rw [hθ, hz _ (CQ_le_rootSpan σ i c.2), frobGL_eq_self_of_mem_CQ σ i c.2]
  have hzA : ∀ a ∈ P.A, z * a * z⁻¹ ∈ P.A := by
    have h : P.A ≤ P.A.comap (MulAut.conj z).toMonoidHom := by
      refine iSup_le fun k => ?_
      obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
      intro g hg
      have hg' : g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) := by
        rw [hj]
        exact hg
      have h2 := (hnorm j g).1 hg'
      rw [hj] at h2
      exact P.S_le_A k h2
    exact fun a ha => h ha
  have hZconj : ∀ X : ModGL τ L, z * X * z⁻¹ ∈ P.Z → X ∈ P.Z := by
    intro X hX
    rw [CycFamily.mem_Z] at hX ⊢
    intro a ha
    have h := hX (z * a * z⁻¹) (hzA a ha)
    have e : z * a * z⁻¹ * (z * X * z⁻¹) = z * (a * X) * z⁻¹ := by group
    have e' : z * X * z⁻¹ * (z * a * z⁻¹) = z * (X * a) * z⁻¹ := by group
    rw [e, e'] at h
    simpa using h
  have hYc : ∀ u ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s u * u⁻¹ ∈ P.Z →
      ∃ g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
        u = z * g' * z⁻¹ ∧ frobGL σ g' * g'⁻¹ ∈ P.Z := by
    intro u hu huZ
    have e : z * (z⁻¹ * u * z) * z⁻¹ = u := by group
    have hg : z⁻¹ * u * z ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
      (hnorm i (z⁻¹ * u * z)).2 (by rw [e]; exact hu)
    refine ⟨z⁻¹ * u * z, hg, by group, hZconj _ ?_⟩
    have h1 := hz _ hg
    rw [e] at h1
    have e2 : z * (frobGL σ (z⁻¹ * u * z) * (z⁻¹ * u * z)⁻¹) * z⁻¹ =
        (z * frobGL σ (z⁻¹ * u * z) * z⁻¹) * u⁻¹ := by group
    rw [e2, ← h1]
    exact huZ
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_unit_sq_ne_one_alg
  have hθY : ∀ g' g'' : ModGL τ L,
      g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      g'' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      iterHom S.D.step s g' * g'⁻¹ ∈ P.Z →
      iterHom S.D.step s g'' * g''⁻¹ ∈ P.Z → ⁅g', g''⁆ ∈ θ.range := by
    intro u u' hu hu' huZ huZ'
    obtain ⟨g₀, hg₀, rfl, hg₀Z⟩ := hYc u hu huZ
    obtain ⟨g₁, hg₁, rfl, hg₁Z⟩ := hYc u' hu' huZ'
    have hmem : ⁅g₀, g₁⁆ ∈ CQ σ i :=
      orbit_commutator_mem_CQT S hT i hs hmin σ hsL hg₀ hg₁ hg₀Z hg₁Z
    refine ⟨⟨⁅g₀, g₁⁆, hmem⟩, ?_⟩
    show θ ⟨⁅g₀, g₁⁆, hmem⟩ = ⁅z * g₀ * z⁻¹, z * g₁ * z⁻¹⁆
    rw [hθ]
    simp only [commutatorElement_def]
    group
  have hθZ : ∀ c : ↥(CQ σ i), θ c ∈ P.Z → c ∈ Subgroup.center ↥(CQ σ i) := by
    intro c hc
    have hc' : z * (c : ModGL τ L) * z⁻¹ ∈ P.Z := by
      simpa only [hθ] using hc
    have hcz : (c : ModGL τ L) ∈ P.Z := hZconj _ hc'
    rw [Subgroup.mem_center_iff]
    intro c'
    have h := P.mem_Z.1 hcz (c' : ModGL τ L) (P.S_le_A 0 (by
      rw [hP0]
      exact CQ_le_rootSpan σ i c'.2))
    exact Subtype.ext h
  have hθα : ∀ c : ↥(CQ σ i),
      θ ((subgroupStabRestrict (CQ σ i) ⟨MulAut.conj g, hgC⟩) c) =
        y * θ c * y⁻¹ := by
    intro c
    have hc : (c : ModGL τ L) ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
      CQ_le_rootSpan σ i c.2
    have hαc : (((subgroupStabRestrict (CQ σ i) ⟨MulAut.conj g, hgC⟩) c :
        ↥(CQ σ i)) : ModGL τ L) = g * (c : ModGL τ L) * g⁻¹ := by
      rw [subgroupStabRestrict_apply, MulAut.conj_apply]
    rw [hθ, hαc, hθ c, ← hgconj _ hc]
    rw [hy₁def]
    group
  exact centerQuotientHom_subgroupStabRestrict_mem_innAutDerived_of_norm S hT i hs hmin θ
    hθS hθfix hθY hθZ hperf hyZ hyF hyStab
    (subgroupStabRestrict (CQ σ i) ⟨MulAut.conj g, hgC⟩) hgrest hθα

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
