module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020OrthA1
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFourQuasisimpleNormal
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerivedImage
public import CFSG.LocalAnalysis.GLTheoremA.S9.Basic
public import CFSG.RankThree.PartOne.S11d.OrthCaseH

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open Module CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p q f : ℕ} {x : V ≃ₗ[K] V}

theorem card_centerQuotient_fixedFactor_of_finrank_four (hq : q.Prime) (hq2 : q ≠ 2)
    (hring : ringChar K = q) (hcardK : Nat.card K = q ^ f)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hx : OddOrderIsometry Q p x) (hdim0 : Module.finrank K (fixedSpace x) = 4)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) :
    ∃ f' : ℕ, 1 ≤ f' ∧
      Nat.card (↥F ⧸ Subgroup.center ↥F) * 2 = (q ^ f') * ((q ^ f') ^ 2 - 1) := by
  haveI : Finite V := Module.finite_of_finite K
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hodd : Odd (Nat.card K) := by
    rw [hcardK]
    exact hqodd.pow
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with hf | hf
    · exfalso
      rw [hf, pow_zero] at hcardK
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact hf
  set Q₀ := Q.comp (fixedSpace x).subtype with hQ₀def
  have hQ₀ : (QuadraticMap.polarBilin Q₀).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  set M₀ : Subgroup ↥(orthDerived Q₀) := fixedDerivedImage hx F with hM₀
  have hM₀q : CFSG.IsQuasisimple ↥M₀ := isQuasisimple_fixedDerivedImage hx hFq hFle
  have hM₀n : M₀.Normal := normal_fixedDerivedImage hx hFn
  set M : Subgroup ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q₀)) :=
    M₀.map (CFSG.RankThree.PartOne.orthDerivedEquivCommutator Q₀).symm.toMonoidHom with hM
  have hMq : CFSG.IsQuasisimple ↥M :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective M₀ _
        (CFSG.RankThree.PartOne.orthDerivedEquivCommutator Q₀).symm.injective) hM₀q
  have hMn : M.Normal :=
    hM₀n.map _ (CFSG.RankThree.PartOne.orthDerivedEquivCommutator Q₀).symm.surjective
  obtain ⟨eFM₀⟩ := nonempty_fixedDerivedImage_equiv (Q := Q) hx hFle
  have hFM : ↥F ≃* ↥M :=
    eFM₀.trans (Subgroup.equivMapOfInjective M₀ _
      (CFSG.RankThree.PartOne.orthDerivedEquivCommutator Q₀).symm.injective)
  have hqFM : Nat.card (↥F ⧸ Subgroup.center ↥F) = Nat.card (↥M ⧸ Subgroup.center ↥M) :=
    Nat.card_congr (QuotientGroup.congr _ _ hFM (Subgroup.map_center_eq hFM)).toEquiv
  by_cases hsplit : ∃ S : Submodule K (fixedSpace x), Module.finrank K S = 2 ∧
      ∀ s ∈ S, Q₀ s = 0
  · rcases eq_or_ne (Nat.card K) 3 with h3 | h3
    · exact (false_of_splitFour_card_three hQ₀ hdim0 hsplit h3 hMq).elim
    · refine ⟨f, hf1, ?_⟩
      have hcard := card_centerQuotient_of_splitFour hodd h3 hQ₀ hdim0 hsplit hMq hMn
      rw [hqFM, hcard, hcardK]
  · refine ⟨2 * f, by omega, ?_⟩
    have hcard := card_centerQuotient_of_nonsplitFour hodd hQ₀ hdim0 hsplit hMq hMn
    have h2f : q ^ (2 * f) = Nat.card K ^ 2 := by
      rw [hcardK, ← pow_mul, mul_comm f 2]
    rw [hqFM, hcard, h2f]

theorem card_pSimple_fixedFactor_of_finrank_four (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2)
    (hring : ringChar K = q) (hcardK : Nat.card K = q ^ f)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hx : OddOrderIsometry Q p x) (hdim0 : Module.finrank K (fixedSpace x) = 4)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal)
    {X : Subgroup (ProjOrthDerived Q)}
    (hJ : GLAPComponent p X ((F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))) :
    ∃ f' : ℕ, 1 ≤ f' ∧ Nat.card (PSimple p ((F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))) * 2 =
      (q ^ f') * ((q ^ f') ^ 2 - 1) := by
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨f', hf'1, hf'⟩ :=
    card_centerQuotient_fixedFactor_of_finrank_four hq hq2 hring hcardK hQ hx hdim0 hFq hFle hFn
  have hFΩ : F ≤ orthDerived Q := hFle.trans hx.supportedFixedDerived_le_orthDerived
  let f₀ : ↥F →* ProjOrthDerived Q :=
    (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))).comp
      (Subgroup.inclusion hFΩ)
  have hf₀ : ∀ x : ↥F, f₀ x ∈ (F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := by
    intro x
    exact ⟨⟨x, hFΩ x.2⟩, x.2, rfl⟩
  let f : ↥F →* ↥((F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) :=
    f₀.codRestrict _ hf₀
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨g.1, Subgroup.mem_subgroupOf.1 hg⟩, Subtype.ext hgy⟩
  have hfker : f.ker ≤ Subgroup.center ↥F := by
    intro x hx0
    rw [MonoidHom.mem_ker] at hx0
    have hx1 : f₀ x = 1 := by
      simpa [f] using congrArg Subtype.val hx0
    have hxN : (⟨(x : ↥F), hFΩ x.2⟩ : ↥(orthDerived Q)) ∈
        (scalars K V).subgroupOf (orthDerived Q) := by
      rw [← QuotientGroup.eq_one_iff]
      exact hx1
    have hx2 : ((x : ↥F) : V ≃ₗ[K] V) ∈ scalars K V := Subgroup.mem_subgroupOf.1 hxN
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (CFSG.ClassicalGroups.Orthogonal.commute_of_mem_scalars hx2
      (y : V ≃ₗ[K] V)).symm
  have hJq : CFSG.IsQuasisimple ↥((F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hFq f hfsurj hfker
  obtain ⟨eP⟩ := CFSG.LocalAnalysis.GLTheoremA.S9.nonempty_pSimple_equiv hp hJ
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hJq)
  obtain ⟨eC⟩ := CFSG.RankThree.PartOne.nonempty_centerQuotientEquiv_of_surjective hFq.1
    f hfsurj hfker
  have hcard : Nat.card (PSimple p ((F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))) =
      Nat.card (↥F ⧸ Subgroup.center ↥F) :=
    Nat.card_congr (eP.trans eC.symm).toEquiv
  exact ⟨f', hf'1, by rw [hcard]; exact hf'⟩

section Cert


theorem not_jType_fixedFactor_of_finrank_four' (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hq2 : q ≠ 2) (hring : ringChar K = q) (hcardK : Nat.card K = q ^ f)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hx : OddOrderIsometry Q p x) (hdim0 : Module.finrank K (fixedSpace x) = 4)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal)
    {X : Subgroup (ProjOrthDerived Q)}
    (hJ : GLAPComponent p X ((F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))) :
    ¬ JType p q ((F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) := by
  obtain ⟨f', hf'1, hf'⟩ :=
    card_pSimple_fixedFactor_of_finrank_four hp hq hq2 hring hcardK hQ hx hdim0 hFq hFle hFn hJ
  exact not_jType_fixedFactor_of_finrank_four hp hp2 hq hq2 hring hcardK hQ hT hx hdim0 hFq hFle
    hFn ⟨f', hf'1, hf'⟩

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
