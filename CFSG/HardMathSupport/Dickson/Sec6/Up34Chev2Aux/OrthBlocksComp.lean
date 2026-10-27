module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocks
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

section Components

variable {T : Type*} [Group T] [Finite T]

theorem exists_eq_of_isComponentOf_le_iSup {N : Subgroup T} {ι : Type*} (G : ι → Subgroup T)
    (hG : ∀ j, CFSG.Open.IsComponentOf (G j) N) {I : Subgroup T}
    (hI : CFSG.Open.IsComponentOf I N) (hle : I ≤ ⨆ j, G j) : ∃ j, G j = I := by
  have hex : ∃ j, G j ≤ I := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ j, ⁅G j, I⁆ = ⊥ := fun j =>
      (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_comp_le_or_comm (hG j) hI.1
        hI.2.1).resolve_left (hcon j)
    have hMcI : (⨆ j, G j) ≤ Subgroup.centralizer (I : Set T) :=
      iSup_le fun j => Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm j)
    have hIcI : I ≤ Subgroup.centralizer (I : Set T) := hle.trans hMcI
    have hZ : Subgroup.center ↥I = ⊤ := by
      refine eq_top_iff.2 fun z _ => ?_
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hIcI z.2)) g g.2)
    haveI := hI.2.2.2
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (↥I ⧸ Subgroup.center ↥I)
    apply hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    exact QuotientGroup.eq.2 (hZ ▸ Subgroup.mem_top _)
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, ?_⟩
  have hGsn : CFSG.Open.IsSubnormal (G j) I :=
    CFSG.LocalAnalysis.GLTheoremB.isSubnormal_of_le_of_le (hG j).2.1 hj hI.1
  have hGq := (hG j).2.2
  have hGp : ⁅G j, G j⁆ = G j := Subgroup.isPerfect_iff.1 ⟨hGq.1⟩
  have hGne : G j ≠ ⊥ := by
    intro h
    haveI := hGq.2
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (↥(G j) ⧸ Subgroup.center ↥(G j))
    apply hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have ha : (a : T) ∈ (⊥ : Subgroup T) := h ▸ a.2
    have hb : (b : T) ∈ (⊥ : Subgroup T) := h ▸ b.2
    rw [Subgroup.mem_bot] at ha hb
    exact congrArg _ (Subtype.ext (ha.trans hb.symm))
  exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.eq_of_isSubnormal_of_quasisimple
    hI.2.2 hGsn hGp hGne

end Components


section Dichotomy

open Polynomial Module CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem isComponentOf_centralizerImage_cases
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (x : orthDerived Q) (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V)) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep) {I : Subgroup (ProjOrthDerived Q)}
    (hI : CFSG.Open.IsComponentOf I (centralizerImage Q (x : V ≃ₗ[K] V))) :
    (∃ h ∈ Rep, h ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ∧
        I = componentImage Q (x : V ≃ₗ[K] V) h) ∨
      (FixedLayerListed Q (x : V ≃ₗ[K] V) ∧
        ∃ (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)),
          (⨆ i, C i) = fixedComponentImage Q (x : V ≃ₗ[K] V) ∧
          (∀ i, CFSG.IsQuasisimple ↥(C i) ∧ C i ≤ centralizerImage Q (x : V ≃ₗ[K] V) ∧
            ((C i).subgroupOf (centralizerImage Q (x : V ≃ₗ[K] V))).IsSubnormal) ∧
          (∀ i j, i ≠ j → ∀ u ∈ C i, ∀ v ∈ C j, u * v = v * u) ∧ ∃ i, I = C i) := by
  classical
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set N : Subgroup (ProjOrthDerived Q) := centralizerImage Q xe with hN
  obtain ⟨n, C, hC⟩ : ∃ (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)),
      (FixedLayerListed Q xe → (⨆ i, C i) = fixedComponentImage Q xe ∧
        (∀ i, CFSG.IsQuasisimple ↥(C i) ∧ C i ≤ N ∧ ((C i).subgroupOf N).IsSubnormal) ∧
        (∀ i j, i ≠ j → ∀ u ∈ C i, ∀ v ∈ C j, u * v = v * u)) ∧
      (¬ FixedLayerListed Q xe → n = 0) := by
    by_cases hlist : FixedLayerListed Q xe
    · obtain ⟨n, C, -, -, hsup, hC, hcomm, -⟩ := hx.fixedLayer_data hlist
      exact ⟨n, C, fun _ => ⟨hsup, hC, hcomm⟩, fun h => absurd hlist h⟩
    · exact ⟨0, fun i => i.elim0, fun h => absurd h hlist, fun _ => rfl⟩
  let ι₁ := {h : K[X] // h ∈ Rep ∧ h ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q xe h)}
  let G : ι₁ ⊕ Fin n → Subgroup (ProjOrthDerived Q) :=
    Sum.elim (fun h => componentImage Q xe h.1) C
  have hFΩ : ∀ h : K[X], CFSG.IsQuasisimple ↥(specialBlock Q xe h) → specialBlock Q xe h ≤
      orthDerived Q := fun h hq => specialBlock_le_orthDerived_of_perfect hq.1
    ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  have hlistn : ∀ i : Fin n, FixedLayerListed Q xe := by
    intro i
    by_contra hnl
    have := hC.2 hnl
    subst this
    exact i.elim0
  have hGc : ∀ j, CFSG.Open.IsComponentOf (G j) N := by
    rintro (⟨h, hh, hne, hq⟩ | i)
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isComponentOf_of_normal_normal
        (C := N) (N := N) componentImage_le_centralizerImage le_rfl normal_componentImage
        (by rw [Subgroup.subgroupOf_self]; infer_instance)
        (isQuasisimple_map_projective (hFΩ h hq) hq)
    · obtain ⟨hq, hle, hsub⟩ := ((hC.1 (hlistn i)).2.1) i
      exact CFSG.Assembly.isComponentOf_iff_open.1
        ((CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hle).2
          ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hq,
            hsub⟩)
  set EN : Subgroup (ProjOrthDerived Q) := ⨆ j, G j with hEN
  have hENN : EN ≤ N := iSup_le fun j => (hGc j).1
  have hENnormal : ((⨆ h : ι₁, componentImage Q xe h.1).subgroupOf N).Normal :=
    normal_subgroupOf_iSup _ (fun h => componentImage_le_centralizerImage)
      (fun h => normal_componentImage)
  have hFixnormal : ((⨆ i, C i).subgroupOf N).Normal := by
    by_cases hlist : FixedLayerListed Q xe
    · rw [(hC.1 hlist).1]
      exact hx.normal_fixedComponentImage
    · have := hC.2 hlist
      subst this
      simp only [iSup_of_empty, Subgroup.subgroupOf_bot_eq_bot]
      infer_instance
  have hENeq : EN = (⨆ h : ι₁, componentImage Q xe h.1) ⊔ ⨆ i, C i := by
    rw [hEN, iSup_sum]
    rfl
  have hENn : ∀ c ∈ N, ∀ e ∈ EN, c * e * c⁻¹ ∈ EN := by
    have hle1 : (⨆ h : ι₁, componentImage Q xe h.1) ≤ N :=
      iSup_le fun h => componentImage_le_centralizerImage
    have hle2 : (⨆ i, C i) ≤ N := iSup_le fun i => (hGc (Sum.inr i)).1
    have h1 := fun c (hc : c ∈ N) e (he : e ∈ ⨆ h : ι₁, componentImage Q xe h.1) =>
      (Subgroup.normal_subgroupOf_iff hle1).mp hENnormal e c he hc
    have h2 := fun c (hc : c ∈ N) e (he : e ∈ ⨆ i, C i) =>
      (Subgroup.normal_subgroupOf_iff hle2).mp hFixnormal e c he hc
    intro c hc e he
    rw [hENeq] at he ⊢
    have hmap : ((⨆ h : ι₁, componentImage Q xe h.1) ⊔ ⨆ i, C i).map
        (MulAut.conj c).toMonoidHom ≤ (⨆ h : ι₁, componentImage Q xe h.1) ⊔ ⨆ i, C i := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (by rintro _ ⟨e, he, rfl⟩; exact h1 c hc e he)
        (by rintro _ ⟨e, he, rfl⟩; exact h2 c hc e he)
    simpa [MulAut.conj_apply] using hmap ⟨e, he, rfl⟩
  have hJ : ∀ h ∈ Rep, h ≠ X - 1 → CFSG.IsQuasisimple ↥(specialBlock Q xe h) →
      componentImage Q xe h ≤ EN := fun h hh hne hq =>
    le_iSup G (Sum.inl ⟨h, hh, hne, hq⟩)
  have hfix : FixedLayerListed Q xe → fixedComponentImage Q xe ≤ EN := by
    intro hlist
    rw [← (hC.1 hlist).1]
    exact iSup_le fun i => le_iSup G (Sum.inr i)
  obtain ⟨S₀, hS₀N, hS₀sol, hcomm⟩ := exists_solvable_comm_le hQ hp hp2 x hx hRep EN hJ hfix
  haveI := hS₀sol
  have hIperf : ⁅I, I⁆ = I := Subgroup.isPerfect_iff.1 ⟨hI.2.2.1⟩
  have hIEN : I ≤ EN :=
    perfect_le_of_le_sup_solvable hENN hS₀N hENn hcomm hI.1 hIperf
  obtain ⟨j, hj⟩ := exists_eq_of_isComponentOf_le_iSup G hGc hI hIEN
  rcases j with ⟨h, hh, hne, hq⟩ | i
  · exact Or.inl ⟨h, hh, hne, hq, hj.symm⟩
  · exact Or.inr ⟨hlistn i, n, C, (hC.1 (hlistn i)).1, (hC.1 (hlistn i)).2.1, (hC.1 (hlistn i)).2.2,
      i, hj.symm⟩


theorem exists_lift_isComponentOf_centralizer_cases
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) {a : ProjOrthDerived Q}
    (ha : orderOf a = p) :
    ∃ (x : orthDerived Q) (Rep : Finset K[X]),
      (QuotientGroup.mk x : ProjOrthDerived Q) = a ∧ orderOf x = p ∧
      OddOrderIsometry Q p (x : V ≃ₗ[K] V) ∧ IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep ∧
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
        centralizerImage Q (x : V ≃ₗ[K] V) ∧
      ∀ I : Subgroup (ProjOrthDerived Q),
        CFSG.Open.IsComponentOf I (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))) →
        (∃ h ∈ Rep, h ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ∧
            I = componentImage Q (x : V ≃ₗ[K] V) h) ∨
          (FixedLayerListed Q (x : V ≃ₗ[K] V) ∧
            ∃ (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)),
              (⨆ i, C i) = fixedComponentImage Q (x : V ≃ₗ[K] V) ∧
              (∀ i, CFSG.IsQuasisimple ↥(C i) ∧ C i ≤ centralizerImage Q (x : V ≃ₗ[K] V) ∧
                ((C i).subgroupOf (centralizerImage Q (x : V ≃ₗ[K] V))).IsSubnormal) ∧
              (∀ i j, i ≠ j → ∀ u ∈ C i, ∀ v ∈ C j, u * v = v * u) ∧ ∃ i, I = C i) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨x, ⟨hxa, hxp⟩, -, hcent⟩ := hlift p hp hp2 a ha
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  have hNeq : Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
      centralizerImage Q (x : V ≃ₗ[K] V) := by
    rw [hcent]
    exact map_centralizer_eq_centralizerImage x
  refine ⟨x, Rep, hxa, hxp, hx, hRep, hNeq, fun I hI => ?_⟩
  rw [hNeq] at hI
  exact isComponentOf_centralizerImage_cases hQ hp hp2 x hx hRep hI

end Dichotomy

end CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks
