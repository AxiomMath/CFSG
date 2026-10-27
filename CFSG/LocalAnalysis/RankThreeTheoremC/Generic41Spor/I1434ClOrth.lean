module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitFourClause
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

section Components

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_components_named {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hpℓ : p ≠ ringChar K)
    (a : ProjOrthDerived Q) (ha : a ^ p = 1) (ha1 : a ≠ 1) :
    ∃ (x : ↥(orthDerived Q)) (Rep : Finset K[X]) (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V))
      (Cset : Set (Subgroup (ProjOrthDerived Q))),
      QuotientGroup.mk x = a ∧ IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep ∧
      (∀ J : Subgroup (ProjOrthDerived Q),
        CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))) →
        (∃ h ∈ Rep, h ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ∧
            J = componentImage Q (x : V ≃ₗ[K] V) h) ∨ J ∈ Cset) ∧
      ((¬ FixedLayerListed Q (x : V ≃ₗ[K] V) ∧ Cset = ∅) ∨
        (FixedLayerListed Q (x : V ≃ₗ[K] V) ∧
          ¬ (finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
            ∃ S : Submodule K (fixedSpace (x : V ≃ₗ[K] V)), finrank K S = 2 ∧
              ∀ s ∈ S, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) s = 0) ∧
          CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
              (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype))) ∧
          Cset = {fixedComponentImage Q (x : V ≃ₗ[K] V)}) ∨
        (FixedLayerListed Q (x : V ≃ₗ[K] V) ∧
          ∃ e : ↥(TauCeti.QuadraticMap.orthogonalGroup
              (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype)) ≃* DeterminantIsometries K,
            finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
            (∃ S : Submodule K (fixedSpace (x : V ≃ₗ[K] V)), finrank K S = 2 ∧
              ∀ s ∈ S, (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) s = 0) ∧
            3 < Nat.card K ∧
            (∀ i : Fin 2, supportedFactor hx (splitFourFactors e i) ≤ orthDerived Q) ∧
            Cset = {fixedFactorImage hx (splitFourFactors e 0),
              fixedFactorImage hx (splitFourFactors e 1)})) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  obtain ⟨x, hxa, hx, hcent⟩ : ∃ x : ↥(orthDerived Q), ρ x = a ∧
      OddOrderIsometry Q p (x : V ≃ₗ[K] V) ∧
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
        (Subgroup.centralizer ({x} : Set ↥(orthDerived Q))).map ρ := by
    obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
    obtain ⟨x, ⟨hxa, hxp⟩, -, hcent⟩ := hlift p hp hp2 a (orderOf_eq_prime ha ha1)
    exact ⟨x, hxa, oddOrderIsometry_of_orthDerived hp hpℓ hQ x hxp, hcent⟩
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := centralizerImage Q xe with hN
  have hNeq : Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) = N := by
    rw [hcent]
    exact CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage x
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hcompOf : ∀ L : Subgroup (ProjOrthDerived Q), CFSG.IsQuasisimple ↥L → L ≤ N →
      (L.subgroupOf N).IsSubnormal → CFSG.Open.IsComponentOf L N := by
    intro L hq hle hsub
    have hc : CFSG.IsComponent (L.subgroupOf N) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hq, hsub⟩
    have := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isComponentOf_map_subtype hc
    rwa [Subgroup.map_subgroupOf_eq_of_le hle] at this
  obtain ⟨n, C, hCcomp, hCsup, Cset, Cset_eq, htype⟩ :
      ∃ (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)),
      (∀ i, CFSG.Open.IsComponentOf (C i) N) ∧ (⨆ i, C i) = fixedLayerImage Q xe ∧
      ∃ Cset : Set (Subgroup (ProjOrthDerived Q)), Set.range C = Cset ∧
      ((¬ FixedLayerListed Q xe ∧ Cset = ∅) ∨
        (FixedLayerListed Q xe ∧
          ¬ (finrank K (fixedSpace xe) = 4 ∧
            ∃ S : Submodule K (fixedSpace xe), finrank K S = 2 ∧
              ∀ s ∈ S, (Q.comp (fixedSpace xe).subtype) s = 0) ∧
          CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
              (Q.comp (fixedSpace xe).subtype))) ∧
          Cset = {fixedComponentImage Q xe}) ∨
        (FixedLayerListed Q xe ∧
          ∃ e : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace xe).subtype)) ≃*
              DeterminantIsometries K,
            finrank K (fixedSpace xe) = 4 ∧
            (∃ S : Submodule K (fixedSpace xe), finrank K S = 2 ∧
              ∀ s ∈ S, (Q.comp (fixedSpace xe).subtype) s = 0) ∧
            3 < Nat.card K ∧
            (∀ i : Fin 2, supportedFactor hx (splitFourFactors e i) ≤ orthDerived Q) ∧
            Cset = {fixedFactorImage hx (splitFourFactors e 0),
              fixedFactorImage hx (splitFourFactors e 1)})) := by
    by_cases hlist : FixedLayerListed Q xe
    · by_cases hsplit : finrank K (fixedSpace xe) = 4 ∧
          ∃ S : Submodule K (fixedSpace xe), finrank K S = 2 ∧
            ∀ s ∈ S, (Q.comp (fixedSpace xe).subtype) s = 0
      · have hq : 3 < Nat.card K := by
          by_contra hle
          have h2 : 1 < Nat.card K := Finite.one_lt_card
          exact hlist.2 (Or.inr ⟨hsplit, by omega⟩)
        obtain ⟨ψ, e, -, -, hsup, hC, -⟩ := hx.fixedLayer_splitFour hsplit.1 hsplit.2 hq
        refine ⟨2, fun i => fixedFactorImage hx (splitFourFactors e i), fun i => ?_, ?_, _, rfl,
          Or.inr (Or.inr ⟨hlist, e, hsplit.1, hsplit.2, hq, fun i => (hC i).1, ?_⟩)⟩
        · exact hcompOf _ (hC i).2.2.1 (hC i).2.2.2.1 (hC i).2.2.2.2
        · rw [fixedLayerImage_of_listed hlist, ← hsup]
        · ext J
          simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]
          exact or_congr eq_comm eq_comm
      · have hqs := orthogonal_regular_space_derived_quasisimple (Q.comp (fixedSpace xe).subtype)
          hQW hlist.1 hlist.2 hsplit
        obtain ⟨-, hq', -, hle, hsub⟩ := hx.fixedLayer_unsplit hqs
        refine ⟨1, fun _ => fixedComponentImage Q xe, fun i => hcompOf _ hq' hle hsub, ?_, _, rfl,
          Or.inr (Or.inl ⟨hlist, hsplit, hqs, ?_⟩)⟩
        · rw [iSup_const, fixedLayerImage_of_listed hlist]
        · ext J
          simp
    · refine ⟨0, fun i => i.elim0, fun i => i.elim0, by simp [fixedLayerImage, hlist], _, rfl,
        Or.inl ⟨hlist, ?_⟩⟩
      ext J
      simp
  let ι₁ := {r : ↥Rep // r.1 ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q xe r.1)}
  have hspecΩ : ∀ r : ι₁, specialBlock Q xe r.1.1 ≤ orthDerived Q := fun r =>
    specialBlock_le_orthDerived_of_perfect r.2.2.1
      ((specialBlock_le_isometryCentralizer r.1.1).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  let S : ι₁ → Subgroup (ProjOrthDerived Q) := fun r => componentImage Q xe r.1.1
  have hScomp : ∀ r, CFSG.Open.IsComponentOf (S r) N := fun r =>
    isComponentOf_of_normal_normal componentImage_le_centralizerImage le_rfl normal_componentImage
      (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
      (isQuasisimple_map_projective (hspecΩ r) r.2.2)
  set EN : Subgroup (ProjOrthDerived Q) := (⨆ r, S r) ⊔ fixedLayerImage Q xe with hEN
  have hSN : ∀ r, S r ≤ N := fun r => componentImage_le_centralizerImage
  have hENN : EN ≤ N :=
    sup_le (iSup_le hSN) fixedLayerImage_le_centralizerImage
  have hENnormal : (EN.subgroupOf N).Normal :=
    normal_subgroupOf_sup (iSup_le hSN) fixedLayerImage_le_centralizerImage
      (normal_subgroupOf_iSup S hSN fun r => normal_componentImage) hx.normal_fixedLayerImage
  have hENn : ∀ c ∈ N, ∀ e ∈ EN, c * e * c⁻¹ ∈ EN := fun c hc e he =>
    (Subgroup.normal_subgroupOf_iff hENN).mp hENnormal e c he hc
  have hperf : ∀ P : Subgroup (ProjOrthDerived Q), P ≤ N → commutator ↥P = ⊤ → P ≤ EN := by
    intro P hPN hP
    obtain ⟨S₀, hS₀N, hS₀sol, hcomm⟩ := exists_solvable_comm_le hQ hp hp2 x hx hRep EN
      (fun h hh hne hq => le_sup_of_le_left
        (le_iSup S (⟨⟨h, hh⟩, hne, hq⟩ : ι₁)))
      (fun hlist => by
        rw [← fixedLayerImage_of_listed hlist]
        exact le_sup_right)
    haveI := hS₀sol
    exact perfect_le_of_le_sup_solvable hENN hS₀N hENn hcomm hPN (Subgroup.isPerfect_iff.1 ⟨hP⟩)
  let Fm : ι₁ ⊕ Fin n → Subgroup (ProjOrthDerived Q) := Sum.elim S C
  have hFm : ∀ i, CFSG.Open.IsComponentOf (Fm i) N := by
    rintro (r | i)
    · exact hScomp r
    · exact hCcomp i
  have hiSup : (⨆ i, Fm i) = EN := by
    rw [iSup_sum]
    simp only [Fm, Sum.elim_inl, Sum.elim_inr]
    rw [hCsup]
  refine ⟨x, Rep, hx, Cset, hxa, hRep, fun J hJ => ?_, htype⟩
  rw [hNeq] at hJ
  obtain ⟨i, rfl⟩ := component_mem_named_factors Fm hFm
    (fun P hPN hP => hiSup ▸ hperf P hPN hP) hJ
  rcases i with ⟨⟨h, hh⟩, hne, hq⟩ | i
  · exact Or.inl ⟨h, hh, hne, hq, rfl⟩
  · exact Or.inr (by rw [← Cset_eq]; exact ⟨i, rfl⟩)

end Components

section Transfer

theorem commutator_eq_top_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : commutator G = ⊤) : commutator H = ⊤ := by
  have h1 : (commutator G).map e.toMonoidHom = commutator H := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr e.surjective]
  rw [← h1, h, Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective]

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem card_quotient_center_map_projective {F : Subgroup (V ≃ₗ[K] V)} (hFΩ : F ≤ orthDerived Q)
    (hperf : commutator ↥F = ⊤) :
    Nat.card (↥((F.subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) ⧸
      Subgroup.center ↥((F.subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))) =
      Nat.card (↥F ⧸ Subgroup.center ↥F) := by
  set A : Subgroup ↥(orthDerived Q) := F.subgroupOf (orthDerived Q) with hA
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  let eAF : ↥A ≃* ↥F := Subgroup.subgroupOfEquivOfLe hFΩ
  have hAperf : commutator ↥A = ⊤ := commutator_eq_top_of_mulEquiv eAF.symm hperf
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hAperf (ρ.subgroupMap A)
    (MonoidHom.subgroupMap_surjective ρ A) (ker_subgroupMap_le_center A)
  rw [← Nat.card_congr e.toEquiv]
  exact Nat.card_congr (QuotientGroup.congr _ _ eAF (Subgroup.map_center_eq eAF)).toEquiv

end Transfer

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
