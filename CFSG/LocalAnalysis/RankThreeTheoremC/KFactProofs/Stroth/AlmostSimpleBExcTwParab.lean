module

public import CFSG.LieType.Chevalley.GraphFixedParabolicCells
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedWeyl
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedUnipotent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders

section


@[expose] def foldMask (t : TwistTag) (J : Set (Fin t.foldedTag.rank)) : Set (Fin t.tag.rank) :=
  {i | t.orbitIndex i ∈ J}

theorem orbitReflection_mem_parabolic_foldMask (t : TwistTag) {J : Set (Fin t.foldedTag.rank)}
    {a : Fin t.foldedTag.rank} (ha : a ∈ J) :
    t.orbitReflection a ∈ (coxeterSystem t.tag).parabolic (foldMask t J) := by
  refine (coxeterSystem t.tag).wordProd_mem_parabolic fun j hj => ?_
  have hj' := (t.mem_orbit_iff).1 ((t.mem_orbitWord).1 hj)
  show t.orbitIndex j ∈ J
  rw [hj']
  exact ha

theorem foldedParabolicWeylGroup_eq_inf (t : TwistTag) (J : Set (Fin t.foldedTag.rank)) :
    foldedParabolicWeylGroup t J =
      (coxeterSystem t.tag).parabolic (foldMask t J) ⊓ relWeylTwist t := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_inf.2 ⟨orbitReflection_mem_parabolic_foldMask t ha, t.orbitReflection_mem a⟩
  · intro w hw
    obtain ⟨hwP, hwρ⟩ := Subgroup.mem_inf.1 hw
    suffices h : ∀ n : ℕ, ∀ w : WeylGroup t.tag,
        w ∈ (coxeterSystem t.tag).parabolic (foldMask t J) → w ∈ relWeylTwist t →
        (coxeterSystem t.tag).length w = n → w ∈ foldedParabolicWeylGroup t J from
      h _ w hwP hwρ rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hP hρ hn
      by_cases h1 : w = 1
      · rw [h1]
        exact one_mem _
      obtain ⟨i, hiJ, hdesc⟩ :=
        (coxeterSystem t.tag).exists_rightDescent_mem_of_mem_parabolic_of_ne_one hP h1
      have hneg : height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0 :=
        ((smul_single_mem_negRoots_iff w i).2 hdesc).2
      have hlen := length_mul_orbitReflection_add_card t hρ hneg
      have hcard : 0 < (t.orbit (t.orbitIndex i)).card :=
        Finset.card_pos.2 ⟨i, t.mem_orbit_orbitIndex i⟩
      have haJ : t.orbitIndex i ∈ J := hiJ
      have hP' : w * t.orbitReflection (t.orbitIndex i) ∈
          (coxeterSystem t.tag).parabolic (foldMask t J) :=
        mul_mem hP (orbitReflection_mem_parabolic_foldMask t haJ)
      have hρ' : w * t.orbitReflection (t.orbitIndex i) ∈ relWeylTwist t :=
        mul_mem hρ (t.orbitReflection_mem _)
      have hw' := ih _ (by omega) _ hP' hρ' rfl
      rw [← mul_one w, ← t.orbitReflection_mul_self (t.orbitIndex i), ← mul_assoc]
      exact mul_mem hw' (Subgroup.subset_closure ⟨_, haJ, rfl⟩)

open Classical in
theorem card_graphFixedParabolic_eq_sum {t : TwistTag} {K : Type} [Field K] [Finite K]
    [Fintype (WeylGroup t.tag)] (σ : K ≃+* K) {q : ℕ}
    (hq : ∀ a, Nat.card (orbitField t K σ.toRingHom a) = q ^ (t.orbit a).card)
    (J : Set (Fin t.foldedTag.rank)) :
    Nat.card (graphFixedParabolic t K σ.toRingHom J) =
      Nat.card (graphFixedRootBorel t K σ.toRingHom) *
        ∑ w ∈ Finset.univ.filter (· ∈ foldedParabolicWeylGroup t J),
          q ^ (coxeterSystem t.tag).length w := by
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  have : Fintype (foldedParabolicWeylGroup t J) := Fintype.ofFinite _
  have : Finite (Module.End K (RootModule t.tag K)) := Module.finite_of_finite K
  have e : (graphFixedParabolic t K σ.toRingHom J : Set (ModGL t.tag K)) ≃
      Σ w : foldedParabolicWeylGroup t J, graphFixedRootBruhatCell t K σ.toRingHom w := by
    rw [(fixed_standard_parabolic_cells t K σ).1 J]
    exact Set.unionEqSigmaOfDisjoint fun w w' h =>
      disjoint_graphFixedRootBruhatCell fun h' => h (Subtype.ext h')
  have hcell : ∀ w : foldedParabolicWeylGroup t J,
      Nat.card (graphFixedRootBruhatCell t K σ.toRingHom w) =
        Nat.card (graphFixedRootBorel t K σ.toRingHom) *
          Nat.card (graphFixedInversionUnipotent t K σ.toRingHom w) := by
    intro w
    rw [← Nat.card_congr (bijOn_graphFixedRootBruhatCell hσ
        (foldedParabolicWeylGroup_le t J w.2)).equiv,
      Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
    rfl
  calc Nat.card (graphFixedParabolic t K σ.toRingHom J) =
        Nat.card (Σ w : foldedParabolicWeylGroup t J,
          graphFixedRootBruhatCell t K σ.toRingHom w) := Nat.card_congr e
    _ = ∑ w : foldedParabolicWeylGroup t J,
          Nat.card (graphFixedRootBruhatCell t K σ.toRingHom w) := Nat.card_sigma
    _ = _ := by
      rw [Finset.mul_sum,
        Finset.sum_subtype (p := (· ∈ foldedParabolicWeylGroup t J))
          (Finset.univ.filter (· ∈ foldedParabolicWeylGroup t J)) (fun w => by simp) (fun w => Nat.card (graphFixedRootBorel t K σ.toRingHom) *
            q ^ (coxeterSystem t.tag).length w)]
      exact Finset.sum_congr rfl fun w _ => by
        rw [hcell w, card_graphFixedInversionUnipotent hσ hq
          (foldedParabolicWeylGroup_le t J w.2)]

open Classical in
theorem card_graphFixedParabolic_eq_borel_mul {t : TwistTag} {K : Type} [Field K] [Finite K]
    [Fintype (WeylGroup t.tag)] (σ : K ≃+* K) {q : ℕ}
    (hq : ∀ a, Nat.card (orbitField t K σ.toRingHom a) = q ^ (t.orbit a).card)
    (J : Set (Fin t.foldedTag.rank)) :
    Nat.card (graphFixedParabolic t K σ.toRingHom J) =
      Nat.card (graphFixedRootBorel t K σ.toRingHom) * twistedParabolicSum t (foldMask t J) q := by
  rw [card_graphFixedParabolic_eq_sum σ hq J, twistedParabolicSum]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, foldedParabolicWeylGroup_eq_inf,
    Subgroup.mem_inf]

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
