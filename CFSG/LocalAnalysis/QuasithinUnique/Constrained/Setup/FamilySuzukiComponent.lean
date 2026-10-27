module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.Quasithin CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem not_isSolvable_of_isComp {G : Type} [Group G] {L H : Subgroup G} (hL : IsComp L H) :
    ¬ Group.IsSolvable H := by
  intro hsolv
  have hq := isQuasisimple_of_isComp hL
  have hLsolv : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hL.1)
  have hperf : Group.IsPerfect ↥L := hq.1
  obtain ⟨a', b', hab⟩ := hq.2.2
  have hne : a' ≠ b' := fun h => hab (by rw [h])
  have : Nontrivial (↥L ⧸ Subgroup.center ↥L) := ⟨⟨a', b', hne⟩⟩
  have : Nontrivial ↥L := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  exact Group.IsPerfect.not_isSolvable (G := ↥L) hLsolv

theorem quasisimple_range_centerQuotientEquiv {Q H : Type*} [Group Q] [Group H]
    (hQ : CFSG.IsQuasisimple Q) (ρ : Q →* H) (h0 : ρ.range ≠ ⊥) :
    CFSG.IsQuasisimple ρ.range ∧
      Nonempty ((ρ.range ⧸ Subgroup.center ρ.range) ≃* (Q ⧸ Subgroup.center Q)) := by
  have hker : ρ.ker ≤ Subgroup.center Q := by
    rcases quasisimple_normal_subgroups hQ ρ.normal_ker with h | h
    · exact absurd (by rw [MonoidHom.range_eq_bot_iff, ← MonoidHom.ker_eq_top_iff]; exact h) h0
    · exact h
  obtain ⟨hqs, -, hmap⟩ := quasisimple_central_quotient hQ hker
  let e₁ : Q ⧸ ρ.ker ≃* ρ.range := QuotientGroup.quotientKerEquivRange ρ
  refine ⟨(isQuasisimple_congr e₁).1 hqs, ⟨?_⟩⟩
  have hc : (Subgroup.center (Q ⧸ ρ.ker)).map e₁.toMonoidHom = Subgroup.center ρ.range :=
    Subgroup.map_center_eq e₁
  have h1 : (Q ⧸ ρ.ker) ⧸ Subgroup.center (Q ⧸ ρ.ker) ≃* ρ.range ⧸ Subgroup.center ρ.range :=
    QuotientGroup.congr _ _ e₁ hc
  have h2 : (Q ⧸ ρ.ker) ⧸ (Subgroup.center Q).map (QuotientGroup.mk' ρ.ker) ≃*
      Q ⧸ Subgroup.center Q :=
    QuotientGroup.quotientQuotientEquivQuotient ρ.ker (Subgroup.center Q) hker
  have h3 : (Q ⧸ ρ.ker) ⧸ Subgroup.center (Q ⧸ ρ.ker) ≃*
      (Q ⧸ ρ.ker) ⧸ (Subgroup.center Q).map (QuotientGroup.mk' ρ.ker) :=
    QuotientGroup.quotientMulEquivOfEq hmap
  exact h1.symm.trans (h3.trans h2)

@[expose] def SectionProductionProp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
    ∀ G L A : Subgroup (MulAut V), IsComp L G → IsBestOffender G A → ⁅L, A⁆ ≠ ⊥ →
      ∃ (W : Type) (_ : CommGroup W) (_ : Finite W) (ρ : ↥L →* MulAut W)
        (A₀ : Subgroup (MulAut W)),
        (∀ w : W, w * w = 1) ∧ Nontrivial W ∧ ρ.range ≠ ⊥ ∧
        (∀ U : Subgroup W, (∀ g ∈ ρ.range, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
        A₀ ≠ ⊥ ∧ IsElemAbelian2 A₀ ∧ A₀ ≤ Subgroup.normalizer (ρ.range : Set (MulAut W)) ∧
        Nat.card W ≤ Nat.card A₀ * Nat.card (fixV A₀)

theorem minimal_best_offender_centralizes_Suzuki_component
    (hsec : SectionProductionProp)
    (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    {G L A : Subgroup (MulAut V)} (hL : IsComp L G) (hA : IsBestOffender G A)
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : CQ L ≃* suzukiGroup a K) : ⁅L, A⁆ = ⊥ := by
  by_contra hne
  obtain ⟨W, hWg, hWf, ρ, A₀, hW2, hWn, h0, hirr, hA0, hAe, hAn, hoff⟩ :=
    hsec V hV G L A hL hA hne
  have hq := isQuasisimple_of_isComp hL
  obtain ⟨hq0, ⟨e⟩⟩ := quasisimple_range_centerQuotientEquiv hq ρ h0
  have h5 := (suzuki_irreducible_normalizer_excludes a ha hK W hW2 ρ.range hq0.1 hirr
    (e.trans α)).2.2.2.2 A₀ hA0 hAe hAn
  exact absurd hoff (not_le.2 h5)

theorem noSuzukiComponent
    (hlayer : ActorLayerProp) (hsec : SectionProductionProp) :
    NoSuzukiComponentProp := by
  intro V _ _ H T M E hFF L hL f hSz
  obtain ⟨-, a, ha, K, _, _, hf, hK', ⟨α⟩⟩ := hSz
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hf ▸ hK'
  have hns : ¬ Group.IsSolvable H := not_isSolvable_of_isComp hL
  obtain ⟨A, hA, hLA⟩ := (hlayer V H T M E hFF hns).component_commutator L hL
  have hcent := minimal_best_offender_centralizes_Suzuki_component hsec V hFF.elementary hL hA ha
    hK α
  have hL0 : L = ⊥ := hLA.symm.trans hcent
  obtain ⟨a', b', hab⟩ := (isQuasisimple_of_isComp hL).2.2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b'
  have hL1 : ∀ g ∈ L, g = 1 := fun g hg => by rwa [hL0, Subgroup.mem_bot] at hg
  have hx : x = 1 := Subtype.ext (hL1 x x.2)
  have hy : y = 1 := Subtype.ext (hL1 y y.2)
  exact hab (by rw [hx, hy])

end CFSG.QuasithinUnique.Setup.Family
