module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Assembly

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

@[expose] def D2IndexCase (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ) (P : Sylow p G) (M A H R : Subgroup G), D2Escape p P M A H R →
    D2EscapeMax p P M R → p ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* i.Group) → False

theorem d2ComponentCase_of_indexCases (h : ∀ i, D2IndexCase i) : D2ComponentCase := by
  intro G _ _ hglob hD1 p P M A H R hesc hmax hβ Rbar K hRbar hK
  obtain ⟨i, hi⟩ := hK.catalog
  exact h i G hglob hD1 p P M A H R hesc hmax hβ Rbar K hRbar hK hi

theorem D2AlmostSimple.false_of_cyclic {X : Type*} [Group X] [Finite X] {p : ℕ}
    {R : Sylow p X} {A X₀ K : Subgroup X} (hK : D2AlmostSimple p X R A X₀ K) (q : ℕ)
    (hq : q.Prime) (e : K ≃* (TauCeti.CFSGIndex.cyclic q hq).Group) : False := by
  have hcomm : ∀ a b : K, a * b = b * a := by
    intro a b
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod q)) (e a) (e b)
  have hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.component.2.2.2
  obtain ⟨x, y, hxy⟩ := hsimple.toNontrivial.exists_pair_ne
  apply hxy
  induction x using QuotientGroup.induction_on with | H x => ?_
  induction y using QuotientGroup.induction_on with | H y => ?_
  rw [QuotientGroup.eq]
  rw [Subgroup.mem_center_iff]
  intro z
  exact hcomm z _

theorem d2IndexCase_cyclic (q : ℕ) (hq : q.Prime) : D2IndexCase (.cyclic q hq) := by
  intro G _ _ _ _ p P M A H R _ _ _ Rbar K _ hK ⟨e⟩
  exact hK.false_of_cyclic q hq e

@[expose] def D2AltCase : Prop := ∀ (n : ℕ) (hn : 5 ≤ n), D2IndexCase (.alternating n hn)

@[expose] def D2LieCase : Prop := ∀ d : TauCeti.ValidLieTypeIndex, D2IndexCase (.lie d)

@[expose] def D2SporadicCase : Prop := ∀ s : TauCeti.SporadicName, D2IndexCase (.sporadic s)

theorem d2ComponentCase_of_families (hA : D2AltCase) (hL : D2LieCase) (hS : D2SporadicCase) :
    D2ComponentCase :=
  d2ComponentCase_of_indexCases fun i => match i with
    | .cyclic q hq => d2IndexCase_cyclic q hq
    | .alternating n hn => hA n hn
    | .lie d => hL d
    | .sporadic s => hS s

end CFSG.AGLEmbeddingD2
