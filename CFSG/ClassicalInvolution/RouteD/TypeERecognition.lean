module

public import CFSG.ClassicalInvolution.RouteD.TypeEModel
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv InClass IsClassicalMember LocalOddCentral LieSystemData)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem map_fundamental_mem {t : StatedLieTag} {T : LieUniversal}
    (hsc : FundamentalSingleClass t T.D) {R₀ : Subgroup T.K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t T.D) (Ψ : T.K →* G) {Ω : Set (Subgroup G)}
    (hΩ : CFSG.ClassicalInvolution.Generic.ConjInvariant Ω) (h₀ : R₀.map Ψ ∈ Ω) :
    ∀ R ∈ fundamentalSubgroups t T.D, R.map Ψ ∈ Ω := by
  intro R hR
  obtain ⟨g, rfl⟩ := hsc R₀ hR₀ R hR
  rw [← CFSG.ClassicalInvolution.Generic.conjSub_map]
  exact hΩ _ _ h₀

theorem routeD_typeE6_of_chain [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .PSL 6 Ω z)
    (hP1 : LocalOddCentral Ω {z}) (U : Fin 6 → Subgroup G) (hUΩ : ∀ i, U i ∈ Ω)
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 6, edgeE 6 i j →
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E6 ∧ D.rank i = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hadm : StatedLieAdmissible .E6 0 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, rfl⟩
  have hadmY : StatedLieAdmissible .PSL 6 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, by norm_num,
    by simp, by simp⟩
  obtain ⟨Ψ, hker, -, hrk⟩ := exists_psi_E6 hadm (by omega) U hcomm hpair
  obtain ⟨M⟩ := nonempty_extModel_E6 hadm (by omega)
  have hsc : FundamentalSingleClass .E6 (modelUniv .E6 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .E6 0 p f hp trivial hadm (by decide) (by decide)
  have hl : ∀ i, ModelFacts.IsLongestRoot (modelUniv .E6 0 p f Fact.out).D (Pi.single i 1) :=
    fun i => ModelFacts.isLongestRoot_single .E6 0 p f hp trivial hadm i trivial
  let R₀ : Subgroup (modelUniv .E6 0 p f Fact.out).K :=
    rankOne (modelUniv .E6 0 p f Fact.out).D.rootGroup ⟨0, by show 0 < 6; decide⟩
  have hR₀ : R₀.map Ψ = U ⟨0, by show 0 < 6; decide⟩ := hrk _
  have hΩψ : ∀ R ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 p f Fact.out).D, R.map Ψ ∈ Ω :=
    map_fundamental_mem hsc (R₀ := R₀) (rankOne_mem_fundamental _ (hl _)) Ψ hΩ.conjInvariant
      (by rw [hR₀]; exact hUΩ _)
  exact routeD_core (t := .E6) (by norm_num) trivial hadm hsc (by decide)
    (ModelFacts.finite_modelUniv (t := .PSL) hp2 hp trivial hadmY) M hΩ hK hsingle hconn hz hshape hP1 Ψ hker
    hΩψ

theorem routeD_typeE7_of_chain [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .POmegaPlus 6 Ω z)
    (hP1 : LocalOddCentral Ω {z}) (U : Fin 7 → Subgroup G) (hUΩ : ∀ i, U i ∈ Ω)
    (hcomm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 7, edgeE 7 i j →
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E7 ∧ D.rank i = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, rfl⟩
  have hadmY : StatedLieAdmissible .POmegaPlus 6 p f :=
    ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, by norm_num⟩
  obtain ⟨Ψ, hker, -, hrk⟩ := exists_psi_E7 hadm (by omega) U hcomm hpair
  obtain ⟨M⟩ := nonempty_extModel_E7 hadm (by omega)
  have hsc : FundamentalSingleClass .E7 (modelUniv .E7 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .E7 0 p f hp trivial hadm (by decide) (by decide)
  have hl : ∀ i, ModelFacts.IsLongestRoot (modelUniv .E7 0 p f Fact.out).D (Pi.single i 1) :=
    fun i => ModelFacts.isLongestRoot_single .E7 0 p f hp trivial hadm i trivial
  let R₀ : Subgroup (modelUniv .E7 0 p f Fact.out).K :=
    rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup ⟨0, by show 0 < 7; decide⟩
  have hR₀ : R₀.map Ψ = U ⟨0, by show 0 < 7; decide⟩ := hrk _
  have hΩψ : ∀ R ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D,
      R.map Ψ ∈ Ω :=
    map_fundamental_mem hsc (R₀ := R₀) (rankOne_mem_fundamental _ (hl _)) Ψ hΩ.conjInvariant
      (by rw [hR₀]; exact hUΩ _)
  exact routeD_core (t := .E7) (by norm_num) trivial hadm hsc (by decide)
    (ModelFacts.finite_modelUniv (t := .POmegaPlus) hp2 hp trivial hadmY) M hΩ hK hsingle hconn hz hshape
    hP1 Ψ hker hΩψ

theorem routeD_typeE8_of_chain [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 1 .E7 0 Ω z)
    (hP1 : LocalOddCentral Ω {z}) (U : Fin 8 → Subgroup G) (hUΩ : ∀ i, U i ∈ Ω)
    (hcomm : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i → Commutes (U i) (U j))
    (hpair : ∀ i j : Fin 8, edgeE 8 i j →
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .E8 ∧ D.rank i = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hadm : StatedLieAdmissible .E8 0 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, rfl⟩
  have hadmY : StatedLieAdmissible .E7 0 p f := ⟨hp, Nat.one_le_iff_ne_zero.mpr hf, rfl⟩
  obtain ⟨Ψ, hker, -, hrk⟩ := exists_psi_E8 hadm (by omega) U hcomm hpair
  obtain ⟨M⟩ := nonempty_extModel_E8 hadm (by omega)
  have hsc : FundamentalSingleClass .E8 (modelUniv .E8 0 p f Fact.out).D :=
    ModelFacts.fundamentalSingleClass .E8 0 p f hp trivial hadm (by decide) (by decide)
  have hl : ∀ i, ModelFacts.IsLongestRoot (modelUniv .E8 0 p f Fact.out).D (Pi.single i 1) :=
    fun i => ModelFacts.isLongestRoot_single .E8 0 p f hp trivial hadm i trivial
  let R₀ : Subgroup (modelUniv .E8 0 p f Fact.out).K :=
    rankOne (modelUniv .E8 0 p f Fact.out).D.rootGroup ⟨0, by show 0 < 8; decide⟩
  have hR₀ : R₀.map Ψ = U ⟨0, by show 0 < 8; decide⟩ := hrk _
  have hΩψ : ∀ R ∈ fundamentalSubgroups .E8 (modelUniv .E8 0 p f Fact.out).D,
      R.map Ψ ∈ Ω :=
    map_fundamental_mem hsc (R₀ := R₀) (rankOne_mem_fundamental _ (hl _)) Ψ hΩ.conjInvariant
      (by rw [hR₀]; exact hUΩ _)
  exact routeD_core (t := .E8) (by norm_num) trivial hadm hsc (by decide)
    (ModelFacts.finite_modelUniv (t := .E7) hp2 hp trivial hadmY) M hΩ hK hsingle hconn hz hshape
    hP1 Ψ hker hΩψ

end CFSG.ClassicalInvolution.RouteD
