module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueD4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GluePSULie
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.ModelFacts.TG3Models

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.ModelFacts.TG3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Classical2
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


private theorem model1520_plus_four_aux (M : LieUniversal)
    (hM : M = ⟨spinGroup (quadPlus 4 𝔽₃), plusDatum 4 𝔽₃ (by norm_num)⟩)
    (hsingle : ModelFacts.FundamentalSingleClass .POmegaPlus M.D)
    (hG3 : ∀ R ∈ ModelFacts.fundamentalSubgroups .POmegaPlus M.D, ModelFacts.Gen3 R)
    (hlong : ∀ k : Fin M.D.rank, ModelFacts.IsLongestRoot M.D (Pi.single k 1))
    (hsl2 : ∀ R ∈ ModelFacts.fundamentalSubgroups .POmegaPlus M.D, Nonempty (R ≃* SL(2, 𝔽₃)))
    (hfin : Finite M.K) {G : Type} [Group G] [Finite G] {X : Subgroup G} (ψ : M.K →* ↥X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center M.K) {R : Subgroup M.K}
    (hR : R ∈ ModelFacts.fundamentalSubgroups .POmegaPlus M.D) (e : R ≃* SL(2, 𝔽₃)) :
    Model1520 X ((ψ (sl2Inv e) : ↥X) : G) := by
  subst hM
  have hn3 : 3 ≤ 4 := by norm_num
  have hn4 : 4 ≤ 4 := le_rfl
  have : Finite (spinGroup (quadPlus 4 𝔽₃)) := hfin
  have ctx := spinCtx3_plus hn3 hn4 hsingle hlong hG3 hsl2
  have hQ := regular_quadPlus (K := 𝔽₃) hn3
  have hOD : orthDerived (quadPlus 4 𝔽₃) = elementaryGroup (quadPlus 4 𝔽₃) :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ.1 hQ.2).1
  exact model1520_of_spinCtx3_d4 ctx (isPerfect_spinGroup_quadPlus hn3) hOD ψ hψ hker hR e

theorem model1520_of_modelUniv_plus_four (hadm : StatedLieAdmissible .POmegaPlus 4 3 1)
    {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (ψ : (ModelFacts.modelUniv .POmegaPlus 4 3 1 Fact.out).K →* ↥X)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (ModelFacts.modelUniv .POmegaPlus 4 3 1 Fact.out).K)
    {R : Subgroup (ModelFacts.modelUniv .POmegaPlus 4 3 1 Fact.out).K}
    (hR : R ∈ ModelFacts.fundamentalSubgroups .POmegaPlus
      (ModelFacts.modelUniv .POmegaPlus 4 3 1 Fact.out).D)
    (e : R ≃* SL(2, 𝔽₃)) : Model1520 X ((ψ (sl2Inv e) : ↥X) : G) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  refine model1520_plus_four_aux (ModelFacts.modelUniv .POmegaPlus 4 3 1 Fact.out)
    (ModelFacts.modelUniv_POmegaPlus (by norm_num))
    (ModelFacts.fundamentalSingleClass .POmegaPlus 4 3 1 Fact.out trivial hadm (by decide)
      (by decide))
    (fun R hR => ModelFacts.gen3_of_mem_longestFundamental3 (t := .POmegaPlus) h3 trivial hadm
      (by decide) (by decide)
      (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR))
    (fun k => ModelFacts.isLongestRoot_single .POmegaPlus 4 3 1 Fact.out trivial hadm k trivial)
    (fun R hR => ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaPlus)
      trivial hadm (by decide) (by decide) hR)
    (ModelFacts.finite_modelUniv (t := .POmegaPlus) hp2 Nat.prime_three trivial hadm) ψ hψ hker
    hR e

@[expose] def Model1520CoveredD4 (tag : StatedLieTag) (n : ℕ) : Prop :=
  Model1520CoveredAll tag n ∨ (tag = .POmegaPlus ∧ n = 4)

theorem covered_facts_d4 {tag : StatedLieTag} {n : ℕ} (hcov : Model1520CoveredD4 tag n) :
    StatedLieAdmissible tag n 3 1 ∧ ModelFacts.IsFundTag tag ∧ tag ≠ .G2 ∧ tag ≠ .trialityD4 := by
  rcases hcov with h | ⟨rfl, rfl⟩
  · exact covered_facts_all h
  · exact ⟨⟨Nat.prime_three, le_rfl, le_rfl⟩, trivial, by decide, by decide⟩

theorem model1520_of_modelUniv_d4 (tag : StatedLieTag) (n : ℕ) (hcov : Model1520CoveredD4 tag n)
    {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (ψ : (Generic.modelUniv tag n 3 1 Nat.prime_three).K →* ↥X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv tag n 3 1 Nat.prime_three).K)
    {R : Subgroup (Generic.modelUniv tag n 3 1 Nat.prime_three).K}
    (hR : R ∈ Generic.fundamentalSubgroups tag (Generic.modelUniv tag n 3 1 Nat.prime_three).D)
    (e : R ≃* SL(2, 𝔽₃)) : Model1520 X ((ψ (sl2Inv e) : ↥X) : G) := by
  rcases hcov with h | ⟨rfl, rfl⟩
  · exact model1520_of_modelUniv_all tag n h ψ hψ hker hR e
  · exact model1520_of_modelUniv_plus_four ⟨Nat.prime_three, le_rfl, le_rfl⟩ ψ hψ hker hR e

theorem model1520_of_modelUniv_member_d4 (tag : StatedLieTag) (n : ℕ)
    (hcov : Model1520CoveredD4 tag n)
    {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (ψ : (Generic.modelUniv tag n 3 1 Nat.prime_three).K →* ↥X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv tag n 3 1 Nat.prime_three).K)
    {R : Subgroup (Generic.modelUniv tag n 3 1 Nat.prime_three).K}
    (hR : R ∈ Generic.fundamentalSubgroups tag (Generic.modelUniv tag n 3 1 Nat.prime_three).D)
    {L : Subgroup ↥X} (hLR : L = R.map ψ) (hL24 : Nat.card L = 24) {t : ↥X}
    (hLt : IsClassicalMember3 L t) : Model1520 X (t : G) := by
  obtain ⟨hadm, hfund, hG2, hD4⟩ := covered_facts_d4 hcov
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨e⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := tag) hfund
    hadm hG2 hD4 hR
  have hfin : Finite (Generic.modelUniv tag n 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (t := tag) hp2 Nat.prime_three hfund hadm
  have hcard : Nat.card (R.map ψ) = 24 := hLR ▸ hL24
  obtain ⟨hu, -⟩ := uniqueInvolution_map3 ψ e hcard
  have htsq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hLt.orderOf_eq_two, pow_two] at h
    exact h
  have ht1 : t ≠ 1 := by
    intro h
    have := hLt.orderOf_eq_two
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have htz : t = ψ (sl2Inv e) :=
    (hu.unique t (hLR ▸ hLt.mem) htsq).resolve_left ht1
  rw [htz]
  exact model1520_of_modelUniv_d4 tag n hcov ψ hψ hker hR e

theorem model1520_of_lieSystem3_full {G : Type} [Group G] [Finite G] (X : Subgroup G) {ι : Type}
    {Φ : Set (Subgroup ↥X)} (D : LieSystemData3 ι ↥X Φ) (i : ι) (hi : ∀ j, j = i)
    (tag : StatedLieTag) (n : ℕ) (hcov : Model1520CoveredD4 tag n)
    (hk : D.kind i = CompData.model tag n) {L : Subgroup ↥X} (hL : L ∈ Φ) {t : ↥X}
    (hLt : IsClassicalMember3 L t) : Model1520 X (t : G) := by
  have hrange : (D.hom i).range = ⊤ := by
    rw [eq_top_iff, ← D.generate]
    exact iSup_le fun j => by rw [hi j]
  obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
  have hj : j = i := hi j
  subst hj
  have key : ∀ (c : CompData) (hc : c = CompData.model tag n) (φ : c.G →* ↥X)
      (hsurj : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center c.G) (R : Subgroup c.G),
      R ∈ c.fund → L = R.map φ → Model1520 X (t : G) := by
    intro c hc φ hsurj hker R hR hLR
    subst hc
    exact model1520_of_modelUniv_member_d4 tag n hcov φ hsurj hker hR hLR (D.card_eq L hL) hLt
  exact key (D.kind j) hk (D.hom j) (MonoidHom.range_eq_top.mp hrange) (D.ker_le_center j) R hR hLR

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux
