module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Datum

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.ClassicalInvolution.ModelFacts
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

@[expose] def A6NontrivForm (G : Type) [Group G] : Prop :=
  ∀ L : Subgroup G, IsComponent L → Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) →
    center L ≠ ⊥

theorem a6NontrivForm_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : A6NontrivForm H) : A6NontrivForm G := by
  rintro L hL ⟨eA⟩ hbot
  let eL : L ≃* L.map e.toMonoidHom := L.equivMapOfInjective _ e.injective
  refine h _ (LocalCores.isComponent_map_mulEquiv e hL)
    ⟨(QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).symm.trans eA⟩ ?_
  rw [← Subgroup.map_center_eq eL, hbot, Subgroup.map_bot]

theorem center_eq_bot_of_mulEquiv_a6 {D : Type} [Group D]
    (e : D ≃* alternatingGroup (Fin 6)) : center D = ⊥ := by
  rw [eq_bot_iff]
  intro d hd
  have h1 : (Subgroup.centerCongr e ⟨d, hd⟩ : alternatingGroup (Fin 6)) ∈ (⊥ : Subgroup _) := by
    rw [← a6sq_center]
    exact (Subgroup.centerCongr e ⟨d, hd⟩).2
  have h2 : Subgroup.centerCongr e ⟨d, hd⟩ = 1 := Subtype.ext (Subgroup.mem_bot.1 h1)
  have h3 : (⟨d, hd⟩ : center D) = 1 := (Subgroup.centerCongr e).injective (by rw [h2, map_one])
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h3)

theorem a6_false_of_nontrivForm {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : A6Hyp σ D)
    (hform : A6NontrivForm ↥(fixedSubgroup σ)) : False := by
  obtain ⟨hDc, hDZ⟩ := hD.component
  obtain ⟨-, ⟨eD⟩, -⟩ := hD
  exact hform D hDc hDZ (center_eq_bot_of_mulEquiv_a6 eD)


section Datum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]

theorem orbitGroup_center_ne_bot_of_single
    (D : OrthogonalSemilinearFixedRootDatum τ p₀ k) {O : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits) (hA : D.orbits = {O}) (hne : D.orbitMap O (-1) ≠ 1) :
    Subgroup.center D.orbitGroup ≠ ⊥ := by
  have hsurj := D.orbitGroupHom_surjective hO hA
  intro hbot
  have hz : (⟨D.orbitMap O (-1), D.orbitMap_mem_orbitGroup hO (-1)⟩ : D.orbitGroup) ∈
      Subgroup.center D.orbitGroup := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨A, rfl⟩ := hsurj y
    apply Subtype.ext
    change D.orbitMap O A * D.orbitMap O (-1) = D.orbitMap O (-1) * D.orbitMap O A
    rw [← D.orbitMap_mul hO, ← D.orbitMap_mul hO, mul_neg_one, neg_one_mul]
  rw [hbot, Subgroup.mem_bot] at hz
  exact hne (congrArg Subtype.val hz)

theorem orbitGroup_a6_center_ne_bot
    (D : OrthogonalSemilinearFixedRootDatum τ p₀ k) [Nontrivial D.orbitGroup]
    (hsingle : ∀ O ∈ D.orbits, D.orbits = {O} → D.orbitMap O (-1) ≠ 1)
    (hA6 : Nonempty (D.orbitGroup ⧸ Subgroup.center D.orbitGroup ≃* alternatingGroup (Fin 6))) :
    Subgroup.center D.orbitGroup ≠ ⊥ := by
  by_cases h2 : 2 ≤ D.orbits.ncard
  · exfalso
    obtain ⟨eA⟩ := hA6
    obtain ⟨O₁, hO₁⟩ := Set.nonempty_of_ncard_ne_zero (s := D.orbits) (by omega)
    obtain ⟨P, hP, hne, hadj⟩ := D.exists_adjacent_orbit h2 hO₁
    rcases ExcSelector.exists_odd_orbitPairing' D hO₁ hP hne hadj with
      ⟨γ, hγ, hodd⟩ | ⟨β, hβ, hodd⟩
    · obtain ⟨i, -, rfl⟩ := D.exists_orbitVec_eq hP hγ
      rw [ExcSelector.orbitPairing_orbitVec D hO₁ hP] at hodd
      exact (orbitGroup_isEmpty_a6_of_odd D hO₁ hP hodd).false eA
    · obtain ⟨i, -, rfl⟩ := D.exists_orbitVec_eq hO₁ hβ
      rw [ExcSelector.orbitPairing_orbitVec D hP hO₁] at hodd
      exact (orbitGroup_isEmpty_a6_of_odd D hP hO₁ hodd).false eA
  · have hfin := ExcSelector.finite_orbits' D
    rcases Nat.lt_or_ge D.orbits.ncard 1 with h0 | h1
    · exfalso
      have he : D.orbits = ∅ := by
        rw [← Set.ncard_eq_zero hfin]
        omega
      have hbot : D.orbitGroup = ⊥ := by
        rw [eq_bot_iff]
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨O, hO, -⟩
        rw [he] at hO
        exact absurd hO (Set.notMem_empty O)
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := exists_pair_ne D.orbitGroup
      rw [hbot, Subgroup.mem_bot] at hx hy
      exact hxy (Subtype.ext (hx.trans hy.symm))
    · obtain ⟨O, hO⟩ := Set.ncard_eq_one.1 (by omega : D.orbits.ncard = 1)
      have hOm : O ∈ D.orbits := by
        rw [hO]
        exact Set.mem_singleton O
      exact orbitGroup_center_ne_bot_of_single D hOm hO (hsingle O hOm hO)

end Datum

theorem a6NontrivForm_of_twistReduction
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j) {r₀ : ℕ}
    (hr₀ : ((τ = .E6 ∨ τ = .E7) ∧ r₀ = 2) ∨ (τ = .D4 ∧ r₀ = 3))
    {reps : List (SignRep τ)}
    (htheta : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      ThetaProperties ρ r₀ (signMaskChar τ m.mask) (ToralSign.wordElt τ l))
    {D : ModGL τ k}
    (hDX : ∀ (l : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      (wordWeylMatrix τ k l * D) * pinnedX τ k γ c * (wordWeylMatrix τ k l * D)⁻¹ =
        pinnedX τ k (thetaMap (ToralSign.wordElt τ l) ρ γ) (μ * c))
    (hDT : D ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hDG : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (hpin : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      IsTwistPinningNormalization τ k p e (signMaskChar τ m.mask)
        (thetaMap (ToralSign.wordElt τ l) ρ) (wordWeylMatrix τ k l * D))
    {x : ModGL τ k} (hred : IsFiniteToralTwistReduction τ k p e D reps x)
    [Finite ↥(⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x})] :
    A6NontrivForm ↥(⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x}) := by
  set N := ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x}
    with hN
  intro L hL hA6
  have hL2 : IsPComponent 2 L := isPComponent_two_of_isComponent hL
  have hsub : (L.map N.subtype).subgroupOf N = L :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective L
  have hL2' : IsPComponent 2 ((L.map N.subtype).subgroupOf N) := by rw [hsub]; exact hL2
  obtain ⟨Dd, ⟨m, hm, l, hl, hDχ, hDθ⟩, -, hXfin, hall⟩ :=
    exists_datum_uniform_of_twistReduction p hp hk he hτ hA hB htheta hDX hDT hDG hpin hred
      (L.map N.subtype) (Subgroup.map_subtype_le _) hL2'
  obtain ⟨J₀, hJ₀X, hJ₀c, ⟨eL⟩⟩ := hall _ (Subgroup.map_subtype_le _) hL2'
  obtain ⟨J', hJ', hq⟩ := ExcSelector.exists_eq_orbitGroupC_of_isPComponent' Dd hXfin hJ₀X hJ₀c
  have hθ : ThetaProperties ρ r₀ Dd.χ (ToralSign.wordElt τ l) := by
    rw [hDχ]
    exact htheta m hm l hl
  let eLO : L ≃* (Dd.withOrbit J').orbitGroup :=
    ((L.equivMapOfInjective _ N.subtype_injective).trans
      (eL.trans (MulEquiv.subgroupCongr hJ'))).trans
        (Subgroup.subgroupOfEquivOfLe (Dd.withOrbit J').orbitGroup_le_adjointGroup)
  have : Nontrivial (Dd.withOrbit J').orbitGroup := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hsingle : ∀ O ∈ (Dd.withOrbit J').orbits, (Dd.withOrbit J').orbits = {O} →
      (Dd.withOrbit J').orbitMap O (-1) ≠ 1 := fun O hO _ =>
    ExcSelector.orbitMap_neg_one_ne_one (Dd.withOrbit J') hr₀ hO
      (orbitCard_eq_of_thetaProperties (Dd.withOrbit J') hθ hDθ hO)
  obtain ⟨eA⟩ := hA6
  have hA' : Nonempty ((Dd.withOrbit J').orbitGroup ⧸
      Subgroup.center (Dd.withOrbit J').orbitGroup ≃* alternatingGroup (Fin 6)) :=
    ⟨(QuotientGroup.congr _ _ eLO.symm (Subgroup.map_center_eq eLO.symm)).trans eA⟩
  intro hbot
  refine orbitGroup_a6_center_ne_bot (Dd.withOrbit J') hsingle hA' ?_
  rw [← Subgroup.map_center_eq eLO, hbot, Subgroup.map_bot]

end CFSG.ComponentClassification.CatFC
