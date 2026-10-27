module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairExc
public import CFSG.ClassicalInvolution.ModelFacts.CF3B
public import CFSG.LieType.HighestRoot.ModelCenter

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.Asc77.T3CII (eq_three_of_pow_eq_three ne_two_of_pow_eq_three)
open scoped MatrixGroups commutatorElement

section Transfer

variable {τ : Tag} {K : Type} [Field K] {G : Type} [Group G]

theorem commute_rankOne_of_isogeny3 (θ : G →* adjointGroup τ K) (hker : θ.ker ≤ Subgroup.center G)
    (hk3 : ∀ x ∈ θ.ker, x ^ 3 = 1 → x = 1) (X : (Fin τ.rank → ℤ) → Subgroup G)
    (hX : ∀ γ, IsRoot τ γ → (X γ).map θ = rootGroup (rootOperatorFamily τ) K γ) (i : Fin τ.rank)
    (hG3 : Gen3 (rankOne X i)) {u : G} {b : Fin τ.rank → Kˣ}
    (hu : ((θ u : adjointGroup τ K) : ModGL τ K) = rootDiagUnit τ b) (hi : b i = 1) :
    ∀ r ∈ rankOne X i, u * r = r * u := by
  intro r hr
  have hmap : (rankOne X i).map θ = rankOne (rootGroup (rootOperatorFamily τ) K) i := by
    unfold rankOne
    rw [Subgroup.map_sup, hX _ (isRoot_single τ i), hX _ (isRoot_neg_single τ i)]
  refine (commute_of_map_commute_of_gen3 θ hker hk3 hG3 (b := u) (fun a ha => ?_) r hr).symm
  have hmap' : θ a ∈ rankOne (rootGroup (rootOperatorFamily τ) K) i := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem θ ha
  have hc' := rootDiagUnit_commute_rankOne (K := K) b i hi hmap'
  rw [← hu] at hc'
  exact (Subtype.ext hc').symm
end Transfer

section Tags

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

theorem commute_rankOne_of_excEmbed_eq3 (h3 : p ^ e = 3) {t : StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4) (hadm : StatedLieAdmissible t 0 p e)
    {u : (Generic.modelUniv t 0 p e Fact.out).K} {b : Fin (excTag t).rank → (GaloisField p e)ˣ}
    (hu : excEmbed t p e u = rootDiagUnit (excTag t) b)
    (k : Fin (Generic.modelUniv t 0 p e Fact.out).D.rank)
    (hk : b (Fin.cast (excRank_eq ht) k) = 1) :
    ∀ r ∈ rankOne (Generic.modelUniv t 0 p e Fact.out).D.rootGroup k, u * r = r * u := by
  have hfund : Generic.IsFundTag t := by rcases ht with rfl | rfl | rfl | rfl <;> trivial
  have hG2 : t ≠ .G2 := by rcases ht with rfl | rfl | rfl | rfl <;> decide
  have hD4 : t ≠ .trialityD4 := by rcases ht with rfl | rfl | rfl | rfl <;> decide
  have hp2 : p ≠ 2 := ne_two_of_pow_eq_three h3
  have hG3 : ∀ R ∈ fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D, Gen3 R :=
    fun R hR => gen3_of_mem_longestFundamental3 h3 hfund hadm hG2 hD4
      (fundamentalSubgroups_subset_longest hG2 hD4 _ hR)
  have hZ3 : ∀ z ∈ Subgroup.center (Generic.modelUniv t 0 p e Fact.out).K, z ^ 3 = 1 → z = 1 := by
    obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact fun z hz hz3 => CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime t 0 3 1
      Nat.prime_three hp2 hfund hadm z hz hz3
  rcases ht with rfl | rfl | rfl | rfl
  ·
    have hlong := isLongestRoot_single .E6 0 p e Fact.out trivial hadm k trivial
    refine commute_rankOne_of_isogeny3 (e6Isogeny (GaloisField p e))
      (ker_le_center_of_isQuasisimple (isQuasisimple_e6 (GaloisField p e))
        (e6Isogeny_ne_one (GaloisField p e)))
      (fun x hx hx3 => hZ3 x (ker_le_center_of_isQuasisimple (isQuasisimple_e6 (GaloisField p e))
        (e6Isogeny_ne_one (GaloisField p e)) hx) hx3)
      (e6Datum (GaloisField p e)).rootGroup (fun γ hγ => map_e6Isogeny_rootGroup _ hγ) k
      (hG3 _ ⟨1, Pi.single k 1, Or.inl hlong, (conjSub_one _).symm⟩) hu hk
  ·
    have hlong := isLongestRoot_single .E7 0 p e Fact.out trivial hadm k trivial
    refine commute_rankOne_of_isogeny3 (e7Isogeny (GaloisField p e))
      (ker_le_center_of_isQuasisimple (isQuasisimple_e7 (GaloisField p e))
        (exists_e7Isogeny_ne_one (GaloisField p e)))
      (fun x hx hx3 => hZ3 x (ker_le_center_of_isQuasisimple (isQuasisimple_e7 (GaloisField p e))
        (exists_e7Isogeny_ne_one (GaloisField p e)) hx) hx3)
      (e7Datum (GaloisField p e)).rootGroup (fun γ hγ => map_e7Isogeny_rootGroup _ hγ) k
      (hG3 _ ⟨1, Pi.single k 1, Or.inl hlong, (conjSub_one _).symm⟩) hu hk
  ·
    intro r hr
    exact Subtype.ext (by
      have := rootDiagUnit_commute_rankOne (K := GaloisField p e) b k hk hr
      rw [← hu] at this
      exact this)
  ·
    intro r hr
    exact Subtype.ext (by
      have := rootDiagUnit_commute_rankOne (K := GaloisField p e) b k hk hr
      rw [← hu] at this
      exact this)

end Tags

end CFSG.ClassicalInvolution.ModelFacts

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
  CFSG.Assembly.LowTwoRank

section Tags

open CFSG.LieType.Chevalley

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

theorem commutingFundamentalGeneration3_exc (h3 : p ^ e = 3) {t : StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) (hadm : StatedLieAdmissible t 0 p e)
    (hframe : PairFrame (ModelFacts.excSignGroup t p e)
      (Generic.fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D)) :
    ModelFacts.CommutingFundamentalGeneration p t 0 e := by
  have ht' : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4 := by tauto
  have hfund : Generic.IsFundTag t := by rcases ht with rfl | rfl | rfl <;> trivial
  have hlong : ∀ k : Fin (Generic.modelUniv t 0 p e Fact.out).D.rank,
      IsLongestRoot (Generic.modelUniv t 0 p e Fact.out).D (Pi.single k 1) := fun k =>
    ModelFacts.isLongestRoot_single t 0 p e Fact.out hfund hadm k
      (by rcases ht with rfl | rfl | rfl <;> trivial)
  exact commutingGeneration_of_signTorus _ (ModelFacts.excSignGroup t p e)
    (ModelFacts.excEmbed t p e) (Fin.cast (ModelFacts.excRank_eq ht'))
    (rootDiagUnitHom (ModelFacts.excTag t) (GaloisField p e)) hframe
    (fun u hu => ModelFacts.mem_excSignGroup.1 hu)
    (fun _ _ k hu hk => ModelFacts.commute_rankOne_of_excEmbed_eq3 h3 ht' hadm hu k hk) hlong
    (iSup_rankOneRoot_simple_eq_top t 0 p e Fact.out hfund hadm)

end Tags

end CFSG.ClassicalInvolution.Balance.Bootstrap
