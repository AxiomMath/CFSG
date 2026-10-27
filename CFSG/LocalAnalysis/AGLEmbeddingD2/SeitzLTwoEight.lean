module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreePairStrong
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PerfectSchreier
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PrimeThree3Seitz
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSL2

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC

theorem d2IndexCaseAt_of_split {i : TauCeti.CFSGIndex} {Pp Q : ℕ → Prop}
    (h₁ : D2IndexCaseAt i fun p => Pp p ∧ ¬ Q p) (h₂ : D2IndexCaseAt i Q) : D2IndexCaseAt i Pp := by
  intro G _ _ hglob hD1 p hp
  by_cases hq : Q p
  · exact h₂ G hglob hD1 p hq
  · exact h₁ G hglob hD1 p ⟨hp, hq⟩

theorem D2AlmostSimple.isSolvable_inf_of_psl28 {X : Type*}
    [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}
    (h : D2AlmostSimple p X R A X₀ K) [Fact (Nat.Prime 2)] (e : K ≃* PSL2GF 2 3) :
    Group.IsSolvable (X₀ ⊓ K : Subgroup X) := by
  have hne : (X₀.subgroupOf K).map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply h.not_le
    intro k hk
    have hmem : e ⟨k, hk⟩ ∈ (X₀.subgroupOf K).map e.toMonoidHom := htop ▸ Subgroup.mem_top _
    obtain ⟨k', hk', hkk'⟩ := hmem
    have hk'' : k' = ⟨k, hk⟩ := e.injective hkk'
    rw [hk''] at hk'
    exact Subgroup.mem_subgroupOf.mp hk'
  have hs := CFSG.SignalizerFunctorTheorem.CatalogBridge.proper_subgroup_solvable_psl2_even
    (p := 3) Nat.prime_three (by decide) _ hne
  have e' := (X₀.subgroupOf K).equivMapOfInjective e.toMonoidHom e.injective
  have : Group.IsSolvable (X₀.subgroupOf K) :=
    Group.isSolvable_of_surjective (f := e'.symm.toMonoidHom) e'.symm.surjective
  exact isSolvable_inf_of_subgroupOf this

theorem d2IndexCaseAt_l28_of_pairStrong
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hS : D2PairStrongThree) (d : TauCeti.ValidLieTypeIndex) :
    D2IndexCaseAt (.lie d) fun p => IsD2SeitzLTwoEight p d.1 := by
  intro G _ _ hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK he
  have hU := d2PairAt_l28 d _ p hp Rbar _ _ K hK he
  obtain ⟨hp3, q, hq2, hq3, hdq⟩ := hp
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := he
  obtain ⟨e'⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 2) (n := 3) (d := d)
    ⟨q, hdq, hq2, hq3⟩
  have hpr : AGLPair 3 M H R := hesc.toPair hglob.toAGLGlobal
    (hesc.twoCore_inf_eq_of_primeCore_inf_eq (hesc.primeCore_inf_eq_iff.mpr hU))
  exact hS G hglob hD1 P M A H R hesc hmax hβ hpr
    (hesc.stronglyEmbedded_of_pair hglob hβ hpr h84 (hD2.noXBlockFor hglob.toD1Global))
    (d2PerfectThreePrime_of_perfect_eq_bot
      (hK.perfect_eq_bot_of_isSolvable_inf hSch (hK.isSolvable_inf_of_psl28 (e.trans e'))))

end CFSG.AGLEmbeddingD2
