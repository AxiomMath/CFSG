module

public import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Open.MonsterDefs
public import CFSG.RankThree.PartOne.CTP.FusionDefs
public import CFSG.Sporadic.He.Setup
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.Suz.Simple
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP.Fus

theorem prime_pow_three_dvd_monsterOrder {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ 3 ∣ monsterOrder) : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 := by
  have hN : monsterOrder ≠ 0 := by norm_num [monsterOrder]
  have hmem : p ∈ monsterOrder.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans h, hN⟩
  clear hN
  norm_num [monsterOrder, Nat.primeFactors, Nat.primeFactorsList] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals first
    | exact absurd rfl hp2
    | (exfalso; norm_num [monsterOrder] at h; done)
    | simp

theorem ker_comp_mulEquiv {E X Y : Type} [Group E] [Group X] [Group Y] (f : X ≃* Y)
    (π : E →* X) : (f.toMonoidHom.comp π).ker = π.ker := by
  ext x
  simp [MonoidHom.mem_ker]

theorem hasNoncommPair_of_mulEquiv {X Y : Type} [Group X] [Group Y] {p : ℕ} (f : X ≃* Y)
    (h : HasNoncommPair p Y) : HasNoncommPair p X := by
  obtain ⟨x, y, hx, hy, hxy, hP⟩ := h
  refine ⟨f.symm x, f.symm y, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hx, map_one]
  · rw [← map_pow, hy, map_one]
  · intro h'
    apply hxy
    have := congrArg f h'
    simpa using this
  · have hc : (Subgroup.closure ({x, y} : Set Y)).map f.symm.toMonoidHom =
        Subgroup.closure ({f.symm x, f.symm y} : Set X) := by
      rw [MonoidHom.map_closure]
      congr 1
      simp [Set.image_insert_eq, Set.image_singleton]
    rw [← hc]
    exact hP.map f.symm.toMonoidHom

theorem kernelTrivialAt_of_mulEquiv {X Y : Type} [Group X] [Group Y] {p : ℕ} (f : X ≃* Y)
    (h : KernelTrivialAt Y p) : KernelTrivialAt X p := by
  intro E _ _ _ π hπ hker hp
  have hk := ker_comp_mulEquiv f π
  have := h E (f.toMonoidHom.comp π) (f.surjective.comp hπ) (by rw [hk]; exact hker)
    (by rw [hk]; exact hp)
  rw [hk] at this
  exact this

theorem coverWeakGen_of_mulEquiv {X Y : Type} [Group X] [Group Y] {p : ℕ} [Fact p.Prime]
    (f : X ≃* Y) (h : CoverWeakGen Y p) : CoverWeakGen X p := by
  intro K _ _ π hπ hker hperf hc hp hcyc T
  exact h K (f.toMonoidHom.comp π) (f.surjective.comp hπ)
    (by rw [ker_comp_mulEquiv f π]; exact hker) hperf hc hp hcyc T

theorem sporCaseThreePrimeData_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X]
    [Finite Y] {p : ℕ} [Fact p.Prime] (f : X ≃* Y) (h : SporCaseThreePrimeData Y p) :
    SporCaseThreePrimeData X p := by
  have hcard : Nat.card X = Nat.card Y := Nat.card_congr f.toEquiv
  rcases h with h1 | ⟨h4, hpair, hkt⟩ | ⟨hG, hk⟩
  · exact Or.inl (by rw [hcard]; exact h1)
  · exact Or.inr (Or.inl ⟨by rw [hcard]; exact h4, hasNoncommPair_of_mulEquiv f hpair,
      kernelTrivialAt_of_mulEquiv f hkt⟩)
  · refine Or.inr (Or.inr ⟨fun T => weakCore_or_klingenAlt_of_mulEquiv f hG T, ?_⟩)
    rcases hk with hkt | hcw
    · exact Or.inl (kernelTrivialAt_of_mulEquiv f hkt)
    · exact Or.inr (coverWeakGen_of_mulEquiv f hcw)

theorem sporadicCaseThreeData_of_mulEquiv {X Y : Type} [Group X] [Group Y] (f : X ≃* Y)
    (h : SporadicCaseThreeData Y) : SporadicCaseThreeData X := by
  refine ⟨fun h0 => h.1 ?_, fun p hp hp2 => ?_⟩
  · rw [← Nat.card_congr f.toEquiv]
    exact h0
  · have : Finite Y := Finite.of_equiv X f.toEquiv
    exact sporCaseThreePrimeData_of_mulEquiv f (h.2 p hp2)

theorem sporadicCaseThreeData_of_monsterPrimes {X : Type} [Group X]
    (hcard : Nat.card X = monsterOrder)
    (h3 : ∀ [Finite X], SporCaseThreePrimeData X 3)
    (h5 : ∀ [Finite X], SporCaseThreePrimeData X 5)
    (h7 : ∀ [Finite X], SporCaseThreePrimeData X 7)
    (h13 : ∀ [Finite X], SporCaseThreePrimeData X 13) :
    SporadicCaseThreeData X := by
  refine ⟨by rw [hcard]; norm_num [monsterOrder], fun p hp hp2 => ?_⟩
  have hpp : p.Prime := hp.out
  by_cases hdvd : p ^ 3 ∣ Nat.card X
  · rw [hcard] at hdvd
    rcases prime_pow_three_dvd_monsterOrder hpp hp2 hdvd with rfl | rfl | rfl | rfl
    · exact h3
    · exact h5
    · exact h7
    · exact h13
  · exact Or.inl hdvd

end CFSG.AGLEmbedding.Norton.OrdinaryProofs

end
