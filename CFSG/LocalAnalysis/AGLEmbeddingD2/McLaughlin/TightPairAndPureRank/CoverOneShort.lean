module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycGroup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTits
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding.BlockCyc CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.Open CFSG.HallHigman
open scoped commutatorElement

section Torus

variable {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem commute_of_card_le_two {X : Subgroup K} (hX : Nat.card X ≤ 2) {h : K}
    (hn : ∀ x ∈ X, h * x * h⁻¹ ∈ X) : ∀ x ∈ X, h * x = x * h := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]; simp
  have hy : h * x * h⁻¹ ∈ X := hn x hx
  have hy1 : h * x * h⁻¹ ≠ 1 := fun e => hx1 (by
    have := congrArg (fun z => h⁻¹ * z * h) e
    simpa [mul_assoc] using this)
  by_contra hne
  have hne' : h * x * h⁻¹ ≠ x := fun e => hne (by
    have := congrArg (fun z => z * h) e
    simpa [mul_assoc] using this)
  have hcard : 3 ≤ Nat.card X := by
    have hsub : ({1, x, h * x * h⁻¹} : Set K) ⊆ (X : Set K) := by
      intro z hz
      rcases hz with rfl | rfl | rfl
      · exact X.one_mem
      · exact hx
      · exact hy
    have h3 : ({1, x, h * x * h⁻¹} : Set K).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair hne'.symm]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Ne.symm hx1, Ne.symm hy1⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h3] at this
    have e : Nat.card X = (X : Set K).ncard := Nat.card_coe_set_eq (X : Set K)
    omega
  omega

section TorusCentral

variable {Y : Type} [Group Y] {π : K →* Y} {M : ℕ}

theorem card_le_two_of_isPGroup_two {L X : Subgroup K} (h6 : Nat.card L = 6) (hXL : X ≤ L)
    (hX : IsPGroup 2 X) : Nat.card X ≤ 2 := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hX
  have hd : 2 ^ a ∣ 6 := by rw [← ha, ← h6]; exact Subgroup.card_dvd_of_le hXL
  by_contra hlt
  have : 2 ≤ a := by
    by_contra ha2
    have h1 : a ≤ 1 := by omega
    have : 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have h4 : 4 ∣ 2 ^ a := by
    have := pow_dvd_pow 2 this
    simpa using this
  have := h4.trans hd
  omega

theorem torus_centralizes_rankOne_of_card_six (h : BorelQuotient D n H π M) {j : Fin D.rank}
    (h6 : Nat.card (rankOne D.rootGroup j) = 6) {k : Fin D.rank} {t : K} (ht : t ∈ H k) :
    ∀ g ∈ rankOne D.rootGroup j, t * g = g * t := by
  have hα : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
  have hα' : (-Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  have hX : ∀ γ ∈ D.roots, D.rootGroup γ ≤ rankOne D.rootGroup j → ∀ x ∈ D.rootGroup γ,
      t * x = x * t := by
    intro γ hγ hle
    have hc := card_le_two_of_isPGroup_two h6 hle (h.pGroup γ hγ)
    refine commute_of_card_le_two hc fun x hx => ?_
    exact h.ct.H_conj_mem k γ hγ t ht x hx
  have hle : rankOne D.rootGroup j ≤ Subgroup.centralizer ({t} : Set K) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hX _ hα le_sup_left x hx
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hX _ hα' le_sup_right x hx
  intro g hg
  have := Subgroup.mem_centralizer_iff.1 (hle hg) t (Set.mem_singleton t)
  exact this

end TorusCentral

end Torus

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
