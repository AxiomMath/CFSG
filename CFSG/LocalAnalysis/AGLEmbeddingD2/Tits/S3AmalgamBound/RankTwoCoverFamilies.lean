module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviFam
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg

variable {K Y : Type} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y}

theorem borelQuotient_injective_of_one (h : BorelQuotient D n H π 1) : Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have := h.ker_pow z hz
  rwa [pow_one] at this

theorem borelQuotient_torus_eq_bot_of_one (h : BorelQuotient D n H π 1) (k : Fin D.rank) :
    H k = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have := h.torus_pow k g hg
  rwa [pow_one] at this

theorem hasOrderThree_data {k : Fin D.rank} (h3 : HasOrderThree D k) :
    ∃ x ∈ D.rootGroup (Pi.single k 1), ∃ y ∈ D.rootGroup (-Pi.single k 1),
      (x * y) ^ 3 = 1 ∧ x * y ≠ 1 := by
  obtain ⟨x, hx, y, hy, h3', c, hc⟩ := h3
  exact ⟨x, hx, y, hy, h3', fun h1 => hc (by rw [h1, one_mul, mul_one])⟩

theorem not_isPSolvable_map_of_injective [Finite K] [Finite Y] (hπ : Function.Injective π)
    {S : Subgroup K} (hS : ¬ CFSG.HallHigman.IsPSolvable 3 ↥S) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(S.map π) := fun hsolv =>
  hS (OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    (Subgroup.equivMapOfInjective S π hπ).symm hsolv)

theorem exists_pair_of_three {ι : Type*} (a b c : ι) (P : ι → ι → Prop) (hab : P a b)
    (hac : P a c) (hbc : P b c) (col : ι → Bool) :
    ∃ i j, col i = col j ∧ P i j ∧ ((i = a ∧ j = b) ∨ (i = a ∧ j = c) ∨ (i = b ∧ j = c)) := by
  cases h1 : col a <;> cases h2 : col b <;> cases h3 : col c
  all_goals first
    | exact ⟨a, b, h1.trans h2.symm, hab, Or.inl ⟨rfl, rfl⟩⟩
    | exact ⟨a, c, h1.trans h3.symm, hac, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | exact ⟨b, c, h2.trans h3.symm, hbc, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

section Six

variable [Finite K]

theorem card_rankOne_eq_six {k : Fin D.rank} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {x : (Fin D.rank → ℤ) → F → K}
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x)
    {φ : Matrix.SpecialLinearGroup (Fin 2) F →* K} (hφ : Function.Injective φ)
    (hU : ∀ c, φ (sl2Upper c) = x (Pi.single k 1) c)
    (hL : ∀ c, φ (sl2Lower c) = x (-Pi.single k 1) c) :
    Nat.card (rankOne D.rootGroup k) = 6 := by
  have hdvd := card_rankOne_dvd_six_of_sl2 hF hx hU hL
  have hα : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k
  have hα' : (-Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  have hle : φ.range ≤ rankOne D.rootGroup k := by
    rintro _ ⟨A, rfl⟩
    have hA := Sp.mem_closure_sl2 A
    have hcl : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
        (rankOne D.rootGroup k).comap φ := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, hU c]
        exact le_sup_left (a := D.rootGroup (Pi.single k 1)) (((hx _ hα).1 _).2 ⟨c, rfl⟩)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, hL c]
        exact le_sup_right (b := D.rootGroup (-Pi.single k 1)) (((hx _ hα').1 _).2 ⟨c, rfl⟩)
    exact hcl hA
  have h6 : 6 ∣ Nat.card (rankOne D.rootGroup k) := by
    have h1 := Subgroup.card_dvd_of_le hle
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, card_sl2, hF] at h1
    simpa using h1
  exact Nat.dvd_antisymm hdvd h6

end Six

theorem sq_eq_one_of_isParametrization {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι}
    {k : Type} [Field k] [CharP k 2] {G : Type} [Group G] {X : (ι → ℤ) → Subgroup G}
    {x : (ι → ℤ) → k → G} (hx : IsParametrization (Φ := Φ) X x) {γ : ι → ℤ}
    (hγ : γ ∈ Φ.roots) {g : G} (hg : g ∈ X γ) : g ^ 2 = 1 := by
  obtain ⟨c, rfl⟩ := ((hx γ hγ).1 g).1 hg
  rw [sq, ← (hx γ hγ).2.1 c c, CharTwo.add_self_eq_zero]
  have := (hx γ hγ).2.1 0 0
  rw [add_zero] at this
  exact mul_left_cancel (a := x γ (0 : k)) (by rw [mul_one]; exact this.symm)

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
