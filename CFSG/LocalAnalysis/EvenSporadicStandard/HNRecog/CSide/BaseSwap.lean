module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Factors
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Free.Wreath
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.BaseLe

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog.Fpf
  CFSG.EvenSporadicStandard.HNRecog

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]

theorem WeakHyp.index_commutator [Finite C] (hC : WeakHyp C Q) : (commutator C).index = 2 := by
  let π : C →* C ⧸ Q := QuotientGroup.mk' Q
  let e : C ⧸ Q ≃* A5WrTwo := hC.quotient.some
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hker : π.ker = Q := QuotientGroup.ker_mk' Q
  have hmapC : (commutator C).map π = commutator (C ⧸ Q) := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π hπ]
    rfl
  have hindexC : ((commutator C).map π).index = (commutator C).index :=
    Subgroup.index_map_eq (H := commutator C) (f := π) hπ (by
      rw [hker]; exact WeakHyp.le_commutator hC)
  have hmape : (commutator (C ⧸ Q)).map (e : C ⧸ Q →* A5WrTwo) = commutator A5WrTwo := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective (e : C ⧸ Q →* A5WrTwo) e.surjective]
    rfl
  calc (commutator C).index
      = ((commutator C).map π).index := hindexC.symm
    _ = (commutator (C ⧸ Q)).index := by rw [hmapC]
    _ = ((commutator (C ⧸ Q)).map (e : C ⧸ Q →* A5WrTwo)).index :=
          (Subgroup.index_map_equiv (H := commutator (C ⧸ Q)) e).symm
    _ = (commutator A5WrTwo).index := by rw [hmape]
    _ = 2 := A5WrTwo.index_commutator

variable [Module (ZMod 2) (Additive (Abelianization Q))]

theorem CSideSetup.exists_swap (S : CSideSetup C Q) (hQL : Q ≤ commutator C) {t : C}
    (ht : t ∉ commutator C) (ht2 : (t : C ⧸ Q) ^ 2 = 1) :
    ∃ s : A5 × A5 ≃* A5 × A5, Swap.SwapsFactorsAut s ∧
      ∀ g : A5 × A5, conjLinEquiv hQn t * S.σ g * (conjLinEquiv hQn t)⁻¹ = S.σ (s g) := by
  classical
  let u : A5WrTwo := S.e (QuotientGroup.mk t)
  have hu2 : u ^ 2 = 1 := by
    have ht2' : (QuotientGroup.mk' Q t : C ⧸ Q) ^ 2 = 1 := ht2
    have h : u = S.e (QuotientGroup.mk' Q t) := rfl
    rw [h, ← map_pow, ht2', map_one]
  have hu : u ∉ commutator A5WrTwo := by
    rw [← A5WrTwo.range_baseEmb]
    rintro ⟨g, hg⟩
    obtain ⟨l, hl⟩ := S.surj g
    have heq : S.e (QuotientGroup.mk (l : C)) = S.e (QuotientGroup.mk t) := by
      rw [← S.emb l, hl, hg]
    have hmk : (QuotientGroup.mk (l : C) : C ⧸ Q) = QuotientGroup.mk t := S.e.injective heq
    have hmem : (l : C)⁻¹ * t ∈ Q := QuotientGroup.eq.mp hmk
    have htL : t ∈ commutator C := by
      have h1 : (l : C) * ((l : C)⁻¹ * t) ∈ commutator C :=
        (commutator C).mul_mem l.2 (hQL hmem)
      simpa using h1
    exact ht htL
  obtain ⟨x₀, hx₀⟩ := A5WrTwo.exists_conj_baseEmb hu hu2
  let s : A5 × A5 ≃* A5 × A5 :=
    { toFun := fun p => (x₀ * p.2 * x₀⁻¹, x₀⁻¹ * p.1 * x₀)
      invFun := fun p => (x₀ * p.2 * x₀⁻¹, x₀⁻¹ * p.1 * x₀)
      left_inv := fun p => by apply Prod.ext <;> group
      right_inv := fun p => by apply Prod.ext <;> group
      map_mul' := fun p q => by
        apply Prod.ext <;> simp only [Prod.fst_mul, Prod.snd_mul] <;> group }
  have hs : Swap.SwapsFactorsAut s := by
    unfold Swap.SwapsFactorsAut
    constructor
    · intro x
      exact ⟨x₀⁻¹ * x * x₀, by apply Prod.ext <;> simp [s]⟩
    · intro y
      exact ⟨x₀ * y * x₀⁻¹, by apply Prod.ext <;> simp [s]⟩
  have hkey : ∀ l : ↥(commutator C),
      S.θ ⟨t * (l : C) * t⁻¹,
          (inferInstance : (commutator C).Normal).conj_mem (l : C) l.2 t⟩ = s (S.θ l) := by
    intro l
    apply A5WrTwo.baseEmb_injective
    have hΦ : S.e (QuotientGroup.mk (t * (l : C) * t⁻¹)) =
        u * S.e (QuotientGroup.mk (l : C)) * u⁻¹ := by
      have hq : (QuotientGroup.mk (t * (l : C) * t⁻¹) : C ⧸ Q) =
          QuotientGroup.mk t * QuotientGroup.mk (l : C) * (QuotientGroup.mk t)⁻¹ := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hq, map_mul, map_mul, map_inv]
    rw [S.emb, hΦ, ← S.emb l]
    simpa [s] using hx₀ (S.θ l).1 (S.θ l).2
  have hrel : ∀ g : A5 × A5,
      conjLinEquiv hQn t * S.σ g * (conjLinEquiv hQn t)⁻¹ = S.σ (s g) := by
    intro g
    obtain ⟨l, hl⟩ := S.surj g
    let l' : ↥(commutator C) :=
      ⟨t * (l : C) * t⁻¹,
        (inferInstance : (commutator C).Normal).conj_mem (l : C) l.2 t⟩
    have hθl' : S.θ l' = s (S.θ l) := hkey l
    calc conjLinEquiv hQn t * S.σ g * (conjLinEquiv hQn t)⁻¹
        = conjLinEquiv hQn t * S.σ (S.θ l) * (conjLinEquiv hQn t)⁻¹ := by rw [hl]
      _ = conjLinEquiv hQn t * conjLinEquiv hQn (l : C) *
            (conjLinEquiv hQn t)⁻¹ := by rw [S.sigma_eq l]
      _ = conjLinEquiv hQn (t * (l : C) * t⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = conjLinEquiv hQn (l' : C) := by
            rw [show (l' : C) = t * (l : C) * t⁻¹ from rfl]
      _ = S.σ (S.θ l') := by rw [S.sigma_eq l']
      _ = S.σ (s (S.θ l)) := by rw [hθl']
      _ = S.σ (s g) := by rw [hl]
  exact ⟨s, hs, hrel⟩

end CFSG.EvenSporadicStandard.HNRecog.CSide
