module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def InnGoodAt (p : ℕ) (d : TauCeti.LieTypeIndex) (S : Type) [Group S] : Prop :=
  ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 2 → D ≤ innAutDerived S →
    (∃ β ∈ D, β ≠ 1 ∧ ∃ P : Subgroup S, P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P) ∨
      (lpEpsIdx p d ∧ innAutDerived S ⊓ Subgroup.centralizer (D : Set (MulAut S)) = D)

theorem innGoodAt_of_forall_card_ne {p : ℕ} {d : TauCeti.LieTypeIndex} {S : Type} [Group S]
    (h : ∀ D : Subgroup (MulAut S), IsElemAbelian p D → D ≤ innAutDerived S →
      Nat.card D ≠ p ^ 2) :
    InnGoodAt p d S :=
  fun D hD hcard hle => absurd hcard (h D hD hle)

theorem innGoodAt_of_mulEquiv {p : ℕ} {d : TauCeti.LieTypeIndex} {S S' : Type} [Group S]
    [Group S'] (e : S ≃* S') (h : InnGoodAt p d S) : InnGoodAt p d S' := by
  intro D' hD' hcard hle
  let c : MulAut S ≃* MulAut S' := MulAut.congr e
  let D : Subgroup (MulAut S) := D'.map (c.symm : MulAut S' →* MulAut S)
  have hmemD : ∀ x : MulAut S', c.symm x ∈ D ↔ x ∈ D' := fun x =>
    Subgroup.mem_map_equiv.trans (by simp)
  have hinn : ∀ x : MulAut S', c.symm x ∈ innAutDerived S ↔ x ∈ innAutDerived S' := fun x => by
    rw [← mem_innAutDerived_congr e]
    exact Iff.of_eq (congrArg (· ∈ innAutDerived S') (c.apply_symm_apply x))
  have hDel : IsElemAbelian p D := hD'.map _
  have hDcard : Nat.card D = p ^ 2 := by
    rw [← hcard]
    exact Subgroup.card_map_of_injective c.symm.injective
  have hDle : D ≤ innAutDerived S := by
    intro x hx
    rw [← c.symm_apply_apply x] at hx ⊢
    exact (hinn _).2 (hle ((hmemD _).1 hx))
  rcases h D hDel hDcard hDle with ⟨β, hβD, hβ1, P, hPfix, hPperf, hPdvd⟩ | ⟨hlp, hcent⟩
  · left
    refine ⟨c β, ?_, fun h1 => hβ1 (c.injective (h1.trans (map_one c).symm)),
      P.map (e : S →* S'), ?_, ?_, ?_⟩
    · rw [← c.symm_apply_apply β] at hβD
      exact (hmemD _).1 hβD
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_fixSubgroup]
      have hy' : β y = y := hPfix hy
      change e (β (e.symm (e y))) = e y
      rw [e.symm_apply_apply, hy']
    · rw [← Subgroup.map_commutator, hPperf]
    · rw [Subgroup.card_map_of_injective e.injective]
      exact hPdvd
  · right
    refine ⟨hlp, ?_⟩
    ext x
    have hcomm : x ∈ Subgroup.centralizer (D' : Set (MulAut S')) ↔
        c.symm x ∈ Subgroup.centralizer (D : Set (MulAut S)) := by
      simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe]
      constructor
      · intro hx y hy
        rw [← c.symm_apply_apply y] at hy ⊢
        have := hx _ ((hmemD _).1 hy)
        rw [← map_mul, ← map_mul, this]
      · intro hx y hy
        have := hx (c.symm y) ((hmemD y).2 hy)
        rw [← map_mul, ← map_mul] at this
        exact c.symm.injective this
    rw [Subgroup.mem_inf, hcomm, ← hinn, ← Subgroup.mem_inf, hcent, hmemD]

@[expose] def LieInnGood (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ¬ (p = 3 ∧ ov2Idx d.1) → ¬ (p = 5 ∧ d.1 = .tits) → P d.1 →
      InnGoodAt p d.1 (TauCeti.CFSGIndex.lie d).Group

theorem kd264InnGood_iff : KD264InnGood ↔ LieInnGood fun _ => True :=
  ⟨fun h d p hp hp2 hpc h3 h5 _ => h d p hp hp2 hpc h3 h5,
    fun h d p hp hp2 hpc h3 h5 => h d p hp hp2 hpc h3 h5 trivial⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
