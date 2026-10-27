module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDeduce

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne (centerQuotientConj)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)
open scoped commutatorElement

@[expose] def GenFixes (p : ℕ) {T : Type} [Group T] (α : MulAut T) : Prop :=
  (∃ N₀ : Subgroup T, NonLocalized N₀ ∧
      N₀ ≤ Subgroup.closure {y : T | α y = y ∧ ¬ p ∣ orderOf y}) ∧
    ∃ P : Subgroup T, ⁅P, P⁆ = P ∧ P ≠ ⊥ ∧ ∀ y ∈ P, α y = y

theorem exists_perfect_of_fixed_perfect {Y : Type} [Group Y] (L : Subgroup Y) {x : Y}
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) {P : Subgroup (↥L ⧸ Subgroup.center ↥L)}
    (hP : ⁅P, P⁆ = P) (hP0 : P ≠ ⊥) (hfix : ∀ y ∈ P, centerQuotientConj L ⟨x, hx⟩ y = y) :
    ∃ D : Subgroup Y, D ≤ L ∧ D ≠ ⊥ ∧ ⁅D, D⁆ = D ∧ D ≤ Subgroup.centralizer ({x} : Set Y) := by
  obtain ⟨W, hW, hWmap, hWfix⟩ := exists_perfect_centralizer_lift L hx hP hfix
  refine ⟨W.map L.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨w, -, rfl⟩
    exact w.2
  · intro hbot
    have hW1 : W = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 hbot
    apply hP0
    rw [← hWmap, hW1, Subgroup.map_bot]
  · rw [← Subgroup.map_commutator, hW]
  · rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hWfix w hw
    exact (mul_inv_eq_iff_eq_mul.1 this).symm

theorem lieOutConcl_of_genFixes {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {x : Y} {p : ℕ}
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) (hp : p.Prime) (hxp : x ^ p = 1)
    (hOL : OvergroupLocal (↥L ⧸ Subgroup.center ↥L))
    (hF : GenFixes p (centerQuotientConj L ⟨x, hx⟩)) : LieOutConcl L x := by
  obtain ⟨⟨N₀, hNL, hN₀⟩, P, hP, hP0, hPfix⟩ := hF
  refine ⟨fun J ⟨hJL, T, hT, hNT⟩ hCJ => ?_, fun _ => ?_⟩
  · by_contra hne
    refine not_le_quotImage_of_nonLocalized hOL hT hNT hJL hne hNL (hN₀.trans ?_)
    rw [Subgroup.closure_le]
    rintro y ⟨hy1, hy2⟩
    exact mem_quotImage_of_coprime L J hx hp hxp hCJ hy1
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hy2).symm (pow_orderOf_eq_one y)
  · exact exists_perfect_of_fixed_perfect L hx hP hP0 hPfix

end CFSG.AGLEmbedding.LieOut
