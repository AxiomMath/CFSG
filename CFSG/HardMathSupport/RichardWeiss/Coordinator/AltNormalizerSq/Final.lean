module

public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.Pair
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.Quad
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.Eight
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.PerfectCyclic
public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocksAux
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBDefs

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.HardMathSupport.Cooperstein

variable {G : Type} [Group G]

theorem sq_of_relIndex_le {M L : Subgroup G} {p : ℕ} {U : Subgroup G}
    (h : (U ⊓ blockCentralizer M L).relIndex U ≤ p) :
    ∃ U₁ U₂ : Subgroup G, U₁ ≤ U ∧ U₂ ≤ U ∧ U₁ ⊓ U₂ ≤ blockCentralizer M L ∧
      U₁.relIndex U ≤ p ∧ U₂.relIndex U ≤ p ∧
      ∀ y ∈ M, y ∈ Subgroup.normalizer (L : Set G) → y ∈ Subgroup.normalizer (U : Set G) →
        y ∈ Subgroup.normalizer (U₁ : Set G) ∧ y ∈ Subgroup.normalizer (U₂ : Set G) := by
  refine ⟨U ⊓ blockCentralizer M L, U ⊓ blockCentralizer M L, inf_le_left, inf_le_left,
    inf_le_right.trans' (inf_le_left), h, h, fun y hyM hyL hyU => ?_⟩
  have := mem_normalizer_inf hyU (mem_normalizer_blockCentralizer hyM hyL)
  exact ⟨this, this⟩

theorem false_of_quotient_alt_seven {Q : Type*} [Group Q] {m : ℕ} (hm : 10 ≤ m)
    (e : (Q ⧸ Subgroup.center Q) ≃* alternatingGroup (Fin m))
    (e7 : Q ≃* alternatingGroup (Fin 7)) : False := by
  have h1 : Nat.card (Q ⧸ Subgroup.center Q) ∣ Nat.card Q := by
    rw [← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_card _
  have hQ : Nat.card Q = Nat.card (alternatingGroup (Fin 7)) := Nat.card_congr e7.toEquiv
  have hq : Nat.card (Q ⧸ Subgroup.center Q) = Nat.card (alternatingGroup (Fin m)) :=
    Nat.card_congr e.toEquiv
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h7 : 2 * Nat.card (alternatingGroup (Fin 7)) = Nat.factorial 7 := by
    rw [two_mul_nat_card_alternatingGroup (α := Fin 7), Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hm' : 2 * Nat.card (alternatingGroup (Fin m)) = Nat.factorial m := by
    rw [two_mul_nat_card_alternatingGroup (α := Fin m), Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hpos : 0 < Nat.card Q := by
    rw [hQ]
    exact Nat.card_pos
  have hle := Nat.le_of_dvd hpos h1
  rw [hq, hQ] at hle
  have hfac : Nat.factorial 10 ≤ Nat.factorial m := Nat.factorial_le hm
  have h10 : Nat.factorial 10 = 3628800 := by decide
  have h7' : Nat.factorial 7 = 5040 := by decide
  omega

theorem altNormalizerSq_of_eightTen_large [Finite G]
    (h810 : AlternatingGeometry.Asc81bEightTen)
    {M S L : Subgroup G} {p : ℕ} (hK : CFSG.Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hX1 : ¬ InClassXBlock L)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hJ : PerfectCyclicSylow p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
    {m : ℕ} (hm : 10 ≤ m)
    (hdeg : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m)))
    {U : Subgroup G} (hUK : U ≤ M ⊓ Subgroup.normalizer (S : Set G))
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) (hUp : IsPGroup p U) :
    ∃ U₁ U₂ : Subgroup G, U₁ ≤ U ∧ U₂ ≤ U ∧ U₁ ⊓ U₂ ≤ blockCentralizer M L ∧
      U₁.relIndex U ≤ p ∧ U₂.relIndex U ≤ p ∧
      ∀ y ∈ M ⊓ Subgroup.normalizer (S : Set G), y ∈ Subgroup.normalizer (L : Set G) →
        y ∈ Subgroup.normalizer (U : Set G) →
        y ∈ Subgroup.normalizer (U₁ : Set G) ∧ y ∈ Subgroup.normalizer (U₂ : Set G) := by
  obtain ⟨e⟩ := hdeg
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    Cooperstein.Coordinator.le_normalizer_of_isWeakSBlock hK hA hL
  have hUM : U ≤ M := fun u hu => (hUK hu).1
  have hUS : U ≤ Subgroup.normalizer (S : Set G) := fun u hu => (hUK hu).2
  have hlt : ∀ (k : ℕ)
      (ρ : ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →* Perm (Fin k)),
      Function.Surjective ρ → k < 2 * p := fun k ρ hρ =>
    lt_two_mul_of_perfect_cyclic hp hp2 hJ ρ hρ
  have e' : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃*
      alternatingGroup (Fin m) :=
    (Cooperstein.Coordinator.barMSupCenterEquiv hA hL hSL).symm.trans e
  have hmain := h810 G M S L hK hA hL hSL m (Or.inr (by omega)) ⟨e'⟩
  rcases hmain with h1 | ⟨h5, -⟩ | ⟨n, hn, hd, -⟩ | ⟨n, hn, hd, -⟩ |
    ⟨N, r, hN, hr2, hr1, hr, hs, hD, -, -⟩
  · exact absurd h1 hX1
  · obtain ⟨-, ⟨e7⟩, -⟩ := h5
    exact (false_of_quotient_alt_seven hm e' e7).elim
  · obtain ⟨φ, hE, hB⟩ := pair_data_at_M hA hL hSL (by omega) hd
    have h := pair_case hp hp2 hn hlt φ hE hB hUM hUS hUL hUp
    obtain ⟨U₁, U₂, a, b, c, d, f, g⟩ := sq_of_relIndex_le h
    exact ⟨U₁, U₂, a, b, c, d, f, fun y hy hyL hyU => g y hy.1 hyL hyU⟩
  · obtain ⟨φ, hB⟩ := quad_data_at_M hA hL hSL hd
    have h := quad_case hp hp2 hn hlt φ hB hUM hUS hUL hUp
    obtain ⟨U₁, U₂, a, b, c, d, f, g⟩ := sq_of_relIndex_le h
    exact ⟨U₁, U₂, a, b, c, d, f, fun y hy hyL hyU => g y hy.1 hyL hyU⟩
  · exact eight_case hp hp2 hr1 (by omega) hlt hD hUM hUS hUL hUp

end CFSG.HardMathSupport.RichardWeiss.Coordinator
