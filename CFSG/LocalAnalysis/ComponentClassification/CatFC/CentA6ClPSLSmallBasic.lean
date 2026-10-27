module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness

public section

namespace CFSG.ComponentClassification.CatFC.PSLSmall

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Basic

variable {S : Type} [Group S] [Finite S] {σ : MulAut S} {D : Subgroup ↥(fixedSubgroup σ)}

theorem _root_.CFSG.ComponentClassification.CatFC.A6Hyp.perfect_D (h : A6Hyp σ D) : ⁅D, D⁆ = D :=
  Subgroup.isPerfect_iff.mp h.component.1.1.1

theorem map_eq_one_of_mem {A : Type*} [CommGroup A] (h : A6Hyp σ D)
    (ψ : ↥(fixedSubgroup σ) →* A) {d : ↥(fixedSubgroup σ)} (hd : d ∈ D) : ψ d = 1 := by
  have h1 : ⁅D, D⁆ ≤ ψ.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
    simp
  have h2 : d ∈ ⁅D, D⁆ := by rw [h.perfect_D]; exact hd
  exact MonoidHom.mem_ker.mp (h1 h2)

theorem not_mem_of_character {A : Type*} [CommGroup A] (h : A6Hyp σ D)
    (ψ : ↥(fixedSubgroup σ) →* A) {x : ↥(fixedSubgroup σ)} (hx : ψ x ≠ 1) : x ∉ D :=
  fun hxD => hx (map_eq_one_of_mem h ψ hxD)

theorem card_eq_720 (h : A6Hyp σ D) (hle : Nat.card (fixedSubgroup σ) ≤ 720)
    {x : ↥(fixedSubgroup σ)} (hx : x ∉ D) : Nat.card (fixedSubgroup σ) = 720 := by
  obtain ⟨m, hm⟩ := h.dvd
  have hpos : 0 < Nat.card (fixedSubgroup σ) := Nat.card_pos
  have hm1 : 1 ≤ m := by omega
  have hm2 : m ≤ 2 := by omega
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · exfalso
    have hm1' : m = 1 := by omega
    have hcard : Nat.card ↥D = Nat.card (fixedSubgroup σ) := by rw [h.card_D, hm, hm1']
    exact hx (by rw [Subgroup.eq_top_of_card_eq D hcard]; exact Subgroup.mem_top x)
  · have hm2' : m = 2 := by omega
    rw [hm, hm2']

@[expose] def OuterEvidence (σ : MulAut S) : Prop :=
  ∃ (x : ↥(fixedSubgroup σ)) (A : Type) (_ : CommGroup A) (ψ : ↥(fixedSubgroup σ) →* A),
    orderOf x = 2 ∧ ψ x ≠ 1

theorem outer_concl (h : A6Hyp σ D) (hev : OuterEvidence σ) (t : StatedLieTag) (n f : ℕ) :
    Nat.card (fixedSubgroup σ) ≤ 720 →
      Nat.card (fixedSubgroup σ) = 720 ∧
        ((∃ x : ↥(fixedSubgroup σ), orderOf x = 2 ∧ x ∉ D) ∨ (t = .PSU ∧ n = 4 ∧ f = 1)) := by
  intro hle
  obtain ⟨x, A, _, ψ, hx2, hψ⟩ := hev
  have hxD := not_mem_of_character h ψ hψ
  exact ⟨card_eq_720 h hle hxD, Or.inl ⟨x, hx2, hxD⟩⟩

theorem smallConcl_of_evidence (h : A6Hyp σ D) (hev : OuterEvidence σ)
    {t : StatedLieTag} {n f : ℕ}
    (hin : σ ∈ (MulAut.conj : S →* MulAut S).range → 1440 < Nat.card (fixedSubgroup σ)) :
    A6SmallConcl t n f σ D :=
  ⟨hin, fun _ hle => outer_concl h hev t n f hle⟩

theorem smallConcl_of_big {t : StatedLieTag} {n f : ℕ}
    (hbig : 1440 < Nat.card (fixedSubgroup σ)) : A6SmallConcl t n f σ D :=
  ⟨fun _ => hbig, fun _ hle => absurd hle (by omega)⟩

end Basic

@[expose] def SmallStmt (t : StatedLieTag) (n f : ℕ) {S : Type} [Group S] (σ : MulAut S) : Prop :=
  ∀ D : Subgroup ↥(fixedSubgroup σ), A6Hyp σ D → A6SmallConcl t n f σ D

theorem SmallStmt.of_eq {t : StatedLieTag} {n f : ℕ} {S : Type} [Group S] {σ τ : MulAut S}
    (hστ : σ = τ) (h : SmallStmt t n f τ) : SmallStmt t n f σ := by
  subst hστ; exact h

end CFSG.ComponentClassification.CatFC.PSLSmall
