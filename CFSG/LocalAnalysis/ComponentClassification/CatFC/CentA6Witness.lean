module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Classify
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofGLS3Split

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Witness

variable {S : Type} [Group S] [Finite S] {σ : MulAut S} {D : Subgroup ↥(fixedSubgroup σ)}

theorem A6Hyp.card_D (h : A6Hyp σ D) : Nat.card ↥D = 360 := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  rw [Nat.card_congr e.toEquiv, a6sq_card]

theorem A6Hyp.dvd (h : A6Hyp σ D) : 360 ∣ Nat.card (fixedSubgroup σ) := by
  have := Subgroup.card_subgroup_dvd_card D
  rwa [h.card_D] at this

theorem A6Hyp.perfect_card_le (h : A6Hyp σ D) {P : Subgroup ↥(fixedSubgroup σ)}
    (hP : ⁅P, P⁆ = P) : Nat.card ↥P ≤ 360 := by
  have := Subgroup.card_le_of_le (h.2.2 P hP)
  rwa [h.card_D] at this

theorem A6Hyp.range_card_le (h : A6Hyp σ D) {Q : Type} [Group Q]
    (φ : Q →* ↥(fixedSubgroup σ)) (hQ : commutator Q = ⊤) : Nat.card ↥φ.range ≤ 360 := by
  apply h.perfect_card_le
  have h1 : φ.range = Subgroup.map φ ⊤ := MonoidHom.range_eq_map φ
  have h2 : commutator Q = ⁅(⊤ : Subgroup Q), ⊤⁆ := rfl
  rw [h2] at hQ
  rw [h1, ← Subgroup.map_commutator, hQ]

theorem A6Hyp.perfect_card_le_mul (h : A6Hyp σ D) {Q : Type} [Group Q] [Finite Q]
    (φ : Q →* ↥(fixedSubgroup σ)) (hQ : commutator Q = ⊤) {k : ℕ} (hk : Nat.card ↥φ.ker ≤ k) :
    Nat.card Q ≤ 360 * k := by
  have h1 := h.range_card_le φ hQ
  have h2 : Nat.card Q = Nat.card ↥φ.range * Nat.card ↥φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  rw [h2]
  exact Nat.mul_le_mul h1 hk

theorem A6Hyp.perfect_witness (h : A6Hyp σ D) {Q : Type} [Group Q] [Finite Q]
    (φ : Q →* ↥(fixedSubgroup σ)) (hQ : commutator Q = ⊤) {k : ℕ} (hk : Nat.card ↥φ.ker ≤ k)
    (hbig : 360 * k < Nat.card Q) : False :=
  absurd (h.perfect_card_le_mul φ hQ hk) (not_le.2 hbig)

theorem A6Hyp.not_solvable (h : A6Hyp σ D) : ¬ Group.IsSolvable ↥(fixedSubgroup σ) := by
  intro hs
  obtain ⟨-, ⟨e⟩, -⟩ := h
  haveI := hs
  have h1 : Group.IsSolvable ↥D := Group.isSolvable_of_isSolvable_injective D.subtype_injective
  have h2 : Group.IsSolvable (alternatingGroup (Fin 6)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  haveI := a6sq_simple
  obtain ⟨a, b, hab⟩ := a6sq_nonab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 h2) a b)

theorem A6Hyp.component (h : A6Hyp σ D) :
    IsComponent D ∧ Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨hDn, ⟨eD⟩, -⟩ := h
  haveI := a6sq_simple
  have hq : CFSG.IsQuasisimple ↥D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eD.symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup a6sq_nonab).1
  refine ⟨⟨hq, Subgroup.Normal.isSubnormal hDn⟩, ⟨?_⟩⟩
  exact (quotientCenterEquiv eD).trans
    ((QuotientGroup.quotientMulEquivOfEq a6sq_center).trans QuotientGroup.quotientBot)

theorem A6Hyp.char_three (h : A6Hyp σ D) (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {t : StatedLieTag} (hgls : CFSG.ComponentClassification.CatLeafProof.GLS3OddFamilyInput t)
    {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hm : LieModel S t n p f) (hσ : orderOf σ = 2) : p = 3 := by
  obtain ⟨hD, hDZ⟩ := h.component
  rcases hgls S n p f hp hp2 hadm hm σ hσ D hD with ⟨τ', n', f', hadm', hmod'⟩ | ⟨h3, -, -, -⟩
  · exact (a6sq_lieModel_a6 hO hDZ hadm' hp2 hmod').2.2.1
  · exact h3

end Witness

end CFSG.ComponentClassification.CatFC
