module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpCent
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent)

section Witness

variable {S : Type} [Group S] [Finite S] {σ : MulAut S} {D : Subgroup ↥(fixedSubgroup σ)}

theorem A6Hyp.range_le (h : A6Hyp σ D) {Q : Type} [Group Q] (φ : Q →* ↥(fixedSubgroup σ))
    (hQ : commutator Q = ⊤) : φ.range ≤ D := by
  apply h.2.2
  have h1 : φ.range = Subgroup.map φ ⊤ := MonoidHom.range_eq_map φ
  have h2 : commutator Q = ⁅(⊤ : Subgroup Q), ⊤⁆ := rfl
  rw [h2] at hQ
  rw [h1, ← Subgroup.map_commutator, hQ]

theorem A6Hyp.perfect_dvd (h : A6Hyp σ D) {Q : Type} [Group Q] [Finite Q]
    (φ : Q →* ↥(fixedSubgroup σ)) (hQ : commutator Q = ⊤) (hk : Nat.card ↥φ.ker ≤ 2) :
    Nat.card Q ∣ 720 := by
  have h1 : Nat.card ↥φ.range ∣ 360 := by
    have := Subgroup.card_dvd_of_le (h.range_le φ hQ)
    rwa [h.card_D] at this
  have h2 : Nat.card Q = Nat.card ↥φ.range * Nat.card ↥φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have h3 : 0 < Nat.card ↥φ.ker := Nat.card_pos
  rw [h2]
  have h4 : Nat.card ↥φ.ker = 1 ∨ Nat.card ↥φ.ker = 2 := by omega
  rcases h4 with h4 | h4 <;> rw [h4]
  · rw [mul_one]
    exact h1.trans (by norm_num)
  · have := Nat.mul_dvd_mul h1 (dvd_refl 2)
    simpa using this

theorem A6Hyp.range_eq (h : A6Hyp σ D) {Q : Type} [Group Q] [Finite Q]
    (φ : Q →* ↥(fixedSubgroup σ)) (hQ : commutator Q = ⊤) (hker : φ.ker ≤ center Q)
    (hcard : 360 ≤ Nat.card (Q ⧸ center Q)) : φ.range = D := by
  have hle := h.range_le φ hQ
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [h.card_D]
  have h2 : Nat.card Q = Nat.card ↥φ.range * Nat.card ↥φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have h3 : Nat.card Q = Nat.card (Q ⧸ center Q) * Nat.card ↥(center Q) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q)]
  have h4 : Nat.card ↥φ.ker ≤ Nat.card ↥(center Q) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hker)
  have h5 : 0 < Nat.card ↥φ.ker := Nat.card_pos
  by_contra hlt
  push_neg at hlt
  have h6 : Nat.card ↥φ.range * Nat.card ↥φ.ker < 360 * Nat.card ↥φ.ker :=
    Nat.mul_lt_mul_of_pos_right hlt h5
  have h7 : 360 * Nat.card ↥(center Q) ≤ Nat.card (Q ⧸ center Q) * Nat.card ↥(center Q) :=
    Nat.mul_le_mul_right _ hcard
  have h8 : 360 * Nat.card ↥φ.ker ≤ 360 * Nat.card ↥(center Q) := Nat.mul_le_mul_left _ h4
  omega

end Witness

section SpCent

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spCentFix (A : gsp r K) : spCent r K A →* fixedSubgroup (conjAut r K A) where
  toFun g := ⟨proj r K g.1, by
    have hg : conjSp r K A g.1 = g.1 := g.2
    change conjAut r K A (proj r K g.1) = proj r K g.1
    rw [conjAut_proj, hg]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g g' := Subtype.ext (map_mul _ _ _)

theorem spCentFix_eq_one_iff (A : gsp r K) (g : spCent r K A) :
    spCentFix A g = 1 ↔ g.1 ∈ (proj r K).ker := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem ker_proj_le_center : (proj r K).ker ≤ center (StatedSp r K) := by
  rw [ker_proj]
  intro z hz
  rw [Subgroup.mem_subgroupOf, StatedScalars,
    ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp hz g)

variable [Finite K]

theorem card_ker_proj_le (hr : 1 ≤ r) : Nat.card ↥(proj r K).ker ≤ 2 := by
  rw [ker_proj]
  have := card_spScalars_eq_gcd K hr
  rw [this]
  exact Nat.gcd_le_left _ (by norm_num)

theorem card_ker_spCentFix_le (hr : 1 ≤ r) (A : gsp r K) :
    Nat.card ↥(spCentFix A).ker ≤ 2 := by
  refine le_trans (Nat.card_le_card_of_injective
    (fun g : ↥(spCentFix A).ker => (⟨g.1.1, (spCentFix_eq_one_iff A g.1).1 g.2⟩ :
      ↥(proj r K).ker)) ?_) (card_ker_proj_le hr)
  intro g g' hg
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ↥(proj r K).ker => z.1) hg

end SpCent

@[expose] def PerfectBig3 (G : Type) [Group G] : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (ι : Q →* G), Function.Injective ι ∧
    commutator Q = ⊤ ∧ 27 ∣ Nat.card Q

@[expose] def Perfect360 (G : Type) [Group G] : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (ι : Q →* G), Function.Injective ι ∧
    commutator Q = ⊤ ∧ Nat.card (Q ⧸ center Q) = 360

theorem PerfectBig3.of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : PerfectBig3 G) : PerfectBig3 G' := by
  obtain ⟨Q, _, _, ι, hι, hQ, h27⟩ := h
  exact ⟨Q, inferInstance, inferInstance, e.toMonoidHom.comp ι, e.injective.comp hι, hQ, h27⟩

theorem Perfect360.of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : Perfect360 G) : Perfect360 G' := by
  obtain ⟨Q, _, _, ι, hι, hQ, h360⟩ := h
  exact ⟨Q, inferInstance, inferInstance, e.toMonoidHom.comp ι, e.injective.comp hι, hQ, h360⟩

section Consequences

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem card_ker_comp_spCentFix_le (hr : 1 ≤ r) (A : gsp r K) {Q : Type} [Group Q]
    (ι : Q →* spCent r K A) (hι : Function.Injective ι) :
    Nat.card ↥((spCentFix A).comp ι).ker ≤ 2 := by
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : ↥((spCentFix A).comp ι).ker =>
      (⟨ι x.1, x.2⟩ : ↥(spCentFix A).ker)) ?_) (card_ker_spCentFix_le hr A)
  intro x x' hx
  apply Subtype.ext
  exact hι (congrArg (fun z : ↥(spCentFix A).ker => z.1) hx)

theorem ker_comp_spCentFix_le_center (A : gsp r K) {Q : Type} [Group Q]
    (ι : Q →* spCent r K A) (hι : Function.Injective ι) :
    ((spCentFix A).comp ι).ker ≤ center Q := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro q
  have h1 : (ι x).1 ∈ (proj r K).ker := (spCentFix_eq_one_iff A (ι x)).1 hx
  have h2 := Subgroup.mem_center_iff.1 (ker_proj_le_center h1) (ι q).1
  apply hι
  rw [map_mul, map_mul]
  exact Subtype.ext h2

variable {A : gsp r K}
  {D : Subgroup ↥(fixedSubgroup (conjAut r K A))}

theorem A6Hyp.false_of_perfectBig3 (hr : 1 ≤ r) (h : A6Hyp (conjAut r K A) D)
    (hP : PerfectBig3 (spCent r K A)) : False := by
  obtain ⟨Q, _, _, ι, hι, hQ, h27⟩ := hP
  have := h.perfect_dvd ((spCentFix A).comp ι) hQ (card_ker_comp_spCentFix_le hr A ι hι)
  have h2 := h27.trans this
  revert h2
  norm_num

theorem A6Hyp.exists_map_eq_of_perfect360 (hr : 1 ≤ r) (h : A6Hyp (conjAut r K A) D)
    (hP : Perfect360 (spCent r K A)) :
    ∃ H : Subgroup (spCent r K A), H.map (spCentFix A) = D := by
  obtain ⟨Q, _, _, ι, hι, hQ, h360⟩ := hP
  refine ⟨ι.range, ?_⟩
  rw [← MonoidHom.range_comp]
  exact h.range_eq ((spCentFix A).comp ι) hQ (ker_comp_spCentFix_le_center A ι hι) h360.ge

end Consequences

end CFSG.ComponentClassification.CatFC
