module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

@[expose] def U42Hyp {S : Type} [Group S] (σ : MulAut S) (J : Subgroup ↥(fixedSubgroup σ)) : Prop :=
  J.Normal ∧ IsSimpleGroup ↥J ∧ Nat.card ↥J = 25920 ∧
    (σ ∈ inner S → Nat.card ↥(fixedSubgroup σ) = 51840) ∧
    (σ ∉ inner S → Nat.card ↥(fixedSubgroup σ) = 25920)

@[expose] def OddU42Free (t : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n f : ℕ), StatedLieAdmissible t n 3 f → LieModel S t n 3 f →
    ∀ (σ : MulAut S) (J : Subgroup ↥(fixedSubgroup σ)), orderOf σ = 2 → U42Hyp σ J → False

@[expose] def OddU42ShapePSU : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n f : ℕ), StatedLieAdmissible .PSU n 3 f →
    LieModel S .PSU n 3 f → ∀ (σ : MulAut S) (J : Subgroup ↥(fixedSubgroup σ)), orderOf σ = 2 →
      U42Hyp σ J → n = 4 ∧ f = 1

theorem factorization_two_three_five (a b c r : ℕ) :
    (2 ^ a * 3 ^ b * 5 ^ c).factorization r =
      (if r = 2 then a else 0) + (if r = 3 then b else 0) + (if r = 5 then c else 0) := by
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
    Nat.Prime.factorization Nat.prime_two, Nat.Prime.factorization Nat.prime_three,
    Nat.Prime.factorization Nat.prime_five, Finsupp.single_apply, smul_eq_mul]
  by_cases h2 : r = 2
  · subst h2; norm_num
  by_cases h3 : r = 3
  · subst h3; norm_num
  by_cases h5 : r = 5
  · subst h5; norm_num
  simp [h2, h3, h5, Ne.symm h2, Ne.symm h3, Ne.symm h5]

theorem factorization_25920 (r : ℕ) :
    (25920 : ℕ).factorization r =
      (if r = 2 then 6 else 0) + (if r = 3 then 4 else 0) + (if r = 5 then 1 else 0) := by
  have h : (25920 : ℕ) = 2 ^ 6 * 3 ^ 4 * 5 ^ 1 := by norm_num
  rw [h]
  exact factorization_two_three_five 6 4 1 r

section Basic

variable {S : Type} [Group S] [Finite S] {σ : MulAut S} {J : Subgroup ↥(fixedSubgroup σ)}

theorem U42Hyp.normal (h : U42Hyp σ J) : J.Normal := h.1

theorem U42Hyp.isSimpleGroup (h : U42Hyp σ J) : IsSimpleGroup ↥J := h.2.1

theorem U42Hyp.card_J (h : U42Hyp σ J) : Nat.card ↥J = 25920 := h.2.2.1

theorem U42Hyp.card_inner (h : U42Hyp σ J) (hσ : σ ∈ inner S) :
    Nat.card ↥(fixedSubgroup σ) = 51840 := h.2.2.2.1 hσ

theorem U42Hyp.card_outer (h : U42Hyp σ J) (hσ : σ ∉ inner S) :
    Nat.card ↥(fixedSubgroup σ) = 25920 := h.2.2.2.2 hσ

theorem U42Hyp.card_mem (h : U42Hyp σ J) :
    Nat.card ↥(fixedSubgroup σ) = 25920 ∨ Nat.card ↥(fixedSubgroup σ) = 51840 := by
  by_cases hσ : σ ∈ inner S
  · exact Or.inr (h.card_inner hσ)
  · exact Or.inl (h.card_outer hσ)

theorem U42Hyp.card_dvd (h : U42Hyp σ J) : Nat.card ↥(fixedSubgroup σ) ∣ 51840 := by
  rcases h.card_mem with h1 | h1 <;> rw [h1] <;> norm_num

theorem U42Hyp.dvd_card (h : U42Hyp σ J) : 25920 ∣ Nat.card ↥(fixedSubgroup σ) := by
  rcases h.card_mem with h1 | h1 <;> rw [h1] <;> norm_num

theorem U42Hyp.card_dvd_mul (h : U42Hyp σ J) {Q : Type} [Group Q] [Finite Q]
    (φ : Q →* ↥(fixedSubgroup σ)) : Nat.card Q ∣ 51840 * Nat.card ↥φ.ker := by
  have h1 : Nat.card ↥φ.range ∣ 51840 :=
    (Subgroup.card_subgroup_dvd_card φ.range).trans h.card_dvd
  have h2 : Nat.card Q = Nat.card ↥φ.range * Nat.card ↥φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  rw [h2]
  exact Nat.mul_dvd_mul_right h1 _

end Basic

section Transport

variable {S S' : Type} [Group S] [Group S']

theorem u42FixedSubgroup_congr_eq (e : S ≃* S') (σ : MulAut S) :
    fixedSubgroup (MulAut.congr e σ) = (fixedSubgroup σ).map e.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  change e (σ (e.symm x)) = x ↔ σ (e.symm x) = e.symm x
  constructor
  · intro h
    have := congrArg e.symm h
    simpa using this
  · intro h
    rw [h]
    simp

def u42FixedEquiv (e : S ≃* S') (σ : MulAut S) :
    ↥(fixedSubgroup σ) ≃* ↥(fixedSubgroup (MulAut.congr e σ)) :=
  (MulEquiv.subgroupMap e _).trans (MulEquiv.subgroupCongr (u42FixedSubgroup_congr_eq e σ).symm)

theorem u42Congr_conj_eq (e : S ≃* S') (g : S) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem u42Congr_mem_inner_iff (e : S ≃* S') (σ : MulAut S) :
    MulAut.congr e σ ∈ inner S' ↔ σ ∈ inner S := by
  constructor
  · rintro ⟨g', hg'⟩
    refine ⟨e.symm g', ?_⟩
    have h1 : MulAut.congr e σ = MulAut.conj g' := hg'.symm
    have h2 : σ = MulAut.congr e.symm (MulAut.conj g') := by
      rw [← h1]; ext x; simp [MulAut.congr_apply]
    rw [h2, u42Congr_conj_eq]
  · rintro ⟨g, hg⟩
    refine ⟨e g, ?_⟩
    rw [← hg, u42Congr_conj_eq]

theorem u42OrderOf_congr (e : S ≃* S') (σ : MulAut S) :
    orderOf (MulAut.congr e σ) = orderOf σ :=
  orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective σ

theorem U42Hyp.congr (e : S ≃* S') (σ : MulAut S) (J : Subgroup ↥(fixedSubgroup σ))
    (h : U42Hyp σ J) :
    U42Hyp (MulAut.congr e σ) (J.map (u42FixedEquiv e σ).toMonoidHom) := by
  obtain ⟨hJn, hJs, hJc, hin, hout⟩ := h
  set Φ := u42FixedEquiv e σ with hΦ
  have hcard : Nat.card ↥(fixedSubgroup (MulAut.congr e σ)) = Nat.card ↥(fixedSubgroup σ) :=
    (Nat.card_congr Φ.toEquiv).symm
  refine ⟨Subgroup.Normal.map hJn Φ.toMonoidHom Φ.surjective,
    (J.equivMapOfInjective Φ.toMonoidHom Φ.injective).symm.isSimpleGroup, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr (J.equivMapOfInjective Φ.toMonoidHom Φ.injective).toEquiv]
    exact hJc
  · intro hσ
    rw [hcard]
    exact hin ((u42Congr_mem_inner_iff e σ).1 hσ)
  · intro hσ
    rw [hcard]
    exact hout fun h' => hσ ((u42Congr_mem_inner_iff e σ).2 h')

end Transport

theorem oddU42Free_of_concrete {t : StatedLieTag}
    (H : ∀ (S : Type) [Group S] [Finite S] (n f : ℕ), StatedLieAdmissible t n 3 f →
      LieModel S t n 3 f →
      ∃ (X : Type) (_ : Group X) (_ : Finite X) (_ : S ≃* X),
        ∀ (σ : MulAut X) (J : Subgroup ↥(fixedSubgroup σ)), orderOf σ = 2 → U42Hyp σ J →
          False) :
    OddU42Free t := by
  intro S _ _ n f hadm hm σ J hσ hJ
  obtain ⟨X, _, _, e, hX⟩ := H S n f hadm hm
  exact hX (MulAut.congr e σ) _ ((u42OrderOf_congr e σ).trans hσ) (hJ.congr e σ J)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
