module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeaklyClosed
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveBarTools

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}

omit [Finite G] in
theorem le_normalizer_of_weaklyClosed {Q R S : Subgroup G} (hSQ : S ≤ Q)
    (hwc : ∀ c ∈ Q, rightConjugate R c ≤ S ⊔ R → rightConjugate R c = R) :
    S ≤ Subgroup.normalizer (R : Set G) := by
  intro c hc
  rw [← rightConjugate_eq_self_iff]
  apply hwc c (hSQ hc)
  rw [← AschbacherTheorem3.rightConjugate_eq_of_mem (Subgroup.mem_sup_left hc :
    c ∈ S ⊔ R)]
  exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_right c

theorem centralizes_of_weaklyClosed {Q R S : Subgroup G} (hQD : Q ≤ D)
    (hOQ : aschbacherThm5Core D ≤ Q) (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hRH : R ≤ Subgroup.normalizer (D : Set G)) (hRQ : R ≤ Subgroup.normalizer (Q : Set G))
    (hR2 : IsPGroup 2 R) (hRQ1 : R ⊓ Q = ⊥) (hS : IsSylowOf 2 S Q)
    (hRS : R ≤ Subgroup.normalizer (S : Set G))
    (hwc : ∀ c ∈ Q, rightConjugate R c ≤ S ⊔ R → rightConjugate R c = R) :
    ∀ x ∈ R, aschbacherThm5Centralizes (aschbacherThm5Core D) Q x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (D : Set G)
  have hQH : Q ≤ H := hQD.trans Subgroup.le_normalizer
  have hSH : S ≤ H := hS.le.trans hQH
  set G' := bar D Q
  set T' := bar D R
  have hF : AschbacherTheorem3.Frame G' T' :=
    ⟨bar_le_normalizer hRQ hQH, by
      rw [← bar_inf_of_core_le hOQ, hRQ1, bar, Subgroup.bot_subgroupOf, Subgroup.map_bot],
      isPGroup_bar hR2⟩
  have hSR : S ≤ Subgroup.normalizer (R : Set G) := le_normalizer_of_weaklyClosed hS.le hwc
  set S' := T' ⊔ bar D S
  have hS'syl : IsSylowOf 2 S' (G' ⊔ T') :=
    AschbacherTheorem3.isSylowOf_sup_of_frame hF (isSylowOf_bar hS hQH)
      (bar_le_normalizer hRS hSH)
  have hS'N : S' ≤ Subgroup.normalizer (T' : Set (Bar D)) :=
    sup_le Subgroup.le_normalizer (bar_le_normalizer hSR hRH)
  have hSF : AschbacherTheorem3.SylowFrame G' T' S' := by
    refine ⟨hF, hS'syl, ?_⟩
    rw [inf_eq_left.mpr hS'N]
    exact hS'syl.of_le (le_inf hS'syl.le hS'N) inf_le_left
  have hwc' : ∀ c ∈ G', rightConjugate T' c ≤ S' → rightConjugate T' c = T' := by
    intro c hc hle
    obtain ⟨h, hhQ, rfl⟩ := (mem_bar_iff D Q c).mp hc
    rw [← bar_rightConjugate] at hle ⊢
    have hRhH : rightConjugate R h ≤ H := rightConjugate_le_normalizer hRH h
    have hS'eq : S' = bar D (R ⊔ S) := (bar_sup hRH hSH).symm
    rw [hS'eq] at hle
    have h1 := BarTools.le_sup_core_of_bar_le hRhH hle
    obtain ⟨o, ho, hle'⟩ := le_rightConjugate_of_le_sup_core (sup_le hRH hSH)
      (AschbacherTheorem3.isPGroup_rightConjugate hR2 h) h1
    have hmem : (h : G) * o⁻¹ ∈ Q := Q.mul_mem hhQ (Q.inv_mem (hOQ ho))
    have hle2 : rightConjugate R ((h : G) * o⁻¹) ≤ S ⊔ R := by
      have := AschbacherTheorem3.rightConjugate_le_rightConjugate hle' o⁻¹
      rw [rightConjugate_mul, rightConjugate_mul, mul_inv_cancel, rightConjugate_one,
        sup_comm] at this
      exact this
    have heq := hwc _ hmem hle2
    have heq' : rightConjugate R (h : G) = rightConjugate R o := by
      rw [show (h : G) = (h : G) * o⁻¹ * o by group, ← rightConjugate_mul, heq]
    have hoH : o ∈ H := core_le_normalizer D ho
    have hbar : bar D (rightConjugate R o) = T' := by
      rw [show (o : G) = ((⟨o, hoH⟩ : H) : G) from rfl, bar_rightConjugate,
        (toBar_eq_one_iff D ⟨o, hoH⟩).mpr ho, rightConjugate_one]
    rw [heq', hbar]
  have hcomm := AschbacherTheorem3.lemma_4_2 hSF hwc' (oddCore_bar_eq_bot hQD hDQ)
  have hTC : T' ≤ Subgroup.centralizer (G' : Set (Bar D)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm
  intro x hx
  exact (centralizes_iff_mem_centralizer D Q hQD ⟨x, hRH hx⟩).mpr
    (hTC (toBar_mem_bar D (h := ⟨x, hRH hx⟩) hx))


theorem weaklyClosed_of_normalizer {Q R S : Subgroup G} (hSQ : S ≤ Q) (hS2 : IsPGroup 2 S)
    (hR2 : IsPGroup 2 R) (hRS : R ≤ Subgroup.normalizer (S : Set G))
    (hwcN : ∀ c ∈ Q, rightConjugate R c ≤ (S ⊔ R) ⊓ Subgroup.normalizer (R : Set G) →
      rightConjugate R c = R) :
    ∀ c ∈ Q, rightConjugate R c ≤ S ⊔ R → rightConjugate R c = R := by
  set X := S ⊔ R with hXdef
  have hX2 : IsPGroup 2 X := by
    rw [hXdef, sup_comm]
    exact IsPGroup.to_sup_of_normal_right' hR2 hS2 hRS
  have hmem : ∀ x ∈ X, ∃ s ∈ S, rightConjugate R x = rightConjugate R s := by
    intro x hx
    have hx' : x ∈ ((R ⊔ S : Subgroup G) : Set G) := by rw [sup_comm]; exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right R S hRS] at hx'
    obtain ⟨r₀, hr₀, s, hs, rfl⟩ := Set.mem_mul.mp hx'
    refine ⟨s, hs, ?_⟩
    rw [← rightConjugate_mul, (rightConjugate_eq_self_iff R r₀).mpr (Subgroup.le_normalizer hr₀)]
  have hXN : X ≤ Subgroup.normalizer (R : Set G) := by
    by_contra hcon
    let M : Subgroup X := (Subgroup.normalizer (R : Set G)).subgroupOf X
    have hMtop : M < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun hM => hcon fun x hx => ?_
      have hm : (⟨x, hx⟩ : X) ∈ M := hM ▸ Subgroup.mem_top _
      exact hm
    have : Group.IsNilpotent X := hX2.isNilpotent
    obtain ⟨x, hxN, hxM⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent M hMtop)
    have hxN' : (x : G) ∉ Subgroup.normalizer (R : Set G) := hxM
    have hle : rightConjugate R x ≤ X ⊓ Subgroup.normalizer (R : Set G) := by
      intro y hy
      rw [mem_rightConjugate_iff] at hy
      have hyeq : y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * x := by group
      have hrX : (x : G) * y * (x : G)⁻¹ ∈ X := Subgroup.mem_sup_right hy
      have hrM : (⟨(x : G) * y * (x : G)⁻¹, hrX⟩ : X) ∈ M := Subgroup.le_normalizer hy
      have hconj := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp hrM
      rw [hyeq]
      have hconj' := Subgroup.mem_subgroupOf.mp hconj
      exact ⟨X.mul_mem (X.mul_mem (X.inv_mem x.2) hrX) x.2, by simpa using hconj'⟩
    obtain ⟨s, hs, hseq⟩ := hmem x x.2
    rw [hseq] at hle
    have h1 := hwcN s (hSQ hs) hle
    rw [← hseq] at h1
    exact hxN' ((rightConjugate_eq_self_iff R x).mp h1)
  intro c hc hle
  exact hwcN c hc (le_inf hle (hle.trans hXN))


theorem exists_conj_le_normalizer {Q R S : Subgroup G} (hQD : Q ≤ D)
    (hOQ : aschbacherThm5Core D ≤ Q) (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hRH : R ≤ Subgroup.normalizer (D : Set G)) (hRQ : R ≤ Subgroup.normalizer (Q : Set G))
    (hR2 : IsPGroup 2 R) (hRQ1 : R ⊓ Q = ⊥) (hS : IsSylowOf 2 S Q)
    (hRS : R ≤ Subgroup.normalizer (S : Set G))
    (hnot : ¬ ∀ x ∈ R, aschbacherThm5Centralizes (aschbacherThm5Core D) Q x) :
    ∃ c ∈ Q, rightConjugate R c ≤ (S ⊔ R) ⊓ Subgroup.normalizer (R : Set G) ∧
      rightConjugate R c ≠ R := by
  by_contra hcon
  push Not at hcon
  exact hnot (centralizes_of_weaklyClosed hQD hOQ hDQ hRH hRQ hR2 hRQ1 hS hRS
    (weaklyClosed_of_normalizer hS.le hS.isPGroup hR2 hRS hcon))

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
