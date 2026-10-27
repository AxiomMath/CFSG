module

public import CFSG.CGT.PushingUpLit.BHS.FourTwoA
public import CFSG.CGT.PushingUpLit.BHS.FourOneD

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne

namespace FourTwoTools

variable {Γ : Type*} [Group Γ]

theorem le_normalizer_iSup {P : Subgroup Γ} {D₀ : Set (Subgroup Γ)}
    (hnorm : ∀ A ∈ D₀, ∀ g ∈ P, conjSub g A ∈ D₀) :
    P ≤ Subgroup.normalizer ((⨆ A ∈ D₀, A : Subgroup Γ) : Set Γ) := by
  have h1 : ∀ g ∈ P, conjSub g (⨆ A ∈ D₀, A) ≤ ⨆ A ∈ D₀, A := by
    intro g hg
    refine Subgroup.map_le_iff_le_comap.2 (iSup₂_le fun A hA => ?_)
    exact Subgroup.map_le_iff_le_comap.1
      (le_iSup₂_of_le (f := fun (B : Subgroup Γ) (_ : B ∈ D₀) => B) (conjSub g A)
        (hnorm A hA g hg) le_rfl)
  exact fun g hg => mem_normalizer_of_conjSub_le (h1 g hg) (h1 g⁻¹ (P.inv_mem hg))

end FourTwoTools

namespace Hyp41

variable {V : Type} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}
  {D D₀ : Set (Subgroup (MulAut V))}

theorem commute_of_not_mem (h : Hyp41 P D) (hD₀ : D₀ ⊆ D)
    (hnorm : ∀ A ∈ D₀, ∀ g ∈ P, conjSub g A ∈ D₀) {A B : Subgroup (MulAut V)} (hA : A ∈ D₀)
    (hB : B ∈ D) (hB₀ : B ∉ D₀) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  rcases h.four_eight_conj (hD₀ hA) hB with hc | ⟨g, hg, hgB⟩
  · exact hc
  · refine absurd ?_ hB₀
    rw [hgB]
    exact hnorm A hA g (sup_le (h.le A (hD₀ hA)) (h.le B hB) hg)

theorem comm_of_not_mem_iSup (h : Hyp41 P D) (hD₀ : D₀ ⊆ D)
    (hnorm : ∀ A ∈ D₀, ∀ g ∈ P, conjSub g A ∈ D₀) {B : Subgroup (MulAut V)} (hB : B ∈ D)
    (hB₀ : B ∉ D₀) : ∀ x ∈ (⨆ A ∈ D₀, A : Subgroup (MulAut V)), ∀ b ∈ B, x * b = b * x := by
  intro x hx b hb
  have hle : (⨆ A ∈ D₀, A : Subgroup (MulAut V)) ≤ Subgroup.centralizer {b} :=
    iSup₂_le fun A hA a ha => by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff.1 hz]
      exact (h.commute_of_not_mem hD₀ hnorm hA hB hB₀ a ha b hb).symm
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) b rfl).symm

theorem setNormalizer_iSup_le (h : Hyp41 P D) (hD₀ : D₀ ⊆ D)
    (hnorm : ∀ A ∈ D₀, ∀ g ∈ P, conjSub g A ∈ D₀) (T : Subgroup (MulAut V)) :
    setNormalizer (⨆ A ∈ D₀, A) (dInter D₀ ((⨆ A ∈ D₀, A) ⊓ T)) ≤ setNormalizer P (dInter D T) := by
  have hP₀P : (⨆ A ∈ D₀, A : Subgroup (MulAut V)) ≤ P := iSup₂_le fun A hA => h.le A (hD₀ hA)
  have key : ∀ n ∈ setNormalizer (⨆ A ∈ D₀, A) (dInter D₀ ((⨆ A ∈ D₀, A) ⊓ T)),
      ∀ B ∈ dInter D T, conjSub n B ∈ dInter D T := by
    intro n hn B hB
    by_cases hB₀ : B ∈ D₀
    · have hBT₀ : B ∈ dInter D₀ ((⨆ A ∈ D₀, A) ⊓ T) :=
        ⟨hB₀, le_inf (le_iSup₂_of_le (f := fun (C : Subgroup (MulAut V)) (_ : C ∈ D₀) => C) B hB₀
          le_rfl) hB.2⟩
      have := (hn.2 B).1 hBT₀
      exact ⟨hD₀ this.1, this.2.trans inf_le_right⟩
    · have hc := h.comm_of_not_mem_iSup hD₀ hnorm hB.1 hB₀
      rwa [FourOneTools.conjSub_eq_of_comm fun x hx => hc n hn.1 x hx]
  intro n hn
  refine ⟨hP₀P hn.1, fun B => ⟨key n hn B, fun hB => ?_⟩⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hB
  rwa [FourTwoTools.conjSub_inv_conjSub] at this

end Hyp41

namespace Hyp42

variable {V : Type} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}
  {D D₀ : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}

omit [Finite V] in
theorem ne_core_iSup (hnorm : ∀ A ∈ D₀, ∀ g ∈ P, conjSub g A ∈ D₀) (hD₀ : D₀ ⊆ D)
    (hcore : ¬ D₀ ⊆ dCore P D M) :
    D₀ ≠ dCore (⨆ A ∈ D₀, A) D₀ (M ⊓ ⨆ A ∈ D₀, A) := by
  intro heq
  refine hcore fun A hA => ⟨hD₀ hA, fun g hg => ?_⟩
  have h1 := (Set.ext_iff.1 heq _).1 (hnorm A hA g⁻¹ (P.inv_mem hg))
  have h2 := h1.2 1 (Subgroup.one_mem _)
  rw [conjSub_one] at h2
  have h3 := conjSub_mono g (h2.trans inf_le_left)
  rwa [FourTwoTools.conjSub_conjSub_inv] at h3

theorem restrict_normalSet (h : Hyp42 P D T M) (hD₀ : D₀ ⊆ D)
    (hnorm : ∀ A ∈ D₀, ∀ g ∈ P, conjSub g A ∈ D₀) (hcore : ¬ D₀ ⊆ dCore P D M) :
    Hyp42 (⨆ A ∈ D₀, A) D₀ ((⨆ A ∈ D₀, A) ⊓ T) (M ⊓ ⨆ A ∈ D₀, A) := by
  have hP₀P : (⨆ A ∈ D₀, A : Subgroup (MulAut V)) ≤ P := iSup₂_le fun A hA => h.le A (hD₀ hA)
  exact
  { toHyp41 := h.toHyp41.restrict hD₀
      (fun A hA => le_iSup₂_of_le (f := fun (C : Subgroup (MulAut V)) (_ : C ∈ D₀) => C) A hA
        le_rfl)
      fun A hA g hg => hnorm A hA g (hP₀P hg)
    syl := FourTwoTools.isSylowOf_inf_of_le_normalizer h.syl hP₀P
      (FourTwoTools.le_normalizer_iSup hnorm)
    le_M := le_inf (inf_le_right.trans h.le_M) inf_le_left
    M_le := inf_le_right
    ne_core := ne_core_iSup hnorm hD₀ hcore
    normSet_le := fun n hn =>
      ⟨h.normSet_le (h.toHyp41.setNormalizer_iSup_le hD₀ hnorm T hn), hn.1⟩
    cen_le := fun x hx =>
      ⟨h.cen_le ⟨hP₀P hx.1, fun u hu => hx.2 u (fixV_anti inf_le_right hu)⟩, hx.1⟩ }

end Hyp42

end CFSG.CGT.PushingUpLit.BHS
