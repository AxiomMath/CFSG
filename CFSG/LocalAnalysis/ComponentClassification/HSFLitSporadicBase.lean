module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitExclusion
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAmbient
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Sylow
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn map_centralizer_subtype)

theorem Excluded.conj {X : Type} [Group X] [Finite X] {t : X} (h : Excluded t) (c : X) :
    Excluded (c * t * c⁻¹) := by
  refine Excluded.of_mulEquiv (MulAut.conj c⁻¹) ?_
  have e : MulAut.conj c⁻¹ (c * t * c⁻¹) = t := by rw [MulAut.conj_apply]; group
  rw [e]
  exact h

theorem excluded_of_mulEquiv_all {X Y : Type} [Group X] [Group Y] [Finite Y] (e : X ≃* Y)
    (h : ∀ y : Y, orderOf y = 2 → Excluded y) (x : X) (hx : orderOf x = 2) : Excluded x :=
  Excluded.of_mulEquiv e (h _ (by rw [MulEquiv.orderOf_eq]; exact hx))

variable {M : Type} [Group M] (H : Subgroup M)

noncomputable def centralizerEquivIn {r : M} (hr : r ∈ H) {K : Subgroup M}
    (hK : centralizerIn H r = K) : centralizer ({(⟨r, hr⟩ : H)} : Set H) ≃* K :=
  ((centralizer ({(⟨r, hr⟩ : H)} : Set H)).equivMapOfInjective H.subtype
    H.subtype_injective).trans
    (MulEquiv.subgroupCongr ((map_centralizer_subtype H ⟨r, hr⟩).trans hK))

theorem excluded_of_ambient_card {r : M} (hr : r ∈ H) {K : Subgroup M}
    (hK : centralizerIn H r = K) (h7 : ¬ 7 ∣ Nat.card K) (h9 : ¬ 9 ∣ Nat.card K)
    (h2000 : Nat.card K ≤ 2000) : Excluded (⟨r, hr⟩ : H) := by
  right; right; right
  rw [Nat.card_congr (centralizerEquivIn H hr hK).toEquiv]
  exact ⟨h7, h9, h2000⟩

theorem excluded_of_ambient_quasisimple {r : M} (hr : r ∈ H) {K : Subgroup M}
    (hK : centralizerIn H r = K) (hq : Open.IsQuasisimple K) : Excluded (⟨r, hr⟩ : H) :=
  Or.inr (Or.inr (Or.inl
    (ClassicalInvolution.isQuasisimple_of_mulEquiv (centralizerEquivIn H hr hK).symm hq)))

theorem excluded_of_ambient_normal_pGroup {r : M} (hr : r ∈ H) {K : Subgroup M}
    (hK : centralizerIn H r = K)
    (hU : ∃ U : Subgroup M, U ≤ K ∧ K ≤ normalizer (U : Set M) ∧ IsPGroup 2 U ∧
      K ⊓ centralizer (U : Set M) ≤ U) : Excluded (⟨r, hr⟩ : H) := by
  subst hK
  obtain ⟨U, hUK, hUn, hU, hcon⟩ := hU
  have hUH : U ≤ H := fun x hx => (mem_centralizerIn.1 (hUK hx)).1
  have hmem : ∀ g : H, g ∈ centralizer ({(⟨r, hr⟩ : H)} : Set H) →
      (g : M) ∈ centralizerIn H r := fun g hg => mem_centralizerIn.2 ⟨g.2, by
        simpa using congrArg Subtype.val (mem_centralizer_singleton_iff.1 hg)⟩
  right; left
  refine ⟨U.subgroupOf H, ?_, hU.comap_of_injective H.subtype H.subtype_injective, ?_, ?_⟩
  · intro x hx
    have hxK := mem_centralizerIn.1 (hUK hx)
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (by simpa using hxK.2)
  · intro g hg
    rw [mem_normalizer_iff]
    intro x
    have := mem_normalizer_iff.1 (hUn (hmem g hg)) (x : M)
    simpa [mem_subgroupOf] using this
  · rintro g ⟨hg, hgU⟩
    have hgC : (g : M) ∈ centralizer (U : Set M) := by
      rw [mem_centralizer_iff]
      intro u hu
      have := mem_centralizer_iff.1 hgU ⟨u, hUH hu⟩ (by simpa [mem_subgroupOf] using hu)
      exact congrArg Subtype.val this
    exact hcon ⟨hmem g hg, hgC⟩

theorem excluded_of_reps [Finite H] (reps : List M)
    (hcov : ∀ u ∈ H, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ H, u = c * r * c⁻¹)
    (hgood : ∀ r ∈ reps, ∀ hr : r ∈ H, Excluded (⟨r, hr⟩ : H)) (y : H) (hy : orderOf y = 2) :
    Excluded y := by
  obtain ⟨r, hr, c, hc, hyr⟩ := hcov y y.2 (by rw [orderOf_coe]; exact hy)
  have hrH : r ∈ H := by
    have e : r = c⁻¹ * y * c := by rw [hyr]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hc) y.2) hc
  have e : y = ⟨c, hc⟩ * ⟨r, hrH⟩ * (⟨c, hc⟩ : H)⁻¹ := Subtype.ext (by simp [hyr])
  rw [e]
  exact (hgood r hr hrH).conj _

theorem excluded_of_sylow_cover [Finite H] (S : Subgroup M) (hS : IsPGroup 2 S)
    (hidx : ¬ 2 ∣ (S.subgroupOf H).index) {r : M} (hr : r ∈ H)
    (hSr : ∀ s ∈ S, orderOf s = 2 → ∃ c ∈ H, s = c * r * c⁻¹)
    (hgood : Excluded (⟨r, hr⟩ : H)) (y : H) (hy : orderOf y = 2) : Excluded y := by
  refine excluded_of_reps H [r] (fun u hu ho => ?_) (fun r' hr' hr'H => ?_) y hy
  · obtain ⟨c, hc, hu⟩ := ClassicalInvolution.cover_of_sylow H S hS hidx r hSr u hu ho
    exact ⟨r, List.mem_singleton_self r, c, hc, hu⟩
  · rw [List.mem_singleton] at hr'
    subst hr'
    exact hgood

end CFSG.ComponentClassification.HSFLit
