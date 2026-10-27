module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24QuotC

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

private lemma eq_one_of_mem_zpowers_of_sq_eq_one {Y : Type} [Group Y] {a t : Y} {τ : Y → Prop}
    {F P : Subgroup Y} (h : Cfg24 Y a t τ F P) {s : Y} (hs : s ∈ zpowers a) (hs2 : s ^ 2 = 1) :
    s = 1 := by
  rw [Subgroup.mem_zpowers_iff] at hs
  obtain ⟨k, rfl⟩ := hs
  have hdvd2 : orderOf (a ^ k) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hs2
  have hdvd3 : orderOf (a ^ k) ∣ 3 := by
    rw [← h.orderOf_a]
    exact orderOf_dvd_of_mem_zpowers (zpow_mem_zpowers a k)
  have hdvd1 : orderOf (a ^ k) ∣ 1 := by
    have hg := Nat.dvd_gcd hdvd2 hdvd3
    rwa [show Nat.gcd 2 3 = 1 by decide] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)

private lemma eq_one_of_mk'_eq_one_of_sq_eq_one {Y : Type} [Group Y] {a t : Y} {τ : Y → Prop}
    {F P : Subgroup Y} [(zpowers a).Normal] (h : Cfg24 Y a t τ F P) {s : Y} (hs2 : s ^ 2 = 1)
    (hs : QuotientGroup.mk' (zpowers a) s = 1) : s = 1 := by
  have hz : s ∈ zpowers a :=
    (QuotientGroup.eq_one_iff (N := zpowers a) s).mp
      (by simpa only [QuotientGroup.mk'_apply] using hs)
  exact eq_one_of_mem_zpowers_of_sq_eq_one h hz hs2

private lemma injOn_mk'_tInvolutions {Y : Type} [Group Y] {a t : Y} {τ : Y → Prop}
    {F P : Subgroup Y} [(zpowers a).Normal] (h : Cfg24 Y a t τ F P) :
    Set.InjOn (QuotientGroup.mk' (zpowers a)) (tInvolutions t τ) := by
  intro s hs s' hs' heq
  rw [tInvolutions, Set.mem_setOf_eq] at hs hs'
  obtain ⟨hsC, hs2, -, -⟩ := hs
  obtain ⟨-, hs'2, -, -⟩ := hs'
  rw [QuotientGroup.mk'_eq_mk'] at heq
  obtain ⟨z, hz, hzs⟩ := heq
  have hzC : z ∈ Subgroup.center Y := Subgroup.zpowers_le.mpr h.a_central hz
  have hcomm : Commute s z := Subgroup.mem_center_iff.mp hzC s
  have hz2 : z ^ 2 = 1 := by
    have h2 := hs'2
    rw [← hzs, hcomm.mul_pow 2, hs2, one_mul] at h2
    exact h2
  have hz1 : z = 1 := eq_one_of_mem_zpowers_of_sq_eq_one h hz hz2
  rw [← hzs, hz1, mul_one]

theorem quot_involutions {Y : Type} [Group Y] [Finite Y] {a t : Y} {τ : Y → Prop}
    {F P : Subgroup Y} [(zpowers a).Normal] (h : Cfg24 Y a t τ F P) :
    ∃ I : Set (Y ⧸ zpowers a), I.ncard = 46 ∧
      (∀ c ∈ I, c ∈ centralizer ({QuotientGroup.mk' (zpowers a) t} : Set (Y ⧸ zpowers a)) ∧
        c ^ 2 = 1 ∧ c ≠ 1 ∧ IsConj (QuotientGroup.mk' (zpowers a) t) c) ∧
      (∀ c ∈ centralizer ({QuotientGroup.mk' (zpowers a) t} : Set (Y ⧸ zpowers a)),
        c ^ 2 = 1 → c ≠ 1 → IsConj (QuotientGroup.mk' (zpowers a) t) c → c ∈ I) := by
  refine ⟨QuotientGroup.mk' (zpowers a) '' tInvolutions t τ, ?_, ?_, ?_⟩
  · rw [Set.InjOn.ncard_image (injOn_mk'_tInvolutions h), h.card_tT]
  · intro c hc
    rw [Set.mem_image] at hc
    obtain ⟨s, hsT, rfl⟩ := hc
    rw [tInvolutions, Set.mem_setOf_eq] at hsT
    obtain ⟨hsC, hs2, hsne, hτs⟩ := hsT
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simpa only [map_mul] using
        congrArg (QuotientGroup.mk' (zpowers a))
          (Subgroup.mem_centralizer_iff.mp hsC t (Set.mem_singleton t))
    · rw [← map_pow, hs2, map_one]
    · intro hc1
      exact hsne (eq_one_of_mk'_eq_one_of_sq_eq_one h hs2 hc1)
    · obtain ⟨y, hy⟩ := h.τ_fusion s hτs hs2 hsne
      exact MonoidHom.map_isConj (QuotientGroup.mk' (zpowers a)) (isConj_iff.mpr ⟨y, hy⟩)
  · intro c hc hc2 hcne hconj
    rw [Set.mem_image]
    have hcmap : c ∈ (centralizer ({t} : Set Y)).map (QuotientGroup.mk' (zpowers a)) := by
      rwa [← centralizer_quot_eq h]
    obtain ⟨s, hsC, hsc⟩ := Subgroup.mem_map.mp hcmap
    rw [isConj_iff] at hconj
    obtain ⟨g, hg⟩ := hconj
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (zpowers a) g
    rw [← hy] at hg
    have hs'c : QuotientGroup.mk' (zpowers a) (y * t * y⁻¹) = c := by
      rw [← hg]
      simp only [map_mul, map_inv]
    have hs'2 : (y * t * y⁻¹) ^ 2 = 1 := by
      have hconjy : IsConj t (y * t * y⁻¹) := isConj_iff.mpr ⟨y, rfl⟩
      have hp := hconjy.pow 2
      rw [h.t_sq] at hp
      exact isConj_one_right.mp hp
    have hs'τ : τ (y * t * y⁻¹) := h.τ_conj y t h.τ_t
    have hs'ne : y * t * y⁻¹ ≠ 1 := by
      intro h1
      apply hcne
      rw [← hs'c, h1, map_one]
    have heq : QuotientGroup.mk' (zpowers a) s =
        QuotientGroup.mk' (zpowers a) (y * t * y⁻¹) := by
      rw [hsc, hs'c]
    rw [QuotientGroup.mk'_eq_mk'] at heq
    obtain ⟨z, hz, hzs⟩ := heq
    have hzC : z ∈ Subgroup.center Y := Subgroup.zpowers_le.mpr h.a_central hz
    have hs'C : y * t * y⁻¹ ∈ centralizer ({t} : Set Y) := by
      rw [← hzs]
      exact (centralizer ({t} : Set Y)).mul_mem hsC
        (Subgroup.center_le_centralizer ({t} : Set Y) hzC)
    exact ⟨y * t * y⁻¹, by
      rw [tInvolutions, Set.mem_setOf_eq]
      exact ⟨hs'C, hs'2, hs'ne, hs'τ⟩, hs'c⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada
