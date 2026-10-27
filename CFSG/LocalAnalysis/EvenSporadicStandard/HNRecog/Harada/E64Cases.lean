module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.E64

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {t z b z₁ : G} {S Eg T T' W0 : Subgroup G} {ι : Elem2 6 →* G}

private lemma lam_zero : lam (0 : V6) = 0 := by simp [lam]

private lemma qm_zero : qm (0 : V6) = 0 := by simp [qm]

private lemma lam_tv : lam tv = 0 := by decide +kernel

private lemma qm_tv : qm tv = 1 := by decide +kernel

private lemma qm_add_tv (v : V6) : qm (v + tv) = qm v + 1 + lam v := by
  rw [qm_add, lam_eq_bil, qm_tv]

private lemma zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private lemma zmod_two_zero_ne_one : (0 : ZMod 2) ≠ 1 := by decide

private lemma zmod_two_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

private lemma ne_zero_of_lam_eq_one {u : V6} (h : lam u = 1) : u ≠ 0 := by
  intro hu
  rw [hu, lam_zero] at h
  exact zmod_two_zero_ne_one h

private lemma ne_tv_of_lam_eq_one {u : V6} (h : lam u = 1) : u ≠ tv := by
  intro hu
  rw [hu, lam_tv] at h
  exact zmod_two_zero_ne_one h

private lemma mem_Yv2 {v : V6} : v ∈ Yv2 ↔ v = tv ∨ (lam v = 1 ∧ qm v = 0) := by
  simp [Yv2]

private lemma mem_Yv1 {v : V6} : v ∈ Yv1 ↔ v = tv ∨ (lam v = 1 ∧ qm v = 1) := by
  simp [Yv1]

private lemma mem_Yv12 {v : V6} : v ∈ Yv12 ↔ v = tv ∨ lam v = 1 := by
  simp [Yv12]

private lemma mem_X36 {v : V6} : v ∈ X36 ↔ qm v = 1 := by
  simp [X36]

private lemma mem_X48 {v : V6} : v ∈ X48 ↔ (lam v = 0 ∧ qm v = 1) ∨ lam v = 1 := by
  simp [X48]

private lemma mem_X28 {v : V6} : v ∈ X28 ↔ qm v + lam v = 1 := by
  have h : v ∈ X28 ↔ qp v = 1 := by simp [X28]
  rw [h]
  rfl

theorem HData.X_cases_prop21 (hD : HData G t z b z₁ S Eg T T' W0 ι)
    (hker : ∀ v, lam v = 0 → IsConj t (coordElt ι v) → v = tv)
    (hex : ∃ v, lam v = 1 ∧ IsConj t (coordElt ι v)) :
    (∀ v, IsConj t (coordElt ι v) ↔ v ∈ Yv2) ∨ (∀ v, IsConj t (coordElt ι v) ↔ v ∈ Yv1) ∨
      (∀ v, IsConj t (coordElt ι v) ↔ v ∈ Yv12) := by
  obtain ⟨v₀, hv₀l, hv₀X⟩ := hex
  let P0 : Prop := ∃ u : V6, lam u = 1 ∧ qm u = 0 ∧ IsConj t (coordElt ι u)
  let P1 : Prop := ∃ u : V6, lam u = 1 ∧ qm u = 1 ∧ IsConj t (coordElt ι u)
  have hP : P0 ∨ P1 := by
    rcases zmod_two_eq_zero_or_one (qm v₀) with h | h
    · exact Or.inl ⟨v₀, hv₀l, h, hv₀X⟩
    · exact Or.inr ⟨v₀, hv₀l, h, hv₀X⟩
  have hC0 : P0 → ∀ w, lam w = 1 → qm w = 0 → IsConj t (coordElt ι w) := by
    rintro ⟨u, hul, huq, huX⟩ w hwl hwq
    exact hD.isConj_fuse huX (ne_zero_of_lam_eq_one hwl) (ne_tv_of_lam_eq_one hwl)
      (ne_zero_of_lam_eq_one hul) (ne_tv_of_lam_eq_one hul)
      (by rw [hul, hwl]) (by rw [huq, hwq])
  have hC1 : P1 → ∀ w, lam w = 1 → qm w = 1 → IsConj t (coordElt ι w) := by
    rintro ⟨u, hul, huq, huX⟩ w hwl hwq
    exact hD.isConj_fuse huX (ne_zero_of_lam_eq_one hwl) (ne_tv_of_lam_eq_one hwl)
      (ne_zero_of_lam_eq_one hul) (ne_tv_of_lam_eq_one hul)
      (by rw [hul, hwl]) (by rw [huq, hwq])
  have hYv2 : P0 → ¬ P1 → (∀ v, IsConj t (coordElt ι v) ↔ v ∈ Yv2) := by
    intro hP0 hP1' v
    rw [mem_Yv2]
    constructor
    · intro hX
      rcases zmod_two_eq_zero_or_one (lam v) with hl | hl
      · exact Or.inl (hker v hl hX)
      · refine Or.inr ⟨hl, ?_⟩
        rcases zmod_two_eq_zero_or_one (qm v) with hq | hq
        · exact hq
        · exact absurd ⟨v, hl, hq, hX⟩ hP1'
    · intro hv
      rcases hv with hv | ⟨hl, hq⟩
      · rw [hv]
        simpa [hD.ι_tv] using IsConj.refl t
      · exact hC0 hP0 v hl hq
  have hYv1 : ¬ P0 → P1 → (∀ v, IsConj t (coordElt ι v) ↔ v ∈ Yv1) := by
    intro hP0' hP1 v
    rw [mem_Yv1]
    constructor
    · intro hX
      rcases zmod_two_eq_zero_or_one (lam v) with hl | hl
      · exact Or.inl (hker v hl hX)
      · refine Or.inr ⟨hl, ?_⟩
        rcases zmod_two_eq_zero_or_one (qm v) with hq | hq
        · exact absurd ⟨v, hl, hq, hX⟩ hP0'
        · exact hq
    · intro hv
      rcases hv with hv | ⟨hl, hq⟩
      · rw [hv]
        simpa [hD.ι_tv] using IsConj.refl t
      · exact hC1 hP1 v hl hq
  have hYv12 : P0 → P1 → (∀ v, IsConj t (coordElt ι v) ↔ v ∈ Yv12) := by
    intro hP0 hP1 v
    rw [mem_Yv12]
    constructor
    · intro hX
      rcases zmod_two_eq_zero_or_one (lam v) with hl | hl
      · exact Or.inl (hker v hl hX)
      · exact Or.inr hl
    · intro hv
      rcases hv with hv | hl
      · rw [hv]
        simpa [hD.ι_tv] using IsConj.refl t
      · rcases zmod_two_eq_zero_or_one (qm v) with hq | hq
        · exact hC0 hP0 v hl hq
        · exact hC1 hP1 v hl hq
  rcases hP with hP0 | hP1
  · by_cases hP1' : P1
    · exact Or.inr (Or.inr (hYv12 hP0 hP1'))
    · exact Or.inl (hYv2 hP0 hP1')
  · by_cases hP0' : P0
    · exact Or.inr (Or.inr (hYv12 hP0' hP1))
    · exact Or.inr (Or.inl (hYv1 hP0' hP1))

theorem HData.X_cases_lemma23 (hD : HData G t z b z₁ S Eg T T' W0 ι) (hz : ¬ IsConj t z)
    (htz : IsConj t (t * z)) (hex : ∃ v, lam v = 1 ∧ IsConj t (coordElt ι v)) :
    (∀ v, IsConj t (coordElt ι v) ↔ v ∈ X36) ∨ (∀ v, IsConj t (coordElt ι v) ↔ v ∈ X28) ∨
      (∀ v, IsConj t (coordElt ι v) ↔ v ∈ X48) := by
  obtain ⟨vz, hvzcoord, hvzl, hvzq⟩ := hD.coords_z
  have hvz0 : vz ≠ 0 := by
    intro h
    have hz1 : z = 1 := by rw [← hvzcoord, h, coordElt_zero]
    exact hD.core.z1_ne_one hz1
  have hvzt : vz ≠ tv := by
    intro h
    rw [h, qm_tv] at hvzq
    exact zmod_two_one_ne_zero hvzq
  have hzt : z * t = t * z := hD.core.z1_comm t hD.core.t_mem
  have hwzX : IsConj t (coordElt ι (vz + tv)) := by
    rw [coordElt_add, hvzcoord, hD.ι_tv, hzt]
    exact htz
  have hlamwz : lam (vz + tv) = 0 := by
    have h : lam (vz + tv) = lam vz + lam tv := rfl
    rw [h, hvzl, lam_tv, add_zero]
  have hqmwz : qm (vz + tv) = 1 := by
    rw [qm_add_tv, hvzq, hvzl]
    ring
  have hwz0 : vz + tv ≠ 0 := by
    intro h
    rw [h, qm_zero] at hqmwz
    exact zmod_two_zero_ne_one hqmwz
  have hwztv : vz + tv ≠ tv := by
    intro h
    exact hvz0 (add_right_cancel (show vz + tv = 0 + tv from by rw [h, zero_add]))
  have hlam0 : ∀ v : V6, lam v = 0 → (IsConj t (coordElt ι v) ↔ qm v = 1) := by
    intro v hvl
    constructor
    · intro hX
      rcases zmod_two_eq_zero_or_one (qm v) with hq | hq
      · exfalso
        by_cases hv0 : v = 0
        · subst hv0
          rw [coordElt_zero] at hX
          exact hD.core.t_ne_one (isConj_one_left.mp hX)
        · have hvt : v ≠ tv := by
            intro h
            rw [h, qm_tv] at hq
            exact zmod_two_one_ne_zero hq
          have hzv : IsConj t (coordElt ι vz) :=
            hD.isConj_fuse hX hvz0 hvzt hv0 hvt (by rw [hvl, hvzl]) (by rw [hq, hvzq])
          rw [hvzcoord] at hzv
          exact hz hzv
      · exact hq
    · intro hq
      by_cases hvt : v = tv
      · rw [hvt]
        simpa [hD.ι_tv] using IsConj.refl t
      · by_cases hv0 : v = 0
        · subst hv0
          rw [qm_zero] at hq
          exact absurd hq zmod_two_zero_ne_one
        · exact hD.isConj_fuse hwzX hv0 hvt hwz0 hwztv (by rw [hlamwz, hvl])
            (by rw [hqmwz, hq])
  let P0 : Prop := ∃ u : V6, lam u = 1 ∧ qm u = 0 ∧ IsConj t (coordElt ι u)
  let P1 : Prop := ∃ u : V6, lam u = 1 ∧ qm u = 1 ∧ IsConj t (coordElt ι u)
  have hP : P0 ∨ P1 := by
    obtain ⟨v₀, hv₀l, hv₀X⟩ := hex
    rcases zmod_two_eq_zero_or_one (qm v₀) with h | h
    · exact Or.inl ⟨v₀, hv₀l, h, hv₀X⟩
    · exact Or.inr ⟨v₀, hv₀l, h, hv₀X⟩
  have hC0 : P0 → ∀ w, lam w = 1 → qm w = 0 → IsConj t (coordElt ι w) := by
    rintro ⟨u, hul, huq, huX⟩ w hwl hwq
    exact hD.isConj_fuse huX (ne_zero_of_lam_eq_one hwl) (ne_tv_of_lam_eq_one hwl)
      (ne_zero_of_lam_eq_one hul) (ne_tv_of_lam_eq_one hul)
      (by rw [hul, hwl]) (by rw [huq, hwq])
  have hC1 : P1 → ∀ w, lam w = 1 → qm w = 1 → IsConj t (coordElt ι w) := by
    rintro ⟨u, hul, huq, huX⟩ w hwl hwq
    exact hD.isConj_fuse huX (ne_zero_of_lam_eq_one hwl) (ne_tv_of_lam_eq_one hwl)
      (ne_zero_of_lam_eq_one hul) (ne_tv_of_lam_eq_one hul)
      (by rw [hul, hwl]) (by rw [huq, hwq])
  have hX36 : ¬ P0 → P1 → (∀ v, IsConj t (coordElt ι v) ↔ v ∈ X36) := by
    intro hP0' hP1 v
    rw [mem_X36]
    constructor
    · intro hX
      by_cases hvl : lam v = 0
      · exact (hlam0 v hvl).mp hX
      · have hvl1 : lam v = 1 := by
          rcases zmod_two_eq_zero_or_one (lam v) with h | h
          · exact absurd h hvl
          · exact h
        rcases zmod_two_eq_zero_or_one (qm v) with hq | hq
        · exact absurd ⟨v, hvl1, hq, hX⟩ hP0'
        · exact hq
    · intro hq
      by_cases hvl : lam v = 0
      · exact (hlam0 v hvl).mpr hq
      · have hvl1 : lam v = 1 := by
          rcases zmod_two_eq_zero_or_one (lam v) with h | h
          · exact absurd h hvl
          · exact h
        exact hC1 hP1 v hvl1 hq
  have hX28 : P0 → ¬ P1 → (∀ v, IsConj t (coordElt ι v) ↔ v ∈ X28) := by
    intro hP0 hP1' v
    rw [mem_X28]
    constructor
    · intro hX
      by_cases hvl : lam v = 0
      · have hq := (hlam0 v hvl).mp hX
        rw [hq, hvl, add_zero]
      · have hvl1 : lam v = 1 := by
          rcases zmod_two_eq_zero_or_one (lam v) with h | h
          · exact absurd h hvl
          · exact h
        rcases zmod_two_eq_zero_or_one (qm v) with hq | hq
        · rw [hq, hvl1, zero_add]
        · exact absurd ⟨v, hvl1, hq, hX⟩ hP1'
    · intro hv
      by_cases hvl : lam v = 0
      · have hq : qm v = 1 := by rw [hvl, add_zero] at hv; exact hv
        exact (hlam0 v hvl).mpr hq
      · have hvl1 : lam v = 1 := by
          rcases zmod_two_eq_zero_or_one (lam v) with h | h
          · exact absurd h hvl
          · exact h
        have hq : qm v = 0 := by
          have h : qm v + 1 = 1 := by rw [hvl1] at hv; exact hv
          exact add_right_cancel (show qm v + 1 = 0 + 1 from by rw [h, zero_add])
        exact hC0 hP0 v hvl1 hq
  have hX48 : P0 → P1 → (∀ v, IsConj t (coordElt ι v) ↔ v ∈ X48) := by
    intro hP0 hP1 v
    rw [mem_X48]
    constructor
    · intro hX
      by_cases hvl : lam v = 0
      · exact Or.inl ⟨hvl, (hlam0 v hvl).mp hX⟩
      · right
        rcases zmod_two_eq_zero_or_one (lam v) with h | h
        · exact absurd h hvl
        · exact h
    · intro hv
      rcases hv with ⟨hvl, hq⟩ | hvl1
      · exact (hlam0 v hvl).mpr hq
      · rcases zmod_two_eq_zero_or_one (qm v) with hq | hq
        · exact hC0 hP0 v hvl1 hq
        · exact hC1 hP1 v hvl1 hq
  rcases hP with hP0 | hP1
  · by_cases hP1' : P1
    · exact Or.inr (Or.inr (hX48 hP0 hP1'))
    · exact Or.inr (Or.inl (hX28 hP0 hP1'))
  · by_cases hP0' : P0
    · exact Or.inr (Or.inr (hX48 hP0' hP1))
    · exact Or.inl (hX36 hP0' hP1)

end CFSG.EvenSporadicStandard.HNRecog.Harada
