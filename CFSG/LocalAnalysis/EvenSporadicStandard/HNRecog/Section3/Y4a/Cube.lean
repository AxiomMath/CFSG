module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Decomp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeEnum
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma y4aCube_orderOf_eq_two {G : Type} [Group G] {u v : G} (h : IsConj u v)
    (hu : orderOf u = 2) : orderOf v = 2 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc, ← MulAut.conj_apply c u, MulEquiv.orderOf_eq, hu]

private lemma y4aCube_sq_eq_one {G : Type} [Group G] {u v : G} (h : IsConj u v)
    (hu : orderOf u = 2) : v ^ 2 = 1 := by
  rw [← y4aCube_orderOf_eq_two h hu, pow_orderOf_eq_one]

private lemma y4aCube_ne_one {G : Type} [Group G] {u v : G} (h : IsConj u v)
    (hu : orderOf u = 2) : v ≠ 1 := by
  intro hv
  have h2 : orderOf v = 2 := y4aCube_orderOf_eq_two h hu
  rw [hv, orderOf_one] at h2
  exact absurd h2 (by decide)

private lemma y4aCube_symm_pow_two {G : Type} [Group G] {H : Subgroup G} {s : G}
    (hsD : s ∈ derivedOf H) (hs2 : s ^ 2 = 1)
    (φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf H)) : (φ.symm ⟨s, hsD⟩) ^ 2 = 1 := by
  apply φ.injective
  rw [map_pow, map_one, MulEquiv.apply_symm_apply]
  apply Subtype.ext
  simpa using hs2

private lemma y4aCube_symm_ne_one {G : Type} [Group G] {H : Subgroup G} {s : G}
    (hsD : s ∈ derivedOf H) (hsne : s ≠ 1)
    (φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf H)) : φ.symm ⟨s, hsD⟩ ≠ 1 := by
  intro h1
  apply hsne
  have h2 : (⟨s, hsD⟩ : ↥(derivedOf H)) = 1 := by
    rw [← MulEquiv.apply_symm_apply φ (⟨s, hsD⟩ : ↥(derivedOf H)), h1, map_one]
  simpa using congrArg Subtype.val h2

private lemma y4aCube_false_of_mem_2B (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hPic : Vert A8Pictures a z) {x y s : G} (hx : IsConj a x)
    (hy : IsConj a y) (hxyA : IsConj a (x * y)) (hH : IsShapeTwoTwoTimesA8 ↥(Gxy x y))
    (hsD : s ∈ derivedOf (Gxy x y)) (hsB : IsConj z s)
    (hmul : IsConj z (x * s) ∨ IsConj z (y * s)) : False := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 hH
  have hs2 : s ^ 2 = 1 := y4aCube_sq_eq_one hsB h.orderOf_z
  have hsne : s ≠ 1 := y4aCube_ne_one hsB h.orderOf_z
  have hσ2 : (φ.symm ⟨s, hsD⟩ : alternatingGroup (Fin 8)) ^ 2 = 1 :=
    y4aCube_symm_pow_two hsD hs2 φ
  have hσne : (φ.symm ⟨s, hsD⟩ : alternatingGroup (Fin 8)) ≠ 1 :=
    y4aCube_symm_ne_one hsD hsne φ
  have hσcoe : (φ (φ.symm ⟨s, hsD⟩) : G) = s :=
    congrArg Subtype.val (MulEquiv.apply_symm_apply φ (⟨s, hsD⟩ : ↥(derivedOf (Gxy x y))))
  have hy_orb : y ∈ orb2A x x := ⟨hx.symm.trans hy, hx.symm.trans hxyA⟩
  have hPicx : A8Pictures x z := hPic x z hx (IsConj.refl z)
  rcases cycleType_eq_of_sq_eq_one hσ2 hσne with hct | hct
  · have hxs : IsConj x s := by
      have h1 := (hPicx.fig8a y hy_orb φ (φ.symm ⟨s, hsD⟩) hct).1
      rw [hσcoe] at h1
      exact h1
    exact not_isConj_of_isF5Type hI h ((hx.trans hxs).trans hsB.symm)
  · have hfig := hPicx.fig8b y hy_orb φ (φ.symm ⟨s, hsD⟩) hct
    rcases hmul with hxsB | hysB
    · have hxs : IsConj x (x * s) := by
        have h1 := hfig.2.1
        rw [hσcoe] at h1
        exact h1
      exact not_isConj_of_isF5Type hI h ((hx.trans hxs).trans hxsB.symm)
    · have hys : IsConj x (y * s) := by
        have h1 := hfig.2.2.1
        rw [hσcoe] at h1
        exact h1
      exact not_isConj_of_isF5Type hI h ((hx.trans hys).trans hysB.symm)

private lemma y4aCube_cycleType_two_two (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hPic : Vert A8Pictures a z) {x y t : G} (hx : IsConj a x)
    (hy : IsConj a y) (hxyA : IsConj a (x * y)) (htD : t ∈ derivedOf (Gxy x y))
    (htA : IsConj a t) :
    ∀ φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy x y)),
      ((φ.symm ⟨t, htD⟩ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)).cycleType = {2, 2} := by
  intro φ
  have ht2 : t ^ 2 = 1 := y4aCube_sq_eq_one htA h.orderOf_a
  have htne : t ≠ 1 := y4aCube_ne_one htA h.orderOf_a
  have hσ2 : (φ.symm ⟨t, htD⟩ : alternatingGroup (Fin 8)) ^ 2 = 1 :=
    y4aCube_symm_pow_two htD ht2 φ
  have hσne : (φ.symm ⟨t, htD⟩ : alternatingGroup (Fin 8)) ≠ 1 :=
    y4aCube_symm_ne_one htD htne φ
  rcases cycleType_eq_of_sq_eq_one hσ2 hσne with hct | hct
  · exact hct
  · exfalso
    have hy_orb : y ∈ orb2A x x := ⟨hx.symm.trans hy, hx.symm.trans hxyA⟩
    have hfig := (hPic x z hx (IsConj.refl z)).fig8b y hy_orb φ (φ.symm ⟨t, htD⟩) hct
    have hzt : IsConj z t := by
      have h1 := hfig.1
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1
    exact not_isConj_of_isF5Type hI h (htA.trans hzt.symm)

theorem y4a_mem_derived_of_cube (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z) {x y t : G}
    (hxy : x * y = y * x) (hxt : x * t = t * x) (hyt : y * t = t * y) (hx : IsConj a x)
    (hy : IsConj a y) (hxyA : IsConj a (x * y)) (ht : IsConj a t) (hxtB : IsConj z (x * t))
    (hytB : IsConj z (y * t)) (hxytB : IsConj z (x * y * t)) :
    IsShapeTwoTwoTimesA8 ↥(Gxy x y) ∧ ∃ htD : t ∈ derivedOf (Gxy x y),
      ∀ φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy x y)),
        ((φ.symm ⟨t, htD⟩ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)).cycleType =
          {2, 2} := by
  have hF3x : Fusion3Facts x z := hF3 x z hx (IsConj.refl z)
  have hy_orb : y ∈ orb2A x x := ⟨hx.symm.trans hy, hx.symm.trans hxyA⟩
  have hH : IsShapeTwoTwoTimesA8 ↥(Gxy x y) := hF3x.shape_2A y hy_orb
  refine ⟨hH, ?_⟩
  have hx2 : x ^ 2 = 1 := y4aCube_sq_eq_one hx h.orderOf_a
  have hy2 : y ^ 2 = 1 := y4aCube_sq_eq_one hy h.orderOf_a
  have hxx : x * x = 1 := by simpa [pow_two] using hx2
  have hyy : y * y = 1 := by simpa [pow_two] using hy2
  have hx1 : x ≠ 1 := y4aCube_ne_one hx h.orderOf_a
  have hy1 : y ≠ 1 := y4aCube_ne_one hy h.orderOf_a
  have hxy1 : x ≠ y := by
    intro hxy_eq
    exact y4aCube_ne_one hxyA h.orderOf_a (by rw [← hxy_eq, ← pow_two, hx2])
  have htH : t ∈ Gxy x y := mem_Gxy.mpr ⟨mem_Gx.mpr hxt, mem_Gx.mpr hyt⟩
  obtain ⟨u, hu, s, hs, heq⟩ :=
    exists_mul_eq_of_isShapeTwoTwoTimesA8 hH hx2 hy2 hxy hx1 hy1 hxy1 t htH
  rcases eq_of_mem_closure_two hx2 hy2 hxy hu with hu1 | hu2 | hu3 | hu4
  · subst u
    have htD : t ∈ derivedOf (Gxy x y) := by
      rw [heq, one_mul]
      exact hs
    exact ⟨htD, y4aCube_cycleType_two_two hI h hPic hx hy hxyA htD ht⟩
  · subst u
    exfalso
    have hs_eq : s = x * t := by
      have h1 : x * t = s := by rw [heq, ← mul_assoc, hxx, one_mul]
      exact h1.symm
    have hsB : IsConj z s := by rw [hs_eq]; exact hxtB
    have hysB : IsConj z (y * s) := by
      rw [hs_eq]
      have h1 : y * (x * t) = x * y * t := by rw [← mul_assoc, hxy.symm]
      rw [h1]; exact hxytB
    exact y4aCube_false_of_mem_2B hI h hPic hx hy hxyA hH hs hsB (Or.inr hysB)
  · subst u
    exfalso
    have hs_eq : s = y * t := by
      have h1 : y * t = s := by rw [heq, ← mul_assoc, hyy, one_mul]
      exact h1.symm
    have hsB : IsConj z s := by rw [hs_eq]; exact hytB
    have hxsB : IsConj z (x * s) := by
      rw [hs_eq, ← mul_assoc]; exact hxytB
    exact y4aCube_false_of_mem_2B hI h hPic hx hy hxyA hH hs hsB (Or.inl hxsB)
  · subst u
    exfalso
    have hxy2 : (x * y) * (x * y) = 1 := by
      have h1 : (x * y) ^ 2 = 1 := y4aCube_sq_eq_one hxyA h.orderOf_a
      simpa [pow_two] using h1
    have hs_eq : s = x * y * t := by
      have h1 : x * y * t = s := by rw [heq, ← mul_assoc, hxy2, one_mul]
      exact h1.symm
    have hsB : IsConj z s := by rw [hs_eq]; exact hxytB
    have hxsB : IsConj z (x * s) := by
      rw [hs_eq]
      have h1 : x * ((x * y) * t) = y * t := by
        rw [← mul_assoc x (x * y) t, ← mul_assoc x x y, hxx, one_mul]
      rw [h1]; exact hytB
    exact y4aCube_false_of_mem_2B hI h hPic hx hy hxyA hH hs hsB (Or.inl hxsB)

end CFSG.EvenSporadicStandard.HNRecog.Section3
