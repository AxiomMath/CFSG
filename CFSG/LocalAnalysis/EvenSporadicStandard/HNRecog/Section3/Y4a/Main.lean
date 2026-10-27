module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.NoPair

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4a_struct_of_good (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z) (hCls : GzClassFacts a z)
    {a₁ : G} (ha₁ : a₁ ∈ Gx z) (ha₁A : IsConj a a₁) (ha₁z : IsConj z (a₁ * z)) :
    Y4aStruct a z a₁ ∧ Y4bStruct a z a₁ := by
  obtain ⟨hshape, h5, hMeq, hM4, h960, -, ψ, -, hker⟩ :=
    y4a_setup hI h hF1.self hF2.self hF3 ha₁ ha₁A ha₁z
  obtain ⟨hcover, h96, hAorb, hAcard, hBorb, hBcard⟩ :=
    y4a_orbits hI h hF1 hF2 hF3 hPic hCls ha₁ ha₁A ha₁z
  have hMY : CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) ≤ derivedOf (Gxy a₁ z) :=
    Subgroup.map_subtype_le _
  have hQle : Qz z ≤ Gx z := Subgroup.map_subtype_le _
  have hNot : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have h1A : ∀ x : G, IsConj a x → x ≠ 1 := by
    rintro x hx rfl
    have ha1 : a = 1 := isConj_one_left.mp hx
    have h2 := h.orderOf_a
    rw [ha1, orderOf_one] at h2
    exact absurd h2 (by decide)
  have h1B : ∀ x : G, IsConj z x → x ≠ 1 := by
    rintro x hx rfl
    have hz1 : z = 1 := isConj_one_left.mp hx
    have h2 := h.orderOf_z
    rw [hz1, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hAB : Disjoint
      {t | t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) ∧ IsConj z t}
      {t | t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) ∧ IsConj a t} := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hxB⟩ ⟨-, hxA⟩
    exact hNot (hxA.trans hxB.symm)
  refine ⟨⟨hshape, ?_, ?_, hM4, ?_⟩, ⟨hAorb, ?_, ?_⟩⟩
  ·
    have hEq : Gxy a₁ z ⊓ Qz z = Qz z ⊓ Gx a₁ := by
      rw [Gxy_eq_inf, inf_assoc, inf_eq_right.mpr hQle, inf_comm]
    rw [hEq]
    exact h5
  · rw [inf_assoc, ← hMeq]
    exact (inf_eq_right.mpr hMY).symm
  · refine ⟨![{t | t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) ∧ IsConj z t},
      {t | t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) ∧ IsConj a t}], ⟨?_, ?_, ?_, ?_⟩,
      hBcard, hAcard⟩
    · intro i
      fin_cases i
      · rintro x ⟨hxM, hxB⟩
        exact ⟨hxM, h1B x hxB⟩
      · rintro x ⟨hxM, hxA⟩
        exact ⟨hxM, h1A x hxA⟩
    · rintro x ⟨hxM, hx1⟩
      rcases hcover x hxM hx1 with hxA | hxB
      · exact ⟨1, hxM, hxA⟩
      · exact ⟨0, hxM, hxB⟩
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hAB
      · exact hAB.symm
      · exact absurd rfl hij
    · intro i
      fin_cases i
      · exact hBorb
      · exact hAorb
  · intro t ht htA
    exact y4a_cent_shape ψ hker hMY hM4 ht (h96 t ht htA)
  · rintro ⟨E, hEM, hE2, hEB⟩
    have hfree := y4a_fixed_free (Y := derivedOf (Gxy a₁ z))
      (M := CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)))
      (A := {t | t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) ∧ IsConj a t})
      (B := {t | t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) ∧ IsConj z t})
      (fun m hm hm1 => (hcover m hm hm1).imp (fun hA => ⟨hm, hA⟩) (fun hB => ⟨hm, hB⟩))
      h960 (fun c hc => h96 c hc.1 hc.2) hBorb hBcard
    exact y4a_no_pair hM4 (fun l hl m hm => y4a_conj_mem_pCoreOf hl hm) (fun x hx => hx.1)
      (fun hx => h1B 1 hx.2 rfl) hBcard hBorb.conj_mem hfree
      ⟨E, hEM, hE2, fun t ht ht1 => ⟨hEM ht, hEB t ht ht1⟩⟩

theorem y4a_of_hyps (hI : TwoHSInterface) (hC : CSideFacts) {G : Type} [Group G] [Finite G]
    {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hCube : Vert CubeFacts a z)
    (hA8 : Vert A8Shapes a z) (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z)
    (hPic : Vert A8Pictures a z) (hOrb : Vert GzOrbitFacts a z)
    (hCls : Vert GzClassFacts a z) : Y4aFacts a z :=
  ⟨fun _ ha₁ ha₁A ha₁z =>
    (y4a_struct_of_good hI h hF1 hF2 hF3 hPic hCls.self ha₁ ha₁A ha₁z).1⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
