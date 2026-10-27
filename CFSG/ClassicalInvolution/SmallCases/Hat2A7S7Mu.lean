module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7P1Th
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S3Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Hat2A7P1
  CFSG.ClassicalInvolution.Asc77.Thompson

section Mu


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {W : Subgroup G}


theorem piG_comm_a7 (hs : Std2A7 Ω K) (hW : W ∈ WSet Ω) {R T : Subgroup G}
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W)
    (htW : t ∉ W) : piG W r * piG W t = piG W t * piG W r := by
  have hP : PartIHypG8 Ω := partIHypG8_of_std2A7 hs
  have hΩ : HypOmegaGen Ω := hP.hyp
  have hkey := thompsonKey hP W hW
  obtain ⟨K₁, hK₁, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨J, hJ, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT.1
  by_cases hKJ : K₁ = J
  · subst hKJ
    exact Q3.Q3CL.Thompson.piG_comm_of_le hΩ hW hR hT
      (hkey R hR T hT K₁ hK₁ hRK.1 hTJ.1) hr ht hrW htW
  · have hstar : J ∈ omegaStarNbr Ω K₁ :=
      (Q3.Q3CL.Thompson.mem_omegaStarNbr_of_inf_W hΩ hW hK₁ hJ hKJ hR hT hRK hTJ).1
    have hnbr : J ∈ omegaNbr Ω K₁ :=
      omegaStarNbr_subset_omegaNbr_a7 hs.toPre2A7 hK₁ hJ hstar
    exact Q3.Q3CL.Thompson.piG_comm_of_mem_omegaNbr Sec6Gen.l6_2Gen hΩ hW
      (fun R hR T hT J hJ hRJ hTJ' => hkey R hR T hT J hJ hRJ hTJ') hK₁ hJ hKJ hR hT hRK hTJ
      hnbr hr ht hrW

theorem muGroup_comm_a7 (hs : Std2A7 Ω K) (hW : W ∈ WSet Ω) (x y : ↥(muGroup Ω W)) :
    x * y = y * x := by
  have hP : PartIHypG8 Ω := partIHypG8_of_std2A7 hs
  have hcomm : ∀ a ∈ muDelta Ω W, ∀ b ∈ muDelta Ω W, a * b = b * a := by
    rintro a ⟨R, hR, r, hr, hrW, hra⟩ b ⟨T, hT, t, ht, htW, htb⟩
    apply Subtype.ext
    show (a : NQuot (W ⊔ OCW W)) * b = b * a
    rw [hra, htb]
    exact piG_comm_a7 hs hW hR hT hr ht hrW htW
  have hgen : Subgroup.closure (muDelta Ω W) = ⊤ := closure_muDelta_eq_top Ω W
  have h1 : ∀ a ∈ muDelta Ω W, ∀ z : ↥(muGroup Ω W), z * a = a * z := by
    intro a ha z
    have hz : z ∈ Subgroup.centralizer ({a} : Set ↥(muGroup Ω W)) := by
      have hle : Subgroup.closure (muDelta Ω W) ≤
          Subgroup.centralizer ({a} : Set ↥(muGroup Ω W)) := by
        rw [Subgroup.closure_le]
        intro b hb
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact hcomm b hb a ha
      exact hle (hgen ▸ Subgroup.mem_top z)
    exact Subgroup.mem_centralizer_singleton_iff.mp hz
  have hx : y ∈ Subgroup.centralizer ({x} : Set ↥(muGroup Ω W)) := by
    have hle : Subgroup.closure (muDelta Ω W) ≤
        Subgroup.centralizer ({x} : Set ↥(muGroup Ω W)) := by
      rw [Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (h1 a ha x).symm
    exact hle (hgen ▸ Subgroup.mem_top y)
  exact (Subgroup.mem_centralizer_singleton_iff.mp hx).symm

theorem not_muIsoS4_a7 (hs : Std2A7 Ω K) (hW : W ∈ WSet Ω) : ¬ MuIsoS4 Ω W := by
  rintro ⟨e⟩
  have hc := muGroup_comm_a7 hs hW (e.symm (Equiv.swap 0 1)) (e.symm (Equiv.swap 1 2))
  have h2 := congrArg e hc
  simp only [map_mul, MulEquiv.apply_symm_apply] at h2
  exact absurd h2 (by decide)

theorem a7C23_3_proved : A7C23_3 := by
  intro G _ _ _ Ω K K' z h W hW _ hS4
  exact absurd hS4 (not_muIsoS4_a7 h.1.stand hW)

theorem a7C24_1_proved : A7C24_1 := by
  intro G _ _ _ Ω K K' z h W hW _ hS4 _
  exact not_muIsoS4_a7 h.1.stand hW hS4

end Mu

end CFSG.ClassicalInvolution.Hat2A7S
