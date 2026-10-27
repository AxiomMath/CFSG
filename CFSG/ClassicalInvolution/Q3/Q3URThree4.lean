module

public import CFSG.ClassicalInvolution.Q3.Q3URThree3
public import CFSG.ClassicalInvolution.Q3.Q3URDict
public import CFSG.ClassicalInvolution.Q3.Q3URKer3
public import CFSG.ClassicalInvolution.Q3.Q3URThree2
public import CFSG.ClassicalInvolution.Q3.Q3URTriple
public import CFSG.ClassicalInvolution.Q3.Q3WARow

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped MatrixGroups

section Row

theorem chainRow3U_three (h3 : OddThreeFreeInput) : ChainRow3U 3 := by
  intro G _ _ _ hnab K z hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hshape' := hshape
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dictU (m := 3) (by norm_num) hR.inClass hK hR.cls hshape
  let c : UCtx3 3 (conjClass3 K) K z :=
    { hm := by norm_num, hΩ := hR.inClass, hex := hex, hK := hK, hz := hR.cls, hP1 := hP1,
      hO3 := h3 G K z hR, d := d,
      hlift := Or.inr (ShapeUDict.kerInvolutionFree_three3 hR.inClass hex hK hsingle hR.cls hP1
        (h3 G K z hR) d) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  obtain ⟨ι, -, D, -⟩ := hshape'
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  obtain ⟨β, hβΩ, ⟨t, hwβ⟩, hnK, hW1, hnβ0, hW2, hlast⟩ := c.exists_partner_three nd hsingle
  obtain ⟨N, hNz, hNK, hβN, hn03, hn32, hW3, hW4⟩ :=
    c.exists_middle_three nd hMFZ D hsingle hβΩ hwβ hnK hW1 hnβ0 hlast
  obtain ⟨wN, hwN⟩ := c.hΩ.classical N hNz.1
  obtain ⟨H, hHΩ, hHβ, hHj0, hHN⟩ := c.exists_hexagon_closure nd hMFZ D hsingle hβΩ hwβ hnK hW2
    hnβ0 hlast hNz hNK hwN hW3 hn03 hn32
  obtain ⟨W1, hW1'⟩ := hW1
  obtain ⟨W2, hW2'⟩ := hW2
  obtain ⟨W3, hW3'⟩ := hW3
  obtain ⟨W4, hW4'⟩ := hW4
  have hwj0 := nd.isCl 0 (by omega)
  have hwj2 := nd.isCl 2 (by omega)
  have hKβ : K ≠ β := by
    intro h
    subst h
    exact hnβ0 (nd.commK 0 (by omega))
  have hβj0 : β ≠ nd.j 0 := by
    intro h
    apply hn03
    rw [← h]
    exact hβN
  have hβj2 : β ≠ nd.j 2 := by
    intro h
    have h1 := hlast
    rw [h] at h1
    exact not_commutes_self3 hwj2 h1
  have hβN' : β ≠ N := by
    intro h
    have h1 := hβN
    rw [← h] at h1
    exact not_commutes_self3 hwβ h1
  have hj0N : nd.j 0 ≠ N := by
    intro h
    apply hnβ0
    rw [h]
    exact hβN
  have hNj2 : N ≠ nd.j 2 := by
    intro h
    apply hn03
    rw [h]
    exact nd.far 0 (by omega) 2 (by omega) (by omega)
  have hj02 : nd.j 0 ≠ nd.j 2 := nd.inj 0 (by omega) 2 (by omega) (by omega)
  have hzβ : z * t = t * z :=
    unitaryStandardPair_involutions_commute card_gf9 (by norm_num) hW1' c.hz.mem hwβ.mem
      c.hz.orderOf_eq_two hwβ.orderOf_eq_two
  have hβ0w : t * nd.w 0 = nd.w 0 * t :=
    unitaryStandardPair_involutions_commute card_gf9 (by norm_num) hW2' hwβ.mem hwj0.mem
      hwβ.orderOf_eq_two hwj0.orderOf_eq_two
  have hw0N : nd.w 0 * wN = wN * nd.w 0 :=
    unitaryStandardPair_involutions_commute card_gf9 (by norm_num) hW3' hwj0.mem hwN.mem
      hwj0.orderOf_eq_two hwN.orderOf_eq_two
  have hNw2 : wN * nd.w 2 = nd.w 2 * wN :=
    unitaryStandardPair_involutions_commute card_gf9 (by norm_num) hW4' hwN.mem hwj2.mem
      hwN.orderOf_eq_two hwj2.orderOf_eq_two
  have hβwN : t * wN = wN * t := hβN t hwβ.mem wN hwN.mem
  obtain ⟨g₂, hg₂⟩ := hsingle (nd.j 2) (nd.mem 2 (by omega)).1
  have hT0 : ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G, θ.range = (K ⊔ β) ⊔ (β ⊔ nd.j 0) ∧
      θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = K ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = β ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = nd.j 0 :=
    c.triple_of_members_conj noCover_su4_three (by norm_num) hg₂ c.hK hβΩ (nd.mem 0 (by omega)).1
      (nd.commK 2 (by omega)) hlast (nd.far 0 (by omega) 2 (by omega) (by omega))
      (nd.ne_K 2 (by omega)).symm hβj2 hj02 c.hz hwβ hwj0 hzβ hβ0w (nd.wz 0 (by omega)).symm hKβ
      hβj0 (nd.ne_K 0 (by omega)).symm (nd.commK 0 (by omega)) hnK hnβ0
  obtain ⟨gH, hgH⟩ := hsingle H hHΩ
  have hβH : β ≠ H := by
    intro h
    have h1 := hHβ
    rw [← h] at h1
    exact not_commutes_self3 hwβ h1
  have hj0H : nd.j 0 ≠ H := by
    intro h
    have h1 := hHj0
    rw [← h] at h1
    exact not_commutes_self3 hwj0 h1
  have hNH : N ≠ H := by
    intro h
    have h1 := hHN
    rw [← h] at h1
    exact not_commutes_self3 hwN h1
  have hT1 : ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G, θ.range = (β ⊔ nd.j 0) ⊔ (nd.j 0 ⊔ N) ∧
      θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = β ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = nd.j 0 ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = N :=
    c.triple_of_members_conj noCover_su4_three (by norm_num) hgH hβΩ (nd.mem 0 (by omega)).1
      hNz.1 (Gaps.commutes_symm hHβ) (Gaps.commutes_symm hHj0) (Gaps.commutes_symm hHN) hβH hj0H
      hNH hwβ hwj0 hwN hβ0w hw0N hβwN hβj0 hj0N hβN' hβN hnβ0 hn03
  have hT2 : ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G, θ.range = (nd.j 0 ⊔ N) ⊔ (N ⊔ nd.j 2) ∧
      θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = nd.j 0 ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = N ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = nd.j 2 :=
    c.triple_of_members noCover_su4_three (by norm_num) (nd.mem 0 (by omega)) hNz
      (nd.mem 2 (by omega)) (nd.ne_K 0 (by omega)) hNK (nd.ne_K 2 (by omega)) hwj0 hwN hwj2 hw0N
      hNw2 (nd.wcomm 0 (by omega) 2 (by omega)) hj0N hNj2 hj02
      (nd.far 0 (by omega) 2 (by omega) (by omega)) hn03 hn32
  refine ⟨![K, β, nd.j 0, N, nd.j 2], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hK
    · exact hβΩ
    · exact (nd.mem 0 (by omega)).1
    · exact hNz.1
    · exact (nd.mem 2 (by omega)).1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    · exact nd.commK 0 (by omega)
    · exact commutes_K_of_neU3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d hNz hNK
    · exact nd.commK 2 (by omega)
    · exact hβN
    · exact hlast
    · exact nd.far 0 (by omega) 2 (by omega) (by omega)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    · exact ⟨W1, hW1'⟩
    · exact ⟨W2, hW2'⟩
    · exact ⟨W3, hW3'⟩
    · exact ⟨W4, hW4'⟩
  · intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      first | (exfalso; exact absurd hij (by decide)) | (exfalso; exact absurd hjk (by decide)) |
        skip
    · exact hT0
    · exact hT1
    · exact hT2

end Row

end CFSG.ClassicalInvolution.Q3.Q3W
