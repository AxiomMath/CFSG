module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.Reduce
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.L3Lay
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.L2Type
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.L3Quot

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.RankThree.PartTwo.Sec4 CFSG.HardMathSupport.Solomon.Coordinator

private theorem kdClubL3_cube_mod_nine (n : ℕ) :
    n ^ 3 % 9 = 0 ∨ n ^ 3 % 9 = 1 ∨ n ^ 3 % 9 = 8 := by
  have key : ∀ m, m < 9 → m ^ 3 % 9 = 0 ∨ m ^ 3 % 9 = 1 ∨ m ^ 3 % 9 = 8 := by decide
  rw [Nat.pow_mod]
  exact key _ (Nat.mod_lt _ (by norm_num))

theorem kdClubAt_of_projModel {π : Bool} {p f : ℕ} {K : Type}
    [Field K] (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (h3 : (p ^ f) % 3 ≠ 0) (h1 : (p ^ f) % 9 ≠ 1) (h8 : (p ^ f) % 9 ≠ 8) {Y : Type} [Group Y]
    (e : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K))) :
    KDClubAt Y := by
  have hfin := hK.finite
  haveI : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  intro β hβ1 hβ3 J hJ
  rcases dichot_proj_field hK hq hq2 e hβ3 hβ1 with ⟨σ, hσ⟩ | hin
  · exfalso
    obtain ⟨d⟩ := exists_frobData hK hσ
    have hc := kdClubL3_cube_mod_nine (p ^ d.f₀)
    rw [← d.pow_eq] at hc
    omega
  · rcases inner_lay_iso hK hq hq2 hin with hnone | ⟨Φ, hΦ, hall⟩
    · exact absurd hJ (hnone J)
    · have hJΦ : J = Φ.range := hall J hJ
      obtain ⟨F, _, _, hFc, ⟨eF⟩⟩ := exists_sl2_model hK
      let eJ : ↥(slPi π 2 (p ^ f) K) ≃* J :=
        (MonoidHom.ofInjective hΦ).trans (MulEquiv.subgroupCongr hJΦ.symm)
      refine kdClub_of_iso_quasisimple (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ)
        eJ (isQuasisimple_open (isQuasisimple_slPi_two hK hq hq2)) ?_ ?_
      · intro z hz
        have hz' : eF z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
          rw [← Subgroup.map_center_eq eF]
          exact ⟨z, hz, rfl⟩
        apply eF.injective
        rw [map_pow, map_one]
        exact sl2_center_sq hz'
      · refine (catalogIs_congr (QuotientGroup.congr _ _ eF (Subgroup.map_center_eq eF))).2 ?_
        refine catalogIs_psl_two_club ?_ ?_ ?_ ?_ <;> rw [hFc] <;> omega

theorem kdClubAt_l3 (K : Type) [Field K] [Finite K]
    (hK : Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7) :
    KDClubAt (StatedProj (StatedSL 3 K)) := by
  obtain ⟨p, f, hKp, hmod, h2⟩ := exists_true_data K (by omega)
  have hc : Nat.card K = p ^ f := by rw [hKp.card, piCard, Bool.cond_true]
  refine kdClubAt_of_projModel hKp hmod h2 (by omega) (by omega) (by omega) ?_
  exact (MulEquiv.refl _).trans (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hKp hmod)).symm

theorem kdClubAt_u3 (K : Type) [Field K] [Finite K] (q : ℕ)
    (hKq : Nat.card K = q ^ 2) (hq : q % 9 = 2 ∨ q % 9 = 5) (hq2 : q ≠ 2) :
    KDClubAt (StatedProj (StatedSU 3 q K)) := by
  obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hKq
  have hK : PiField false p f K := ⟨hF.prime, hF.one_le, by rw [piCard, Bool.cond_false]; exact hKq⟩
  have hmod : ModThree false (p ^ f) := by
    change p ^ f % 3 = 2
    omega
  refine kdClubAt_of_projModel hK hmod (by omega) (by omega) (by omega) (by omega) ?_
  exact (MulEquiv.refl _).trans (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm

end CFSG.LocalAnalysis.GLTheoremA
