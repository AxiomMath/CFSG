module

public import CFSG.ClassicalInvolution.Asc77.AscT8RVL
public import CFSG.ClassicalInvolution.Asc77.AscT8Y3
public import CFSG.ClassicalInvolution.Asc77.AscT8RVEng
public import CFSG.ClassicalInvolution.Asc77.AscT8RNbrEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8

namespace T8R

section Pure

variable {Γ : Type} [Group Γ]

theorem braid_conj {a b : Γ} (ha : a * a = 1) (hb : b * b = 1) (h3 : (a * b) ^ 3 = 1) :
    a * b * a * b⁻¹ * a⁻¹ = b :=
  braid_conj_gen ha hb h3

end Pure


section Cert

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem sylow_inf_omegaNbrGen (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) :
    (S : Subgroup G) ⊓ omegaNbrGen Ω K = T := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  exact sylow_inf_omegaNbrGen_gen hs.hJ hTJ hTS
    (T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.hJ.1 hTΩ hTJ) hX

theorem not_mem_omegaNbr_of_four_le (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {M : Subgroup G} (hM : M ∈ Ω)
    (h4 : 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G))) (hMJ : M ≠ J) : M ∉ omegaNbr Ω K := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  exact not_mem_omegaNbr_of_four_le_gen hs.hJ hTJ hTS
    (T3.isSylow2In_of_mem_RSet_of_le hs.stand.odd hΩ hs.hJ.1 hTΩ hTJ) hX
    (fun hA h4' hAM hAJ => hΩ.eq_of_le_of_le hM hs.hJ.1 hA (by omega) hAM hAJ) h4 hMJ

theorem extraTrans (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) : ExtraTrans Ω K J S z t := by
  intro M hM h4 hMK hMJ
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hcl := hΩ.conjInvariant
  have hP := partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hWS : W ≤ (S : Subgroup G) := hs.hW.2.1
  have hc := ctxOf hP hW
  obtain ⟨η, hηG, hWη⟩ := id hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (hWη ▸ le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV : V ≤ W).trans hWS
  have hU : M ⊓ W ∈ η := by
    have := l6_11_proved p f hp hq G Ω hΩ S η hηG hηS M hM (by omega)
    rwa [← hWη] at this
  obtain ⟨S₀, hη, -⟩ := id hηG
  have hUU : M ⊓ W ∈ USet Ω := (hη.1 hU).1
  obtain ⟨RM, hRMD, hRMsyl⟩ := exists_sylow_mem_DSet hp hq hΩ hW hWS hM hUU inf_le_left
    (inf_le_right.trans hWS)
  obtain ⟨ρK, hρK, hρKR⟩ : ∃ ρ : Rep Ω W, ρ.K = K ∧ ρ.R = R := ⟨stdRepK hs, rfl, rfl⟩
  obtain ⟨ρJ, hρJ, -⟩ : ∃ ρ : Rep Ω W, ρ.K = J ∧ ρ.R = T := ⟨stdRepJ hs, rfl, rfl⟩
  obtain ⟨ρM, hρM, -⟩ : ∃ ρ : Rep Ω W, ρ.K = M ∧ ρ.R = RM :=
    ⟨mkRep hP hW hM hRMD hRMsyl, rfl, rfl⟩
  obtain ⟨zM, hzM⟩ := hΩ.exists_uniqueInvolution hp hq hM
  have hMnK : M ∉ omegaNbr Ω K := not_mem_omegaNbr_of_four_le hs hX hM h4 hMJ
  have hMnJ : M ∉ omegaNbr Ω J :=
    not_mem_omegaNbr_of_four_le (Std8.symm' hs) (eq_sup_oddCoreOf_swap hs hX) hM h4 hMK
  have hKnM : K ∉ omegaNbr Ω M := fun h =>
    hMnK (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hM hK h)
  have hJnM : J ∉ omegaNbr Ω M := fun h =>
    hMnJ (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hM hJΩ h)
  have hzK : IsUniqueInvolution ρK.K z := by rw [hρK]; exact hs.hz
  have htJ : IsUniqueInvolution ρJ.K t := by rw [hρJ]; exact hs.ht
  have hzMρ : IsUniqueInvolution ρM.K zM := by rw [hρM]; exact hzM
  have hsz : ρM.r * z * ρM.r⁻¹ = zM * z :=
    hc.conj_involution ρM ρK (by rw [hρK, hρM]; exact hMK) (by rw [hρK, hρM]; exact hKnM) hzMρ hzK
  have hst : ρM.r * t * ρM.r⁻¹ = zM * t :=
    hc.conj_involution ρM ρJ (by rw [hρJ, hρM]; exact hMJ) (by rw [hρJ, hρM]; exact hJnM) hzMρ htJ
  have hzW : z ∈ W := (uniqueInvolution_mem_W hp hq hΩ hW ρK.hK ρK.hR ρK.hRK hzK).2
  have hzMW : zM ∈ W := (uniqueInvolution_mem_W hp hq hΩ hW ρM.hK ρM.hR ρM.hRK hzMρ).2
  have hzzM : zM * z = z * zM := hc.comm_W zM hzMW z hzW
  have hrC : ρK.r ∈ Subgroup.centralizer ({z * t} : Set G) :=
    T8.le_centralizer_mul hs (hρKR ▸ ρK.hr)
  have hrN : ρK.r ∈ Subgroup.normalizer (W : Set G) := ρK.r_mem_normalizer
  have hsN : ρM.r ∈ Subgroup.normalizer (W : Set G) := ρM.r_mem_normalizer
  have hr2 : ρK.r * ρK.r ∈ W := D_sq_mem hp hq hΩ hW ρK.hR ρK.hr
  have hs2 : ρM.r * ρM.r ∈ W := D_sq_mem hp hq hΩ hW ρM.hR ρM.hr
  have hne : ρK.K ≠ ρM.K := by rw [hρK, hρM]; exact Ne.symm hMK
  have hnot : ρM.K ∉ omegaNbr Ω ρK.K := by rw [hρK, hρM]; exact hMnK
  have hcube : (piG W ρK.r * piG W ρM.r) ^ 3 = 1 := by
    rcases thompsonCube G Ω hP W hW ρK.R ρK.hR ρM.R ρM.hR ρK.r ρK.hr ρM.r ρM.hr ρK.hrW ρM.hrW with
      h | h
    · exact absurd ((piG_comm_iff hrN hsN).mpr h) (hc.noncomm ρK ρM hne hnot)
    · exact (piG_cube_iff hrN hsN).mpr h
  obtain ⟨c, hcC, hcK⟩ := CFSG.ClassicalInvolution.Asc77.T8R.extraTrans_core hcl ρK ρM hzM.sq hsz hst hzzM hrC hr2 hs2 hcube
    (fun ρ' h => hc.K_eq_of_img_eq ρ' ρM h)
  exact ⟨c, hcC, Or.inl (by rw [← hρK, ← hρM]; exact hcK)⟩

end Cert

end T8R

end CFSG.ClassicalInvolution.Asc77
