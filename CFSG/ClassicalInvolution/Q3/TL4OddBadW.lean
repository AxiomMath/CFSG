module

public import CFSG.ClassicalInvolution.Q3.TL4OddFrLinkP

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight

section Graph

variable {Y : Type} [Group Y]

@[expose] def NoGNbr (R : Subgroup Y) (t : Y) (J : Subgroup Y) : Prop :=
  ∀ K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
    K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J → ∀ u z' : Y,
      IsUniqueInvolution J u → IsUniqueInvolution K' z' → z' = t * u

theorem exists_noGNbr_of_not_triNbrAll {R : Subgroup Y} {t : Y} (h : ¬ TriNbrAll R t) :
    ∃ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), NoGNbr R t J := by
  unfold TriNbrAll at h
  push Not at h
  obtain ⟨J, hJ, u, hu, hK⟩ := h
  refine ⟨J, hJ, fun K' hK'K hK'J u' z' hu' hz' => ?_⟩
  obtain rfl := hu'.eq hu
  exact hK K' hK'K hK'J z' hz'

end Graph

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem noGNbr_conj (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y} (hbad : NoGNbr R t J)
    {c : Y} (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) : NoGNbr R t (conjSub c J) := by
  have hcl := hL.datum.hypOmegaGen.conjInvariant
  have hci : c⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) :=
    (Subgroup.centralizer ({t} : Set Y)).inv_mem hc
  intro K' hK'K hK'J u z' hu hz'
  have h1 : conjSub c⁻¹ K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
    conjSub_mem_omegaNbr_core hL hK'K hci
  have h2 : conjSub c⁻¹ K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J := by
    have h3 := omegaNbr_conj hcl hK'J c⁻¹
    rwa [conjSub_inv_conjSub] at h3
  have hu' : IsUniqueInvolution J (c⁻¹ * u * c⁻¹⁻¹) := by
    have h3 := hu.conj c⁻¹
    rwa [conjSub_inv_conjSub] at h3
  have e := hbad _ h1 h2 _ _ hu' (hz'.conj c⁻¹)
  have hct : c * t * c⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  calc z' = c * (c⁻¹ * z' * c⁻¹⁻¹) * c⁻¹ := by group
    _ = c * (t * (c⁻¹ * u * c⁻¹⁻¹)) * c⁻¹ := by rw [e]
    _ = (c * t * c⁻¹) * u := by group
    _ = t * u := by rw [hct]

theorem xMem_core (hL : TightLargeHypR r n Y R S t) :
    XMem (CoreAssembly.conjClass (tightCore R)) t (tightCore R) := by
  have hd := hL.datum
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := tightCore R) (IsPGroup.of_bot (p := 2)) bot_le
  refine ⟨CoreAssembly.mem_conjClass_self _, Subgroup.le_normalizer
    hd.isUniqueInvolution_core.mem, P, hP, fun p hp => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (hd.cent (tightCore_le R (hP.1 hp)))

theorem mul_eq_of_noGNbr (hL : TightLargeHypR r n Y R S t) {J M : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hbad : NoGNbr R t J)
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hnbr : secImg (CoreAssembly.conjClass (tightCore R)) t M ∈
      omegaNbr (secFam (CoreAssembly.conjClass (tightCore R)) t)
        (secImg (CoreAssembly.conjClass (tightCore R)) t J))
    {a b c : SecQuot (CoreAssembly.conjClass (tightCore R)) t}
    (ha : IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) t J) a)
    (hb : IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) t M) b)
    (hc : IsUniqueInvolution (secImg (CoreAssembly.conjClass (tightCore R)) t (tightCore R)) c) :
    b = c * a := by
  have h := TightLargeHypR.typeRFam hL
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hJx := xMem_of_mem_omegaNbr_core hL hJ
  have hMx := xMem_of_mem_omegaNbr_core hL hM
  have hKx := xMem_core hL
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution hΩ hM.1
  obtain ⟨ν, hν, hMν⟩ := exists_conj_omegaNbr_of_secImg h hJx hMx hnbr
  have hνt : (ν : Y) ∈ Subgroup.centralizer ({t} : Set Y) := layerY_le_centralizer ν.2
  have hJν := conjSub_mem_omegaNbr_core hL hJ hνt
  have e : w = t * ((ν : Y) * u * (ν : Y)⁻¹) :=
    noGNbr_conj hL hbad hνt M hM hMν _ _ (hu.conj (ν : Y)) hw
  have hu' := isUniqueInvolution_secImg h hJx hu
  have hw' := isUniqueInvolution_secImg h hMx hw
  have ht' := isUniqueInvolution_secImg h hKx hd.isUniqueInvolution_core
  rw [ha.eq hu', hb.eq hw', hc.eq ht']
  have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY
      (CoreAssembly.conjClass (tightCore R)) t))) ν = 1 := (QuotientGroup.eq_one_iff ν).mpr hν
  have h2 : (⟨w, mem_layerY_of_isUniqueInvolution h hMx hw⟩ :
      ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) =
      ⟨t, mem_layerY_of_isUniqueInvolution h hKx hd.isUniqueInvolution_core⟩ *
        (ν * ⟨u, mem_layerY_of_isUniqueInvolution h hJx hu⟩ * ν⁻¹) := Subtype.ext e
  rw [h2, map_mul, map_mul, map_mul, map_inv, h1, one_mul, inv_one, mul_one]

theorem eq_of_mem_omegaNbr_coreLinkFam_of_noGNbr (hL : TightLargeHypR r n Y R S t)
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hbad : NoGNbr R t J)
    {Mb Mb' : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore R)) t)}
    (h₁ : Mb ∈ omegaNbr (coreLinkFam R t) (secImg (CoreAssembly.conjClass (tightCore R)) t J))
    (h₂ : Mb' ∈ omegaNbr (coreLinkFam R t) (secImg (CoreAssembly.conjClass (tightCore R)) t J)) :
    Mb = Mb' := by
  have h := TightLargeHypR.typeRFam hL
  have hΦ := h.secFam (x := t)
  have hd := hL.datum
  obtain ⟨M, hM, rfl⟩ := h₁.1
  obtain ⟨M', hM', rfl⟩ := h₂.1
  have hJx := xMem_of_mem_omegaNbr_core hL hJ
  have hMx := xMem_of_mem_omegaNbr_core hL hM
  have hMx' := xMem_of_mem_omegaNbr_core hL hM'
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hd.hypOmegaGen hJ.1
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution hd.hypOmegaGen hM.1
  obtain ⟨w', hw'⟩ := Sec6Gen.exists_uniqueInvolution hd.hypOmegaGen hM'.1
  have ha := isUniqueInvolution_secImg h hJx hu
  have hb := isUniqueInvolution_secImg h hMx hw
  have hb' := isUniqueInvolution_secImg h hMx' hw'
  have hc := isUniqueInvolution_secImg h (xMem_core hL) hd.isUniqueInvolution_core
  have e₁ := mul_eq_of_noGNbr hL hJ hbad hM (omegaNbr_secFam_of_coreLinkFam hL h₁) ha hb hc
  have e₂ := mul_eq_of_noGNbr hL hJ hbad hM' (omegaNbr_secFam_of_coreLinkFam hL h₂) ha hb' hc
  refine (hΦ.noTwins _ (secImg_mem hMx) _ ⟨secImg_mem hMx', _, hb, ?_⟩).symm
  rw [e₁, ← e₂]
  exact hb'

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
