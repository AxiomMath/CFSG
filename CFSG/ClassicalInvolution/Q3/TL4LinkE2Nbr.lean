module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu9L

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkE2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem eq_of_mem_omegaNbr_link_of_noGNbr (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hbad : NoGNbr R t J) {M M' : Subgroup Y}
    (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hM' : M' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (h₁ : (secImg (CoreAssembly.conjClass (tightCore R)) t M).subgroupOf (linkGrp R t) ∈
      omegaNbr (restrictFamily (coreLinkFam R t) (linkGrp R t))
        ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t)))
    (h₂ : (secImg (CoreAssembly.conjClass (tightCore R)) t M').subgroupOf (linkGrp R t) ∈
      omegaNbr (restrictFamily (coreLinkFam R t) (linkGrp R t))
        ((secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t))) :
    secImg (CoreAssembly.conjClass (tightCore R)) t M =
      secImg (CoreAssembly.conjClass (tightCore R)) t M' := by
  have h := TightLargeHypR.typeRFam hL
  have hΦ := h.secFam (x := t)
  have hd := hL.datum
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
  have e₁ := mul_eq_of_noGNbr hL hJ hbad hM (omegaNbr_secFam_of_link hL hJ hM h₁) ha hb hc
  have e₂ := mul_eq_of_noGNbr hL hJ hbad hM' (omegaNbr_secFam_of_link hL hJ hM' h₂) ha hb' hc
  refine (hΦ.noTwins _ (secImg_mem hMx) _ ⟨secImg_mem hMx', _, hb, ?_⟩).symm
  rw [e₁, ← e₂]
  exact hb'

theorem subsingleton_omegaNbr_link (hL : TightLargeHypR r n Y R S t) (hT : ¬ TriNbrAll R t)
    (htr : ∀ L ∈ restrictFamily (coreLinkFam R t) (linkGrp R t),
      ∀ L' ∈ restrictFamily (coreLinkFam R t) (linkGrp R t),
        ∃ g : ↥(linkGrp R t), conjSub g L = L') :
    ∀ L ∈ restrictFamily (coreLinkFam R t) (linkGrp R t),
      ∀ M ∈ omegaNbr (restrictFamily (coreLinkFam R t) (linkGrp R t)) L,
        ∀ M' ∈ omegaNbr (restrictFamily (coreLinkFam R t) (linkGrp R t)) L, M = M' := by
  intro L hL' M hM M' hM'
  obtain ⟨J, hJ, hbad⟩ := exists_noGNbr_of_not_triNbrAll hT
  obtain ⟨g, hg⟩ := htr L hL' _ (subgroupOf_mem_linkRestrict hJ)
  have hcl := ((typeRFam_coreLinkFam hL).restrict (linkGrp R t)).hyp.conjInvariant
  have h1 := omegaNbr_conj hcl hM g
  have h2 := omegaNbr_conj hcl hM' g
  rw [hg] at h1 h2
  obtain ⟨_, ⟨K₁, hK₁, rfl⟩, -, e₁⟩ := h1.1
  obtain ⟨_, ⟨K₂, hK₂, rfl⟩, -, e₂⟩ := h2.1
  rw [e₁] at h1
  rw [e₂] at h2
  have he := eq_of_mem_omegaNbr_link_of_noGNbr hL hJ hbad hK₁ hK₂ h1 h2
  apply conjSub_injective g
  rw [e₁, e₂, he]

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.LinkE2
