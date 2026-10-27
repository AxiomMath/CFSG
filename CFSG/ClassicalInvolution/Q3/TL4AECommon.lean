module

public import CFSG.ClassicalInvolution.Q3.TL4StepNoTri
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEM
public import CFSG.ClassicalInvolution.Q3.TL4OddMu9L

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent)

section Twin

variable {r : ℕ} {Z : Type} [Group Z] [Finite Z]

omit [Finite Z] in
theorem map_le_of_label {P : Set (Subgroup Z)} {m : ℕ} (φ : ↥(pSpan P) →* AE.AEQ m)
    {L T : Subgroup Z} (hTL : T ≤ L) {M : Subgroup (AE.AEQ m)}
    (hlab : (L.subgroupOf (pSpan P)).map φ = M) : (T.subgroupOf (pSpan P)).map φ ≤ M := by
  rw [← hlab]
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hTL)

theorem mem_omegaNbr_of_twin_labels {Φ P : Set (Subgroup Z)} (hΦ : TypeRFam r Φ) (hPΦ : P ⊆ Φ)
    {m : ℕ} (hm : 5 ≤ m) (I : AEIdent P m)
    (hO : classicalInvolutionOddCore ↥(pSpan P) = ⊥) {L L' : Subgroup Z} (hL : L ∈ P)
    (hL' : L' ∈ P) {α : Finset (Fin m)} {hα : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα b)
    (hlab' : (L'.subgroupOf (pSpan P)).map I.φ = AE.memBar α hα (!b)) :
    L' ∈ omegaNbr Φ L := by
  have hne : L' ≠ L := by
    rintro rfl
    rw [hlab] at hlab'
    cases b
    · exact AE.memBar_true_ne_false hm α hα hlab'.symm
    · exact AE.memBar_true_ne_false hm α hα hlab'
  obtain ⟨z, hz⟩ := (hΦ.hyp.omega1 L (hPΦ hL)).1
  obtain ⟨z', hz'⟩ := (hΦ.hyp.omega1 L' (hPΦ hL')).1
  obtain ⟨T, hT⟩ := Sec7.exists_isSylow2In L
  obtain ⟨T', hT'⟩ := Sec7.exists_isSylow2In L'
  have hzT : z ∈ T := Q3CP.mem_of_isSylow2In_of_isUniqueInvolution hz hT
  have hz'T' : z' ∈ T' := Q3CP.mem_of_isSylow2In_of_isUniqueInvolution hz' hT'
  have hTT : T ≠ T' := by
    intro e
    have hz'L : z' ∈ L := hT.1 (by rw [e]; exact hz'T')
    have hzz : z' = z := (hz.unique z' hz'L hz'.sq).resolve_left hz'.ne_one
    exact hne (hΦ.noTwins L (hPΦ hL) L' ⟨hPΦ hL', z, hz, hzz ▸ hz'⟩)
  have hLP : L ≤ pSpan P := le_pSpan hL
  have hL'P : L' ≤ pSpan P := le_pSpan hL'
  have hTP : T ≤ pSpan P := hT.1.trans hLP
  have hT'P : T' ≤ pSpan P := hT'.1.trans hL'P
  have hM2 : ∀ c : Bool, IsPGroup 2 ↥(AE.memBar α hα c) := fun c =>
    IsPGroup.of_card (n := 3) (by rw [AE.natCard_memBar hm α hα c]; norm_num)
  have hcomm : ∀ x ∈ AE.memBar α hα b, ∀ y ∈ AE.memBar α hα (!b), x * y = y * x := by
    cases b
    · intro x hx y hy
      exact (SecIdE2.comm_memBar_twin α hα y hy x hx).symm
    · exact SecIdE2.comm_memBar_twin α hα
  have hN : AE.memBar α hα (!b) ≤
      Subgroup.normalizer (AE.memBar α hα b : Set (AE.AEQ m)) := by
    intro y hy
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x hx y hy
  have hMsup : IsPGroup 2 ↥(AE.memBar α hα b ⊔ AE.memBar α hα (!b)) :=
    IsPGroup.to_sup_of_normal_left' (hM2 b) (hM2 (!b)) hN
  have hker : IsPGroup 2 ↥I.φ.ker := I.isPGroup_ker hO
  have hD : (T ⊔ T').subgroupOf (pSpan P) ≤
      (AE.memBar α hα b ⊔ AE.memBar α hα (!b)).comap I.φ := by
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.subgroupOf_sup hTP hT'P, Subgroup.map_sup]
    exact sup_le_sup (map_le_of_label I.φ hT.1 hlab) (map_le_of_label I.φ hT'.1 hlab')
  have hD2 : IsPGroup 2 ↥((T ⊔ T').subgroupOf (pSpan P)) :=
    (hMsup.comap_of_ker_isPGroup I.φ hker).to_le hD
  have h2 : IsPGroup 2 ↥(T ⊔ T') := by
    have hmap : ((T ⊔ T').subgroupOf (pSpan P)).map (pSpan P).subtype = T ⊔ T' := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_of_le_left (sup_le hTP hT'P)
    rw [← hmap]
    exact hD2.map _
  obtain ⟨Sy, hSy⟩ := h2.exists_le_sylow
  have hRT := mem_RSet_of_isSylow2In (hPΦ hL) hT
  have hRT' := mem_RSet_of_isSylow2In (hPΦ hL') hT'
  have hc := Q3CP.l67Gen Z Φ hΦ.hyp Sy T hRT T' hRT' (le_sup_left.trans hSy)
    (le_sup_right.trans hSy) hTT
  refine ⟨hPΦ hL', hne, T', hRT', hT'.1, ?_⟩
  intro y hy
  refine hΦ.tight L (hPΦ hL) z hz ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hc z hzT y hy).symm

end Twin

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_commonNbr_of_linkAEAt (hL : TightLargeHypR r n Y R S t) (hAE : LinkAEAt R t)
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    ∃ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J := by
  obtain ⟨m, hm, -, ⟨I⟩⟩ := hAE
  have h := TightLargeHypR.typeRFam hL
  have hcl := hL.datum.hypOmegaGen.conjInvariant
  have hO : classicalInvolutionOddCore ↥(pSpan (coreLinkFam R t)) = ⊥ :=
    oddCore_linkGrp_eq_bot hL
  have hJm : secImg (CoreAssembly.conjClass (tightCore R)) t J ∈ coreLinkFam R t := ⟨J, hJ, rfl⟩
  obtain ⟨α, hα, b, hlab⟩ := I.label _ hJm
  obtain ⟨_, ⟨J', hJ', rfl⟩, hlab'⟩ := I.label_surj α hα (!b)
  have hnbr := mem_omegaNbr_of_twin_labels (h.secFam (x := t)) (coreLinkFam_subset hL) hm I hO
    hJm ⟨J', hJ', rfl⟩ hlab hlab'
  obtain ⟨ν, hν, hnbrY⟩ := exists_conj_omegaNbr_of_secImg h (xMem_of_mem_omegaNbr_core hL hJ)
    (xMem_of_mem_omegaNbr_core hL hJ') hnbr
  have hνt : ((ν⁻¹ : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y) ∈
      Subgroup.centralizer ({t} : Set Y) := layerY_le_centralizer (ν⁻¹).2
  set c : Y := ((ν⁻¹ : ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) : Y) with hcdef
  refine ⟨conjSub c J', conjSub_mem_omegaNbr_core hL hJ' hνt, ?_⟩
  have h1 := omegaNbr_conj hcl hnbrY c
  have e : conjSub c (conjSub (ν : Y) J) = J := by
    rw [hcdef, Subgroup.coe_inv, conjSub_inv_conjSub]
  rwa [e] at h1

theorem tightAECommonNbrR_holds : TightAECommonNbrR r n := by
  intro Y _ _ R S t hL _ hAE J hJ
  exact exists_commonNbr_of_linkAEAt hL hAE hJ

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
