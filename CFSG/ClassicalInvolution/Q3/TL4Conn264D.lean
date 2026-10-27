module

public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Hyp
public import CFSG.ClassicalInvolution.Q3.TL4Conn264A

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan ThmDHyp ThmDConcl)

section Orb

variable {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)} {r n : ℕ}

theorem exists_orbGrp_conj_of_le (h4 : Thm4RBelow r n) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K L : Subgroup Q}
    (hK : K ∈ Φ) (hL : L ∈ Φ) (hLX : L ≤ Vtx.orbGrp Φ K) :
    ∃ g ∈ Vtx.orbGrp Φ K, conjSub g K = L := by
  have hcl := h.hyp.conjInvariant
  have hcomm := Vtx.commute_conj_of_not_conj h4 h hO hn hK
  by_cases hc : ∃ g ∈ omegaGen Φ, conjSub g K = L
  · obtain ⟨g, hg, rfl⟩ := hc
    obtain ⟨g', hg', e⟩ := Vtx.exists_orbGrp_conj hcl hK hcomm hg
    exact ⟨g', hg', e.symm⟩
  · exfalso
    have hle : Vtx.orbGrp Φ K ≤ Subgroup.centralizer (L : Set Q) := by
      refine iSup_le fun g => ?_
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm L hL hc g g.2 a ha b hb
    obtain ⟨-, P, hP, hPnc⟩ := h.hyp.omega1 L hL
    apply hPnc
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact (Subgroup.mem_centralizer_iff.mp (hle (hLX (hP.1 b.2)))) _ (hP.1 a.2)

theorem thmDHyp_orbGrp (h4 : Thm4RBelow 3 n) (h : TypeRFam 3 Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q} (hK : K ∈ Φ)
    {u : ↥(Vtx.orbGrp Φ K)} (hu : IsUniqueInvolution (K.subgroupOf (Vtx.orbGrp Φ K)) u)
    {P : Subgroup ↥(Vtx.orbGrp Φ K)} (hPn : P.Normal) (hP2 : IsPGroup 2 ↥P) (huP : u ∈ P) :
    ThmDHyp 3 (restrictFamily Φ (Vtx.orbGrp Φ K)) := by
  have hcl := h.hyp.conjInvariant
  have hcomm := Vtx.commute_conj_of_not_conj h4 h hO hn hK
  have hX : TypeRFam 3 (restrictFamily Φ (Vtx.orbGrp Φ K)) := h.restrict _
  have hOX : classicalInvolutionOddCore ↥(Vtx.orbGrp Φ K) = ⊥ :=
    oddCore_eq_bot_of_isSubnormal (Vtx.isSubnormal_orbGrp hcl hK) hO
  have hconj : ∀ L ∈ restrictFamily Φ (Vtx.orbGrp Φ K),
      ∃ c : ↥(Vtx.orbGrp Φ K), conjSub c (K.subgroupOf (Vtx.orbGrp Φ K)) = L := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    obtain ⟨g, hg, rfl⟩ := exists_orbGrp_conj_of_le h4 h hO hn hK hL hLX
    exact ⟨⟨g, hg⟩, conjSub_subgroupOf _ ⟨g, hg⟩ K⟩
  have hin : ∀ L ∈ restrictFamily Φ (Vtx.orbGrp Φ K), ∀ v : ↥(Vtx.orbGrp Φ K),
      IsUniqueInvolution L v →
        ∃ Q' : Subgroup ↥(Vtx.orbGrp Φ K), Q'.Normal ∧ IsPGroup 2 ↥Q' ∧ v ∈ Q' := by
    intro L hL v hv
    obtain ⟨c, rfl⟩ := hconj L hL
    refine ⟨P, hPn, hP2, ?_⟩
    rw [← (hu.conj c).eq hv]
    exact hPn.conj_mem u huP c
  have htwo : ∀ L ∈ restrictFamily Φ (Vtx.orbGrp Φ K), IsPGroup 2 ↥L := by
    intro L hL
    obtain ⟨v, hv⟩ := Sec6Gen.exists_uniqueInvolution hX.hyp hL
    obtain ⟨Q', hQn, hQ2, hvQ⟩ := hin L hL v hv
    exact LinkE2.isPGroup_of_inO2_typeR hX hOX hL hv hQn hQ2 hvQ
  have hgenA : (⨆ c : ↥(Vtx.orbGrp Φ K), conjSub c (K.subgroupOf (Vtx.orbGrp Φ K))) = ⊤ := by
    apply Subgroup.map_injective (Vtx.orbGrp Φ K).subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have e2 : ∀ c : ↥(Vtx.orbGrp Φ K), (conjSub c (K.subgroupOf (Vtx.orbGrp Φ K))).map
        (Vtx.orbGrp Φ K).subtype = conjSub (c : Q) K := by
      intro c
      rw [conjSub_subgroupOf, Subgroup.map_subgroupOf_eq_of_le]
      exact Vtx.conjSub_le_orbGrp _ ⟨(c : Q), Vtx.orbGrp_le hcl hK c.2⟩
    simp_rw [e2]
    exact (Vtx.orbGrp_eq_iSup hcl hK hcomm).symm
  have hgen : pSpan (restrictFamily Φ (Vtx.orbGrp Φ K)) = ⊤ := by
    rw [eq_top_iff, ← hgenA]
    refine iSup_le fun c => le_pSpan ⟨conjSub (c : Q) K, hcl _ K hK,
      Vtx.conjSub_le_orbGrp _ ⟨(c : Q), Vtx.orbGrp_le hcl hK c.2⟩,
      conjSub_subgroupOf _ c K⟩
  refine ⟨hX.hyp, htwo, fun L hL => LinkE2.card_of_isPGroup_typeR hX hL (htwo L hL),
    fun L hL => aEmpty_of_noTwins hX.hyp hL (hX.noTwins L hL), hgen, ?_, hOX, hin⟩
  intro L hL L' hL'
  obtain ⟨c, rfl⟩ := hconj L hL
  obtain ⟨c', rfl⟩ := hconj L' hL'
  exact ⟨c' * c⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩

end Orb

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.thmDHyp_secOrb (h4 : Thm4RBelow 3 n) (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hO2 : SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z) :
    ThmDHyp 3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) := by
  obtain ⟨P, hPn, hP2, hPz⟩ := hO2
  have h := TightLargeHypR.typeRFam hs.large
  have hzY := mem_layerY_of_isUniqueInvolution h hs.xMem_K hs.hz
  have hzb := isUniqueInvolution_secImg h hs.xMem_K hs.hz
  have hKX : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ≤
      secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) := Vtx.le_orbGrp _
  have hu := isUniqueInvolution_subgroupOf hzb hKX
  have huP := hPz ⟨_, hKX hzb.mem⟩
    ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z), rfl⟩
  exact thmDHyp_orbGrp h4 h.secFam secQuot_oddCore_eq_bot hs.natCard_secQuot_lt
    (secImg_mem hs.xMem_K) hu hPn hP2 huP

theorem TightStd8R.thmDConcl_secOrb (hP : TightBelowRPlus 3 n) (h4 : Thm4RBelow 3 n)
    (hs : TightStd8R 3 n Rd Sd z J S R T W t)
    (hO2 : SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z) :
    ThmDConcl (restrictFamily (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) :=
  TC.Thin.thmDAbsAt_iff.mp (hP.thmD.d2 _ (lt_of_le_of_lt (Subgroup.card_le_card_group _)
    hs.natCard_secQuot_lt)) _ (hs.thmDHyp_secOrb h4 hO2)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
