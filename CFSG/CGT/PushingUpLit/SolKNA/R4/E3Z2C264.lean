module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3Lem77
public import CFSG.ClassicalInvolution.Q3.TL4Conn264O
public import CFSG.ClassicalInvolution.Q3.TL4Conn264D

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.T8 (XMem ne_of_mem_omegaNbr)
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3AM710
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan ThmDHyp ThmDConcl)
open CFSG.ClassicalInvolution.Q3.TL4 (card_inf_subgroupOf_le)
open scoped commutatorElement

section Orb

variable {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)} {r n : ℕ}

omit [Finite Q] in
theorem card_of_isPGroup_typeR_of_two_le (hr : 2 ≤ r) (h : TypeRFam r Φ) {L : Subgroup Q}
    (hL : L ∈ Φ) (h2 : IsPGroup 2 ↥L) : Nat.card ↥L = 2 ^ r := by
  obtain ⟨e⟩ := h.quat L hL L (AlphaFr.E2A.isSylow2In_self h2)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  rw [Nat.add_sub_cancel, pow_add]
  ring

theorem thmDHyp_orbGrpR (hr : 2 ≤ r) (h4 : Thm4RBelow r n) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K : Subgroup Q} (hK : K ∈ Φ)
    {u : ↥(Vtx.orbGrp Φ K)} (hu : IsUniqueInvolution (K.subgroupOf (Vtx.orbGrp Φ K)) u)
    {P : Subgroup ↥(Vtx.orbGrp Φ K)} (hPn : P.Normal) (hP2 : IsPGroup 2 ↥P) (huP : u ∈ P) :
    ThmDHyp r (restrictFamily Φ (Vtx.orbGrp Φ K)) := by
  have hcl := h.hyp.conjInvariant
  have hcomm := Vtx.commute_conj_of_not_conj h4 h hO hn hK
  have hX : TypeRFam r (restrictFamily Φ (Vtx.orbGrp Φ K)) := h.restrict _
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
  refine ⟨hX.hyp, htwo, fun L hL => card_of_isPGroup_typeR_of_two_le hr hX hL (htwo L hL),
    fun L hL => aEmpty_of_noTwins hX.hyp hL (hX.noTwins L hL), hgen, ?_, hOX, hin⟩
  intro L hL L' hL'
  obtain ⟨c, rfl⟩ := hconj L hL
  obtain ⟨c', rfl⟩ := hconj L' hL'
  exact ⟨c' * c⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩

theorem card_inf_of_wSet_eqR (hD : ThmDHyp r Φ) {V : Subgroup Q} (hW1 : WSet Φ = {V}) :
    ∀ L ∈ Φ, 4 ≤ Nat.card ↥(L ⊓ V) := by
  intro L hL
  have hW : V ∈ WSet Φ := by rw [hW1]; rfl
  have hVn : ∀ g : Q, conjSub g V = V := fun g => by
    have := WSet.conj hD.hyp.conjInvariant hW g
    rwa [hW1] at this
  have hLsyl : IsSylow2In L L := ⟨le_rfl, hD.two L hL, fun V' hVL _ hLV => le_antisymm hVL hLV⟩
  have hLD : L ∈ DSet Φ V :=
    ⟨mem_RSet_of_isSylow2In hL hLsyl, fun x _ => mem_normalizer_iff_conjSub_eq.mpr (hVn x)⟩
  obtain ⟨-, -, -, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D hD.hyp hW hLD hL hLsyl
  exact h4

end Orb

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem thmDHyp_secOrbR (hr : 2 ≤ r) (h4 : Thm4RBelow r n) (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hO2 : SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z) :
    ThmDHyp r (restrictFamily (TL4.secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
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
  exact thmDHyp_orbGrpR hr h4 h.secFam secQuot_oddCore_eq_bot hs.natCard_secQuot_lt
    (secImg_mem hs.xMem_K) hu hPn hP2 huP

theorem c264One_of_orbR (hr : 2 ≤ r) (h4 : Thm4RBelow r n) (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (h2K : IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd)))
    (h2J : IsPGroup 2 ↥(secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J))
    (honly : ∀ M ∈ TL4.secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t),
      M ≤ secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) →
        M = secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ∨
          M = secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J) :
    C264One (CoreAssembly.conjClass (tightCore Rd)) z t := by
  refine hs.c264One_of_conj fun c hc => ?_
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΦ := h.secFam (x := z * t)
  have hcl := hs.hyp.conjInvariant
  have hKc : XMem Ω (z * t) (conjSub c (tightCore Rd)) := XMem.conj' hcl hs.xMem_K hc
  have hMΦ := secImg_mem hKc
  by_cases hMX : secImg Ω (z * t) (conjSub c (tightCore Rd)) ≤ secOrb Ω (tightCore Rd) (z * t)
  · exact honly _ hMΦ hMX
  exfalso
  have hKΦ := secImg_mem hs.xMem_K
  have hJΦ := secImg_mem hs.xMem_J
  have hO := secQuot_oddCore_eq_bot (Ω := Ω) (x := z * t)
  have hn := hs.natCard_secQuot_lt
  have hnc : ¬ ∃ g ∈ omegaGen (TL4.secFam Ω (z * t)),
      conjSub g (secImg Ω (z * t) (conjSub c (tightCore Rd))) =
        secImg Ω (z * t) (tightCore Rd) := by
    rintro ⟨g, hg, e⟩
    apply hMX
    have e' : secImg Ω (z * t) (conjSub c (tightCore Rd)) =
        conjSub g⁻¹ (secImg Ω (z * t) (tightCore Rd)) := by
      rw [← e, conjSub_inv_conjSub]
    rw [e']
    exact Vtx.conjSub_le_orbGrp _ ⟨g⁻¹, (omegaGen _).inv_mem hg⟩
  obtain ⟨g₀, hg₀⟩ := hcj
  have hg₀G : g₀ ∈ omegaGen (TL4.secFam Ω (z * t)) := by
    rw [TL4.omegaGen_secFam]
    exact Subgroup.mem_top _
  have hncJ : ¬ ∃ g ∈ omegaGen (TL4.secFam Ω (z * t)),
      conjSub g (secImg Ω (z * t) (conjSub c (tightCore Rd))) = secImg Ω (z * t) J := by
    rintro ⟨g, hg, e⟩
    refine hnc ⟨g₀⁻¹ * g, (omegaGen _).mul_mem ((omegaGen _).inv_mem hg₀G) hg, ?_⟩
    rw [conjSub_mul, e, ← hg₀, conjSub_inv_conjSub]
  have hcK := Vtx.commutes_of_not_conj h4 hΦ hO hn hMΦ hKΦ hnc
  have hcJ := Vtx.commutes_of_not_conj h4 hΦ hO hn hMΦ hJΦ hncJ
  have hM2 : IsPGroup 2 ↥(secImg Ω (z * t) (conjSub c (tightCore Rd))) := by
    rw [secImg_conjSub_eq_map hcl hc]
    exact h2K.map _
  have hJN : secImg Ω (z * t) J ≤
      Subgroup.normalizer ((secImg Ω (z * t) (tightCore Rd) : Subgroup _) : Set _) := by
    obtain ⟨-, -, T', hT', hT'J, hT'N⟩ := hs.secImg_J_mem_omegaNbr
    have hT'syl : IsSylow2In T' (secImg Ω (z * t) J) :=
      Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΦ.hyp hJΦ hT' hT'J
    have hTJ : T' = secImg Ω (z * t) J :=
      (hT'syl.2.2 _ le_rfl h2J hT'syl.1).symm
    rw [← hTJ]
    exact hT'N
  have hJK2 : IsPGroup 2 ↥(secImg Ω (z * t) J ⊔ secImg Ω (z * t) (tightCore Rd)) :=
    h2J.to_sup_of_normal_right' h2K hJN
  have hMN : secImg Ω (z * t) (conjSub c (tightCore Rd)) ≤
      Subgroup.normalizer (((secImg Ω (z * t) J ⊔ secImg Ω (z * t) (tightCore Rd) :
        Subgroup _)) : Set _) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcJ a ha b hb
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcK a ha b hb
  have hP2 := hM2.to_sup_of_normal_right' hJK2 hMN
  have hcard : ∀ {B : Subgroup (SecQuot Ω (z * t))}, B ∈ TL4.secFam Ω (z * t) → IsPGroup 2 ↥B →
      B ≤ secImg Ω (z * t) (conjSub c (tightCore Rd)) ⊔
        (secImg Ω (z * t) J ⊔ secImg Ω (z * t) (tightCore Rd)) →
      2 < Nat.card ↥(B ⊓ (secImg Ω (z * t) (conjSub c (tightCore Rd)) ⊔
        (secImg Ω (z * t) J ⊔ secImg Ω (z * t) (tightCore Rd)))) := by
    intro B hB hB2 hBP
    rw [inf_eq_left.mpr hBP, card_of_isPGroup_typeR_of_two_le hr hΦ hB hB2]
    exact lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hr)
  have hKM : secImg Ω (z * t) (tightCore Rd) ≠ secImg Ω (z * t) (conjSub c (tightCore Rd)) :=
    fun e => hMX (e ▸ Vtx.le_orbGrp _)
  have hJM : secImg Ω (z * t) J ≠ secImg Ω (z * t) (conjSub c (tightCore Rd)) := by
    intro e
    apply hMX
    rw [← e, ← hg₀]
    exact Vtx.conjSub_le_orbGrp _ ⟨g₀, hg₀G⟩
  have hKJ : secImg Ω (z * t) (tightCore Rd) ≠ secImg Ω (z * t) J :=
    hs.secImg_J_mem_omegaNbr.2.1.symm
  exact false_of_three_secImg_E4 hs.partIHypG hs.hW.1 hE hs.xMem_K hs.xMem_J hKc hKJ hKM hJM hP2
    (hcard hKΦ h2K (le_sup_right.trans le_sup_right))
    (hcard hJΦ h2J (le_sup_left.trans le_sup_right)) (hcard hMΦ hM2 le_sup_left)

theorem c264One_of_wSet_secOrbR (hr : 2 ≤ r) (h4 : Thm4RBelow r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t))
    (hD : ThmDHyp r (restrictFamily (TL4.secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))))
    {V : Subgroup ↥(secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))}
    (hW1 : WSet (restrictFamily (TL4.secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) = {V}) :
    C264One (CoreAssembly.conjClass (tightCore Rd)) z t := by
  have hKX : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ≤
      secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) := Vtx.le_orbGrp _
  obtain ⟨g₀, hg₀⟩ := hcj
  have hJX : secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J ≤
      secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) := by
    rw [← hg₀]
    exact Vtx.conjSub_le_orbGrp _ ⟨g₀, by rw [TL4.omegaGen_secFam]; exact Subgroup.mem_top _⟩
  have hKΦ := secImg_mem hs.xMem_K
  have hJΦ := secImg_mem hs.xMem_J
  have h2 : ∀ {B : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t))},
      B ∈ TL4.secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t) →
      B ≤ secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) →
      IsPGroup 2 ↥B := fun hB hBX =>
    (hD.two _ ⟨_, hB, hBX, rfl⟩).of_equiv (Subgroup.subgroupOfEquivOfLe hBX)
  have hW : V ∈ WSet (restrictFamily (TL4.secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t))) := by
    rw [hW1]; rfl
  have hV2 : IsPGroup 2 ↥(V.map
      (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)).subtype) :=
    (Thompson.isPGroup_of_mem_WSet hW).map _
  have hc4 : ∀ {B : Subgroup (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t))},
      B ∈ TL4.secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t) →
      B ≤ secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) →
      2 < Nat.card ↥(B ⊓ V.map
        (secOrb (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t)).subtype) := by
    intro B hB hBX
    have h1 := card_inf_of_wSet_eqR hD hW1 _ ⟨_, hB, hBX, rfl⟩
    have h2 := card_inf_subgroupOf_le (A := B) V
    omega
  refine c264One_of_orbR hr h4 hs hE ⟨g₀, hg₀⟩ (h2 hKΦ hKX) (h2 hJΦ hJX) fun M hM hMX => ?_
  by_contra hne
  rw [not_or] at hne
  obtain ⟨L, hL, rfl⟩ := mem_secFam_iff.mp hM
  exact false_of_three_secImg_E4 hs.partIHypG hs.hW.1 hE hs.xMem_K hs.xMem_J hL
    hs.secImg_J_mem_omegaNbr.2.1.symm (Ne.symm hne.1) (Ne.symm hne.2) hV2 (hc4 hKΦ hKX)
    (hc4 hJΦ hJX) (hc4 hM hMX)

theorem c264PairR (hr : 2 ≤ r) (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hKN : (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd)).Normal)
    (hJN : (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J).Normal) :
    ∀ M ∈ TL4.secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t), M.Normal →
      M = secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) ∨
        M = secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J := by
  intro M hM hMN
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  have h := TightLargeHypR.typeRFam hs.large
  obtain ⟨L, hL, rfl⟩ := mem_secFam_iff.mp hM
  have hKJ : secImg Ω (z * t) (tightCore Rd) ≠ secImg Ω (z * t) J :=
    secImg_ne h hs.xMem_K hs.xMem_J hs.hz hs.ht
      (Q3CL.T8.mul_comm_of_mem_omegaNbr hs.hyp hs.hz hs.hJ hs.ht)
      (ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht)
  by_contra hne
  rw [not_or] at hne
  set H : Subgroup (SecQuot Ω (z * t)) := secImg Ω (z * t) (tightCore Rd) ⊔
    secImg Ω (z * t) J ⊔ secImg Ω (z * t) L with hHdef
  obtain ⟨Pb, hPb, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := H) IsPGroup.of_bot bot_le
  have hcard : ∀ B ∈ TL4.secFam Ω (z * t), B.Normal → B ≤ H → 2 < Nat.card ↥(B ⊓ Pb) := by
    intro B hB hBN hBH
    have hsyl : IsSylow2In (Pb ⊓ B) B :=
      AscP1Nine3.isSylow2In_inf_of_le_normalizer' hPb hBH fun y _ => by
        rw [Subgroup.normalizer_eq_top_iff.mpr hBN]
        exact Subgroup.mem_top y
    obtain ⟨e⟩ : Nonempty (↥(Pb ⊓ B) ≃* QuaternionGroup (2 ^ (r - 2))) := h.secFam.quat B hB _ hsyl
    rw [inf_comm, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have : 0 < 2 ^ (r - 2) := by positivity
    omega
  exact false_of_three_secImg_E4 hs.partIHypG hs.hW.1 hE hs.xMem_K hs.xMem_J hL
    hKJ (Ne.symm hne.1) (Ne.symm hne.2) hPb.2.1
    (hcard _ (secImg_mem hs.xMem_K) hKN (le_sup_left.trans le_sup_left))
    (hcard _ (secImg_mem hs.xMem_J) hJN (le_sup_right.trans le_sup_left))
    (hcard _ hM hMN le_sup_right)

theorem c264One_of_four_le (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hB : TightBelowR r n) (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) :
    C264One (CoreAssembly.conjClass (tightCore Rd)) z t := by
  by_cases hc : SecConj264 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J (z * t)
  · have hO2 := secInO2_of_four_le hr h4 hB hNo hs
    have hD := thmDHyp_secOrbR (by omega) h4 hs hO2
    obtain ⟨V, hV⟩ := wSet_eq_singleton_of_four_le hr hD.hyp hD.two hD.card hD.aEmpty hD.odd hD.inO2
    exact c264One_of_wSet_secOrbR (by omega) h4 hs hE hc hD hV
  · obtain ⟨hKN, hJN⟩ := hs.secImg_normal_of_not_conj h4 hc
    exact hs.c264One_of_pair hKN (c264PairR (by omega : 2 ≤ r) hs hE hKN hJN)

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
