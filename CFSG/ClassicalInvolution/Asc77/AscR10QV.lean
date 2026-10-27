module

public import CFSG.ClassicalInvolution.Asc77.AscR10Tw
public import CFSG.ClassicalInvolution.Asc77.AscR10G2Q

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Uniform
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement



section Restrict

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem hypOmegaModU_restrict {t : MemberType} (hΩ : HypOmegaModU t Ω) (Y : Subgroup G) :
    HypOmegaModU t (restrictFamily Ω Y) where
  conjInvariant := by
    rintro n _ ⟨L, hL, hLY, rfl⟩
    refine ⟨conjSub (n : G) L, hΩ.conjInvariant _ L hL, ?_, conjSub_subgroupOf Y n L⟩
    have := conjSub_mono (n := (n : G)) hLY
    rwa [conjSub_eq_self_of_mem n.2] at this
  classical := by
    rintro _ ⟨L, hL, hLY, rfl⟩
    obtain ⟨z, hz⟩ := hΩ.classical L hL
    exact ⟨_, hz.subgroupOf hLY⟩
  omega4 := by
    rintro _ ⟨K, hK, hKY, rfl⟩ _ ⟨J, hJ, hJY, rfl⟩ hne
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    obtain ⟨h1, h2⟩ := hΩ.omega4 K hK J hJ hKJ
    have hcard : Nat.card ↥(K.subgroupOf Y ⊓ J.subgroupOf Y) = Nat.card ↥(K ⊓ J) := by
      rw [inf_subgroupOf_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKY)).toEquiv
    rw [hcard]
    refine ⟨h1, fun h => ?_⟩
    have hle := h2 h
    rw [oddCoreOf_subgroupOf hKY, oddCoreOf_subgroupOf hJY]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have hab : (⁅(a : G), (b : G)⁆) ∈ ⁅K, J⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb)
    exact ⟨Subgroup.mem_subgroupOf.mpr (hle hab).1, Subgroup.mem_subgroupOf.mpr (hle hab).2⟩
  omega5 := by
    rintro _ ⟨K, hK, hKY, rfl⟩ _ ⟨J, hJ, hJY, rfl⟩ hne z' hz' v hv hnc hv2 hvz
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    have hzK : IsUniqueInvolution K (z' : G) := isUniqueInvolution_of_subgroupOf hz' hKY
    have hvJ : (v : G) ∈ J := Subgroup.mem_subgroupOf.mp hv
    have hnc' : ¬ ∀ w ∈ J, (v : G) * w = w * (v : G) := by
      intro h
      apply hnc
      rintro ⟨w, hw⟩ hw'
      exact Subtype.ext (h w (Subgroup.mem_subgroupOf.mp hw'))
    have hv2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := isPGroup_zpowers_coe_iff.mpr hv2
    have hn := hΩ.omega5 K hK J hJ hKJ (z' : G) hzK (v : G) hvJ hnc' hv2' (congrArg Subtype.val hvz)
    exact (mem_normalizer_subgroupOf_iff hKY).mp hn

theorem omegaStarNbr_subgroupOf_gen (hΩ : HypOmegaGen Ω) {Y K J : Subgroup G} (hKY : K ≤ Y)
    (hJY : J ≤ Y) (h : J ∈ omegaStarNbr Ω K) :
    J.subgroupOf Y ∈ omegaStarNbr (restrictFamily Ω Y) (K.subgroupOf Y) := by
  obtain ⟨hJ, hne, U, hU, hUJ, hUN⟩ := h
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := id hU
  obtain ⟨J₁, hJ₁, hRJ₁⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJ₁J : J₁ = J := Sec6Gen.eq_of_mem_USet hΩ hU hJ₁ hJ (hUR.trans hRJ₁.1) hUJ
  subst hJ₁J
  have hUY : U ≤ Y := hUJ.trans hJY
  have hRY : R ≤ Y := hRJ₁.1.trans hJY
  refine ⟨subgroupOf_mem_restrictFamily hJ₁ hJY, subgroupOf_ne_of_ne hKY hJY hne, U.subgroupOf Y,
    ⟨R.subgroupOf Y, mem_RSet_restrict hJ₁ hJY hRJ₁, Subgroup.subgroupOf_mono Y hUR, ?_, ?_⟩,
    Subgroup.subgroupOf_mono Y hUJ, fun x hx => ?_⟩
  · exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hUY)).mpr hcyc
  · rw [← Subgroup.relIndex_map_map_of_injective _ _ Y.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hUY, Subgroup.map_subgroupOf_eq_of_le hRY]
    exact hidx
  · exact (mem_normalizer_subgroupOf_iff hKY).mp (hUN (Subgroup.mem_subgroupOf.mp hx))

theorem aViol_subgroupOf (hΩ : HypOmegaGen Ω) {L K J : Subgroup G} {zK zJ : G} (hKL : K ≤ L)
    (hJL : J ≤ L) (hv : AViol Ω K J zK zJ) :
    AViol (restrictFamily Ω L) (K.subgroupOf L) (J.subgroupOf L)
      (⟨zK, hKL hv.hzK.mem⟩ : L) (⟨zJ, hJL hv.hzJ.mem⟩ : L) where
  star := omegaStarNbr_subgroupOf_gen hΩ hKL hJL hv.star
  not_nbr := fun h => hv.not_nbr (omegaNbr_of_restrict hKL hJL h)
  hzK := isUniqueInvolution_subgroupOf hv.hzK hKL
  hzJ := isUniqueInvolution_subgroupOf hv.hzJ hJL
  no_conj := by
    intro g hg hgc
    have hmap := T3Typed.map_pairNormalizers_le L.subtype (K.subgroupOf L) (J.subgroupOf L)
      (⟨zK, hKL hv.hzK.mem⟩ : L) (⟨zJ, hJL hv.hzJ.mem⟩ : L)
    rw [Subgroup.map_subgroupOf_eq_of_le hKL, Subgroup.map_subgroupOf_eq_of_le hJL] at hmap
    have hgY : (g : G) ∈ pairNormalizers K J zK zJ := hmap ⟨g, hg, rfl⟩
    have hgL : conjSub (g : G) K ≤ L := by
      have := conjSub_mono (n := (g : G)) hKL
      rwa [conjSub_eq_self_of_mem g.2] at this
    apply hv.no_conj (g : G) hgY
    have h1 : (conjSub (g : G) K).subgroupOf L = J.subgroupOf L := by
      rw [← conjSub_subgroupOf L g K]
      exact hgc
    have h2 := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr hgL, inf_eq_left.mpr hJL] at h2

end Restrict

section Quot3

variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}

theorem quotViol_of_aViol_three (hΛ : HypOmegaModU (.sl2 3 1) Λ) {K J : Subgroup Y}
    {zK zJ : Y} (hK : K ∈ Λ) (hv : AViol Λ K J zK zJ) :
    ∃ a : Y, QuotViol (oddQuotientFamily Λ) (K.map (oddQuot Y)) (J.map (oddQuot Y))
      (oddQuot Y zK) (oddQuot Y zJ) (oddQuot Y a) := by
  set π := oddQuot Y with hπ
  have hN : Odd (Nat.card (classicalInvolutionOddCore Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card Y
  have hΩg : HypOmegaGen Λ := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛ
  obtain ⟨a, ha, haj, hΛ', hz', hne⟩ := exists_twin_three hΛ hK hv
  have hzKbar := isUniqueInvolution_map_mk_of_odd
    (X := classicalInvolutionOddCore Y) (odd_natCard_oddCore_inf K) hv.hzK
  have hzJbar := isUniqueInvolution_map_mk_of_odd
    (X := classicalInvolutionOddCore Y) (odd_natCard_oddCore_inf J) hv.hzJ
  have hcomm : zK * zJ = zJ * zK := AViol.comm_gen hΩg hv
  have hzne : π zK ≠ π zJ := fun h =>
    AViol.ne_involution_gen hΩg hK hv
      (eq_of_map_eq_of_commute hN hv.hzK.sq hv.hzJ.sq hcomm h).symm
  have hKJ : J.map π ≠ K.map π := fun h => hzne (hzKbar.eq (h ▸ hzJbar))
  refine ⟨a, ⟨mem_oddQuotientFamily hK, mem_oddQuotientFamily hv.mem, hzKbar, hzJbar, hzne, ?_,
    omegaStarNbr_map_quot hv.star hKJ,
    T3Typed.map_pairNormalizers_le π K J zK zJ ⟨a, ha, rfl⟩, ?_, ?_⟩⟩
  · rw [← map_mul, ← map_mul, hcomm]
  · rw [← map_mul, ← map_inv, ← map_mul, haj]
  · intro hcon
    refine hne (eq_of_map_eq_of_twin_three hΛ hΛ' hK hz' hv.hzK ?_)
    rw [AscQuot.map_conjSub]
    exact hcon

end Quot3

section Components

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem quotViol_false_of_commutes {K J : Subgroup X} {z j a : X} (h : QuotViol Φ K J z j a)
    (hc : ∀ x ∈ K, ∀ y ∈ J, x * y = y * x) : False := by
  have hcent : pairNormalizers K J z j ≤ Subgroup.centralizer ({j} : Set X) := by
    unfold pairNormalizers
    refine sup_le (inf_le_left.trans fun k hk => ?_) (inf_le_left.trans fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc k hk j h.hj.mem
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (h.hj.commute_of_mem hx).symm
  have h1 : a * j = j * a := Subgroup.mem_centralizer_singleton_iff.mp (hcent h.ha)
  have h2 : a * j * a⁻¹ = j := by rw [h1]; group
  exact h.ne (h.haj.symm.trans h2)

variable {ι : Type}

theorem exists_fund_of_quotViol (D : Q3.LieSystemData3 ι X Φ) {i : ι}
    {R : Subgroup (D.kind i).G} {J : Subgroup X} {z j a : X}
    (h : QuotViol Φ (R.map (D.hom i)) J z j a) :
    ∃ S ∈ (D.kind i).fund, J = S.map (D.hom i) := by
  obtain ⟨i', S, hS, hJS⟩ := D.fundamental J h.mem_right
  by_cases hi : i' = i
  · subst hi
    exact ⟨S, hS, hJS⟩
  · exfalso
    refine quotViol_false_of_commutes h ?_
    rintro _ ⟨x, hx, rfl⟩ y hy
    rw [hJS] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact D.commute i i' (Ne.symm hi) x y'

end Components

section Residual

@[expose] def QV3Comp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), HypOmegaModU (.sl2 3 1) Φ →
    ∀ {ι : Type} (D : Q3.LieSystemData3 ι X Φ) (i : ι) (R S : Subgroup (D.kind i).G),
      R ∈ (D.kind i).fund → S ∈ (D.kind i).fund → ∀ z j a : X,
        QuotViol Φ (R.map (D.hom i)) (S.map (D.hom i)) z j a →
          D.kind i = Q3.CompData.model .G2 0

theorem g2Comp3_of_qv3Comp (hQ : QV3Comp) : G2Comp3 := by
  intro Y _ _ Λ hΩ K J zK zJ hK hv ι D j R hR hKR
  have hΩg : HypOmegaGen Λ := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  have hKL : K ≤ omegaGen Λ := le_omegaGen hK
  have hJL : J ≤ omegaGen Λ := le_omegaGen hv.mem
  have hΩL := hypOmegaModU_restrict hΩ (omegaGen Λ)
  obtain ⟨a, hQ'⟩ := quotViol_of_aViol_three hΩL (subgroupOf_mem_restrictFamily hK hKL)
    (aViol_subgroupOf hΩg hKL hJL hv)
  have hΦ := hypOmegaModU_oddQuotientFamily hΩL
  have hKR' : (K.subgroupOf (omegaGen Λ)).map (oddQuot ↥(omegaGen Λ)) = R.map (D.hom j) := hKR
  rw [hKR'] at hQ'
  obtain ⟨S, hS, hJS⟩ := exists_fund_of_quotViol D hQ'
  rw [hJS] at hQ'
  exact hQ _ _ hΦ D j R S hR hS _ _ _ hQ'

theorem sec3Typing_of_qv3Comp (h3 : Q3.CIT3Inductive) (hQ : QV3Comp) : Sec3Typing :=
  sec3Typing_of_g2Comp3 h3 (g2Comp3_of_qv3Comp hQ)

theorem res10aNoConj_nine_of_qv3Comp (p f : ℕ) [Fact p.Prime] (h3 : Q3.CIT3Inductive)
    (hQ : QV3Comp) (h9 : p ^ f = 9) : Res10aNoConj p f :=
  res10aNoConj_nine_of_cit3 p f h3 (g2Comp3_of_qv3Comp hQ) h9

theorem res10aNoConj9_of_qv3Comp (p f : ℕ) [Fact p.Prime] (hQ : QV3Comp) :
    Q3.CIT3Inductive → p ^ f = 9 → Res10aNoConj p f :=
  res10aNoConj9_of_g2Comp3 p f (g2Comp3_of_qv3Comp hQ)

end Residual

end CFSG.ClassicalInvolution.Asc77.T3CII
