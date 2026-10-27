module

public import CFSG.ClassicalInvolution.RouteD.TwinYStatements
public import CFSG.ClassicalInvolution.RouteD.TwinYP1Cover
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChainMain
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinU
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

section Residuals

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinYGenT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ (J : Subgroup G) (t : G), J ∈ centralizingMembers (𝒞 K) {z} → J ≠ K → J ≠ T →
        IsClassicalMember p f J t →
        CentralizerGenerationStar (𝒞 K) (Subgroup.closure ({z, e.u, t} : Set G)) t

@[expose] def TwinYTransitive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ K₁ ∈ locFamily (𝒞 K) e.u, ∀ L ∈ locFamily (𝒞 K) e.u,
        ∃ g : locQuot (𝒞 K) e.u, conjSub g K₁ = L

@[expose] def TwinYSingle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∃ D : LieSystemData p f (locQuot (𝒞 K) e.u) (locFamily (𝒞 K) e.u), D.card = 1

@[expose] def TwinYRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ D : LieSystemData p f (locQuot (𝒞 K) e.u) (locFamily (𝒞 K) e.u), D.card = 1 →
        ∀ i : Fin D.card, (∃ (d : ℕ) (ε : Bool), 5 ≤ d ∧ IsOrthTag d ε (D.tag i) (D.rank i)) →
          D.tag i = (twinYModel (p ^ f) tY nY).1 ∧ D.rank i = (twinYModel (p ^ f) tY nY).2

end Residuals

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem TwinRow.tag_facts {t : StatedLieTag} {n : ℕ} (h : TwinRow t n) :
    t ≠ .G2 ∧ t ≠ .trialityD4 ∧ ¬ (t = .PSL ∧ n = 2) := by
  rcases h with ⟨-, rfl, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, -⟩ |
    ⟨-, rfl, rfl⟩ <;> exact ⟨by decide, by decide, by simp⟩

theorem exists_frameMembers [IsSimpleGroup G] {K T : Subgroup G} {z : G} {tY : StatedLieTag}
    {nY : ℕ} (hnab : ∃ x y : G, x * y ≠ y * x) (S : RouteDSetup p f K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (clsT : IsClassicalMember p f T z) (e : TwinElt K T z) :
    ∃ (J J' : Subgroup G) (t : G), J ∈ centralizingMembers (𝒞 K) {z} ∧ J ≠ K ∧ J ≠ T ∧
      IsClassicalMember p f J t ∧ t ≠ z ∧ IsClassicalMember p f J' t ∧ Commutes J J' ∧
      J' ∈ centralizingMembers (𝒞 K) {e.u} := by
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass
    (CoreAssembly.mem_conjClass_self K) S.cls hshape
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨J, hJ, hJK, hJT⟩ := exists_big_member S.inClass S.p1 rf d hKiso hTiso
  obtain ⟨t, hJt⟩ := S.inClass.classical J hJ.1
  have htz : t ≠ z := by
    intro htz
    subst htz
    obtain ⟨L', hL', hL'J, hnc⟩ := exists_noncomm_of_ne S.inClass S.exact S.p1 rf d
      ⟨CoreAssembly.mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩ hT.mem
      hT.ne.symm hKiso hTiso hJ hJK hJT
    rcases S.cp_at_member hcen hJ.1 hJt hL' with h | h
    · exact hnc h
    · exact hL'J h
  obtain ⟨J', hJ'Ω, -, hJ'cls, hJJ', hJ'K, hJ'T⟩ := exists_twin_at_t S hT.mem hT.ne.symm hKiso
    hTiso clsT hJ hJK hJT hJt htz
  exact ⟨J, J', t, hJ, hJK, hJT, hJt, htz, hJ'cls, hJJ',
    e.mem_centralizingMembers_u hJ'Ω hJ'K hJ'T⟩

end Members

section LieAtU

variable {p f : ℕ} [Fact p.Prime]

theorem twinElt_u_not_central {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G}
    {z : G} (hnab : ∃ x y : G, x * y ≠ y * x) (S : RouteDSetup p f K z) (e : TwinElt K T z)
    (hKT : Commutes K T) : e.u ≠ 1 ∧ ¬ ({e.u} : Set G) ⊆ Subgroup.center G := by
  have hu1 : e.u ≠ 1 := e.u_ne_one S.cls (S.exact K (CoreAssembly.mem_conjClass_self K))
    (odd_natCard_galoisField S.odd S.five) hKT
  exact ⟨hu1, singleton_not_subset_center hnab hu1⟩

theorem exists_orthLie_twin (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hTrans : TwinYTransitive p f) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K T : Subgroup G} {z : G}
    (S : RouteDSetup p f K z) {tY : StatedLieTag} {nY : ℕ} (hrow : TwinRow tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (clsT : IsClassicalMember p f T z) (e : TwinElt K T z) :
    ∃ D : LieSystemData p f (locQuot (𝒞 K) e.u) (locFamily (𝒞 K) e.u), D.card = 1 ∧
      ∃ i : Fin D.card, ∃ (d : ℕ) (ε : Bool), 5 ≤ d ∧ IsOrthTag d ε (D.tag i) (D.rank i) := by
  have hΩ : HypOmegaMod p f (𝒞 K) := hΩall G hnab S.odd S.five K z S.cls S.below
  have hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M := hAall G hnab S.odd S.five K z S.cls S.below
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, hJ't, hJJ', hJ'u⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hJKc : Commutes J K := (hT.comm_K J hJ hJK).symm
  have hJTc : Commutes J T := (hT.comm_T J hJ hJT).symm
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} := e.mem_centralizingMembers_u hJ.1 hJKc hJTc
  obtain ⟨-, hunc⟩ := twinElt_u_not_central hnab S e hKT
  have htw := twin_locFamily S.inClass S.exact hJu hJ'u
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJt)
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJ't) hJJ'
  exact exists_orthLie_of_trans S.odd S.five hΩ hA hP4 S.below hunc
    (hTrans G hnab K z S tY nY hrow hshape T hT clsT e) htw

end LieAtU

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem twinYType_of_inputs (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hTrans : TwinYTransitive p f) (hRank : TwinYRank p f) :
    TwinYType p f := by
  intro G _ _ _ hnab K z S tY nY hrow hshape T hT clsT e _
  obtain ⟨D, hcard, i, horth⟩ := exists_orthLie_twin hΩall hAall hP4 hTrans hnab S hrow hshape hT
    clsT e
  obtain ⟨hd, hr⟩ := hRank G hnab K z S tY nY hrow hshape T hT clsT e D hcard i horth
  have h := NonClassical.localShapeT_zero_of_card_eq_one D hcard i
  rwa [hd, hr] at h

theorem twinYSingle_of_transitive (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hTrans : TwinYTransitive p f) : TwinYSingle p f := by
  intro G _ _ _ hnab K z S tY nY hrow hshape T hT clsT e
  obtain ⟨D, hcard, -⟩ := exists_orthLie_twin hΩall hAall hP4 hTrans hnab S hrow hshape hT clsT e
  exact ⟨D, hcard⟩

theorem twinYP1_of_single (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenT p f)
    (hS : TwinYSingle p f) : TwinYP1 p f := by
  intro G _ _ _ hnab K z S tY nY hrow hshape T hT clsT e
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hΩ : HypOmegaMod p f (𝒞 K) := hΩall G hnab S.odd S.five K z S.cls S.below
  have hA : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M := hAall G hnab S.odd S.five K z S.cls S.below
  have h7 : Thm7TypedBelow p f (Nat.card G) := thm7TypedBelow_of hP4 S.below
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, hJ't, hJJ', hJ'u⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hJKc : Commutes J K := (hKiso J hJ hJK).symm
  have hJTc : Commutes J T := (hTiso J hJ hJT).symm
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} := e.mem_centralizingMembers_u hJ.1 hJKc hJTc
  obtain ⟨hu1, hunc⟩ := twinElt_u_not_central hnab S e hKT
  have fd : TwinFrameData (𝒞 K) K T z e.u J t :=
    twinFrameData_of S hΩ e hT.mem.1 hT.ne hKT clsT hJ.1 hJ.2 hJt htz hJKc hJTc
  have hbal := rankThreeBalance_of hH S hΩ hA h7 fd
  have hframe := frameSide_of S hcen hΩ hD4 rf hshape e fd hT.mem hT.ne.symm hKiso hTiso clsT hJ
    hJK hJT hJt (hGenT G hnab K z S tY nY hrow hshape T hT clsT e J t hJ hJK hJT hJt)
  have hgen := rankTwoSpan_eq_top_of S hframe
  obtain ⟨D, hcard⟩ := hS G hnab K z S tY nY hrow hshape T hT clsT e
  have hcov : ∀ M ∈ centMembers (𝒞 K) e.u, InCommonComponent e.u M J := fun M hM =>
    inCommonComponent_of_card_one S.odd S.five S.inClass D hcard hM hJu
  have huB : e.u ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, e.u, t} : Set G) := Subgroup.subset_closure (by simp)
  exact (stage2_of_balanced_gen hnab S.odd S.five S.inClass S.ih hbal hJ.1 hJt htB
    (le_centralizer_frame e hJ.2 hJt hJKc hJTc) hgen).2 e.u hu1 fun M hM =>
    ⟨1, by rw [conjSub_one]; exact huB, by rw [conjSub_one]; exact hcov M hM⟩

theorem twinYP1_of_inputs (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenT p f)
    (hTrans : TwinYTransitive p f) : TwinYP1 p f :=
  twinYP1_of_single hΩall hAall hP4 hH hGenT (twinYSingle_of_transitive hΩall hAall hP4 hTrans)

theorem twinYP1_of_residuals (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hP4 : Ih8G2D4 p f) (hin : TwinSmallInner p) (hout : TwinSmallOuter p)
    (hex : G2D4VertexExcl p f) (hGenT : TwinYGenT p f) (hTrans : TwinYTransitive p f) :
    TwinYP1 p f :=
  twinYP1_of_inputs hΩall hAall hP4 (twinFrameHyp51_of hin hout hex) hGenT hTrans

theorem twinYInputs_of (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) (hGenT : TwinYGenT p f) (hTrans : TwinYTransitive p f)
    (hRank : TwinYRank p f) (hY3 : TwinYPartner p f) (hY4 : TwinYPattern p f) :
    TwinYInputs p f :=
  ⟨twinYP1_of_inputs hΩall hAall hP4 hH hGenT hTrans,
    twinYType_of_inputs hΩall hAall hP4 hTrans hRank, hY3, hY4⟩

end Main

end CFSG.ClassicalInvolution.RouteD.TwinY
