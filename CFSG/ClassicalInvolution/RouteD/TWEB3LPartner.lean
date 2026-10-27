module

public import CFSG.ClassicalInvolution.RouteD.TWEB3LCfg
public import CFSG.ClassicalInvolution.RouteD.TWS6Cfg
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

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWS6
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Config

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {tY : StatedLieTag} {nY : ℕ}


theorem twinYConfigL_of_partner' (hcls : Asc77.TwinInvolution p f) (hnab : ∃ x y : G, x * y ≠ y * x)
    (S : RouteDSetup p f K z) (hrow : TwinRow tY nY) (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z)
    (c : TCtx p f tY nY (𝒞 K) K z)
    (hF : SignFacts (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) (GaloisField p f))
    {β : Subgroup G} (hβ : β ∈ 𝒞 K) {t : G} (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfix : HasFixedMember (𝒞 K) K β z) :
    ∃ (T : Subgroup G) (e : TwinElt K T z) (J J' : Subgroup G) (w : G) (e' : TwinElt J J' w)
      (s : G), TwinYConfigL p f (𝒞 K) K T z e J J' w e' β s := by
  classical
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hΩ : InClass p f (𝒞 K) := S.inClass
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f S.odd
  obtain ⟨T, hTz, hTQ⟩ := c.exists_twin
  have hT : IsTwinAt (𝒞 K) K T z := isTwinAt_of_ctx c hTz hTQ.le
  have clsT : IsClassicalMember p f T z := hcls G hnab K z S tY nY hrow hshape T hT
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hsingle : ∀ L ∈ 𝒞 K, ∃ g : G, L = conjSub g K := single_class K
  obtain ⟨M, hMΩ, hKM, hβM, hMnon⟩ := hfix
  obtain ⟨W₀, hW₀⟩ := id hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW₀
  have hKβne : K ≠ β := ne_of_linearBlockStandardPair hW₀
  have hzt : Commute z t := standardPair_involutions_commute h2 hW₀ S.cls.mem ht.mem
    S.cls.orderOf_eq_two ht.orderOf_eq_two
  have hMz : M ∈ centralizingMembers (𝒞 K) {z} :=
    mem_centralizingMembers_of_commutes hMΩ S.cls.mem (commutes_symm hKM)
  have hMK : M ≠ K := fun h => not_commutes_self_of_mem hΩ hKΩ (by rw [h] at hKM; exact hKM)
  have hMT : M ≠ T := fun h => hMnon (fun N hN hNM => by
    rw [h]; exact hT.comm_T N hN (by rw [← h]; exact hNM))
  obtain ⟨w, hw⟩ := hΩ.classical M hMΩ
  have hwz : w ≠ z := by
    intro hwz
    apply hMnon
    intro N hN hNM
    have hN' : N ∈ centralizingMembers (𝒞 K) {w} := by rw [hwz]; exact hN
    exact (S.cp_at_member hcen hMΩ hw hN').resolve_right hNM
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape hMΩ hw
  obtain ⟨J', hJ'⟩ := exists_isTwinAt_of_ctx cx
  have hSM : RouteDSetup p f M w := S.of_mem_conjClass hMΩ hw
  have hclsM : 𝒞 M = 𝒞 K := conjClass_eq_of_mem hMΩ
  have hshapeM : LocalShapeT p f 2 tY nY (𝒞 M) w := by
    rw [hclsM]; exact localShapeT_at_member S hMΩ hw hshape
  have hJ'M : IsTwinAt (𝒞 M) M J' w := by rw [hclsM]; exact hJ'
  have clsJ' : IsClassicalMember p f J' w := hcls G hnab M w hSM tY nY hrow hshapeM J' hJ'M
  have hJ'Ω : J' ∈ 𝒞 K := hJ'.mem.1
  have hKw : K ∈ centralizingMembers (𝒞 K) {w} :=
    mem_centralizingMembers_of_commutes hKΩ hw.mem hKM
  have hTM : Commutes T M := hT.comm_T M hMz hMT
  have hTΩ : T ∈ 𝒞 K := hTz.1
  have hTw : T ∈ centralizingMembers (𝒞 K) {w} :=
    mem_centralizingMembers_of_commutes hTΩ hw.mem hTM
  have hβw : β ∈ centralizingMembers (𝒞 K) {w} :=
    mem_centralizingMembers_of_commutes hβ hw.mem hβM
  have hJ'K : J' ≠ K := fun h => hwz (Gaps.unique_involution_of_isClassicalMember h2
    (S.exact K hKΩ) (h ▸ clsJ') S.cls)
  have hJ'T : J' ≠ T := fun h => hwz (Gaps.unique_involution_of_isClassicalMember h2
    (S.exact T hTΩ) (h ▸ clsJ') clsT)
  have hJ'Kc : Commutes J' K := hJ'.comm_T K hKw hJ'K.symm
  have hJ'Tc : Commutes J' T := hJ'.comm_T T hTw hJ'T.symm
  have hJ'z : J' ∈ centralizingMembers (𝒞 K) {z} :=
    mem_centralizingMembers_of_commutes hJ'Ω S.cls.mem hJ'Kc
  have hβJ' : β ≠ J' := fun h => hnKβ (by rw [h]; exact commutes_symm hJ'Kc)
  have hJ'βc : Commutes J' β := hJ'.comm_T β hβw hβJ'
  obtain ⟨e'⟩ := exists_twinElt hw clsJ' (S.exact M hMΩ) (S.exact J' hJ'Ω)
    (odd_natCard_galoisField S.odd S.five)
  have hβT : β ≠ T := fun h => hnKβ (by rw [h]; exact hKT)
  have hnβT : ¬ Commutes β T := by
    intro h
    have hβz : β ∈ centralizingMembers (𝒞 K) {z} :=
      mem_centralizingMembers_of_commutes hβ clsT.mem h
    rcases S.cp_at_member hcen hKΩ S.cls hβz with h' | h'
    · exact hnKβ h'
    · exact hKβne h'.symm
  have htz : t * z * t⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]; exact hzt.symm.eq
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  have hna : conjSub t K = K := conjSub_eq_of_standardPair h2 hW₀ ht.mem ht.orderOf_eq_two
  have hnd : conjSub t T = T := conjSub_twin_eq c htz htt hna hTz hTQ.le
  obtain ⟨W₁, hW₁⟩ := sign_config' cx hF hKw hβw hTw S.cls ht clsT hKβne hβT hKβ hnβT hKT hzt hzt
    hna hnd
  have hTβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W T β :=
    ⟨W₁, linearBlockStandardPair_symm hW₁⟩
  obtain ⟨e, he⟩ := RouteD.TWD.exists_twinElt_comm h2 S.cls clsT ht hKβ hTβ
  exact ⟨T, e, M, J', w, e', t, ⟨⟨hT, clsT, hMz, hJ'z, hMK, hMT, hJ'K, hJ'T, hJ', hw, clsJ',
    e'.mem_centralizingMembers_u hβ hβM (commutes_symm hJ'βc), ht, hKβ, he⟩, hβM,
    commutes_symm hJ'βc⟩⟩

end Config

section Rows

variable {p f : ℕ} [Fact p.Prime]


theorem twinYPartnerLOn_odd (hcls : Asc77.TwinInvolution p f) :
    TwinYPartnerLOn p f fun t n => t = .POmegaOdd ∧ 3 ≤ n := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape
  obtain ⟨rfl, hm⟩ := hP
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  obtain ⟨c⟩ := TCtx.nonempty_odd hm S.odd S.five S.inClass S.exact
    (CoreAssembly.mem_conjClass_self K) S.cls S.p1 hshape
  have hadm : StatedLieAdmissible .POmegaOdd nY p f := ⟨Fact.out, hf, hm, S.odd⟩
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_odd hm hadm (single_class K) hshape
  obtain ⟨T, e, J, J', w, e', s, hcfg⟩ := twinYConfigL_of_partner' hcls hnab S hrow hshape c
    (signFacts_odd S.odd hm S.five) hβ ht hKβ hfix
  exact ⟨T, e, J, J', w, e', β, s, hcfg⟩

end Rows

end CFSG.ClassicalInvolution.RouteD.TWE.B3
