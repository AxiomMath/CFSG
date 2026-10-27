module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnMain
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf)
open CFSG.ClassicalInvolution.Balance.Theorem5
  (MemberClass conjMembers commuteAdj FuzzyEdgeInFrame FuzzyLinkConn FuzzyFrameBalance
    fuzzyFrames fuzzyVertices conjInvariant_conjMembers fuzzyAxisExact_conjMembers
    fuzzyMemberConn_conjMembers fuzzyVertexConn_of_adj)

section Residual

theorem perfectResidual_eq_of_sup_solvable {H : Type*} [Group H] [Finite H] {P N : Subgroup H}
    (hP : Group.IsPerfect P) (hPn : P.Normal) (hN : N.Normal) (hNsol : Group.IsSolvable N)
    (hPN : P ⊔ N = ⊤) : CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual H = P := by
  apply le_antisymm
  · have hsurj : Function.Surjective ((QuotientGroup.mk' P).comp N.subtype) := by
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective P y
      have hh : h ∈ N ⊔ P := by
        rw [sup_comm, hPN]
        exact Subgroup.mem_top h
      obtain ⟨n, hn, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hh
      refine ⟨⟨n, hn⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff q).mpr hq,
        mul_one]
    have hsol : Group.IsSolvable (H ⧸ P) := Group.isSolvable_of_surjective hsurj
    exact ((CFSG.perfect_residual_characterization (G := H)).2.2.2.2.1 P).mp hsol
  · exact (CFSG.perfect_residual_transport (MonoidHom.id H)).2.2 P hP

end Residual

section Canon

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem canonMember_eq_of_isClassicalMember {J : Subgroup G} {z : G}
    (hJ : IsClassicalMember p f J z) : canonMember J z = J := by
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hN : involutionOddCore z = oddCoreIn C := involutionOddCore_eq_oddCoreIn z
  set N : Subgroup G := involutionOddCore z with hNdef
  have hNtq : N ≤ trivialOnQuot J := by
    rw [hN]
    exact oddCoreIn_le_trivialOnQuot hJ.subnormal hJ.perfect
  set Z : Subgroup G := J ⊔ N with hZ
  have hJZ : J ≤ Z := le_sup_left
  have hNZ : N ≤ Z := le_sup_right
  have hZnorm : Z ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer fun n hn => (hNtq hn).1
  have hJn : (J.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJZ).mpr hZnorm
  have hJC : J ≤ C := isSubnormal_le hJ.subnormal
  have hNC : N ≤ C := by
    rw [hN]
    exact oddCoreIn_le C
  have hZC : Z ≤ C := sup_le hJC hNC
  have hNn : (N.subgroupOf Z).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNZ]
    refine hZC.trans ?_
    rw [hN]
    exact normalizer_oddCoreIn C
  have hNodd : Odd (Nat.card ↥(N.subgroupOf Z)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNZ).toEquiv, hN]
    exact odd_card_oddCoreIn C
  have hNsol : Group.IsSolvable ↥(N.subgroupOf Z) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  have := hJ.perfect
  have hperf : Group.IsPerfect ↥(J.subgroupOf Z) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJZ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJZ).symm.surjective
  have hsup : J.subgroupOf Z ⊔ N.subgroupOf Z = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hJZ hNZ, ← hZ]
    exact Subgroup.subgroupOf_self Z
  have h := perfectResidual_eq_of_sup_solvable hperf hJn hNn
    hNsol hsup
  show perfectResidualOf Z = J
  unfold perfectResidualOf
  rw [h, Subgroup.map_subgroupOf_eq_of_le hJZ]

theorem isCanonical_of_isClassicalMember {J : Subgroup G} {z : G}
    (hJ : IsClassicalMember p f J z) : IsCanonical J z :=
  canonMember_eq_of_isClassicalMember hJ

theorem canonClass_eq_conjClass {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z) :
    canonClass p f K = CoreAssembly.conjClass K := by
  ext J
  constructor
  · rintro ⟨M, hM, w, hw, rfl⟩
    rwa [canonMember_eq_of_isClassicalMember hw]
  · rintro hJ
    obtain ⟨g, rfl⟩ := hJ
    exact ⟨conjSub g K, ⟨g, rfl⟩, g * z * g⁻¹, hz.conj g,
      (canonMember_eq_of_isClassicalMember (hz.conj g)).symm⟩

end Canon

section Conj

variable {p f : ℕ} [Fact p.Prime]

theorem LinkNoF3.of_conjMembers (h : LinkNoF3 p f conjMembers) : LinkNoF3 p f (canonClass p f) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind a M hM hMa
  have hK : canonClass p f K = conjMembers K := canonClass_eq_conjClass hz
  beta_reduce at hM ⊢
  rw [hK] at hM ⊢
  exact h G hnab hp2 hq K z hz hBelow hconn hind a M hM hMa

theorem FuzzyNoF3.of_conjMembers (h : FuzzyNoF3 p f conjMembers) :
    FuzzyNoF3 p f (canonClass p f) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT b hb hb1
  have hK : canonClass p f K = conjMembers K := canonClass_eq_conjClass hz
  beta_reduce at h1 h2 h3
  rw [hK] at h1 h2 h3
  exact h G hnab hp2 hq K z hz hBelow hconn hind J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT b hb hb1

theorem fuzzyEdgeInFrame_conjMembers (hF3 : LinkNoF3 p f conjMembers) :
    FuzzyEdgeInFrame p f conjMembers commuteAdj := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind M hM N hN zM zN hMc hNc hE hne
  have hK : conjMembers K = canonClass p f K := (canonClass_eq_conjClass hz).symm
  have hadj : tqAdj p f M N := by
    refine ⟨zM, zN, hMc, hNc, ?_, ?_⟩
    · exact mem_trivialOnQuot_iff_actsTrivOnQuot.mp
        (Theorem5.mem_trivialOnQuot_of_centralizes fun x hx => (hE x hx zN hNc.mem).symm)
    · exact mem_trivialOnQuot_iff_actsTrivOnQuot.mp
        (Theorem5.mem_trivialOnQuot_of_centralizes fun y hy => hE zM hMc.mem y hy)
  beta_reduce at hM hN ⊢
  rw [hK] at hM hN ⊢
  exact fuzzyEdgeInFrame_canonClass (LinkNoF3.of_conjMembers hF3) G hnab hp2 hq K z hz hBelow
    hconn hind M hM N hN zM zN hMc hNc hadj hne

theorem fuzzyLinkConn_conjMembers (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hF3 : LinkNoF3 p f conjMembers) : FuzzyLinkConn p f conjMembers := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind a A hA A' hA' haA haA'
  have hK : conjMembers K = canonClass p f K := (canonClass_eq_conjClass hz).symm
  beta_reduce at hA hA' haA haA' ⊢
  rw [hK] at hA hA' haA haA' ⊢
  exact fuzzyLinkConn_canonClass hMFC (LinkNoF3.of_conjMembers hF3) G hnab hp2 hq K z hz hBelow
    hconn hind a A hA A' hA' haA haA'

theorem fuzzyFrameBalance_conjMembers
    (hmodel : LayerGenerationHybrid p)
    (hF3 : FuzzyNoF3 p f conjMembers) : FuzzyFrameBalance p f conjMembers := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind A hA
  have hK : conjMembers K = canonClass p f K := (canonClass_eq_conjClass hz).symm
  beta_reduce at hA
  rw [hK] at hA
  exact fuzzyFrameBalance_of_hybrid hmodel (FuzzyNoF3.of_conjMembers hF3) G hnab hp2 hq K z hz
    hBelow hconn hind A hA

theorem bootTriple_conjMembers (hlay : Theorem5.TriangleLayers p f)
    (hmodel : LayerGenerationHybrid p) (hF3 : FuzzyNoF3 p f conjMembers)
    (hlinkF3 : LinkNoF3 p f conjMembers) (hMFC : ModelFacts.CommutingFundamentalFactsFive p)
    (hcov9 : p ^ f = 9 → Theorem5.ConnectedFramesExist p f) (hexotic : ExoticLeviBlock p f) :
    CoreAssembly.BootTriple p f :=
  Theorem5.bootTriple_of_fuzzyFrames conjMembers hlay
    (fun _ _ _ K => conjInvariant_conjMembers K) (fuzzyFrameBalance_conjMembers hmodel hF3)
    fuzzyAxisExact_conjMembers
    (fuzzyVertexConn_of_adj fuzzyMemberConn_conjMembers (fuzzyEdgeInFrame_conjMembers hlinkF3))
    (fuzzyLinkConn_conjMembers hMFC hlinkF3) hcov9 hexotic

end Conj

end CFSG.ClassicalInvolution.Balance.Bootstrap
