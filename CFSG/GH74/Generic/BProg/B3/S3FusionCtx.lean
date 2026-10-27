module

public import CFSG.GH74.Generic.BProg.B3.S3FusionBar
public import CFSG.GH74.Generic.BProg.B1.PilotS3
public import CFSG.GH74.Generic.S3.NbrBase
public import CFSG.GH74.Generic.S3.BFreeBasic
public import CFSG.GH74.Generic.S3.Front
public import CFSG.GH74.Generic.S45.GLevel1
public import CFSG.GH74.Generic.S1.RNormalizer
public import CFSG.GH74.Generic.BProg.Vocab
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.GH74.Generic.BProg.Assembly
public import CFSG.GH74.Generic.BProg.NS.Leaf
public import CFSG.GH74.Generic.S1.RLevelE
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Fusion

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5
  CFSG.GH74.Generic.BProg.B1.PilotS3 CFSG.GH74.Generic.BProg.B1.PilotS5 Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isComponent_imgBar {x : G} {K : Subgroup G}
    (hK : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) K) : IsComponent (S3.imgBar x K) :=
  TwoThin.isComponent_map_barMk (TwoThin.isPCompIn_two_iff.mp hK).2

theorem barShape_of_ctx {x : G} {K : Subgroup G} (hG4 : Gen4 G) (hx : orderOf x = 2)
    (hK : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) K) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K))
    (hC : pRank 2 ↥(CxK x K) ≤ 1) :
    BarShape (CentralizerBar x) (xbar x) (S3.imgBar x K) := by
  obtain ⟨eK⟩ := hat_equiv_imgBar hK
  have hcomp := isComponent_imgBar hK
  have hKnab : ∃ a b : ↥(S3.imgBar x K), a * b ≠ b * a :=
    S45.exists_noncomm_of_isQuasisimple hcomp.1
  have hsimple : IsSimpleGroup ↥(S3.imgBar x K) :=
    (MulEquiv.isSimpleGroup_congr eK).mp (isSimpleGroup_of_qShape3 h3)
  have hcen : center ↥(S3.imgBar x K) = ⊥ := center_eq_bot_of_isSimpleGroup hsimple hKnab
  obtain ⟨p, f, hp, hp2, hq, hmod⟩ := h3
  have hpodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by
    have := Nat.odd_iff.mp hpodd
    omega
  have hmodK : ∃ t : StatedLieTag, (t = .PSL ∨ t = .PSU) ∧ LieModel ↥(S3.imgBar x K) t 3 p f := by
    rcases hmod with hm | hm
    · exact ⟨.PSL, Or.inl rfl, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eK hm⟩
    · exact ⟨.PSU, Or.inr rfl, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eK hm⟩
  obtain ⟨t, ht, hmK⟩ := hmodK
  have hKc : ∀ k : ↥(S3.imgBar x K), (∀ k' : ↥(S3.imgBar x K), k' * k = k * k') → k = 1 :=
    centerless_of_model ht hmK hKnab
  have hK1 : RankCertified ↥(S3.imgBar x K) 1 := rankCertified_one_of_model ht hp2 hmK
  have hnorm : (S3.imgBar x K).Normal :=
    normal_of_component_gen4 (gen4_centralizerBar hG4 x) (xbar_comm x) (xbar_mul_self hx)
      (xbar_ne_one hx) hcomp hKc hK1
  exact ⟨xbar_mul_self hx, xbar_ne_one hx, xbar_comm x, hnorm, hcomp.1, hcen,
    ⟨t, p, f, ht, hp, hp2, h5, hmK⟩, onlyInvX_of_pRank_CxK hx hK rfl hC⟩

theorem eq_one_of_piC_eq_one {x : G} {T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTC : T ≤ centralizer ({x} : Set G)) {a : G} (ha : a ∈ T) (h : piC x a = 1) : a = 1 := by
  have haC : a ∈ centralizer ({x} : Set G) := hTC ha
  rw [piC_of_mem x haC] at h
  have hodd := proj_odd x ⟨a, haC⟩ h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨a, ha⟩
  have h1 : orderOf (⟨a, haC⟩ : ↥(centralizer ({x} : Set G))) = 2 ^ k := by
    rw [Subgroup.orderOf_mk, ← hk, ← Subgroup.orderOf_coe ⟨a, ha⟩]
  rw [h1] at hodd
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
  rw [hk0, pow_zero] at hk
  have := orderOf_eq_one_iff.mp (by rw [← Subgroup.orderOf_coe ⟨a, ha⟩] at hk; simpa using hk)
  exact this

omit [Finite G] in
theorem x_mem_sylow {x : G} (hx2 : x * x = 1) {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) : x ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hT.exists_sylow_eq_subgroupOf
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set xC : ↥(centralizer ({x} : Set G)) := ⟨x, hxC⟩ with hxCdef
  have hxx : xC * xC = 1 := Subtype.ext hx2
  have hcen : ∀ g : ↥(centralizer ({x} : Set G)), g * xC = xC * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hN : (Subgroup.zpowers xC).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g xC := hcen g
    have : g * xC ^ k * g⁻¹ = xC ^ k := by
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem_zpowers _ _
  have hle : Subgroup.zpowers xC ≤ (S : Subgroup ↥(centralizer ({x} : Set G))) :=
    IsPGroup.le_sylow_of_normal (isPGroup_zpowers_of_involution hxx) S
  have hmem : xC ∈ (S : Subgroup ↥(centralizer ({x} : Set G))) := hle (Subgroup.mem_zpowers xC)
  rw [hS] at hmem
  exact hmem

theorem exists_T {x y : G} {K : Subgroup G}
    (hshape : BarShape (CentralizerBar x) (xbar x) (S3.imgBar x K)) (hx : orderOf x = 2)
    (hK : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) K) (hyK : y ∈ K) (hy : orderOf y = 2) :
    ∃ T : Subgroup G, IsSylowOf 2 T (centralizer ({x} : Set G)) ∧ x ∈ T ∧ y ∈ T ∧
      (∀ a ∈ T, a * y = y * a) ∧
      (∀ z ∈ T, (∀ a ∈ T, a * z = z * a) → z * z = 1 → z = 1 ∨ z = x ∨ z = y ∨ z = y * x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hyC : y ∈ centralizer ({x} : Set G) := hK.1 hyK
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  set yb : CentralizerBar x := piC x y with hyb
  have hybK : yb ∈ S3.imgBar x K := mem_imgBar.2 ⟨⟨y, hyC⟩, hyK, (piC_of_mem x hyC).symm⟩
  have hyb2 : yb * yb = 1 := by rw [hyb, ← piC_mul x hyC hyC, hy2, piC_one]
  have hyb1 : yb ≠ 1 := fun h => by
    have h' := proj_odd x ⟨y, hyC⟩ (by rwa [hyb, piC_of_mem x hyC] at h)
    have h2 : orderOf (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hy
    rw [h2] at h'
    exact absurd h' (by decide)
  obtain ⟨Q, hyQ, hyQc, hQZ⟩ := hshape.exists_sylow hybK hyb2 hyb1
  have hsurj : Function.Surjective (proj x) := QuotientGroup.mk'_surjective _
  obtain ⟨P₀, hP₀⟩ := Sylow.mapSurjective_surjective hsurj 2 Q
  have hQmap : (Q : Subgroup (CentralizerBar x)) = (P₀ : Subgroup ↥(centralizer ({x} : Set G))).map (proj x) := by
    rw [← hP₀]
    exact Sylow.coe_mapSurjective hsurj P₀
  obtain ⟨y₀, hy₀P, hy₀⟩ : ∃ y₀ ∈ (P₀ : Subgroup ↥(centralizer ({x} : Set G))), proj x y₀ = yb := by
    have : yb ∈ (Q : Subgroup (CentralizerBar x)) := hyQ
    rw [hQmap] at this
    exact this
  set T₀ : Subgroup G := (P₀ : Subgroup ↥(centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype
    with hT₀
  have hT₀p : IsPGroup 2 ↥T₀ := (P₀.isPGroup').map _
  have hT₀C : T₀ ≤ centralizer ({x} : Set G) := Subgroup.map_subtype_le _
  have hy₀T : (y₀ : G) ∈ T₀ := ⟨y₀, hy₀P, rfl⟩
  have hpi₀ : piC x (y₀ : G) = yb := by rw [piC_of_mem x y₀.2]; exact hy₀
  have hy₀2 : (y₀ : G) * (y₀ : G) = 1 := by
    refine eq_one_of_piC_eq_one hT₀p hT₀C (T₀.mul_mem hy₀T hy₀T) ?_
    rw [piC_mul x y₀.2 y₀.2, hpi₀, hyb2]
  obtain ⟨r, hr, hry⟩ := S1.exists_conj_of_proj_eq (u := y₀) (v := ⟨y, hyC⟩)
    (Subtype.ext hy₀2) (Subtype.ext hy2) (hy₀.trans (piC_of_mem x hyC))
  have hr1 : proj x r = 1 := (QuotientGroup.eq_one_iff r).2 hr
  set P : Sylow 2 ↥(centralizer ({x} : Set G)) := r • P₀ with hP
  have hPcoe : (P : Subgroup ↥(centralizer ({x} : Set G))) =
      MulAut.conj r • (P₀ : Subgroup ↥(centralizer ({x} : Set G))) := Sylow.coe_subgroup_smul
  set T : Subgroup G := (P : Subgroup ↥(centralizer ({x} : Set G))).map
    (centralizer ({x} : Set G)).subtype with hT
  have hTS : IsSylowOf 2 T (centralizer ({x} : Set G)) := ⟨P, rfl⟩
  have hTp : IsPGroup 2 ↥T := hTS.isPGroup
  have hTC : T ≤ centralizer ({x} : Set G) := hTS.le
  have hmemT : ∀ a : G, a ∈ T ↔ ∃ (ha : a ∈ centralizer ({x} : Set G)),
      ∃ p ∈ (P₀ : Subgroup ↥(centralizer ({x} : Set G))), r * p * r⁻¹ = ⟨a, ha⟩ := by
    intro a
    constructor
    · rintro ⟨a', ha', rfl⟩
      have ha'' : a' ∈ (P : Subgroup ↥(centralizer ({x} : Set G))) := ha'
      rw [hPcoe, Subgroup.mem_smul_pointwise_iff_exists] at ha''
      obtain ⟨p, hp, hpa⟩ := ha''
      exact ⟨a'.2, p, hp, by simpa [MulAut.smul_def, MulAut.conj_apply] using hpa⟩
    · rintro ⟨ha, p, hp, hpa⟩
      refine ⟨⟨a, ha⟩, ?_, rfl⟩
      show (⟨a, ha⟩ : ↥(centralizer ({x} : Set G))) ∈ (P : Subgroup ↥(centralizer ({x} : Set G)))
      rw [hPcoe, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨p, hp, by simpa [MulAut.smul_def, MulAut.conj_apply] using hpa⟩
  have hpiT : ∀ a ∈ T, piC x a ∈ (Q : Subgroup (CentralizerBar x)) := by
    intro a ha
    obtain ⟨haC, p, hp, hpa⟩ := (hmemT a).1 ha
    rw [piC_of_mem x haC, ← hpa, map_mul, map_mul, map_inv, hr1, one_mul, inv_one, mul_one, hQmap]
    exact ⟨p, hp, rfl⟩
  have hpiT' : ∀ q ∈ (Q : Subgroup (CentralizerBar x)), ∃ a ∈ T, piC x a = q := by
    intro q hq
    rw [hQmap] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    refine ⟨((r * p * r⁻¹ : ↥(centralizer ({x} : Set G))) : G), (hmemT _).2 ⟨(r * p * r⁻¹).2, p, hp, rfl⟩, ?_⟩
    rw [piC_of_mem x (r * p * r⁻¹).2]
    show proj x (r * p * r⁻¹) = proj x p
    rw [map_mul, map_mul, map_inv, hr1, one_mul, inv_one, mul_one]
  have hyT : y ∈ T := (hmemT y).2 ⟨hyC, y₀, hy₀P, hry⟩
  have hxT : x ∈ T := x_mem_sylow hx2 hTS
  have hinj : ∀ a ∈ T, ∀ b ∈ T, piC x a = piC x b → a = b := by
    intro a ha b hb hab
    have h1 : piC x (a⁻¹ * b) = 1 := by
      rw [piC_mul x (hTC (T.inv_mem ha)) (hTC hb), piC_inv x (hTC ha), hab, inv_mul_cancel]
    have := eq_one_of_piC_eq_one hTp hTC (T.mul_mem (T.inv_mem ha) hb) h1
    exact inv_mul_eq_one.mp this
  have hpiy : piC x y = yb := rfl
  have hyc : ∀ a ∈ T, a * y = y * a := by
    intro a ha
    refine hinj _ (T.mul_mem ha hyT) _ (T.mul_mem hyT ha) ?_
    rw [piC_mul x (hTC ha) hyC, piC_mul x hyC (hTC ha), hpiy]
    exact hyQc _ (hpiT a ha)
  refine ⟨T, hTS, hxT, hyT, hyc, ?_⟩
  intro z hzT hzc hz2
  have hzC : z ∈ centralizer ({x} : Set G) := hTC hzT
  have hzQ : piC x z ∈ (Q : Subgroup (CentralizerBar x)) := hpiT z hzT
  have hzQc : ∀ q ∈ (Q : Subgroup (CentralizerBar x)), q * piC x z = piC x z * q := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := hpiT' q hq
    rw [← piC_mul x (hTC ha) hzC, ← piC_mul x hzC (hTC ha), hzc a ha]
  have hz2' : piC x z * piC x z = 1 := by rw [← piC_mul x hzC hzC, hz2, piC_one]
  have hxb : piC x x = xbar x := piC_x x
  rcases hQZ _ hzQ hzQc hz2' with h | h | h | h
  · left
    exact eq_one_of_piC_eq_one hTp hTC hzT h
  · right; left
    exact hinj _ hzT _ hxT (h.trans hxb.symm)
  · right; right; left
    exact hinj _ hzT _ hyT h
  · right; right; right
    refine hinj _ hzT _ (T.mul_mem hyT hxT) ?_
    rw [piC_mul x hyC (hTC hxT), hxb]
    exact h

end S3Fusion

end CFSG.GH74.Generic.BProg.B3
