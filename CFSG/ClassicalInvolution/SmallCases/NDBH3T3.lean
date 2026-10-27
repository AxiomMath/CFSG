module

public import CFSG.ClassicalInvolution.SmallCases.NDBH3T2
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinU
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.WP3L52Main
import CFSG.ClassicalInvolution.Asc77.AscT3UMain
import CFSG.ClassicalInvolution.Asc77.AscIH8Thm678
import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinRowsOuter
import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Outer
import CFSG.ClassicalInvolution.ModelFacts.Orth15RFixLift
import CFSG.ClassicalInvolution.ModelFacts.Orth15SSec
import CFSG.ClassicalInvolution.RouteD.G2D4Ih8Free
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
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
import CFSG.ClassicalInvolution.Asc77.AscT7CWz
import CFSG.ClassicalInvolution.Asc77.AscT7D242
import CFSG.ClassicalInvolution.Asc77.AscT7EC23
import CFSG.ClassicalInvolution.Asc77.AscT7HX23
import CFSG.ClassicalInvolution.Asc77.AscT7K3
import CFSG.ClassicalInvolution.Asc77.AscT7K4
import CFSG.ClassicalInvolution.Asc77.AscT8Setup
import CFSG.ClassicalInvolution.Asc77.AscThmABasic
import CFSG.ClassicalInvolution.AschTight.C195Wreath
import CFSG.ClassicalInvolution.AschTight.Hall196Idx
import CFSG.ClassicalInvolution.AschTight.Sec7L98J
import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2

public section

namespace CFSG.ClassicalInvolution.NDB.NDBH3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_mul_self_eq_of_two_group {K R : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hRK : R ≤ K) (hR2 : IsPGroup 2 R) (hcard : 2 < Nat.card R) : ∃ x ∈ R, x * x = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hrR, hr1, hrz⟩ : ∃ r ∈ R, r ≠ 1 ∧ r ≠ z := by
    by_contra hcon
    push Not at hcon
    have hle : R ≤ Subgroup.zpowers z := fun r hr => by
      by_cases h1 : r = 1
      · rw [h1]
        exact Subgroup.one_mem _
      · rw [hcon r hr h1]
        exact Subgroup.mem_zpowers z
    have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq, hz.sq]) hz.ne_one
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hz2] at this
    omega
  obtain ⟨k, hk⟩ := hR2.exists_orderOf_eq_pow (⟨r, hrR⟩ : R)
  rw [Subgroup.orderOf_mk] at hk
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hr1 hk
    · rw [pow_one] at hk
      have hrr : r * r = 1 := by rw [← sq, ← hk, pow_orderOf_eq_one]
      rcases hz.unique r (hRK hrR) hrr with h | h
      · exact hr1 h
      · exact hrz h
  refine ⟨r ^ (2 ^ (k - 2)), Subgroup.pow_mem _ hrR _, ?_⟩
  have e1 : r ^ (2 ^ (k - 2)) * r ^ (2 ^ (k - 2)) = r ^ (2 ^ (k - 1)) := by
    rw [← pow_add]
    congr 1
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, pow_succ]
    ring
  have hy2 : r ^ (2 ^ (k - 1)) * r ^ (2 ^ (k - 1)) = 1 := by
    rw [← pow_add]
    have : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
      have : k = (k - 1) + 1 := by omega
      conv_rhs => rw [this, pow_succ]
      ring
    rw [this, ← hk, pow_orderOf_eq_one]
  have hy1 : r ^ (2 ^ (k - 1)) ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hk] at hd
    have := Nat.le_of_dvd (by positivity) hd
    have : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  rw [e1]
  rcases hz.unique _ (K.pow_mem (hRK hrR) _) hy2 with h | h
  · exact absurd h hy1
  · exact h

structure TwinA1Frame (Ω : Set (Subgroup G)) (K T N R R' : Subgroup G) (z n u x y : G) :
    Prop where
  data : TwinFrameData Ω K T z u N n
  syl : IsSylow2In R K
  syl' : IsSylow2In R' T
  comm : Commutes R R'
  cen : ∀ r ∈ R, r * n = n * r
  cen' : ∀ r ∈ R', r * n = n * r
  hx : x ∈ R
  hy : y ∈ R'
  hxx : x * x = z
  hyy : y * y = z
  hxy : x * y = u

theorem cen_of_fix {L R : Subgroup G} {t : G} (hR : IsSylow2In R L) (htL : t ∈ trivialOnQuot L)
    (hfix : conjSub t R = R) : ∀ r ∈ R, r * t = t * r := by
  intro r hr
  have h1 : t * r * t⁻¹ ∈ R := by
    have := conj_mem_conjSub (n := t) hr
    rwa [hfix] at this
  have h2 : t * r * t⁻¹ * r⁻¹ ∈ R := R.mul_mem h1 (R.inv_mem hr)
  have h3 : t * r * t⁻¹ * r⁻¹ ∈ oddCoreIn L := by
    have := htL.2 r (hR.1 hr)
    rwa [commutatorElement_def] at this
  have h4 : IsPGroup 2 (Subgroup.zpowers (t * r * t⁻¹ * r⁻¹)) :=
    hR.2.1.to_le (Subgroup.zpowers_le.mpr h2)
  have h5 : t * r * t⁻¹ * r⁻¹ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L) h3 h4
  have h6 : t * r * t⁻¹ = r := by
    have := congrArg (fun w => w * r) h5
    simpa using this
  calc r * t = t * r * t⁻¹ * t := by rw [h6]
    _ = t * r := by group

theorem exists_twinA1Frame (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hΩ : HypOmegaMod p f (𝒞 K)) (hz : IsClassicalMember p f K z) {T : Subgroup G}
    (hT : T ∈ 𝒞 K) (hTK : T ≠ K) (hTz : IsClassicalMember p f T z) {N : Subgroup G}
    (hN : N ∈ tqMembers (𝒞 K) z) {n : G} (hn : IsClassicalMember p f N n) (hnz : n ≠ z) :
    ∃ (R R' : Subgroup G) (u x y : G), TwinA1Frame (𝒞 K) K T N R R' z n u x y := by
  have hK : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hTzu : IsUniqueInvolution T z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hTz
  have hNn : IsUniqueInvolution N n :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hn
  have hTw : T ∈ twinSet (𝒞 K) K := ⟨hT, z, hKz, hTzu⟩
  have hNW := mem_omegaOfSet_twinSet hp2 hq hΩ hKz hN hn hnz
  have htq : ∀ L ∈ twinSet (𝒞 K) K, n ∈ trivialOnQuot L := by
    intro L hL
    have hNL : N ∈ omegaNbr (𝒞 K) L := hNW.2 L hL
    have hLN : L ∈ omegaNbr (𝒞 K) N := T3.omegaNbr_symm (l6_2 p f) hp2 hq hΩ hL.1 hN.1 hNL
    obtain ⟨a, ha, hLa⟩ := tq_of_mem_omegaNbr hp2 hq hΩ.classical hN.1 hLN
    have han : a = n := (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq ha).eq hNn
    exact (mem_trivialOnQuot_iff_actsTrivOnQuot (J := L)).mpr (han ▸ hLa)
  have hnK := htq K (mem_twinSet_self hK hKz)
  have hnT := htq T hTw
  have hA2 : IsPGroup 2 (Subgroup.zpowers n) := isPGroup_zpowers_of_sq_eq_one hNn.sq
  obtain ⟨R, R', hR, hR', hcomm, hRfix, hR'fix, -⟩ := exists_twinSylow_normalized hp2 hq hΩ
    hK hKz hTw hTK hA2 (Subgroup.zpowers_le.mpr hnK.1) (Subgroup.zpowers_le.mpr hnT.1)
  have hcen := cen_of_fix hR hnK (hRfix n (Subgroup.mem_zpowers n))
  have hcen' := cen_of_fix hR' hnT (hR'fix n (Subgroup.mem_zpowers n))
  have h8 := hΩ.eight_le_of_mem_RSet hp2 (mem_RSet_of_isSylow2In hK hR)
  have h8' := hΩ.eight_le_of_mem_RSet hp2 (mem_RSet_of_isSylow2In hT hR')
  obtain ⟨x, hx, hxx⟩ := exists_mul_self_eq_of_two_group hKz hR.1 hR.2.1 (by omega)
  obtain ⟨y, hy, hyy⟩ := exists_mul_self_eq_of_two_group hTzu hR'.1 hR'.2.1 (by omega)
  have hcard : Nat.card ↥(R ⊓ R') ≤ 2 :=
    hΩ.card_le_two_of_le_inf hK hT hTK.symm (hR.2.1.to_le inf_le_left)
      (inf_le_left.trans hR.1) (inf_le_right.trans hR'.1)
  have hz1 : z ≠ 1 := hKz.ne_one
  have hzR : z ∈ R := by
    rw [← hxx]
    exact R.mul_mem hx hx
  have hyR'z : y * y * (y * y) = 1 := by rw [hyy, hKz.sq]
  have hxyc : x * y = y * x := hcomm x hx y hy
  have hu1 : x * y ≠ 1 := by
    intro h
    have hyx : y = x⁻¹ := eq_inv_of_mul_eq_one_right h
    have hyRR : y ∈ R ⊓ R' := ⟨hyx ▸ R.inv_mem hx, hy⟩
    have := sq_eq_one_of_natCard_le_two hcard hyRR
    rw [hyy] at this
    exact hz1 this
  have huz : x * y ≠ z := by
    intro h
    have hyx : y = x⁻¹ * z := by rw [← h]; group
    have hyRR : y ∈ R ⊓ R' := ⟨hyx ▸ R.mul_mem (R.inv_mem hx) hzR, hy⟩
    have := sq_eq_one_of_natCard_le_two hcard hyRR
    rw [hyy] at this
    exact hz1 this
  have hu2 : x * y * (x * y) = 1 := by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxyc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxx, hyy, hKz.sq]
  have hnu : n * (x * y) = x * y * n := by
    calc n * (x * y) = (n * x) * y := by group
      _ = (x * n) * y := by rw [hcen x hx]
      _ = x * (n * y) := by group
      _ = x * (y * n) := by rw [hcen' y hy]
      _ = x * y * n := by group
  refine ⟨R, R', x * y, x, y, ?_⟩
  exact
    { data :=
        { mem := hK
          hz := hKz
          hK' := hTw
          hne := hTK
          hu := Subgroup.mul_mem_sup (hR.1 hx) (hR'.1 hy)
          hu2 := hu2
          hu1 := hu1
          huz := huz
          hJ := hNW
          ht := hNn
          htu := hnu }
      syl := hR
      syl' := hR'
      comm := hcomm
      cen := hcen
      cen' := hcen'
      hx := hx
      hy := hy
      hxx := hxx
      hyy := hyy
      hxy := rfl }


theorem TwinA1Frame.rankThreeBalance [IsSimpleGroup G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} {z : G} (hΩ : HypOmegaMod p f (𝒞 K)) (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z)
    (hall : ∀ i, D.tag i = .PSL ∧ D.rank i = 2) {T N R R' : Subgroup G} {n u x y : G}
    (F : TwinA1Frame (𝒞 K) K T N R R' z n u x y) (hN : N ∈ tqMembers (𝒞 K) z)
    (hn : IsClassicalMember p f N n) (hnz : n ≠ z) :
    RankThreeBalance (Subgroup.closure ({z, u, n} : Set G)) := by
  have hset : TwinFrameSetting p f (𝒞 K) K T N z u n :=
    { odd := hp2
      five := hq
      hyp := hΩ
      aEmpty := aEmpty_of_allA1 hp2 hq hΩ hz D hall hN hn hnz
      trans := fun M hM => hM
      below := hBelow
      thm7 := thm7TypedBelow_of G2D4Models.ih8G2D4_unconditional hBelow
      frame := F.data }
  have hH51 : Hyp51 (Subgroup.closure ({z, u, n} : Set G)) :=
    twinFrameHyp51_of (T3CII.T3U.twinSmallInner_proved' (p := p))
      (twinSmallOuter_of_d4 (G2D4Models.Twin.twinSmallOuterD4_of_fixLift p
        (fun e => G2D4Models.Twin.d4FixLift_proved (p := p) (f := e))))
      g2d4VertexExcl_proved G _ K T N z u n hset
  exact lemma52 G _ hH51

end CFSG.ClassicalInvolution.NDB.NDBH3
