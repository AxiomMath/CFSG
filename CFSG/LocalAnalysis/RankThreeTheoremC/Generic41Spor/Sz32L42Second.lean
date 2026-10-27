module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32L42Graph
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointWThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPoint
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointStageA
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointWStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointTypes
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfigCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericListPrune3
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42Generic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Sylow
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallShape
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBMinimal
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma41
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfig
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Perm.ChainSpec
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2269
public import Certificates.Certificate3951
public import Certificates.Certificate8033

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T GenericComponentClass u3_sylow_data)

variable {G : Type} [Group G] [Finite G]

theorem sz32_second_point_core {P : Sylow 5 G} {V Z T H : Subgroup G} {x e u : G}
    (hVP : V ≤ (P : Subgroup G)) (hVel : IsElemAbelian 5 V) (hVcard : Nat.card V = 5 ^ 3)
    (hZV : Z ≤ V) (hZcard : Nat.card Z = 5 ^ 2) (hxZ : x ∈ Z) (heZ : e ∈ Z) (hx1 : x ≠ 1)
    (hlines : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x ∨
        (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers e)
    (huV : u ∈ V) (huZ : u ∉ Z)
    (hTV : T ≤ V) (hTel : IsElemAbelian 5 T) (hTcard : Nat.card T = 5 ^ 2)
    (hTu : T ⊔ zpowers u = V)
    (hHT : H ≤ normalizer (T : Set G)) (hHu : ∀ h ∈ H, h * u = u * h)
    (hmoves : ∀ s ∈ T, s ≠ 1 → ∃ h ∈ H, h * s * h⁻¹ ∉ zpowers s)
    (hthree : ∀ s ∈ T, s ≠ 1 → ∃ h₁ ∈ H, ∃ h₂ ∈ H, zpowers (h₁ * s * h₁⁻¹) ≠ zpowers s ∧
      zpowers (h₂ * s * h₂⁻¹) ≠ zpowers s ∧ zpowers (h₁ * s * h₁⁻¹) ≠ zpowers (h₂ * s * h₂⁻¹)) :
    False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : IsMulCommutative V := hVel.1
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : V) ⟨b, hb⟩)
  have hu1 : u ≠ 1 := fun h => huZ (h ▸ one_mem _)
  have hup : u ^ 5 = 1 := hVel.2 u huV
  have hxp : x ^ 5 = 1 := hVel.2 x (hZV hxZ)
  have hxo : orderOf x = 5 := orderOf_eq_prime hxp hx1
  have huo : orderOf u = 5 := orderOf_eq_prime hup hu1
  have hTc : ∀ a ∈ T, ∀ b ∈ zpowers u, a * b = b * a := fun a ha b hb =>
    hVc a (hTV ha) b (zpowers_le.2 huV hb)
  obtain ⟨t, htT, b, hbu, hxtb⟩ := spw_mem_sup_of_commute hTc (hTu ▸ hZV hxZ)
  have ht1 : t ≠ 1 := by
    intro h1
    apply huZ
    have hxb : x = b := by rw [hxtb, h1, one_mul]
    have hxu : x ∈ zpowers u := hxb ▸ hbu
    exact zpowers_le.2 hxZ (spw_mem_zpowers_of_mem_zpowers hxo huo hxu)
  have hid : ∀ h ∈ H, h * t * h⁻¹ * t⁻¹ ∈ Z := by
    intro h hh
    have hhb : h * b * h⁻¹ = b := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hbu
      have hcomm : h * u * h⁻¹ = u := by rw [hHu h hh]; group
      rw [← conj_zpow, hcomm]
    have hhx : h * x * h⁻¹ = (h * t * h⁻¹) * b := by
      calc h * x * h⁻¹ = (h * t * h⁻¹) * (h * b * h⁻¹) := by rw [hxtb]; group
        _ = (h * t * h⁻¹) * b := by rw [hhb]
    have hhtT : h * t * h⁻¹ ∈ T := (mem_normalizer_iff.1 (hHT hh) t).1 htT
    have hx'V : h * x * h⁻¹ ∈ V := by
      rw [hhx]
      exact V.mul_mem (hTV hhtT) (zpowers_le.2 huV hbu)
    have hle : (zpowers x).map (MulAut.conj h).toMonoidHom ≤ (P : Subgroup G) := by
      rw [spw_zpowers_conj]
      exact zpowers_le.2 (hVP hx'V)
    have hx'Z : h * x * h⁻¹ ∈ Z := by
      rcases hlines h hle with h1 | h1
      · rw [spw_zpowers_conj] at h1
        exact zpowers_le.2 hxZ (h1 ▸ mem_zpowers _)
      · rw [spw_zpowers_conj] at h1
        exact zpowers_le.2 heZ (h1 ▸ mem_zpowers _)
    have : h * t * h⁻¹ * t⁻¹ = (h * x * h⁻¹) * x⁻¹ := by
      rw [hhx]
      conv_rhs => rw [hxtb]
      group
    rw [this]
    exact Z.mul_mem hx'Z (Z.inv_mem hxZ)
  have hZT : Z ⊓ T ≠ ⊥ := by
    intro hbot
    let f : Z × T →* G := MonoidHom.noncommCoprod Z.subtype T.subtype
      (fun z t => (show Commute (z : G) t from hVc z (hZV z.2) t (hTV t.2)))
    have hf : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      rintro ⟨x, y⟩ hxy
      have h : (x : G) * y = 1 := hxy
      have hx : (x : G) ∈ Z ⊓ T := Subgroup.mem_inf.2 ⟨x.2, by
        rw [eq_inv_of_mul_eq_one_left h]
        exact T.inv_mem y.2⟩
      rw [hbot, Subgroup.mem_bot] at hx
      have hy : (y : G) = 1 := by rw [hx, one_mul] at h; exact h
      rw [Subgroup.mem_bot, Prod.mk_eq_one]
      exact ⟨Subtype.ext hx, Subtype.ext hy⟩
    have hmem : ∀ q : Z × T, f q ∈ V := fun q => V.mul_mem (hZV q.1.2) (hTV q.2.2)
    have hle : Nat.card (Z × T) ≤ Nat.card V := by
      have hinj : Function.Injective (fun q : Z × T => (⟨f q, hmem q⟩ : V)) := fun a b hab =>
        hf (congrArg Subtype.val hab)
      exact Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hZcard, hTcard, hVcard] at hle
    norm_num at hle
  have hTZ : T ≤ Z := sz32_graph_core hTel hTcard hZT hHT hmoves htT ht1 hid
  have hTeq : T = Z := Subgroup.eq_of_le_of_card_ge hTZ (by rw [hTcard, hZcard])
  have hxT : x ∈ T := hTeq ▸ hxZ
  obtain ⟨h₁, hh₁, h₂, hh₂, hd1, hd2, hd12⟩ := hthree x hxT hx1
  have hnotx : ∀ h ∈ H, zpowers (h * x * h⁻¹) ≠ zpowers x → zpowers (h * x * h⁻¹) = zpowers e := by
    intro h hh hne
    have hconjT : h * x * h⁻¹ ∈ T := (mem_normalizer_iff.1 (hHT hh) x).1 hxT
    have hle : (zpowers x).map (MulAut.conj h).toMonoidHom ≤ (P : Subgroup G) := by
      rw [spw_zpowers_conj]
      exact zpowers_le.2 (hVP (hTV hconjT))
    rcases hlines h hle with h1 | h1
    · rw [spw_zpowers_conj] at h1
      exact absurd h1 hne
    · rwa [spw_zpowers_conj] at h1
  exact hd12 ((hnotx h₁ hh₁ hd1).trans (hnotx h₂ hh₂ hd2).symm)


theorem sz32_psi_mem_zpowers {J : Subgroup G} {Q : Type} [Group Q] (ψ : ↥J →* Q) {c d : G}
    (hc : c ∈ J) (hd : d ∈ J) (hcd : c ∈ zpowers d) : ψ ⟨c, hc⟩ ∈ zpowers (ψ ⟨d, hd⟩) := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hcd
  refine ⟨k, ?_⟩
  have : (⟨d, hd⟩ : ↥J) ^ k = ⟨c, hc⟩ := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
  rw [← this, map_zpow]

theorem sz32_psi_lines_eq {J : Subgroup G} {Q : Type} [Group Q] (ψ : ↥J →* Q) {a b : G}
    (ha : a ∈ J) (hb : b ∈ J) (h : zpowers a = zpowers b) :
    zpowers (ψ ⟨a, ha⟩) = zpowers (ψ ⟨b, hb⟩) :=
  le_antisymm (zpowers_le.2 (sz32_psi_mem_zpowers ψ ha hb (h ▸ mem_zpowers a)))
    (zpowers_le.2 (sz32_psi_mem_zpowers ψ hb ha (h ▸ mem_zpowers b)))

theorem sz32_psi_conj {J : Subgroup G} {Q : Type} [Group Q] (ψ : ↥J →* Q) {h s : G} (hh : h ∈ J)
    (hs : s ∈ J) :
    ψ ⟨h * s * h⁻¹, J.mul_mem (J.mul_mem hh hs) (J.inv_mem hh)⟩ =
      ψ ⟨h, hh⟩ * ψ ⟨s, hs⟩ * (ψ ⟨h, hh⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem sz32_lift_lines {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {u : G}
    (hgen : IsGenericPoint p P M u) {J : Subgroup G}
    (hJC : J ≤ centralizer ({u} : Set G)) (hCJ : centralizer ({u} : Set G) ≤ normalizer (J : Set G))
    {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) :
    (NormalizerMovesLines p Q → ∀ s ∈ u3T P u J, s ≠ 1 →
      ∃ h ∈ J ⊓ normalizer (u3T P u J : Set G), h * s * h⁻¹ ∉ zpowers s) ∧
    (NormalizerThreeLines p Q → ∀ s ∈ u3T P u J, s ≠ 1 →
      ∃ h₁ ∈ J ⊓ normalizer (u3T P u J : Set G), ∃ h₂ ∈ J ⊓ normalizer (u3T P u J : Set G),
        zpowers (h₁ * s * h₁⁻¹) ≠ zpowers s ∧ zpowers (h₂ * s * h₂⁻¹) ≠ zpowers s ∧
          zpowers (h₁ * s * h₁⁻¹) ≠ zpowers (h₂ * s * h₂⁻¹)) := by
  obtain ⟨Tsyl', hTsyl', hTinj, -⟩ := spw_sylow_data hgen hJC hCJ ψ hψ hker
  have hTJ : u3T P u J ≤ J := inf_le_right
  have himg : ∀ s (hs : s ∈ u3T P u J), ψ ⟨s, hTJ hs⟩ ∈ (Tsyl' : Subgroup Q) := by
    intro s hs
    rw [hTsyl']
    exact ⟨⟨s, hTJ hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
  have hne1 : ∀ s (hs : s ∈ u3T P u J), s ≠ 1 → ψ ⟨s, hTJ hs⟩ ≠ 1 := by
    intro s hs hs1 h1
    apply hs1
    have := hTinj ⟨s, hTJ hs⟩ (Subgroup.mem_subgroupOf.2 hs) h1
    exact congrArg Subtype.val this
  have hlift := spw_lift (P := P) ψ hψ hker Tsyl' hTsyl'
  constructor
  · intro hmv s hs hs1
    obtain ⟨n, hn, hnl⟩ := hmv Tsyl' (ψ ⟨s, hTJ hs⟩) (himg s hs) (hne1 s hs hs1)
    obtain ⟨h, hhJ, hhN, hhn⟩ := hlift n hn
    refine ⟨h, ⟨hhJ, hhN⟩, fun hmem => hnl ?_⟩
    have h1 := sz32_psi_mem_zpowers ψ (J.mul_mem (J.mul_mem hhJ (hTJ hs)) (J.inv_mem hhJ))
      (hTJ hs) hmem
    rwa [sz32_psi_conj ψ hhJ (hTJ hs), hhn] at h1
  · intro h3 s hs hs1
    obtain ⟨n₁, hn₁, n₂, hn₂, d1, d2, d12⟩ := h3 Tsyl' (ψ ⟨s, hTJ hs⟩) (himg s hs) (hne1 s hs hs1)
    obtain ⟨h₁, hh₁J, hh₁N, hh₁n⟩ := hlift n₁ hn₁
    obtain ⟨h₂, hh₂J, hh₂N, hh₂n⟩ := hlift n₂ hn₂
    have hc1 := sz32_psi_conj ψ hh₁J (hTJ hs)
    have hc2 := sz32_psi_conj ψ hh₂J (hTJ hs)
    rw [hh₁n] at hc1
    rw [hh₂n] at hc2
    refine ⟨h₁, ⟨hh₁J, hh₁N⟩, h₂, ⟨hh₂J, hh₂N⟩, fun heq => d1 ?_, fun heq => d2 ?_, fun heq => d12 ?_⟩
    · have := sz32_psi_lines_eq ψ (J.mul_mem (J.mul_mem hh₁J (hTJ hs)) (J.inv_mem hh₁J)) (hTJ hs) heq
      rwa [hc1] at this
    · have := sz32_psi_lines_eq ψ (J.mul_mem (J.mul_mem hh₂J (hTJ hs)) (J.inv_mem hh₂J)) (hTJ hs) heq
      rwa [hc2] at this
    · have := sz32_psi_lines_eq ψ (J.mul_mem (J.mul_mem hh₁J (hTJ hs)) (J.inv_mem hh₁J))
        (J.mul_mem (J.mul_mem hh₂J (hTJ hs)) (J.inv_mem hh₂J)) heq
      rwa [hc1, hc2] at this


theorem sz32_second_point_plane_false (hS : Setting G) {P : Sylow 5 G} {M : Subgroup G}
    {V Z : Subgroup G} {x e u : G}
    (hVP : V ≤ (P : Subgroup G)) (hVel : IsElemAbelian 5 V) (hVcard : Nat.card V = 5 ^ 3)
    (hZV : Z ≤ V) (hZcard : Nat.card Z = 5 ^ 2) (hxZ : x ∈ Z) (heZ : e ∈ Z) (hx1 : x ≠ 1)
    (hlines : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x ∨
        (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers e)
    (hgen : IsGenericPoint 5 P M u) (huV : u ∈ V) (huZ : u ∉ Z) (hSu : u3S P u = V)
    {J : Subgroup G} (hJC : J ≤ centralizer ({u} : Set G))
    (hCJ : centralizer ({u} : Set G) ≤ normalizer (J : Set G)) (hperf : Group.IsPerfect J)
    (hlt : rankThreePrimeCore 5 J < J)
    (hmin : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore 5 J ≤ N →
      N = rankThreePrimeCore 5 J ∨ N = J) (hnot : ¬ J ≤ M)
    {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J) (hQ : SecondPointFacts 5 Q)
    (hpl : SylowIsPlane 5 Q) (h3 : NormalizerThreeLines 5 Q) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmvQ : NormalizerMovesLines 5 Q := by
    rcases hQ.shape with ⟨-, h⟩ | ⟨hh, -⟩
    · exact h
    · exfalso
      obtain ⟨S⟩ : Nonempty (Sylow 5 Q) := inferInstance
      have h3' := (hh S).1
      have h2' := (hpl S).2
      rw [h3'] at h2'
      exact absurd (Nat.pow_right_injective (Fact.out : Nat.Prime 5).two_le h2') (by norm_num)
  obtain ⟨hTcard, hTel⟩ := spw_T_structure_plane hgen hJC hCJ ψ hψ hker hpl
  obtain ⟨Zu, hZucyc, huZu, hZuS, hZuT, hTZu, hsup⟩ :=
    second_point_S_decomp hS (by norm_num) hgen hJC hCJ hperf hlt hmin hnot ψ hψ hker hQ
  have hu1 : u ≠ 1 := fun h => huZ (h ▸ one_mem _)
  have hup : u ^ 5 = 1 := hVel.2 u huV
  have hZu_eq : Zu = zpowers u := by
    apply le_antisymm
    · intro z hz
      have hzV : z ∈ V := hSu ▸ hZuS hz
      exact spw_mem_zpowers_of_cyclic hZucyc huZu hu1 hup hz (hVel.2 z hzV)
    · exact zpowers_le.2 huZu
  have hTV : u3T P u J ≤ V := (inf_le_left : u3T P u J ≤ u3S P u).trans hSu.le
  have hTu : u3T P u J ⊔ zpowers u = V := by rw [← hZu_eq, hsup, hSu]
  have hHu : ∀ h ∈ J ⊓ normalizer (u3T P u J : Set G), h * u = u * h := by
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hJC hh.1)
  obtain ⟨hmv, hthr⟩ := sz32_lift_lines hgen hJC hCJ ψ hψ hker
  exact sz32_second_point_core hVP hVel hVcard hZV hZcard hxZ heZ hx1 hlines huV huZ hTV hTel hTcard
    hTu inf_le_right hHu (hmv hmvQ) (hthr h3)

theorem sz32_second_point_not_sz32 (hSz : Sz32Facts) {P : Sylow 5 G} {M : Subgroup G} {V : Subgroup G} {u : G}
    (hgen : IsGenericPoint 5 P M u) (hVel : IsElemAbelian 5 V) (hSu : u3S P u = V)
    {J : Subgroup G} (hJC : J ≤ centralizer ({u} : Set G))
    (hCJ : centralizer ({u} : Set G) ≤ normalizer (J : Set G))
    {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J) (hQ : IsSz32Type 5 Q) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Tsyl', hTsyl', -, -⟩ := spw_sylow_data hgen hJC hCJ ψ hψ hker
  obtain ⟨hcyc, hcard⟩ := hSz.sylow Q hQ Tsyl'
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgo : orderOf g = 5 ^ 2 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg]; exact hcard
  have hgmem : (g : Q) ∈ ((u3T P u J).subgroupOf J).map ψ := hTsyl' ▸ g.2
  obtain ⟨s, hs, hsg⟩ := hgmem
  have hsV : (s : G) ∈ V := hSu ▸ (inf_le_left : u3T P u J ≤ u3S P u) (Subgroup.mem_subgroupOf.1 hs)
  have hs5 : (s : G) ^ 5 = 1 := hVel.2 _ hsV
  have hg5 : (g : Q) ^ 5 = 1 := by
    rw [← hsg, ← map_pow]
    have : s ^ 5 = 1 := Subtype.ext hs5
    rw [this, map_one]
  have hdvd : orderOf (g : Q) ∣ 5 := orderOf_dvd_of_pow_eq_one hg5
  rw [Subgroup.orderOf_coe, hgo] at hdvd
  omega


theorem sz32_second_point_A10 (hS : Setting G) (hClass : GenericComponentClass G) (hTits : TitsFacts)
    (hA10 : A10Facts) (hMcL : ExtraFacts IsMcLType 5 McLShape) (hJ4 : ExtraFacts IsJ4Type 11 J4Shape)
    (hSz : Sz32Facts) (hp : 5 ∈ rankThreeSigmaA G) {P : Sylow 5 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 5 P M) (hfail : ¬ rankThreeGamma 1 5 (P : Subgroup G) ≤ M)
    (hIH : LargerPrimesUnique G 5) {V Z : Subgroup G} {x e u : G}
    (hVP : V ≤ (P : Subgroup G)) (hVel : IsElemAbelian 5 V) (hVcard : Nat.card V = 5 ^ 3)
    (hZV : Z ≤ V) (hZcard : Nat.card Z = 5 ^ 2) (hxZ : x ∈ Z) (heZ : e ∈ Z) (hx1 : x ≠ 1)
    (hlines : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x ∨
        (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers e)
    (hgen : IsGenericPoint 5 P M u) (huV : u ∈ V) (huZ : u ∉ Z) (hSu : u3S P u = V) :
    ∃ J : Subgroup G, PointConfig IsA10Type G 5 P M u J := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨J, hJC, hCJ, hperf, hlt, hmin, hnot, Q, hQg, ψ, hψ, hker, hlist, -⟩ :=
    hClass 5 hp P M hM hfail hIH u hgen (le_refl 5)
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hz : Subgroup.center Q = ⊥ :=
    u3main_center_bot (CFSG.AGLEmbedding.glbPrimeCore_le 5 J) hperf hlt hmin ψ hψ hker
  haveI : IsMulCommutative V := hVel.1
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : V) ⟨b, hb⟩)
  have hTV : u3T P u J ≤ V := (inf_le_left : u3T P u J ≤ u3S P u).trans hSu.le
  rcases hlist with hE | ⟨h5', hSzQ⟩
  · have hQ := secondPointFacts_of_class (le_refl 5) hE hz hTits hA10 hMcL hJ4
    rcases hQ.shape with ⟨hpl, -⟩ | ⟨hheis, -⟩
    · rcases hE with ⟨hpp, ⟨e'⟩⟩ | ⟨q, hqp, hqe, hiso⟩ | ⟨-, hA | hT | hMc⟩ | ⟨h511, -⟩
      · exact (sz32_second_point_plane_false hS hVP hVel hVcard hZV hZcard hxZ heZ hx1 hlines hgen
          huV huZ hSu hJC hCJ hperf hlt hmin hnot ψ hψ hker hQ hpl
          (normalizerThreeLines_of_equiv e' (normalizerThreeLines_psl2 (le_refl 5)))).elim
      · exfalso
        have hU : IsU3Pred 5 Q := ⟨q, hqp, hqe, hiso⟩
        obtain ⟨S⟩ : Nonempty (Sylow 5 Q) := inferInstance
        have h3 := (u3_sylow_data (le_refl 5) hU S).1
        have h2 := (hpl S).2
        rw [h3] at h2
        exact absurd (Nat.pow_right_injective (Fact.out : Nat.Prime 5).two_le h2) (by norm_num)
      · exact ⟨J, ⟨hp, hM, hfail, hIH, hgen, le_refl 5, hJC, hCJ, hperf, hlt, hmin, hnot,
          ⟨Q, hQg, ψ, hψ, hker, ⟨rfl, hA⟩⟩⟩⟩
      · exact (sz32_second_point_plane_false hS hVP hVel hVcard hZV hZcard hxZ heZ hx1 hlines hgen
          huV huZ hSu hJC hCJ hperf hlt hmin hnot ψ hψ hker hQ hpl
          (normalizerThreeLines_of_transitive hpl (hTits.trans Q ⟨rfl, hT⟩))).elim
      · exfalso
        obtain ⟨S⟩ : Nonempty (Sylow 5 Q) := inferInstance
        have h3 := (hMcL.sylow Q ⟨rfl, hMc⟩ S).1
        have h2 := (hpl S).2
        rw [h3] at h2
        exact absurd (Nat.pow_right_injective (Fact.out : Nat.Prime 5).two_le h2) (by norm_num)
      · exact absurd h511 (by norm_num)
    ·
      exfalso
      obtain ⟨-, -, hTnc⟩ := spw_T_structure_heis hgen hJC hCJ ψ hψ hker hheis
      exact hTnc (IsMulCommutative.of_setLike_mul_comm fun a ha b hb => hVc a (hTV ha) b (hTV hb))
  · exact (sz32_second_point_not_sz32 hSz hgen hVel hSu hJC hCJ ψ hψ hker ⟨h5', hSzQ⟩).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
