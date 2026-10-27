module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveKer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneComp
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.GH74.GLS.Bg.Pu5.BalBBasic
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
public import Certificates.Kernel.ThCent.Leaves
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups
import CFSG.GH74.GLS.Bg.Iii2.Statements
import CFSG.GH74.GLS.Bg.Pu5.BalStatements
import CFSG.GH74.GLS.Bg.Pu5.Statements
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
import CFSG.GH74.GLS.IVK.L2.Lemma13
import CFSG.GH74.GLS.IVK.Lifted.GroupAux
import CFSG.GH74.GLS.IVK.Lifted.IIAutB
import CFSG.GH74.GLS.IVK.Lifted.Outer14
import CFSG.GH74.GLS.IVK.Lifted.SolvAut
import CFSG.GH74.GLS.IVK.Lifted.Strong
import CFSG.GH74.GLS.IVK.Prod.Basic
import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Prop41
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.TwoThin.KGroupCore
import CFSG.GH74.L5U5.ModelsBridge
import CFSG.GH74.Statements
import CFSG.GH74.Uniqueness.Bender.Models
import CFSG.GH74.Uniqueness.SU.KInputs2
import CFSG.GH74.Uniqueness.SU.SU13TA1Class
import CFSG.GH74.Uniqueness.SU.SU8Stmts
import CFSG.GroupTheory.PCore.Transport
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

private theorem p_dvd_card_of_isPComponentIn {H Y : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hY : IsPComponentIn p Y H) : p ∣ Nat.card Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Kc, hKc, -, hmap, -⟩ := hY.2
  have hres : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual p Y = ⊤ :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff p Y H hY.1).mp
      hY.2 |>.2.1
  by_contra hpd
  have hcop : Nat.Coprime p (Nat.card Y) := (hp.coprime_iff_not_dvd).mpr hpd
  have hbot : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual p Y = ⊥ :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_bot_of_coprime_card p hcop
  have htopbot : (⊤ : Subgroup ↥Y) = ⊥ := by rw [← hres, hbot]
  have hYbot : Y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥Y) ∈ (⊥ : Subgroup ↥Y) := htopbot ▸ Subgroup.mem_top _
    simpa using hmem
  have hKbot : Kc = ⊥ := by
    rw [← hmap, hYbot]
    simp
  have hKnt : Nontrivial ↥Kc := CFSG.LocalCores.isQuasisimple_nontrivial hKc.1
  exact (Subgroup.nontrivial_iff_ne_bot Kc).mp hKnt hKbot

private theorem exists_mulEquiv_map_pCore {K Y : Subgroup G} (hYK : Y ≤ K)
    (hYF : Y ⊓ pCoreOf 2 K = pCoreOf 2 Y) :
    Nonempty ((↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
      ((Y.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))) := by
  let FK : Subgroup ↥K := CFSG.pCore 2 ↥K
  let π : ↥K →* (↥K ⧸ FK) := QuotientGroup.mk' FK
  let g : ↥Y →* (↥K ⧸ FK) := π.comp (Subgroup.inclusion hYK)
  have hgker : g.ker = CFSG.pCore 2 ↥Y := by
    ext x
    rw [MonoidHom.mem_ker]
    change (Subgroup.inclusion hYK x : ↥K ⧸ FK) = 1 ↔ x ∈ CFSG.pCore 2 ↥Y
    rw [QuotientGroup.eq_one_iff,
      show Subgroup.inclusion hYK x = (⟨x, hYK x.2⟩ : ↥K) from rfl,
      ← CFSG.mem_openPCoreOf_iff (H := K) (x := (⟨x, hYK x.2⟩ : ↥K))]
    change (x : G) ∈ pCoreOf 2 K ↔ x ∈ CFSG.pCore 2 ↥Y
    rw [← CFSG.mem_openPCoreOf_iff (H := Y) x, ← hYF]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hgrange : g.range = (Y.subgroupOf K).map π := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
    ((QuotientGroup.quotientKerEquivRange g).trans (MulEquiv.subgroupCongr hgrange))⟩

private theorem isComponent_map_pCore {K Y : Subgroup G} (hYK : Y ≤ K)
    (hYsn : (Y.subgroupOf K).IsSubnormal)
    (hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hYF : Y ⊓ pCoreOf 2 K = pCoreOf 2 Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ Nat.card Y) :
    CFSG.IsComponent ((Y.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) ∧
      p ∣ Nat.card ((Y.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) := by
  obtain ⟨eY⟩ := exists_mulEquiv_map_pCore hYK hYF
  have hqs : CFSG.IsQuasisimple
      ((Y.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) :=
    CFSG.IsQuasisimple.of_mulEquiv eY.symm hYq
  have hsn : ((Y.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) hYsn
  refine ⟨⟨hqs, hsn⟩, ?_⟩
  have hcard : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) =
      Nat.card ((Y.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) :=
    Nat.card_congr eY.toEquiv
  have hO2_notdvd : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥Y) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥Y) (p := 2)).exists_card_eq
    intro hd
    have hp2' : p = 2 := by
      refine (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ?_
      exact hp.dvd_of_dvd_pow (by rwa [hk] at hd)
    exact hp2 hp2'
  have hquot_dvd : p ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    have hcardY := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Y)
    have hprod : p ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) * Nat.card (CFSG.pCore 2 ↥Y) := by
      rwa [← hcardY]
    exact ((hp.dvd_mul).mp hprod).resolve_right hO2_notdvd
  exact hcard.symm ▸ hquot_dvd

private theorem isSubnormal_of_isPComponentIn_kSub (hL : ¬ pLayerIn p H ≤ M)
    {Y : Subgroup G} (hY : IsPComponentIn p Y H) (hYM : ¬ Y ≤ M) :
    CFSG.Open.IsSubnormal Y (kSub p M H) := by
  have hKKdef : kSub p M H = sSup {Y | IsPComponentIn p Y H ∧ ¬ Y ≤ M} := by
    unfold kSub
    rw [if_neg hL]
  have hYK_le : Y ≤ kSub p M H := hKKdef.symm ▸ le_sSup ⟨hY, hYM⟩
  have hYsnH : CFSG.Open.IsSubnormal Y H :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hY.1).mpr hY.2.choose_spec.2.1
  have hinf := hYsnH.inf_of_le (kSub_le p M H)
  rwa [inf_eq_left.mpr hYK_le] at hinf

private theorem pCoreOf_inter_eq_of_isPComponentIn (hL : ¬ pLayerIn p H ≤ M)
    {Y : Subgroup G} (hY : IsPComponentIn p Y H) (hYM : ¬ Y ≤ M) :
    Y ⊓ pCoreOf 2 (kSub p M H) = pCoreOf 2 Y := by
  let KK := kSub p M H
  let F : Subgroup G := pCoreOf 2 KK
  have hKKdef : KK = sSup {Y | IsPComponentIn p Y H ∧ ¬ Y ≤ M} := by
    change kSub p M H = sSup {Y | IsPComponentIn p Y H ∧ ¬ Y ≤ M}
    unfold kSub
    rw [if_neg hL]
  have hYK_le : Y ≤ KK := hKKdef.symm ▸ le_sSup ⟨hY, hYM⟩
  have hYsnK : CFSG.Open.IsSubnormal Y KK := isSubnormal_of_isPComponentIn_kSub hL hY hYM
  have hO2Y_le_F : pCoreOf 2 Y ≤ F :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2 hYsnK
  have hYF_normal : ((Y ⊓ F).subgroupOf Y).Normal := by
    have hFK : (F.subgroupOf KK).Normal := by
      change ((pCoreOf 2 KK).subgroupOf KK).Normal
      rw [CFSG.openPCoreOf_subgroupOf]
      infer_instance
    have hYnormF : Y ≤ Subgroup.normalizer (F : Set G) :=
      hYK_le.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer
          (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 KK)).mp hFK)
    have hYnorm : Y ≤ Subgroup.normalizer ((Y ⊓ F : Subgroup G) : Set G) :=
      (le_inf Subgroup.le_normalizer hYnormF).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := Y) (K := F))
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hYnorm
  have hYF2 : IsPGroup 2 ↥(Y ⊓ F) :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 KK).of_injective
      (Subgroup.inclusion (inf_le_right : Y ⊓ F ≤ F))
      (Subgroup.inclusion_injective (inf_le_right : Y ⊓ F ≤ F))
  refine le_antisymm ?_ ?_
  · exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf
      2 (Y ⊓ F) Y inf_le_left hYF_normal hYF2
  · exact le_inf (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 Y) hO2Y_le_F

private theorem commutator_le_pCoreOf_of_subgroupOf_le {K Y P : Subgroup G}
    (hYK : Y ≤ K) (hPK : P ≤ K)
    (h : ⁅Y.subgroupOf K, P.subgroupOf K⁆ ≤ CFSG.pCore 2 ↥K) :
    ⁅Y, P⁆ ≤ pCoreOf 2 K := by
  rw [Subgroup.commutator_le]
  intro y hy p hp
  have hyK : (⟨y, hYK hy⟩ : ↥K) ∈ Y.subgroupOf K := hy
  have hpK : (⟨p, hPK hp⟩ : ↥K) ∈ P.subgroupOf K := hp
  have hmem : (⟨y, hYK hy⟩ : ↥K) * (⟨p, hPK hp⟩ : ↥K) *
      (⟨y, hYK hy⟩ : ↥K)⁻¹ * (⟨p, hPK hp⟩ : ↥K)⁻¹ ∈ CFSG.pCore 2 ↥K :=
    Subgroup.commutator_le.mp h _ hyK _ hpK
  change ⁅y, p⁆ ∈ (CFSG.pCore 2 ↥K).map K.subtype
  exact Subgroup.mem_map.mpr ⟨_, hmem, by simp [commutatorElement_def]⟩

private theorem commutator_le_pCoreOf_of_component_map {K Y P : Subgroup G} {p : ℕ}
    (hYK : Y ≤ K) (hPK : P ≤ K)
    (hYbar_comp : CFSG.IsComponent ((Y.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K))))
    (hYbar_pdvd : p ∣ Nat.card ((Y.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K))))
    (hP : P = relPPrimeCore p K) (hp : p.Prime)
    (hPcop : Nat.Coprime p (Nat.card P))
    (hPK_normal : (P.subgroupOf K).Normal) :
    ⁅Y, P⁆ ≤ pCoreOf 2 K := by
  let PK : Subgroup ↥K := P.subgroupOf K
  have hPbar_normal : (PK.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
    hPK_normal.map _ (QuotientGroup.mk'_surjective _)
  have hPbar_cop : ¬ p ∣ Nat.card (PK.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) := by
    refine fun hdvd => (hp.coprime_iff_not_dvd.mp hPcop) (hdvd.trans ?_)
    calc Nat.card (PK.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
        ∣ Nat.card PK := Subgroup.card_map_dvd PK (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      _ = Nat.card P := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv
  have hYbar_notle : ¬ (Y.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      ≤ PK.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
    intro hle
    exact hPbar_cop (hYbar_pdvd.trans (Subgroup.card_dvd_of_le hle))
  have hcomm_bar : ⁅(Y.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)),
      PK.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))⁆ = ⊥ :=
    (CFSG.LocalCores.component_normal_subgroup hYbar_comp hPbar_normal).resolve_left hYbar_notle
  have hcommK : ⁅Y.subgroupOf K, PK⁆ ≤ CFSG.pCore 2 ↥K := by
    have hmap : (⁅Y.subgroupOf K, PK⁆).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) = ⊥ := by
      rw [Subgroup.map_commutator, hcomm_bar]
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
  exact commutator_le_pCoreOf_of_subgroupOf_le hYK hPK hcommK

private theorem commutator_le_pCoreOf_of_isPComponentIn
    (h : TwelveCtx G M p Q H) (h912 : NineTwelveKerConclusion G M Q H Q p)
    (hL : ¬ pLayerIn p H ≤ M) (hp3 : p ≠ 3) {Y : Subgroup G}
    (hY : IsPComponentIn p Y H) (hYM : ¬ Y ≤ M) :
    ⁅Y, relPPrimeCore p (kSub p M H)⁆ ≤ pCoreOf 2 (kSub p M H) := by
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  let KK := kSub p M H
  let P : Subgroup G := relPPrimeCore p KK
  have hKKdef : KK = sSup {Y | IsPComponentIn p Y H ∧ ¬ Y ≤ M} := by
    change kSub p M H = sSup {Y | IsPComponentIn p Y H ∧ ¬ Y ≤ M}
    unfold kSub
    rw [if_neg hL]
  have hYK_le : Y ≤ KK := hKKdef.symm ▸ le_sSup ⟨hY, hYM⟩
  have hYsnK : CFSG.Open.IsSubnormal Y KK := isSubnormal_of_isPComponentIn_kSub hL hY hYM
  have hYsn : (Y.subgroupOf KK).IsSubnormal :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hYK_le).mp hYsnK
  have hint :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff p Y H hY.1).mp
      hY.2
  have hYK : IsPComponentIn p Y KK := by
    refine ⟨hYK_le, ?_⟩
    rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff p Y KK hYK_le]
    exact ⟨hYsn, hint.2.1, hint.2.2⟩
  have hYtwo : IsTwoPrimeComponentIn Y H := by
    rcases h912.1 hL Y hYK with h' | ⟨hp, -⟩
    · exact h'
    · exact absurd hp hp3
  have hYF_eq : Y ⊓ pCoreOf 2 KK = pCoreOf 2 Y := pCoreOf_inter_eq_of_isPComponentIn hL hY hYM
  obtain ⟨hYbar_comp, hYbar_pdvd⟩ :=
    isComponent_map_pCore hYK_le hYsn hYtwo.2.2.1 hYF_eq h.p_prime h.p_odd
      (p_dvd_card_of_isPComponentIn h.p_prime hY)
  exact commutator_le_pCoreOf_of_component_map hYK_le
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le KK)
    hYbar_comp hYbar_pdvd rfl h.p_prime
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      h.p_prime KK)
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      h.p_prime KK)

private theorem kSub_perfect (h : TwelveCtx G M p Q H) (hL : ¬ pLayerIn p H ≤ M) :
    ⁅kSub p M H, kSub p M H⁆ = kSub p M H := by
  classical
  set K : Subgroup G := kSub p M H with hK
  let S : Set (Subgroup G) := {Y | IsPComponentIn p Y H ∧ ¬ Y ≤ M}
  have hKdef : K = sSup S := by
    rw [hK]
    unfold kSub
    rw [if_neg hL]
  refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) ?_
  rw [hKdef]
  refine sSup_le fun Y hY => ?_
  have hYperf : Group.IsPerfect ↥Y := IsPComponentIn.isPerfect h.p_prime hY.1
  calc Y = ⁅Y, Y⁆ := (Subgroup.isPerfect_iff.mp hYperf).symm
    _ ≤ ⁅sSup S, sSup S⁆ := Subgroup.commutator_mono (le_sSup hY) (le_sSup hY)

theorem TwelveCtx.kSub_perfect_and_commutator_le (h : TwelveCtx G M p Q H)
    (h912 : NineTwelveKerConclusion G M Q H Q p) (hL : ¬ pLayerIn p H ≤ M) (hp3 : p ≠ 3) :
    ⁅kSub p M H, kSub p M H⁆ = kSub p M H ∧
      ⁅kSub p M H, relPPrimeCore p (kSub p M H)⁆ ≤ pCoreOf 2 (kSub p M H) := by
  classical
  set K : Subgroup G := kSub p M H with hK
  change ⁅K, K⁆ = K ∧ ⁅K, relPPrimeCore p K⁆ ≤ pCoreOf 2 K
  have hKperf : ⁅K, K⁆ = K := by
    rw [hK]
    exact kSub_perfect h hL
  let S : Set (Subgroup G) := {Y | IsPComponentIn p Y H ∧ ¬ Y ≤ M}
  have hKdef : K = sSup S := by
    rw [hK]
    unfold kSub
    rw [if_neg hL]
  have hgen : ∀ Y ∈ S, ⁅Y, relPPrimeCore p K⁆ ≤ pCoreOf 2 K := fun Y hY =>
    commutator_le_pCoreOf_of_isPComponentIn h h912 hL hp3 hY.1 hY.2
  have hKN : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := by
    have hFK : ((pCoreOf 2 K).subgroupOf K).Normal := by
      rw [CFSG.openPCoreOf_subgroupOf]
      infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 K)).mp hFK
  have hcomm : ⁅K, relPPrimeCore p K⁆ ≤ pCoreOf 2 K := by
    rw [Subgroup.commutator_le]
    intro k hk q hq
    exact CFSG.GH74.GLS.Bg.Pu5.commutator_mem_of_le_sSup (C := K) (N := pCoreOf 2 K)
      (y := q) hKN (fun Y hY => hKdef.symm ▸ le_sSup hY)
      (fun Y hY y hy => Subgroup.commutator_le.mp (hgen Y hY) y hy q hq)
      k (hKdef ▸ hk)
  exact ⟨hKperf, hcomm⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
