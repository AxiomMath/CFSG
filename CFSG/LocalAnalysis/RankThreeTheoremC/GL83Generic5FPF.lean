module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericStructureParts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5CaseIInst
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5CaseIIInst
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Close
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup2
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

private theorem isSylowOf_of_sylow_le [Fact p.Prime] (Q : Sylow p G) {K : Subgroup G}
    (hQK : (Q : Subgroup G) ≤ K) : IsSylowOf p (Q : Subgroup G) K :=
  isSylowOf_iff.mpr ⟨hQK, Q.isPGroup', fun h =>
    Q.not_dvd_index (h.trans (relIndex_dvd_index_of_le hQK))⟩

omit [Finite G] in
private theorem exists_isSylowOf_ge {Q K : Subgroup G} (hQK : Q ≤ K) (hQ : IsPGroup p Q) :
    ∃ S : Subgroup G, IsSylowOf p S K ∧ Q ≤ S := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun q hq =>
    Subgroup.mem_map.mpr ⟨⟨q, hQK hq⟩, hS hq, rfl⟩⟩

theorem gen5_dichotomy (hG : Gen5Global G) (hl : Gen5Local G p P M x) {v : G}
    (hvZ : v ∈ centralizer ((gen5L x : Subgroup G) : Set G)) :
    IsSylowOf p (gen5U (P : Subgroup G) x) (centralizer ({v} : Set G)) ∨
    ∃ d ∈ centralizer ((gen5U (P : Subgroup G) x : Subgroup G) : Set G),
      (d * v * d⁻¹) * x = x * (d * v * d⁻¹) := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  set U := gen5U (P : Subgroup G) x
  set Z := centralizer ((gen5L x : Subgroup G) : Set G)
  have hUP : U ≤ P := inf_le_left
  have hUN : U ≤ centralizer ({v} : Set G) := fun u hu =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hvZ u hu.2)
  obtain ⟨Q, hQN, hUQ⟩ := exists_isSylowOf_ge hUN (P.isPGroup'.to_le hUP)
  by_cases hQU : Q = U
  · exact Or.inl (hQU ▸ hQN)
  right
  obtain ⟨q, hqQ, hqU⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hUQ (Ne.symm hQU))
  obtain ⟨-, hPab⟩ := gen5_P_abelian hG hl
  have hQab : IsMulCommutative Q := (gen5_pgroup hG hl hQN.isPGroup).1
  have hPC : (P : Subgroup G) ≤ centralizer (U : Set G) := fun g hg => mem_centralizer_iff.mpr
    fun u hu => congrArg Subtype.val (hPab.is_comm.comm ⟨u, hUP hu⟩ ⟨g, hg⟩)
  have hQC : Q ≤ centralizer (U : Set G) := fun g hg => mem_centralizer_iff.mpr
    fun u hu => congrArg Subtype.val (hQab.is_comm.comm ⟨u, hUQ hu⟩ ⟨g, hg⟩)
  obtain ⟨S, hS, hQS⟩ := exists_isSylowOf_ge hQC hQN.isPGroup
  obtain ⟨k, hk, hkS⟩ := (isSylowOf_of_sylow_le P hPC).exists_mem_conj hS
  obtain ⟨hdec, -, -, hgen⟩ := gen5_P_decomp hG hl
  have hUnorm : U ≤ normalizer (((P : Subgroup G) ⊓ Z : Subgroup G) : Set G) := fun u hu =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz =>
      (mem_centralizer_iff.mp (hPC hz.1) u hu).symm)
  have hmem : k⁻¹ * q * k ∈ ((U ⊔ ((P : Subgroup G) ⊓ Z) : Subgroup G) : Set G) := by
    rw [← hdec]
    exact (hkS q).mp (hQS hqQ)
  rw [coe_mul_of_left_le_normalizer_right _ _ hUnorm] at hmem
  obtain ⟨u, hu, z, hz, huz⟩ := hmem
  have huz : u * z = k⁻¹ * q * k := huz
  have hku : Commute k u⁻¹ := (Commute.inv_right (mem_centralizer_iff.mp hk u hu).symm)
  have hc : k * z * k⁻¹ = u⁻¹ * q := by
    calc k * z * k⁻¹ = k * (u⁻¹ * (u * z)) * k⁻¹ := by group
      _ = k * (u⁻¹ * (k⁻¹ * q * k)) * k⁻¹ := by rw [huz]
      _ = (k * u⁻¹) * k⁻¹ * q := by group
      _ = u⁻¹ * q := by rw [hku.eq, mul_inv_cancel_right]
  have hcQ : k * z * k⁻¹ ∈ Q := hc ▸ Q.mul_mem (Q.inv_mem (hUQ hu)) hqQ
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [mul_one, mul_inv_cancel] at hc
    rw [(inv_mul_eq_one.mp hc.symm).symm] at hqU
    exact hqU hu
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (P.isPGroup'.to_le (zpowers_le.mpr hz.1))
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_zpowers, orderOf_eq_one_iff] at hn
    exact hz1 hn
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p (hn ▸ dvd_pow_self p hn0)
  rw [← orderOf_coe] at hy
  have hy1 : (y : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact (Fact.out : p.Prime).one_lt.ne hy
  have hyp : (y : G) ^ p = 1 := hy ▸ pow_orderOf_eq_one _
  have hxz : x ∈ zpowers z :=
    zpowers_le.mpr y.2 (hgen (y : G) (zpowers_le.mpr hz y.2) hy1 hyp ▸ mem_zpowers x)
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hxz
  have hxQ : k * z ^ m * k⁻¹ ∈ Q := by
    rw [← conj_zpow]
    exact Q.zpow_mem hcQ m
  have h := mem_centralizer_singleton_iff.mp (hQN.le hxQ)
  refine ⟨k⁻¹, inv_mem hk, ?_⟩
  rw [inv_inv]
  calc k⁻¹ * v * k * z ^ m = k⁻¹ * (v * (k * z ^ m * k⁻¹)) * k := by group
    _ = k⁻¹ * (k * z ^ m * k⁻¹ * v) * k := by rw [h]
    _ = z ^ m * (k⁻¹ * v * k) := by group

theorem gen5_key (hG : Gen5Global G) (hI : GL83Generic5CaseI) (hII : GL83Generic5CaseII)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (Sch : KFactCatalogSchreier)
    (hK : GL83Generic5KFacts) (hExcl : NoExcludedSection3 G)
    (hl : Gen5Local G p P M x) {v : G} (hv1 : v ≠ 1)
    (hvZ : v ∈ centralizer ((gen5L x : Subgroup G) : Set G)) (hvp : ¬ p ∣ orderOf v) :
    pCoreOf 2 M ⊓ centralizer ({v} : Set G) = ⊥ := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  have hPM := (sylow_le_of_isCoreMaxLocal hG.setting hl.sigma hl.core).1
  have hT2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMT : M ≤ normalizer (pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hTM : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hUW : ∀ w : G, (∀ u ∈ gen5U (P : Subgroup G) x, Commute u w) →
      gen5U (P : Subgroup G) x ≤
        normalizer ((pCoreOf 2 M ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) :=
    fun w hw u hu => inf_normalizer_le_normalizer_inf
      ⟨hMT (hPM hu.1), le_normalizer (mem_centralizer_singleton_iff.mpr (hw u hu))⟩
  have hclose : ∀ w ∈ centralizer ((gen5L x : Subgroup G) : Set G),
      (∀ u ∈ gen5U (P : Subgroup G) x, Commute u w) →
      (∀ k ∈ pCoreOf 2 M ⊓ centralizer ({w} : Set G), ∀ l ∈ gen5L x,
        k⁻¹ * (l⁻¹ * k * l) ∈ rankThreePrimeCore p (centralizer ({w} : Set G))) →
      pCoreOf 2 M ⊓ centralizer ({w} : Set G) = ⊥ := fun w hwZ hwU hcomm =>
    gen5_close hG hl
      (fun l hlL => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hwZ l hlL))
      (hT2.to_le inf_le_left) inf_le_right (inf_le_left.trans hTM) (hUW w hwU) hcomm
  have hvU : ∀ u ∈ gen5U (P : Subgroup G) x, Commute u v := fun u hu =>
    mem_centralizer_iff.mp hvZ u hu.2
  rcases gen5_dichotomy hG hl hvZ with hSyl | ⟨d, hd, hdx⟩
  ·
    have hWO := gen5_caseI hG hI K1 Sch hK.signalizer hExcl hl hv1 hvZ hvp hSyl
      (hT2.to_le inf_le_left) inf_le_right (hUW v hvU)
    obtain ⟨-, hNO, -⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p
      (centralizer ({v} : Set G))
    refine hclose v hvZ hvU fun k hk l hlL => ?_
    have hkO := hWO hk
    have hlN : l ∈ centralizer ({v} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hvZ l hlL)
    exact mul_mem (inv_mem hkO) ((mem_normalizer_iff''.mp (hNO hlN) k).mp hkO)
  ·
    have hdM : d ∈ M := gen5_centralizer_U_le hG hl hd
    have hv'1 : d * v * d⁻¹ ≠ 1 := fun h => hv1 (conj_eq_one_iff.mp h)
    have hv'p : ¬ p ∣ orderOf (d * v * d⁻¹) := by
      rwa [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    have hv'U : ∀ u ∈ gen5U (P : Subgroup G) x, Commute u (d * v * d⁻¹) := fun u hu =>
      have hud : Commute u d := mem_centralizer_iff.mp hd u hu
      (hud.mul_right (hvU u hu)).mul_right hud.inv_right
    obtain ⟨e⟩ := gen5_psl hG hl
    have hv'Z : d * v * d⁻¹ ∈ centralizer ((gen5L x : Subgroup G) : Set G) := by
      refine le_centralizer_layer_of_coprime_of_isGenericPoint hl.generic le_rfl e
        (X := zpowers (d * v * d⁻¹)) ?_ ?_ ?_ (mem_zpowers _)
      · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hdx)
      · rwa [Nat.card_zpowers]
      · intro u hu
        refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun g hg => ?_)
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hg
        exact ((hv'U u ⟨hu.1.1, hu.2⟩).zpow_right j).eq.symm
    have hW' := hclose _ hv'Z hv'U (gen5_caseII hG hII Sch hK.weakClosure hK.innerAction hl
      hv'1 hv'Z hv'p hdx (hT2.to_le inf_le_left) inf_le_right (hUW _ hv'U))
    rw [eq_bot_iff]
    intro k hk
    have hk' : d * k * d⁻¹ ∈ pCoreOf 2 M ⊓ centralizer ({d * v * d⁻¹} : Set G) := by
      refine ⟨(mem_normalizer_iff.mp (hMT hdM) k).mp hk.1, mem_centralizer_singleton_iff.mpr ?_⟩
      have hkv : k * v = v * k := mem_centralizer_singleton_iff.mp hk.2
      calc d * k * d⁻¹ * (d * v * d⁻¹) = d * (k * v) * d⁻¹ := by group
        _ = d * (v * k) * d⁻¹ := by rw [hkv]
        _ = d * v * d⁻¹ * (d * k * d⁻¹) := by group
    rwa [hW', mem_bot, conj_eq_one_iff] at hk'

theorem gl83GenericFPF_of_kfacts (hG : Gen5Global G) (hI : GL83Generic5CaseI)
    (hII : GL83Generic5CaseII) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (Sch : KFactCatalogSchreier) (hK : GL83Generic5KFacts) (hExcl : NoExcludedSection3 G) :
    GL83GenericFPF G := by
  intro p hp P M hM hfail hIH x hgen v hv hv1 _ hcop k hk hkv
  have hl : Gen5Local G p P M x := ⟨hp, hM, hfail, hIH, hgen⟩
  have hbot := gen5_key hG hI hII K1 Sch hK hExcl hl hv1 hv
    ((Nat.Prime.coprime_iff_not_dvd (gen5_prime hl)).1 hcop)
  have hkW : k ∈ pCoreOf 2 M ⊓ centralizer ({v} : Set G) :=
    ⟨hk, mem_centralizer_singleton_iff.mpr hkv⟩
  rwa [hbot, mem_bot] at hkW

end CFSG.LocalAnalysis.RankThreeTheoremC
