module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenNotXOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySeven
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneComp
import CFSG.Quasithin.Vol2.Ch3Sec3Comp
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Generic
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InnerNotQJZeroInV

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup
open scoped commutatorElement

namespace TenFiveX

section Generic

variable {Γ : Type*} [Group Γ]

theorem conj_mul_eq_conj_mul {N : Subgroup Γ} [N.Normal] {x a b : Γ}
    (ha : ∀ n ∈ N, Commute a n) (hb : ∀ n ∈ N, Commute b n)
    (hax : a * x * a⁻¹ * x⁻¹ ∈ N) (hbx : b * x * b⁻¹ * x⁻¹ ∈ N) :
    a * b * x * (a * b)⁻¹ = b * a * x * (b * a)⁻¹ := by
  set na := a * x * a⁻¹ * x⁻¹ with hna
  set nb := b * x * b⁻¹ * x⁻¹ with hnb
  have ea : a * x * a⁻¹ = na * x := by rw [hna]; group
  have eb : b * x * b⁻¹ = nb * x := by rw [hnb]; group
  have hcen : ∀ m ∈ N, Commute na m := by
    intro m hm
    have hm' : x⁻¹ * m * x ∈ N := by
      have := (inferInstance : N.Normal).conj_mem m hm x⁻¹
      simpa using this
    have e1 : a * m = m * a := (ha m hm).eq
    have e2 : a * (x⁻¹ * m * x) = (x⁻¹ * m * x) * a := (ha _ hm').eq
    have e2' : a⁻¹ * (x⁻¹ * m * x) = (x⁻¹ * m * x) * a⁻¹ := by
      have := congrArg (fun z => a⁻¹ * z * a⁻¹) e2
      simpa [mul_assoc] using this.symm
    show na * m = m * na
    have em : m = x * (x⁻¹ * m * x) * x⁻¹ := by group
    calc na * m = a * x * (a⁻¹ * (x⁻¹ * m * x)) * x⁻¹ := by rw [hna]; group
      _ = a * x * ((x⁻¹ * m * x) * a⁻¹) * x⁻¹ := by rw [e2']
      _ = (a * m) * x * a⁻¹ * x⁻¹ := by group
      _ = (m * a) * x * a⁻¹ * x⁻¹ := by rw [e1]
      _ = m * na := by rw [hna]; group
  have hnbN : nb ∈ N := hbx
  have hnaN : na ∈ N := hax
  have hab : a * b * x * (a * b)⁻¹ = nb * na * x := by
    calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = a * nb * a⁻¹ * (a * x * a⁻¹) := by rw [eb]; group
      _ = nb * (na * x) := by rw [ea, (ha nb hnbN).eq]; group
      _ = nb * na * x := by group
  have hba : b * a * x * (b * a)⁻¹ = na * nb * x := by
    calc b * a * x * (b * a)⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by group
      _ = b * na * b⁻¹ * (b * x * b⁻¹) := by rw [ea]; group
      _ = na * (nb * x) := by rw [eb, (hb na hnaN).eq]; group
      _ = na * nb * x := by group
  rw [hab, hba, (hcen nb hnbN).eq]

theorem inv_comm_mem {N : Subgroup Γ} {x a : Γ} (ha : ∀ n ∈ N, Commute a n)
    (hax : a * x * a⁻¹ * x⁻¹ ∈ N) : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ ∈ N := by
  have h1 : a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a = a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ := by group
  have h2 : a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a = (a * x * a⁻¹ * x⁻¹)⁻¹ := by
    have := (ha _ (N.inv_mem hax)).eq
    calc a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a = a⁻¹ * ((a * x * a⁻¹ * x⁻¹)⁻¹ * a) := by group
      _ = a⁻¹ * (a * (a * x * a⁻¹ * x⁻¹)⁻¹) := by rw [this]
      _ = _ := by group
  rw [← h1, h2]
  exact N.inv_mem hax

theorem commute_commutatorElement {N : Subgroup Γ} [N.Normal] {x a b : Γ}
    (ha : ∀ n ∈ N, Commute a n) (hb : ∀ n ∈ N, Commute b n)
    (hax : a * x * a⁻¹ * x⁻¹ ∈ N) (hbx : b * x * b⁻¹ * x⁻¹ ∈ N) :
    Commute ⁅a, b⁆ x := by
  have hai : ∀ n ∈ N, Commute a⁻¹ n := fun n hn => (ha n hn).inv_left
  have hbi : ∀ n ∈ N, Commute b⁻¹ n := fun n hn => (hb n hn).inv_left
  have h := conj_mul_eq_conj_mul hai hbi (inv_comm_mem ha hax) (inv_comm_mem hb hbx)
  have h' : (b * a)⁻¹ * x * (b * a) = (a * b)⁻¹ * x * (a * b) := by
    calc (b * a)⁻¹ * x * (b * a) = a⁻¹ * b⁻¹ * x * (a⁻¹ * b⁻¹)⁻¹ := by group
      _ = b⁻¹ * a⁻¹ * x * (b⁻¹ * a⁻¹)⁻¹ := h
      _ = (a * b)⁻¹ * x * (a * b) := by group
  show ⁅a, b⁆ * x = x * ⁅a, b⁆
  rw [commutatorElement_def]
  calc a * b * a⁻¹ * b⁻¹ * x = (a * b) * ((b * a)⁻¹ * x * (b * a)) * (b * a)⁻¹ := by group
    _ = (a * b) * ((a * b)⁻¹ * x * (a * b)) * (b * a)⁻¹ := by rw [h']
    _ = x * (a * b * a⁻¹ * b⁻¹) := by group

theorem pow_three_eq_one_of_conj {a b c : Γ} (hac : a * c = c * a)
    (hc : a * b * a⁻¹ = c * b) (ha : a ^ 3 = 1) : c ^ 3 = 1 := by
  have hac' : a * c * a⁻¹ = c := by rw [hac]; group
  have h2 : a * (a * b * a⁻¹) * a⁻¹ = c * (c * b) := by
    rw [hc]
    calc a * (c * b) * a⁻¹ = (a * c * a⁻¹) * (a * b * a⁻¹) := by group
      _ = c * (c * b) := by rw [hac', hc]
  have h3 : a * (a * (a * b * a⁻¹) * a⁻¹) * a⁻¹ = c * (c * (c * b)) := by
    rw [h2]
    calc a * (c * (c * b)) * a⁻¹ = (a * c * a⁻¹) * (a * c * a⁻¹) * (a * b * a⁻¹) := by group
      _ = c * (c * (c * b)) := by rw [hac', hc]; group
  have h4 : a ^ 3 * b * (a ^ 3)⁻¹ = c ^ 3 * b := by
    calc a ^ 3 * b * (a ^ 3)⁻¹ = a * (a * (a * b * a⁻¹) * a⁻¹) * a⁻¹ := by
          rw [pow_three]; group
      _ = c * (c * (c * b)) := h3
      _ = c ^ 3 * b := by rw [pow_three]; group
  rw [ha] at h4
  have : b = c ^ 3 * b := by simpa using h4
  exact (mul_eq_right.mp this.symm)

theorem eq_one_of_pow_three_pow {c : Γ} {k : ℕ} (hk : c ^ (3 ^ k) = 1) {m : ℕ}
    (hm : Nat.Coprime 3 m) (hcm : c ^ m = 1) : c = 1 := by
  have h1 : orderOf c ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one hcm
  have hcop : Nat.Coprime (3 ^ k) m := Nat.Coprime.pow_left k hm
  have : orderOf c ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

end Generic

section Cfg

variable {G : Type} [Group G] [Finite G]

theorem mem_pCoreOf_of_commute {H : Subgroup G} {x y : G} (hx : x ∈ H) (hy : y ∈ H)
    (h : Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hy⟩)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hx⟩)) :
    y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
  have h1 : ((⟨y, hy⟩ : H) * ⟨x, hx⟩ * (⟨y, hy⟩ : H)⁻¹ * (⟨x, hx⟩ : H)⁻¹ : H) ∈
      CFSG.pCore 2 ↥H := by
    rw [← QuotientGroup.eq_one_iff]
    show QuotientGroup.mk' (CFSG.pCore 2 ↥H) _ = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h.eq]
    group
  exact ⟨_, h1, rfl⟩

theorem commute_of_mem_pCoreOf {H : Subgroup G} {x y : G} (hx : x ∈ H) (hy : y ∈ H)
    (h : y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 H) :
    Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hy⟩)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hx⟩) := by
  obtain ⟨z, hz, hzv⟩ := Subgroup.mem_map.mp h
  have hz' : z = (⟨y, hy⟩ : H) * ⟨x, hx⟩ * (⟨y, hy⟩ : H)⁻¹ * (⟨x, hx⟩ : H)⁻¹ :=
    Subtype.ext (by simpa using hzv)
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) z = 1 := (QuotientGroup.eq_one_iff _).mpr hz
  rw [hz', map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have := mul_inv_eq_one.mp h1
  exact (mul_inv_eq_iff_eq_mul.mp this)

theorem mk_pow_eq_one {H : Subgroup G} {x : G} (hx : x ∈ H) {k : ℕ}
    (h : x ^ k ∈ pCoreOf 2 H) : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hx⟩) ^ k = 1 := by
  obtain ⟨z, hz, hzv⟩ := Subgroup.mem_map.mp h
  have hz' : z = (⟨x, hx⟩ : H) ^ k := Subtype.ext (by simpa using hzv)
  rw [← map_pow, ← hz']
  exact (QuotientGroup.eq_one_iff _).mpr hz

theorem mk_pow_card_eq_one {H : Subgroup G} (N₀ : Subgroup H) {n : H} (hn : n ∈ N₀) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H) n) ^ Nat.card N₀ = 1 := by
  rw [← map_pow]
  have h2 : n ^ Nat.card N₀ = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard N₀ hn)
  rw [h2, map_one]

theorem commutator_mem_of_cfg {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    {x : G} (hx : x ∈ d1PlusCore p H K) (hxH : x ∈ H) {Y : Subgroup G}
    (hY : RankThreeUC.AGL81C.IsPComponentIn p Y H) (hYM : ¬ Y ≤ M) {y : G} (hy : y ∈ Y)
    (hyH : y ∈ H) :
    ((⟨y, hyH⟩ : H) * ⟨x, hxH⟩ * (⟨y, hyH⟩ : H)⁻¹ * (⟨x, hxH⟩ : H)⁻¹ : H) ∈
      primeComplementCore (G := H) p := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hyK : π ⟨y, hyH⟩ ∈ K := by
    rw [hd.kbar]
    obtain ⟨K', hKc, -, hYK, -⟩ := hY.2
    have hYK' : (Y.subgroupOf H).map π = K' := hYK
    have hK' : IsComponentOf ((Y.subgroupOf H).map π) ⊤ := by
      rw [hYK']
      exact isComponentOf_top_of_isComponent' hKc
    have hle : (Y.subgroupOf H).map π ≤ d1KBar p M H := by
      refine le_d1KBar hK' fun hle => hYM fun z hz => ?_
      obtain ⟨⟨m, hmH⟩, hm, hmz⟩ := hle ⟨⟨z, hY.1 hz⟩, hz, rfl⟩
      have ho : (⟨m, hmH⟩ : H)⁻¹ * ⟨z, hY.1 hz⟩ ∈ primeComplementCore (G := H) p := by
        rw [← QuotientGroup.eq_one_iff]
        show π ((⟨m, hmH⟩ : H)⁻¹ * ⟨z, hY.1 hz⟩) = 1
        rw [map_mul, map_inv, hmz, inv_mul_cancel]
      have hoM : ((⟨m, hmH⟩ : H)⁻¹ * ⟨z, hY.1 hz⟩ : H).1 ∈ M := hd.primeCore_le ⟨_, ho, rfl⟩
      have e : z = m * ((⟨m, hmH⟩ : H)⁻¹ * ⟨z, hY.1 hz⟩ : H).1 := by simp
      rw [e]
      exact M.mul_mem (Subgroup.mem_subgroupOf.mp hm).2 hoM
    exact hle ⟨⟨y, hyH⟩, hy, rfl⟩
  have hxC : π ⟨x, hxH⟩ ∈ Subgroup.centralizer (K : Set _) := by
    obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp hx
    have : x' = ⟨x, hxH⟩ := Subtype.ext hxx
    rw [← this]
    exact hx'
  have hc : π ⟨y, hyH⟩ * π ⟨x, hxH⟩ = π ⟨x, hxH⟩ * π ⟨y, hyH⟩ :=
    (Subgroup.mem_centralizer_iff.mp hxC _ hyK)
  rw [← QuotientGroup.eq_one_iff]
  show π _ = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
  group

theorem pCoreOf_le_pCoreOf_of_isSubnormal {A B : Subgroup G} (h : IsSubnormal A B) :
    pCoreOf 2 A ≤ pCoreOf 2 B := by
  have hn : ((pCoreOf 2 A).subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 A)).mpr
      (localGroup_le_normalizer_pCoreOf 2 A)
  exact CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal
    (IsSubnormal.step (CFSG.LieType.BorelTits.pCoreOf_le 2 A) hn h)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A)

theorem isQuasisimple_of_isTwoPrimeComponent_self {I₀ : Subgroup G}
    (h : IsTwoPrimeComponent I₀ I₀) : Open.IsQuasisimple (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) := by
  have h1 := h.component.2.2
  have htop : barM I₀ I₀ = ⊤ := by
    unfold barM
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, QuotientGroup.range_mk']
  rw [htop] at h1
  exact Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm h1

theorem commute_of_cube {H X I : Subgroup G} {N₀ : Subgroup H} [N₀.Normal]
    (hIX : IsSubnormal I X) (hNX : N₀.map H.subtype ≤ X)
    (h3 : ∀ x ∈ I, x ^ 3 ∈ pCoreOf 2 H) (hN3 : Nat.Coprime 3 (Nat.card N₀))
    {x : G} (hx : x ∈ I) (hxH : x ∈ H) {n : H} (hn : n ∈ N₀) :
    Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) n) := by
  set π₂ := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ₂
  set Xh := (X.subgroupOf H).map π₂ with hXh
  set Ih := (I.subgroupOf H).map π₂ with hIh
  set Nh := N₀.map π₂ with hNhdef
  have hNh : Nh.Normal := Subgroup.Normal.map inferInstance π₂ (QuotientGroup.mk'_surjective _)
  have hsub : IsSubnormal Ih Xh := (hIX.comap H.subtype).map π₂
  have hI3 : IsPGroup 3 Ih := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    refine ⟨1, Subtype.ext ?_⟩
    have hw' : (w : G) ∈ I := hw
    have := mk_pow_eq_one w.2 (h3 _ hw')
    simp only [SubgroupClass.coe_pow, pow_one, OneMemClass.coe_one]
    exact this
  have hD : Ih ≤ pCoreOf 3 Xh :=
    CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal hsub hI3
  have hxD : π₂ ⟨x, hxH⟩ ∈ pCoreOf 3 Xh := hD ⟨⟨x, hxH⟩, hx, rfl⟩
  have hnX : π₂ n ∈ Xh := ⟨n, hNX ⟨n, hn, rfl⟩, rfl⟩
  have hcD : π₂ ⟨x, hxH⟩ * π₂ n * (π₂ ⟨x, hxH⟩)⁻¹ * (π₂ n)⁻¹ ∈ pCoreOf 3 Xh := by
    have hnorm := localGroup_le_normalizer_pCoreOf 3 Xh hnX
    have h1 : π₂ n * (π₂ ⟨x, hxH⟩)⁻¹ * (π₂ n)⁻¹ ∈ pCoreOf 3 Xh :=
      (Subgroup.mem_normalizer_iff.mp hnorm _).mp (inv_mem hxD)
    have := mul_mem hxD h1
    simpa [mul_assoc] using this
  have hcN : π₂ ⟨x, hxH⟩ * π₂ n * (π₂ ⟨x, hxH⟩)⁻¹ * (π₂ n)⁻¹ ∈ Nh := by
    have h1 : π₂ ⟨x, hxH⟩ * π₂ n * (π₂ ⟨x, hxH⟩)⁻¹ ∈ Nh :=
      hNh.conj_mem _ ⟨n, hn, rfl⟩ _
    exact mul_mem h1 (inv_mem ⟨n, hn, rfl⟩)
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 Xh ⟨_, hcD⟩
  have hk' : (π₂ ⟨x, hxH⟩ * π₂ n * (π₂ ⟨x, hxH⟩)⁻¹ * (π₂ n)⁻¹) ^ (3 ^ k) = 1 := by
    simpa using congrArg Subtype.val hk
  obtain ⟨m, hm, hmc⟩ := Subgroup.mem_map.mp hcN
  have hcm : (π₂ ⟨x, hxH⟩ * π₂ n * (π₂ ⟨x, hxH⟩)⁻¹ * (π₂ n)⁻¹) ^ Nat.card N₀ = 1 := by
    rw [← hmc]
    exact mk_pow_card_eq_one N₀ hm
  have hc1 := eq_one_of_pow_three_pow hk' hN3 hcm
  have := mul_inv_eq_one.mp hc1
  exact mul_inv_eq_iff_eq_mul.mp this

end Cfg

end TenFiveX

open TenFiveX

variable {G : Type} [Group G] [Finite G]

theorem agl81TenFiveXCfg_three (h1031 : AGL81TenThreeOneAt G) (h98 : AGL81NineEightFour G)
    (hS : Setting G) (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (hd : AGL81CfgData 3 P M H Q K)
    (L : Subgroup G) (hL : IsWeakSBlock M (pCoreOf 2 H) L) (I₀ : Subgroup G)
    (hI₀ : I₀ ∈ cZero (H ⊓ L))
    (hIX : CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ d1PlusCore 3 H K)
    (Y : Subgroup G) (hY : RankThreeUC.AGL81C.IsPComponentIn 3 Y H) (hYM : ¬ Y ≤ M) :
    ∀ y ∈ Y, ∀ x ∈ CFSG.ComponentClassification.AS76b.oUpperTwo I₀,
      y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
  intro y hy x hx
  set I := CFSG.ComponentClassification.AS76b.oUpperTwo I₀ with hIdef
  set π₂ := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ₂
  set N₀ := primeComplementCore (G := H) 3 with hN₀
  obtain ⟨hV, -, -⟩ := hd.nineEightFour' hS h98
  have hN3 : Nat.Coprime 3 (Nat.card N₀) := primeComplementCore_coprime 3
  have hN₀X : N₀.map H.subtype ≤ H ⊓ M := le_inf (Subgroup.map_subtype_le _) hd.primeCore_le
  have hsub2 : IsSubnormal (H ⊓ L) (H ⊓ M) := by
    have h := hL.subnormal.inf H
    rwa [inf_comm L H, inf_comm M H] at h
  have hI₀sub : IsSubnormal I₀ (H ⊓ M) := hI₀.subnormal.trans hsub2
  have hI₀H : I₀ ≤ H := hI₀.le.trans inf_le_left
  have hII₀ : I ≤ I₀ := oUpperTwo_le_self I₀
  have hyH : y ∈ H := hY.1 hy
  have hxH : x ∈ H := hI₀H (hII₀ hx)
  set Nh := N₀.map π₂ with hNhdef
  haveI hNh : Nh.Normal := Subgroup.Normal.map inferInstance π₂ (QuotientGroup.mk'_surjective _)
  have hF2 : ∀ g (hg : g ∈ I) (hgH : g ∈ H),
      π₂ ⟨g, hgH⟩ * π₂ ⟨y, hyH⟩ * (π₂ ⟨g, hgH⟩)⁻¹ * (π₂ ⟨y, hyH⟩)⁻¹ ∈ Nh := by
    intro g hg hgH
    have h := N₀.inv_mem (commutator_mem_of_cfg hd (hIX hg) hgH hY hYM hy hyH)
    refine ⟨_, h, ?_⟩
    simp only [map_inv, map_mul]
    group
  apply mem_pCoreOf_of_commute hxH hyH
  rcases hI₀.shape with ha | ⟨hO2, hb⟩
  ·
    have hperf : ⁅I₀, I₀⁆ = I₀ := ha.perfect
    have hI₀I : I₀ ≤ I :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.closure_odd_of_perfect hperf
    have hq := isQuasisimple_of_isTwoPrimeComponent_self ha
    have hHN : H ⊓ M ≤ Subgroup.normalizer ((N₀.map H.subtype : Subgroup G) : Set G) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · rintro ⟨n, hn, rfl⟩
        refine ⟨⟨h, hh.1⟩ * n * (⟨h, hh.1⟩ : H)⁻¹, ?_, rfl⟩
        exact (inferInstance : N₀.Normal).conj_mem n hn _
      · rintro ⟨n, hn, hng⟩
        refine ⟨(⟨h, hh.1⟩ : H)⁻¹ * n * ⟨h, hh.1⟩, ?_, ?_⟩
        · have := (inferInstance : N₀.Normal).conj_mem n hn (⟨h, hh.1⟩ : H)⁻¹
          simpa using this
        · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hng ⊢
          rw [hng]
          group
    rcases CFSG.Quasithin.H13.Ch3Sec3.le_or_commutator_le_pCoreOf hI₀sub hperf hq hN₀X hHN with
      hle | hcomm
    · exfalso
      have h3I := h1031 hS 3 P M H Q K hd L hL I₀ hI₀
      have hdvd : Nat.card I ∣ Nat.card N₀ := by
        rw [← Subgroup.card_map_of_injective H.subtype_injective]
        exact Subgroup.card_dvd_of_le (hII₀.trans hle)
      exact absurd (hN3.coprime_dvd_right hdvd) (by
        rw [Nat.coprime_comm]
        intro hc
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (Nat.coprime_comm.mp hc) h3I)
    · have hstep1 : ∀ g ∈ I₀, ∀ (hgH : g ∈ H), ∀ n ∈ N₀, Commute (π₂ ⟨g, hgH⟩) (π₂ n) := by
        intro g hg hgH n hn
        have hgn : g * (n : G) * g⁻¹ * (n : G)⁻¹ ∈ pCoreOf 2 H := by
          rw [← hV]
          exact hcomm (Subgroup.commutator_mem_commutator hg ⟨n, hn, rfl⟩)
        exact commute_of_mem_pCoreOf n.2 hgH hgn
      have hC : ⁅I₀, I₀⁆ ≤ ((Subgroup.centralizer {π₂ ⟨y, hyH⟩}).comap π₂).map H.subtype := by
        rw [Subgroup.commutator_le]
        intro a ha' b hb'
        have haH := hI₀H ha'
        have hbH := hI₀H hb'
        refine ⟨⟨a, haH⟩ * ⟨b, hbH⟩ * (⟨a, haH⟩ : H)⁻¹ * (⟨b, hbH⟩ : H)⁻¹, ?_, rfl⟩
        have haN : ∀ n' ∈ Nh, Commute (π₂ ⟨a, haH⟩) n' := by
          rintro _ ⟨n, hn, rfl⟩
          exact hstep1 a ha' haH n hn
        have hbN : ∀ n' ∈ Nh, Commute (π₂ ⟨b, hbH⟩) n' := by
          rintro _ ⟨n, hn, rfl⟩
          exact hstep1 b hb' hbH n hn
        have key := commute_commutatorElement haN hbN (hF2 a (hI₀I ha') haH)
          (hF2 b (hI₀I hb') hbH)
        show π₂ _ ∈ Subgroup.centralizer _
        rw [Subgroup.mem_centralizer_singleton_iff, map_mul, map_mul, map_mul, map_inv, map_inv]
        rw [commutatorElement_def] at key
        exact key.eq
      rw [hperf] at hC
      obtain ⟨x', hx', hxx⟩ := hC (hII₀ hx)
      have : x' = ⟨x, hxH⟩ := Subtype.ext hxx
      rw [this] at hx'
      have := Subgroup.mem_centralizer_singleton_iff.mp hx'
      exact this.symm
  ·
    have hcube : ∀ g ∈ I, g ^ 3 ∈ pCoreOf 2 H := by
      intro g hg
      have h1 := IsCZeroMember.cube_mem kFactSUThreeTwoShape_holds hb g hg
      rw [hO2] at h1
      rw [← hV]
      exact pCoreOf_le_pCoreOf_of_isSubnormal hsub2 h1
    have hIsub : IsSubnormal I (H ⊓ M) := by
      refine IsSubnormal.step hII₀ ?_ hI₀sub
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hII₀).mpr
        fun n hn => mem_normalizer_oUpperTwo hn
    set a := π₂ ⟨x, hxH⟩ with ha
    set b := π₂ ⟨y, hyH⟩ with hb'
    have hcN : a * b * a⁻¹ * b⁻¹ ∈ Nh := hF2 x hx hxH
    obtain ⟨m, hm, hmc⟩ := Subgroup.mem_map.mp hcN
    have hac : a * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * a := by
      rw [← hmc]
      exact (commute_of_cube hIsub hN₀X hcube hN3 hx hxH hm).eq
    have hc' : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
    have ha3 : a ^ 3 = 1 := mk_pow_eq_one hxH (hcube x hx)
    have hc3 := pow_three_eq_one_of_conj hac hc' ha3
    have hcm : (a * b * a⁻¹ * b⁻¹) ^ Nat.card N₀ = 1 := by
      rw [← hmc]
      exact mk_pow_card_eq_one N₀ hm
    have hc1 : a * b * a⁻¹ * b⁻¹ = 1 :=
      eq_one_of_pow_three_pow (k := 1) (by simpa using hc3) hN3 hcm
    have h1 := mul_inv_eq_one.mp hc1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm

variable (G) in
@[expose] def AGL81NineTwelveOneCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → p ≠ 3 →
    ∀ Y : Subgroup G, RankThreeUC.AGL81C.IsPComponentIn p Y H → ¬ Y ≤ M →
      RankThreeUC.AGL81C.IsTwoPrimeComponentIn Y H

theorem agl81TenFiveXCfg_of (h1031 : AGL81TenThreeOneAt G) (h912 : AGL81NineTwelveOneCfg G)
    (h98 : AGL81NineEightFour G) : AGL81TenFiveXCfg G := by
  intro hS p P M H Q K hd L hL I₀ hI₀ hIX Y hY hYM y hy x hx
  by_cases hp3 : p = 3
  · subst hp3
    exact agl81TenFiveXCfg_three h1031 h98 hS P M H Q K hd L hL I₀ hI₀ hIX Y hY hYM y hy x hx
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hp : p.Prime := hesc.prime
  have hYc := h912 hS p P M H Q K hd hp3 Y hY hYM
  set π₂ := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ₂
  set N₀ := primeComplementCore (G := H) p with hN₀
  have hYH : Y ≤ H := hY.1
  have hyH : y ∈ H := hYH hy
  have hxH : x ∈ H := (oUpperTwo_le_self I₀).trans (hI₀.le.trans inf_le_left) hx
  set Nh := N₀.map π₂ with hNhdef
  haveI hNh : Nh.Normal := Subgroup.Normal.map inferInstance π₂ (QuotientGroup.mk'_surjective _)
  have hperf : ⁅Y, Y⁆ = Y := Subgroup.isPerfect_iff.1 (hY.isPerfect hp)
  have hsubY : IsSubnormal Y H := (IsSubnormal.iff_subgroupOf hYH).2 hYc.2.1
  have hq : Open.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    ⟨hYc.2.2.1.1.commutator_eq_top, hYc.2.2.1.2.1⟩
  have hNH : N₀.map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hHN : H ≤ Subgroup.normalizer ((N₀.map H.subtype : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨h, hh⟩ * n * (⟨h, hh⟩ : H)⁻¹, ?_, rfl⟩
      exact (inferInstance : N₀.Normal).conj_mem n hn _
    · rintro ⟨n, hn, hng⟩
      refine ⟨(⟨h, hh⟩ : H)⁻¹ * n * ⟨h, hh⟩, ?_, ?_⟩
      · have := (inferInstance : N₀.Normal).conj_mem n hn (⟨h, hh⟩ : H)⁻¹
        simpa using this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hng ⊢
        rw [hng]
        group
  rcases CFSG.Quasithin.H13.Ch3Sec3.le_or_commutator_le_pCoreOf hsubY hperf hq hNH hHN with
    hle | hcomm
  · exfalso
    obtain ⟨K', hKc, -, hYK, -⟩ := hY.2
    have hbot : (Y.subgroupOf H).map (QuotientGroup.mk' N₀) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      intro w hw
      obtain ⟨n, hn, hnw⟩ := hle hw
      have : n = w := Subtype.ext hnw
      rwa [← this]
    have hK'bot : K' = ⊥ := (hYK : (Y.subgroupOf H).map (QuotientGroup.mk' N₀) = K').symm.trans hbot
    obtain ⟨-, hs, -⟩ := hKc.1
    subst hK'bot
    obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    congr 1
    exact Subtype.ext ((Subgroup.mem_bot.mp a'.2).trans (Subgroup.mem_bot.mp b'.2).symm)
  · have hstep1 : ∀ g ∈ Y, ∀ (hgH : g ∈ H), ∀ n ∈ N₀, Commute (π₂ ⟨g, hgH⟩) (π₂ n) := by
      intro g hg hgH n hn
      exact commute_of_mem_pCoreOf n.2 hgH
        (hcomm (Subgroup.commutator_mem_commutator hg ⟨n, hn, rfl⟩))
    have hF2 : ∀ g (hg : g ∈ Y) (hgH : g ∈ H),
        π₂ ⟨g, hgH⟩ * π₂ ⟨x, hxH⟩ * (π₂ ⟨g, hgH⟩)⁻¹ * (π₂ ⟨x, hxH⟩)⁻¹ ∈ Nh := by
      intro g hg hgH
      refine ⟨_, commutator_mem_of_cfg hd (hIX hx) hxH hY hYM hg hgH, ?_⟩
      simp only [map_inv, map_mul]
    have hC : ⁅Y, Y⁆ ≤ ((Subgroup.centralizer {π₂ ⟨x, hxH⟩}).comap π₂).map H.subtype := by
      rw [Subgroup.commutator_le]
      intro a ha' b hb'
      have haH := hYH ha'
      have hbH := hYH hb'
      refine ⟨⟨a, haH⟩ * ⟨b, hbH⟩ * (⟨a, haH⟩ : H)⁻¹ * (⟨b, hbH⟩ : H)⁻¹, ?_, rfl⟩
      have haN : ∀ n' ∈ Nh, Commute (π₂ ⟨a, haH⟩) n' := by
        rintro _ ⟨n, hn, rfl⟩
        exact hstep1 a ha' haH n hn
      have hbN : ∀ n' ∈ Nh, Commute (π₂ ⟨b, hbH⟩) n' := by
        rintro _ ⟨n, hn, rfl⟩
        exact hstep1 b hb' hbH n hn
      have key := commute_commutatorElement haN hbN (hF2 a ha' haH) (hF2 b hb' hbH)
      show π₂ _ ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_singleton_iff, map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [commutatorElement_def] at key
      exact key.eq
    rw [hperf] at hC
    obtain ⟨y', hy', hyy⟩ := hC hy
    have : y' = ⟨y, hyH⟩ := Subtype.ext hyy
    rw [this] at hy'
    apply mem_pCoreOf_of_commute hxH hyH
    exact Subgroup.mem_centralizer_singleton_iff.mp hy'

end CFSG.LocalAnalysis.RankThreeTheoremC
