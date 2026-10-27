module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenFinalBCycle
public import CFSG.GroupTheory.DiagonalCentralizer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BarBlocks
import CFSG.LocalAnalysis.AGL81I.Section3.SL3Arith
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Point
import CFSG.LocalAnalysis.AGLEmbedding.ComponentCentralizer
public import CFSG.CGT.PushingUpLit.CGT6.EmbHolTop
public import CFSG.GroupTheory.ABGLocalTools.RelativeStability
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]
variable {M Q H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private theorem centralizerInJ_le (M H B : Subgroup G) : centralizerInJ M H B ≤ M :=
  inf_le_right.trans (jSub_le M H)

private abbrev centralizerInJHom (M H B : Subgroup G) :
    ↥(centralizerInJ M H B) →* modTwoCore M :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion (centralizerInJ_le M H B))

private theorem barM_independent_left
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hcard : (weakBlockSet M H).ncard = 3) :
    barM M L₁ ⊓ (barM M L₂ ⊔ barM M L₃) = ⊥ := by
  classical
  have hne := TwelveFiveData.pairwise_ne hd hcard
  have hcenter : Subgroup.center ↥(barM M L₁) = ⊥ :=
    center_barM_eq_bot_of_isTwoPrimeComponent hd.mem₁.toIsTwoPrimeComponent
      ⟨n₁, hd.odd₁, hd.type₁⟩
  have hle : barM M L₂ ⊔ barM M L₃ ≤
      Subgroup.centralizer (barM M L₁ : Set (modTwoCore M)) :=
    sup_le (barM_le_centralizer_barM_of_ne hd.mem₂ hd.mem₁ hne.1.symm)
      (barM_le_centralizer_barM_of_ne hd.mem₃ hd.mem₁ hne.2.1.symm)
  have h := inf_le_inf_left (c := barM M L₁) hle
  rw [inf_centralizer_eq_bot_of_center hcenter] at h
  exact le_bot_iff.mp h

private theorem barM_independent_middle
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hcard : (weakBlockSet M H).ncard = 3) :
    barM M L₂ ⊓ (barM M L₁ ⊔ barM M L₃) = ⊥ := by
  classical
  have hne := TwelveFiveData.pairwise_ne hd hcard
  have hcenter : Subgroup.center ↥(barM M L₂) = ⊥ :=
    center_barM_eq_bot_of_isTwoPrimeComponent hd.mem₂.toIsTwoPrimeComponent
      ⟨n₂, hd.odd₂, hd.type₂⟩
  have hle : barM M L₁ ⊔ barM M L₃ ≤
      Subgroup.centralizer (barM M L₂ : Set (modTwoCore M)) :=
    sup_le (barM_le_centralizer_barM_of_ne hd.mem₁ hd.mem₂ hne.1)
      (barM_le_centralizer_barM_of_ne hd.mem₃ hd.mem₂ hne.2.2.symm)
  have h := inf_le_inf_left (c := barM M L₂) hle
  rw [inf_centralizer_eq_bot_of_center hcenter] at h
  exact le_bot_iff.mp h

private theorem barM_independent_right
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hcard : (weakBlockSet M H).ncard = 3) :
    barM M L₃ ⊓ (barM M L₁ ⊔ barM M L₂) = ⊥ := by
  classical
  have hne := TwelveFiveData.pairwise_ne hd hcard
  have hcenter : Subgroup.center ↥(barM M L₃) = ⊥ :=
    center_barM_eq_bot_of_isTwoPrimeComponent hd.mem₃.toIsTwoPrimeComponent
      ⟨n₃, hd.odd₃, hd.type₃⟩
  have hle : barM M L₁ ⊔ barM M L₂ ≤
      Subgroup.centralizer (barM M L₃ : Set (modTwoCore M)) :=
    sup_le (barM_le_centralizer_barM_of_ne hd.mem₁ hd.mem₃ hne.2.1)
      (barM_le_centralizer_barM_of_ne hd.mem₂ hd.mem₃ hne.2.2)
  have h := inf_le_inf_left (c := barM M L₃) hle
  rw [inf_centralizer_eq_bot_of_center hcenter] at h
  exact le_bot_iff.mp h

private theorem nonempty_barM_centralizer_mulEquiv
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hcard : (weakBlockSet M H).ncard = 3)
    {b : G} (hbM : b ∈ M) (hb : b ^ 3 = 1)
    (hb₁ : L₁.map (MulAut.conj b).toMonoidHom = L₂)
    (hb₂ : L₂.map (MulAut.conj b).toMonoidHom = L₃)
    (hb₃ : L₃.map (MulAut.conj b).toMonoidHom = L₁) :
    Nonempty (↥(Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩} : Set (modTwoCore M)) ⊓
        barM M (jSub M H)) ≃* ↥(barM M L₁)) := by
  classical
  let bbar : modTwoCore M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩
  have hne := TwelveFiveData.pairwise_ne hd hcard
  have hbM3 : (⟨b, hbM⟩ : ↥M) ^ 3 = 1 := by
    ext
    simpa using hb
  have hbbar : bbar ^ 3 = 1 := by
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩) ^ 3 = 1
    rw [← map_pow, hbM3, map_one]
  have hb₁' : (barM M L₁).map (MulAut.conj bbar).toMonoidHom = barM M L₂ := by
    have h := barM_map_conj hbM L₁
    rw [hb₁] at h
    exact h.symm
  have hb₂' : (barM M L₂).map (MulAut.conj bbar).toMonoidHom = barM M L₃ := by
    have h := barM_map_conj hbM L₂
    rw [hb₂] at h
    exact h.symm
  have hb₃' : (barM M L₃).map (MulAut.conj bbar).toMonoidHom = barM M L₁ := by
    have h := barM_map_conj hbM L₃
    rw [hb₃] at h
    exact h.symm
  rw [TwelveFiveData.barM_jSub_eq hd]
  exact CFSG.GroupTheory.nonempty_centralizer_inf_sup_mulEquiv hbbar
    (barM_le_centralizer_barM_of_ne hd.mem₁ hd.mem₂ hne.1)
    (barM_le_centralizer_barM_of_ne hd.mem₁ hd.mem₃ hne.2.1)
    (barM_le_centralizer_barM_of_ne hd.mem₂ hd.mem₃ hne.2.2)
    (barM_independent_left hd hcard) (barM_independent_middle hd hcard)
    (barM_independent_right hd hcard) hb₁' hb₂' hb₃'

private theorem commutator_mem_jSub_inf_pCoreOf
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    {b : G} (hbM : b ∈ M) {m : ↥M} (hmJ : (m : G) ∈ jSub M H)
    (hmcomm : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ *
          QuotientGroup.mk' (CFSG.pCore 2 ↥M) m) :
    b * (m : G) * b⁻¹ * (m : G)⁻¹ ∈ jSub M H ⊓ CFSG.Open.pCoreOf 2 M := by
  classical
  have hqmk : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      (⟨b, hbM⟩ * m * ⟨b, hbM⟩⁻¹ * m⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hmcomm]
    group
  have hcore : ⟨b, hbM⟩ * m * ⟨b, hbM⟩⁻¹ * m⁻¹ ∈ CFSG.pCore 2 ↥M :=
    (QuotientGroup.eq_one_iff _).mp hqmk
  have hcommCore : b * (m : G) * b⁻¹ * (m : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
    have h := (CFSG.mem_openPCoreOf_iff (⟨b, hbM⟩ * m * ⟨b, hbM⟩⁻¹ * m⁻¹)).mpr hcore
    simpa using h
  have hbNJ : b ∈ Subgroup.normalizer (jSub M H : Set G) := TwelveFiveData.le_normalizer_jSub hd hbM
  have hcommJ : b * (m : G) * b⁻¹ * (m : G)⁻¹ ∈ jSub M H := by
    have hbmJ : b * (m : G) * b⁻¹ ∈ jSub M H := by
      have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hbNJ
      rw [← hmap]
      simpa [MulAut.conj_apply] using
        Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hmJ
    exact (jSub M H).mul_mem hbmJ ((jSub M H).inv_mem hmJ)
  exact ⟨hcommJ, hcommCore⟩

private theorem exists_coprime_mul_mem_centralizer
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    {b : G} (hbM : b ∈ M) (hb : b ^ 3 = 1) {m : ↥M} (hmJ : (m : G) ∈ jSub M H)
    (hmcomm : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ *
          QuotientGroup.mk' (CFSG.pCore 2 ↥M) m) :
    ∃ q ∈ jSub M H ⊓ CFSG.Open.pCoreOf 2 M,
      q * (m : G) ∈ Subgroup.centralizer ({b} : Set G) := by
  classical
  let Q : Subgroup G := jSub M H ⊓ CFSG.Open.pCoreOf 2 M
  have hq : b * (m : G) * b⁻¹ * (m : G)⁻¹ ∈ Q :=
    commutator_mem_jSub_inf_pCoreOf hd hbM hmJ hmcomm
  have hQ2 : IsPGroup 2 Q :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M).to_le inf_le_right
  have hcop : Nat.Coprime 3 (Nat.card ↥Q) := by
    rw [Nat.prime_three.coprime_iff_not_dvd]
    intro h3dvd
    obtain ⟨k, hk⟩ := isPGroup_iff_card_dvd_pow.mp hQ2
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (h3dvd.trans hk)
    norm_num at h32
  have hbNJ : b ∈ Subgroup.normalizer (jSub M H : Set G) := TwelveFiveData.le_normalizer_jSub hd hbM
  have hbNO : b ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hbM
  have hbNQ : b ∈ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf (Subgroup.zpowers b)
      (jSub M H) (CFSG.Open.pCoreOf 2 M) (Subgroup.zpowers_le.mpr hbNJ)
      (Subgroup.zpowers_le.mpr hbNO) (Subgroup.mem_zpowers b)
  exact CFSG.LocalAnalysis.RankThreeTheoremC.exists_mul_mem_centralizer_of_coprime hb hbNQ hcop hq

private theorem exists_mem_centralizerInJ_of_mem_barM_centralizer
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    {B : Subgroup G} {b : G} (hB : B = Subgroup.zpowers b) (hbM : b ∈ M) (hb : b ^ 3 = 1)
    {x : modTwoCore M}
    (hx : x ∈ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩} : Set (modTwoCore M)) ⊓
        barM M (jSub M H)) :
    ∃ c : ↥(centralizerInJ M H B),
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion (centralizerInJ_le M H B) c) = x := by
  classical
  obtain ⟨m, hmJ, hxm⟩ := Subgroup.mem_map.mp hx.2
  have hmJ' : (m : G) ∈ jSub M H := Subgroup.mem_subgroupOf.mp hmJ
  have hmcomm : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m *
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) m := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hx.1
    rw [← hxm] at h
    exact h
  obtain ⟨q, hqQ, hqC⟩ := exists_coprime_mul_mem_centralizer hd hbM hb hmJ' hmcomm
  have hqJ : q ∈ jSub M H := hqQ.1
  have hqM : q ∈ M := jSub_le M H hqJ
  have hcz : Subgroup.centralizer (Subgroup.zpowers b : Set G) =
      Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcB : q * (m : G) ∈ Subgroup.centralizer (B : Set G) := by
    rw [hB, hcz]
    exact hqC
  have hcJ : q * (m : G) ∈ jSub M H := (jSub M H).mul_mem hqJ hmJ'
  have hqcore : (⟨q, hqM⟩ : ↥M) ∈ CFSG.pCore 2 ↥M :=
    (CFSG.mem_openPCoreOf_iff (⟨q, hqM⟩ : ↥M)).mp hqQ.2
  have hq1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨q, hqM⟩ : ↥M) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hqcore
  refine ⟨⟨q * (m : G), hcB, hcJ⟩, ?_⟩
  have hsplit : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      (Subgroup.inclusion (centralizerInJ_le M H B) ⟨q * (m : G), hcB, hcJ⟩) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ((⟨q, hqM⟩ : ↥M) * m) := by
    rw [show Subgroup.inclusion (centralizerInJ_le M H B) ⟨q * (m : G), hcB, hcJ⟩ =
      ((⟨q, hqM⟩ : ↥M) * m) from Subtype.ext rfl]
  rw [hsplit, map_mul, hq1, hxm]
  exact one_mul x

private theorem range_centralizerInJ_mk
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    {B : Subgroup G} {b : G} (hB : B = Subgroup.zpowers b) (hbM : b ∈ M) (hb : b ^ 3 = 1) :
    (centralizerInJHom M H B).range = Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩} : Set (modTwoCore M)) ⊓
        barM M (jSub M H) := by
  classical
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    constructor
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hc : (c : G) * b = b * (c : G) := by
        have hbB : b ∈ B := by rw [hB]; exact Subgroup.mem_zpowers b
        exact (Subgroup.mem_centralizer_iff.mp c.2.1 b hbB).symm
      change QuotientGroup.mk' (CFSG.pCore 2 ↥M)
          (Subgroup.inclusion (centralizerInJ_le M H B) c) *
          QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩ *
          QuotientGroup.mk' (CFSG.pCore 2 ↥M)
            (Subgroup.inclusion (centralizerInJ_le M H B) c)
      rw [← map_mul, ← map_mul,
        show Subgroup.inclusion (centralizerInJ_le M H B) c * ⟨b, hbM⟩ =
          ⟨b, hbM⟩ * Subgroup.inclusion (centralizerInJ_le M H B) c from Subtype.ext hc]
    · exact Subgroup.mem_map.mpr
        ⟨Subgroup.inclusion (centralizerInJ_le M H B) c, c.2.2, rfl⟩
  · intro hx
    exact exists_mem_centralizerInJ_of_mem_barM_centralizer hd hB hbM hb hx

private theorem ker_centralizerInJ_eq_pCore
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    {B : Subgroup G} {b : G} (hB : B = Subgroup.zpowers b) (hbM : b ∈ M) (hb : b ^ 3 = 1)
    (hrange : (centralizerInJHom M H B).range = Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩} : Set (modTwoCore M)) ⊓
        barM M (jSub M H))
    (eBar : ↥(Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hbM⟩} : Set (modTwoCore M)) ⊓
        barM M (jSub M H)) ≃* ↥(barM M L₁))
    (hpL₁ : CFSG.pCore 2 ↥(barM M L₁) = ⊥) :
    (centralizerInJHom M H B).ker = CFSG.pCore 2 ↥(centralizerInJ M H B) := by
  classical
  have hpR : CFSG.pCore 2 ↥(centralizerInJHom M H B).range = ⊥ :=
    CFSG.CGT.PushingUpLit.CGT6.pCore_eq_bot_of_equiv
      ((MulEquiv.subgroupCongr hrange).trans eBar) hpL₁
  have hker_le : (centralizerInJHom M H B).ker ≤
      CFSG.pCore 2 ↥(centralizerInJ M H B) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
        (Subgroup.inclusion (centralizerInJ_le M H B) x) = 1 := hx
    have hxcomap : x ∈ (CFSG.pCore 2 ↥M).comap
        (Subgroup.inclusion (centralizerInJ_le M H B)) :=
      (QuotientGroup.eq_one_iff
        (Subgroup.inclusion (centralizerInJ_le M H B) x)).mp hx'
    have hNp : IsPGroup 2 ↥((CFSG.pCore 2 ↥M).comap
        (Subgroup.inclusion (centralizerInJ_le M H B))) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).comap_of_injective
        (Subgroup.inclusion (centralizerInJ_le M H B))
        (Subgroup.inclusion_injective (centralizerInJ_le M H B))
    exact CFSG.LieType.BorelTits.le_pCore 2 inferInstance hNp hxcomap
  have hpCore_le_ker : CFSG.pCore 2 ↥(centralizerInJ M H B) ≤
      (centralizerInJHom M H B).ker := by
    intro x hx
    have hmap := CFSG.ABGLocalTools.map_pCore_le_of_surjective (p := 2)
      (centralizerInJHom M H B).rangeRestrict
      (MonoidHom.rangeRestrict_surjective (centralizerInJHom M H B))
    rw [hpR] at hmap
    have hbot : (centralizerInJHom M H B).rangeRestrict x ∈
        (⊥ : Subgroup ↥(centralizerInJHom M H B).range) := hmap ⟨x, hx, rfl⟩
    have hone : (centralizerInJHom M H B).rangeRestrict x = 1 := by simpa using hbot
    exact congrArg Subtype.val hone
  exact le_antisymm hker_le hpCore_le_ker

theorem isL3TwoPow_one_centralizerInJ_of_threeCycle
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    (hcard : (weakBlockSet M H).ncard = 3) {B : Subgroup G} {b : G}
    (hB : B = Subgroup.zpowers b) (hbM : b ∈ M) (hb : b ^ 3 = 1)
    (hb₁ : L₁.map (MulAut.conj b).toMonoidHom = L₂)
    (hb₂ : L₂.map (MulAut.conj b).toMonoidHom = L₃)
    (hb₃ : L₃.map (MulAut.conj b).toMonoidHom = L₁) :
    IsL3TwoPow 1 (↥(centralizerInJ M H B) ⧸ pCore 2 ↥(centralizerInJ M H B)) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcenter₁ : Subgroup.center ↥(barM M L₁) = ⊥ :=
    center_barM_eq_bot_of_isTwoPrimeComponent hd.mem₁.toIsTwoPrimeComponent
      ⟨n₁, hd.odd₁, hd.type₁⟩
  have hpL₁ : CFSG.pCore 2 ↥(barM M L₁) = ⊥ := by
    have hQ : CFSG.Open.IsQuasisimple ↥(barM M L₁) :=
      hd.mem₁.toIsTwoPrimeComponent.component.2.2
    have hle := CFSG.AGLEmbedding.le_center_of_normal_of_isPGroup_two hQ
      (CFSG.pCore_normal (p := 2) (G := ↥(barM M L₁)))
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(barM M L₁)))
    rwa [hcenter₁, le_bot_iff] at hle
  have hrange := range_centralizerInJ_mk hd hB hbM hb
  obtain ⟨eBar⟩ := nonempty_barM_centralizer_mulEquiv hd hcard hbM hb hb₁ hb₂ hb₃
  have hker := ker_centralizerInJ_eq_pCore hd hB hbM hb hrange eBar hpL₁
  have hcore₁ : L₁ ⊓ CFSG.Open.pCoreOf 2 M = CFSG.Open.pCoreOf 2 L₁ :=
    hd.mem₁.toIsTwoPrimeComponent.inf_twoCore
  obtain ⟨e₁⟩ := CFSG.RankThree.PartTwo.Sec19.Item194Proof.nonempty_barM_mulEquiv
    hd.mem₁.le hcore₁
  let eTop : ↥(centralizerInJ M H B) ⧸ CFSG.pCore 2 ↥(centralizerInJ M H B) ≃*
      ↥(centralizerInJHom M H B).range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange (centralizerInJHom M H B))
  let e : ↥(centralizerInJ M H B) ⧸ CFSG.pCore 2 ↥(centralizerInJ M H B) ≃*
      ↥L₁ ⧸ pCore 2 ↥L₁ := eTop.trans ((MulEquiv.subgroupCongr hrange).trans (eBar.trans e₁.symm))
  have htype : IsL3TwoPow 1 (↥L₁ ⧸ pCore 2 ↥L₁) := hn.1 ▸ hd.type₁
  exact CFSG.LocalAnalysis.AGL81I.Section3.isPSLType_of_mulEquiv e.symm htype

theorem twelveTenFinalB'_of_twelveSix (h : TwelveCtx G M p Q H)
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) (h6 : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃)
    (h3 : CFSG.Open.pRank 3 M ≤ 3) (hcard : (weakBlockSet M H).ncard = 3) :
    TwelveTenFinalB' M H Q p := by
  intro E D hEQ hE hEcard hΓ hD hDQ x hx hxM
  obtain ⟨b, hbB, hb3, hbM, hb₁, hb₂, hb₃⟩ :=
    exists_threeCycle_of_twelveSix h hd h6 h3 hcard hEQ hE hEcard hΓ hD hDQ hx hxM
  exact isL3TwoPow_one_centralizerInJ_of_threeCycle hd
    ⟨TwelveSix.n₁_eq_one hd h6, TwelveSix.n₂_eq_one hd h6, TwelveSix.n₃_eq_one hd h6⟩ hcard
    hbB hbM hb3 hb₁ hb₂ hb₃

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
