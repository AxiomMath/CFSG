module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Core
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem oddCore_eq_pPrimeCore' (Q : Type*) [Group Q] :
    CFSG.oddCore Q = CFSG.pPrimeCore 2 Q := by
  apply le_antisymm
  · apply sSup_le
    intro N hN
    exact le_sSup (show N ∈ {K : Subgroup Q | K.Normal ∧ Nat.Coprime 2 (Nat.card K)} from
      ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩)
  · apply sSup_le
    intro N hN
    exact le_sSup (show N ∈ {K : Subgroup Q | K.Normal ∧ Odd (Nat.card K)} from
      ⟨hN.1, Nat.coprime_two_left.mp hN.2⟩)

private theorem normal_le_center_or_eq_top_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) (N : Subgroup Q) [N.Normal] :
    N ≤ center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  set π := QuotientGroup.mk' (center Q) with hπ
  have hNn : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have hNZ : ∀ q : Q, ∃ n ∈ N, n⁻¹ * q ∈ center Q := by
      intro q
      have : π q ∈ N.map π := h ▸ mem_top _
      obtain ⟨n, hn, hnq⟩ := this
      refine ⟨n, hn, ?_⟩
      rw [← QuotientGroup.ker_mk' (center Q), MonoidHom.mem_ker, map_mul, map_inv, ← hπ, hnq,
        inv_mul_cancel]
    have htop : (⊤ : Subgroup Q) = ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ := by
      rw [← _root_.commutator_def]
      exact (@Group.IsPerfect.commutator_eq_top Q _ hperf).symm
    rw [eq_top_iff, htop, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨n₁, hn₁, hz₁⟩ := hNZ x
    obtain ⟨n₂, hn₂, hz₂⟩ := hNZ y
    have hx : x = n₁ * (n₁⁻¹ * x) := by group
    have hy : y = n₂ * (n₂⁻¹ * y) := by group
    set z₁ := n₁⁻¹ * x
    set z₂ := n₂⁻¹ * y
    have c₁ := Subgroup.mem_center_iff.mp hz₁
    have c₂ := Subgroup.mem_center_iff.mp hz₂
    rw [hx, hy, commutatorElement_def]
    have e : n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by
      calc n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹
          = n₁ * (z₁ * (n₂ * z₂) * z₁⁻¹) * n₁⁻¹ * (n₂ * z₂)⁻¹ := by group
        _ = n₁ * (n₂ * z₂) * n₁⁻¹ * (n₂ * z₂)⁻¹ := by
            rw [← c₁ (n₂ * z₂), mul_assoc _ z₁, mul_inv_cancel, mul_one]
        _ = n₁ * n₂ * (z₂ * n₁⁻¹) * z₂⁻¹ * n₂⁻¹ := by group
        _ = n₁ * n₂ * (n₁⁻¹ * z₂) * z₂⁻¹ * n₂⁻¹ := by rw [← c₂ n₁⁻¹]
        _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁)) (inv_mem hn₂)


theorem case3Core_of_gomiSU {V Hh : Subgroup G} {u : G}
    (hu : orderOf u = 4) (hV : V = zpowers u) (hle : Hh ≤ centralizer (V : Set G))
    (hchar : (Hh.subgroupOf (centralizer (V : Set G))).Characteristic)
    (hq : CFSG.IsQuasisimple ↥Hh) (hVH : V ≤ Hh)
    (hSU : IsSU43 (↥Hh ⧸ CFSG.oddCore ↥Hh)) :
    Case3Core G (u ^ 2) Hh := by
  classical
  set Gh : Subgroup G := centralizer (V : Set G) with hGh_def
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu_mem_V : u ∈ V := by rw [hV]; exact Subgroup.mem_zpowers u
  have hu_mem_Hh : u ∈ Hh := hVH hu_mem_V
  have hu2_mem_V : u ^ 2 ∈ V := by rw [hV]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers u) 2
  have hu2_mem_Hh : u ^ 2 ∈ Hh := hVH hu2_mem_V
  have horder2 : orderOf (u ^ 2) = 2 := by
    rw [orderOf_pow, hu]
    norm_num
  have hle2 : Hh ≤ centralizer ({u ^ 2} : Set G) :=
    hle.trans (Subgroup.centralizer_le (by rintro x rfl; exact hu2_mem_V))
  have hV_le_pcore : V ≤ pCoreOf 2 Hh := by
    apply CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 V Hh hVH
    · apply Subgroup.normal_of_le_center
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact ((Subgroup.mem_centralizer_iff.mp (hle y.2)) x.1 hx).symm
    · exact IsPGroup.of_card (n := 2) (by rw [hV, Nat.card_zpowers, hu]; norm_num)
  set Z : Subgroup ↥Hh := CFSG.pCore 2 ↥Hh with hZ_def
  haveI hZnormal : Z.Normal := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2
  have hpc_center : Z ≤ center ↥Hh := by
    rcases normal_le_center_or_eq_top_of_isQuasisimple hq Z with h | h
    · exact h
    · exfalso
      have hp : IsPGroup 2 (⊤ : Subgroup ↥Hh) :=
        h ▸ CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2
      have hp2 : IsPGroup 2 ↥Hh := hp.of_equiv Subgroup.topEquiv
      haveI : Group.IsNilpotent ↥Hh := IsPGroup.isNilpotent (p := 2) hp2
      haveI : Group.IsPerfect ↥Hh := hq.1
      haveI : Nontrivial ↥Hh := by
        rw [← not_subsingleton_iff_nontrivial]
        intro hsub
        haveI : Subsingleton (↥Hh ⧸ center ↥Hh) := inferInstance
        obtain ⟨a, b, hab⟩ := hq.2.2
        exact hab (by rw [Subsingleton.elim a b])
      exact Group.IsPerfect.not_isSolvable ↥Hh inferInstance
  have hoddCore_odd : Odd (Nat.card (CFSG.oddCore ↥Hh)) := by
    rw [oddCore_eq_pPrimeCore' ↥Hh]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥Hh))
  have hZ_disjoint : Z ⊓ CFSG.oddCore ↥Hh = ⊥ := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxZ, hxO⟩ := hx
      rw [Subgroup.mem_bot, ← orderOf_eq_one_iff]
      have hZ2 : IsPGroup 2 ↥Z := CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hZ2) ⟨x, hxZ⟩
      have hk' : orderOf x = 2 ^ k := by
        rw [← Subgroup.orderOf_mk x hxZ]; exact hk
      have hodd_x : Odd (orderOf x) :=
        hoddCore_odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard (CFSG.oddCore ↥Hh) hxO)
      have hk0 : k = 0 := by
        by_contra hk0
        have heven : Even (2 ^ k) := Even.pow_of_ne_zero even_two hk0
        rw [← hk'] at heven
        exact (Nat.not_even_iff_odd.mpr hodd_x) heven
      rw [hk', hk0, pow_zero]
    · exact bot_le
  have hZ_le_four : Nat.card ↥Z ≤ 4 := by
    let π : ↥Hh →* (↥Hh ⧸ CFSG.oddCore ↥Hh) := QuotientGroup.mk' (CFSG.oddCore ↥Hh)
    have hcenter_mem : ∀ z : ↥Z, π z.1 ∈ center (↥Hh ⧸ CFSG.oddCore ↥Hh) := by
      intro z
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore ↥Hh) y
      have hz : z.1 ∈ center ↥Hh := hpc_center z.2
      calc π x * π z.1 = π (x * z.1) := (map_mul π x z.1).symm
        _ = π (z.1 * x) := by rw [Subgroup.mem_center_iff.mp hz x]
        _ = π z.1 * π x := map_mul π z.1 x
    let f : ↥Z → ↥(center (↥Hh ⧸ CFSG.oddCore ↥Hh)) := fun z => ⟨π z.1, hcenter_mem z⟩
    have hf : Function.Injective f := by
      intro z w hzw
      have h1 : π z.1 = π w.1 := congrArg Subtype.val hzw
      apply Subtype.ext
      have hker : z.1 * w.1⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        simp [map_mul, map_inv, h1]
      have hodd : z.1 * w.1⁻¹ ∈ CFSG.oddCore ↥Hh := by
        have := hker
        rwa [QuotientGroup.ker_mk'] at this
      have hZmem : z.1 * w.1⁻¹ ∈ Z := Z.mul_mem z.2 (Z.inv_mem w.2)
      have hbot : z.1 * w.1⁻¹ ∈ (⊥ : Subgroup ↥Hh) := by
        rw [← hZ_disjoint]
        exact Subgroup.mem_inf.mpr ⟨hZmem, hodd⟩
      exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hbot)
    have hle := Nat.card_le_card_of_injective f hf
    rwa [hSU.2.1] at hle
  have hcard_pcore : Nat.card ↥(pCoreOf 2 Hh) = Nat.card ↥Z :=
    Subgroup.card_map_of_injective (K := CFSG.pCore 2 ↥Hh) Hh.subtype_injective
  have hcard_pcore_le : Nat.card ↥(pCoreOf 2 Hh) ≤ 4 := by
    rw [hcard_pcore]; exact hZ_le_four
  have hcard_V : Nat.card ↥V = 4 := by rw [hV, Nat.card_zpowers, hu]
  have hcard_V_le : Nat.card ↥V ≤ Nat.card ↥(pCoreOf 2 Hh) :=
    Subgroup.card_le_of_le hV_le_pcore
  have hcard_pcore_eq : Nat.card ↥(pCoreOf 2 Hh) = 4 := by
    have : 4 ≤ Nat.card ↥(pCoreOf 2 Hh) := hcard_V ▸ hcard_V_le
    omega
  have hpCore_eq_V : pCoreOf 2 Hh = V := by
    have h := Subgroup.eq_of_le_of_card_ge hV_le_pcore (by simp [hcard_pcore_eq, hcard_V])
    exact h.symm
  have hisCyclic : IsCyclic ↥(pCoreOf 2 Hh) := by
    rw [hpCore_eq_V, hV]
    exact Subgroup.isCyclic_zpowers u
  have hforward : ∀ g ∈ Gh, ∀ h ∈ Hh, g * h * g⁻¹ ∈ Hh := by
    intro g hg h hh
    have hfix := hchar.fixed (MulAut.conj (⟨g, hg⟩ : ↥Gh))
    have hmem : (⟨h, hle hh⟩ : ↥Gh) ∈ Hh.subgroupOf Gh := hh
    have hmem' : (MulAut.conj (⟨g, hg⟩ : ↥Gh)) (⟨h, hle hh⟩ : ↥Gh) ∈ Hh.subgroupOf Gh := by
      have h := congrArg (fun S : Subgroup ↥Gh => (⟨h, hle hh⟩ : ↥Gh) ∈ S) hfix
      rw [Subgroup.mem_comap] at h
      exact h.mpr hmem
    have hcoe : (((MulAut.conj (⟨g, hg⟩ : ↥Gh)) (⟨h, hle hh⟩ : ↥Gh) : ↥Gh) : G) =
        g * h * g⁻¹ := by
      rw [MulAut.conj_apply]; rfl
    have hmemG : (((MulAut.conj (⟨g, hg⟩ : ↥Gh)) (⟨h, hle hh⟩ : ↥Gh) : ↥Gh) : G) ∈ Hh :=
      hmem'
    rwa [hcoe] at hmemG
  have hGh_le_N : Gh ≤ normalizer (Hh : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro x ⟨h, hh, rfl⟩
      simpa [MulAut.conj_apply] using hforward g hg h hh
    · intro h hh
      refine ⟨g⁻¹ * h * g, ?_, ?_⟩
      · have := hforward g⁻¹ (Gh.inv_mem hg) h hh
        simpa using this
      · change g * (g⁻¹ * h * g) * g⁻¹ = h
        group
  have htight : ∀ w : G, w ∈ pCoreOf 2 Hh → orderOf w = 4 →
      centralizer ({w} : Set G) ≤ normalizer (Hh : Set G) := by
    intro w hw hw4
    have hwV : w ∈ V := by rwa [hpCore_eq_V] at hw
    have hzw_le : zpowers w ≤ V := Subgroup.zpowers_le.mpr hwV
    have hzw : zpowers w = V := by
      apply Subgroup.eq_of_le_of_card_ge hzw_le
      simp [hcard_V, Nat.card_zpowers, hw4]
    have hcent_eq : centralizer ({w} : Set G) = centralizer (V : Set G) := by
      apply le_antisymm
      · intro x hx
        rw [Subgroup.mem_centralizer_iff] at hx ⊢
        intro y hy
        have hcomm : Commute w x := hx w (Set.mem_singleton w)
        rw [← hzw] at hy
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [← hn]
        exact (hcomm.zpow_left n).eq
      · exact Subgroup.centralizer_le
          (by rw [← hzw]; exact Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers w))
    rw [hcent_eq]
    exact hGh_le_N
  exact ⟨horder2, hle2, hq, hu2_mem_Hh, hisCyclic, hcard_pcore_eq, hSU, htight⟩

end CFSG.OddStandard.HigherRank.YamadaG23
