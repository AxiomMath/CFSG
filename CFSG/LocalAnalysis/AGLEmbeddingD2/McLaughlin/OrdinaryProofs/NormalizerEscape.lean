module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Pair
import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.QuasithinUnique CFSG.Open

variable {G : Type*} [Group G]

theorem normEsc_exists_mem_normalizer_of_two_group [Finite G] {W T : Subgroup G}
    (hW : IsPGroup 2 W) (hTW : T ≤ W) (hne : T ≠ W) :
    ∃ w ∈ W, w ∈ Subgroup.normalizer (T : Set G) ∧ w ∉ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent W := hW.isNilpotent
  have hNC : NormalizerCondition W := Group.normalizerCondition_of_isNilpotent
  set T' : Subgroup W := T.subgroupOf W with hT'def
  have hT'top : T' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hne
    have hWT : W ≤ T := Subgroup.subgroupOf_eq_top.mp h
    exact le_antisymm hTW hWT
  obtain ⟨x, hxN, hxT⟩ := IsConcreteLE.exists_of_lt (hNC T' hT'top)
  refine ⟨(x : G), x.2, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hmem := (Subgroup.mem_normalizer_iff.mp hxN ⟨h, hTW hh⟩).mp
        (Subgroup.mem_subgroupOf.mpr hh)
      exact Subgroup.mem_subgroupOf.mp hmem
    · intro hh
      have h1 : (x : G) * h * (x : G)⁻¹ ∈ W := hTW hh
      have hhW : h ∈ W := by
        have : h = (x : G)⁻¹ * ((x : G) * h * (x : G)⁻¹) * (x : G) := by group
        rw [this]
        exact W.mul_mem (W.mul_mem (W.inv_mem x.2) h1) x.2
      exact Subgroup.mem_subgroupOf.mp
        ((Subgroup.mem_normalizer_iff.mp hxN ⟨h, hhW⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hh))
  · intro h
    exact hxT (Subgroup.mem_subgroupOf.mpr h)

theorem normEsc_exists_two_group_strict {H T : Subgroup G} [Finite G] (hTH : T ≤ H)
    (hT2 : IsPGroup 2 T) (hn : ¬ IsSylowTwoOf T H) :
    ∃ W : Subgroup G, T ≤ W ∧ W ≤ H ∧ IsPGroup 2 W ∧ T ≠ W := by
  have hT' : IsPGroup 2 (T.subgroupOf H) := by
    intro g
    obtain ⟨k, hk⟩ := hT2 ⟨(g : G), Subgroup.mem_subgroupOf.mp g.2⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have h2 := congrArg (fun t : T => (t : G)) hk
    simpa using h2
  obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
  refine ⟨Q.toSubgroup.map H.subtype, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact Subgroup.mem_map.mpr ⟨⟨t, hTH ht⟩, hQ (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.2
  · let e := Subgroup.equivMapOfInjective Q.toSubgroup H.subtype Subtype.val_injective
    exact Q.isPGroup'.of_injective e.symm.toMonoidHom e.symm.injective
  · intro hTW
    have hidx : T.subgroupOf H = Q.toSubgroup := by
      ext x
      rw [Subgroup.mem_subgroupOf, hTW]
      constructor
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        have : y = x := Subtype.ext hyx
        exact this ▸ hy
      · intro hx
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    apply hn
    refine ⟨hTH, hT2, ?_⟩
    rw [hidx]
    exact Q.not_dvd_index

theorem normEsc_le_of_not_two_dvd_relIndex [Finite G] {T K L : Subgroup G}
    (hTK : T ≤ K) (hKL : K ≤ L) (hK : IsPGroup 2 K) (hodd : ¬ 2 ∣ T.relIndex L) : K ≤ T := by
  obtain ⟨n, hn⟩ := hK.index (T.subgroupOf K)
  have hmul : T.relIndex K * K.relIndex L = T.relIndex L :=
    Subgroup.relIndex_mul_relIndex T K L hTK hKL
  cases n with
  | zero =>
    have h1 : T.relIndex K = 1 := by
      show (T.subgroupOf K).index = 1
      rw [hn]
      norm_num
    exact Subgroup.relIndex_eq_one.mp h1
  | succ k =>
    exfalso
    apply hodd
    rw [← hmul]
    have h2 : 2 ∣ T.relIndex K := by
      show 2 ∣ (T.subgroupOf K).index
      rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero k)
    exact dvd_mul_of_dvd_left h2 _

theorem exists_mem_normalizer_not_mem_of_not_isSylowTwoOf [Finite G] {H M T : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M)) (hn : ¬ IsSylowTwoOf T H) :
    ∃ w ∈ H, w ∈ Subgroup.normalizer (T : Set G) ∧ w ∉ M := by
  obtain ⟨hTLM, hT2, hodd⟩ := hT
  have hTH : T ≤ H := hTLM.trans inf_le_left
  obtain ⟨W, hTW, hWH, hW2, hne⟩ := normEsc_exists_two_group_strict hTH hT2 hn
  obtain ⟨w, hwW, hwN, hwT⟩ := normEsc_exists_mem_normalizer_of_two_group hW2 hTW hne
  refine ⟨w, hWH hwW, hwN, ?_⟩
  intro hwM
  apply hwT
  have hKW : T ⊔ Subgroup.zpowers w ≤ W := sup_le hTW (Subgroup.zpowers_le.mpr hwW)
  have hKL : T ⊔ Subgroup.zpowers w ≤ H ⊓ M :=
    sup_le hTLM (Subgroup.zpowers_le.mpr ⟨hWH hwW, hwM⟩)
  have hK2 : IsPGroup 2 (T ⊔ Subgroup.zpowers w : Subgroup G) :=
    hW2.of_injective (Subgroup.inclusion hKW) (Subgroup.inclusion_injective hKW)
  have hKT : T ⊔ Subgroup.zpowers w ≤ T :=
    normEsc_le_of_not_two_dvd_relIndex le_sup_left hKL hK2 hodd
  exact hKT (IsConcreteLE.le_iff.mp (le_sup_right : Subgroup.zpowers w ≤ T ⊔ Subgroup.zpowers w)
    (Subgroup.mem_zpowers w))

open CFSG.AGLEmbeddingD2 in
theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2Escape.pRank_normalizer_inf_le_two3
    {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}
    (hesc : D2Escape 3 P M A H R) (hD1 : CFSG.AGLEmbedding.D1At G 3)
    {C : Subgroup G} (hC : C ≠ ⊥) (hC2 : IsPGroup 2 C)
    (hNC : ¬ Subgroup.normalizer (C : Set G) ≤ M) :
    Open.pRank 3 (Subgroup.normalizer (C : Set G) ⊓ M) ≤ 2 := by
  by_contra hlt
  have h3 : 3 ≤ Open.pRank 3 (Subgroup.normalizer (C : Set G) ⊓ M) := by omega
  apply hNC
  exact hD1 P M hesc.maxTwoLocal_M
    ((CFSG.PreuniquenessRankFour.Helpers.weakCore_le_fullCore 3 (P : Subgroup G)).trans
      hesc.core_le)
    (Subgroup.normalizer (C : Set G)) ⟨C, hC, hC2, rfl⟩ h3

open CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers in
theorem _root_.CFSG.AGLEmbeddingD2.AGLPair.exists_twoGroup_of_evenIndex {G : Type} [Group G]
    [Finite G] {M H R : Subgroup G} (hpr : AGLPair 3 M H R) (hev : 2 ∣ (H ⊓ M).relIndex H) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ pCoreOf 2 M ≤ T ∧
      ¬ Subgroup.normalizer (T : Set G) ≤ M ∧ IsSylowTwoOf T (H ⊓ M) := by
  have hPM : pCoreOf 2 M ≤ M := pCoreOf_le 2 M
  have hP2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hPH : pCoreOf 2 M ≤ H := hpr.twoCore_M_le.trans (pCoreOf_le 2 H)
  obtain ⟨T, hT, hPT⟩ := EscapingLocal.exists_isSylowTwoOf_ge (le_inf hPH hPM) hP2
  have hnot : ¬ IsSylowTwoOf T H := by
    rintro ⟨-, -, hd⟩
    apply hd
    have hmul : T.relIndex (H ⊓ M) * (H ⊓ M).relIndex H = T.relIndex H :=
      Subgroup.relIndex_mul_relIndex (H := T) (K := H ⊓ M) (L := H) hT.1 inf_le_left
    have key : 2 ∣ T.relIndex H := by
      rw [← hmul]
      exact Dvd.dvd.mul_left hev _
    exact key
  obtain ⟨w, -, hwN, hwM⟩ := exists_mem_normalizer_not_mem_of_not_isSylowTwoOf hT hnot
  exact ⟨T, hT.2.1, hPT, fun hle => hwM (hle hwN), hT⟩

theorem D2Escape.pRank_normalizer_inf_le_two {G : Type} [Group G] [Finite G]
    {P : Sylow 3 G} {M A H R : Subgroup G} (hesc : D2Escape 3 P M A H R) (hD1 : D1For G)
    (hβ : 3 ∈ GLBBetaFour G) {C : Subgroup G} (hC : C ≠ ⊥) (hC2 : IsPGroup 2 C)
    (hNC : ¬ Subgroup.normalizer (C : Set G) ≤ M) :
    pRank 3 (Subgroup.normalizer (C : Set G) ⊓ M) ≤ 2 :=
  CFSG.LocalAnalysis.RankThreeTheoremC.D2Escape.pRank_normalizer_inf_le_two3 hesc (hD1 3 hβ) hC hC2
    hNC

end CFSG.AGLEmbeddingD2.McLaughlin
