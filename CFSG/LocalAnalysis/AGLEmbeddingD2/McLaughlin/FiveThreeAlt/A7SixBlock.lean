module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenOutcomeFive

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN
open CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

section Setting

variable {X : Type} [Group X] {T : Subgroup X}

@[expose] def preL (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : Subgroup X :=
  L.comap (QuotientGroup.mk' (gnC T))

@[expose] def blkE (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : Subgroup X :=
  gnD T ⊓ preL T L

@[expose] def blkY (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : Subgroup X :=
  twoResidual (blkE T L)

theorem blkE_le_gnD {L : Subgroup (X ⧸ gnC T)} : blkE T L ≤ gnD T := inf_le_left

theorem blkE_le_preL {L : Subgroup (X ⧸ gnC T)} : blkE T L ≤ preL T L := inf_le_right

theorem blkY_le_blkE {L : Subgroup (X ⧸ gnC T)} : blkY T L ≤ blkE T L := twoResidual_le _

theorem mk_mem_of_mem_blkY {L : Subgroup (X ⧸ gnC T)} {y : X} (hy : y ∈ blkY T L) :
    QuotientGroup.mk' (gnC T) y ∈ L := by
  have h : y ∈ preL T L := blkE_le_preL (blkY_le_blkE hy)
  exact h

end Setting

section Alt7

theorem not_isPGroup_two_alt7 : ¬ IsPGroup 2 (alternatingGroup (Fin 7)) := by
  intro h
  rw [IsPGroup.iff_card] at h
  obtain ⟨n, hn⟩ := h
  have hc : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [hc] at hn
  have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 2520)
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

theorem isSimpleGroupAlt7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))

end Alt7

section Image

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

omit [Finite X] in
theorem gnImg_blkE (eL : ↥L ≃* alternatingGroup (Fin 7)) (hD : ¬ gnD T ⊓ preL T L ≤ gnC T) :
    gnImg T (blkE T L) = L := by
  have := isSimpleGroupAlt7
  have : IsSimpleGroup ↥L := eL.isSimpleGroup
  apply le_antisymm
  · rintro _ ⟨e, he, rfl⟩
    have h1 : e ∈ preL T L := blkE_le_preL he
    exact h1
  · have hMn : ((gnD T).map (QuotientGroup.mk' (gnC T))).Normal :=
      Subgroup.Normal.map (normal_gnD T) _ (QuotientGroup.mk'_surjective _)
    have hSn : (((gnD T).map (QuotientGroup.mk' (gnC T))).subgroupOf L).Normal :=
      Subgroup.Normal.subgroupOf hMn L
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (((gnD T).map (QuotientGroup.mk' (gnC T))).subgroupOf L) with h | h
    · exfalso
      apply hD
      intro e he
      by_contra hec
      have hmem : (⟨(e : X ⧸ gnC T), he.2⟩ : ↥L) ∈
          ((gnD T).map (QuotientGroup.mk' (gnC T))).subgroupOf L :=
        Subgroup.mem_subgroupOf.2 ⟨e, he.1, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      apply hec
      have : (e : X ⧸ gnC T) = 1 := congrArg Subtype.val hmem
      exact (QuotientGroup.eq_one_iff e).1 this
    · intro l hl
      have hmem : (⟨l, hl⟩ : ↥L) ∈ ((gnD T).map (QuotientGroup.mk' (gnC T))).subgroupOf L := by
        rw [h]; trivial
      obtain ⟨d, hd, hdl⟩ := Subgroup.mem_subgroupOf.1 hmem
      refine ⟨d, ⟨hd, ?_⟩, hdl⟩
      show (d : X ⧸ gnC T) ∈ L
      have : (QuotientGroup.mk' (gnC T)) d = l := hdl
      rw [← this] at hl
      exact hl

theorem gnImg_blkY (eL : ↥L ≃* alternatingGroup (Fin 7)) (hD : ¬ gnD T ⊓ preL T L ≤ gnC T) :
    gnImg T (blkY T L) = L := by
  have := isSimpleGroupAlt7
  have : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hE := gnImg_blkE eL hD
  have hYiL : gnImg T (blkY T L) ≤ L := (Subgroup.map_mono blkY_le_blkE).trans hE.le
  refine le_antisymm hYiL ?_
  have hSn : ((gnImg T (blkY T L)).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : (g : X ⧸ gnC T) ∈ gnImg T (blkE T L) := by rw [hE]; exact g.2
    obtain ⟨e, he, hge⟩ := hg
    obtain ⟨y, hy, hyn⟩ := Subgroup.mem_subgroupOf.1 hn
    refine Subgroup.mem_subgroupOf.2 ⟨e * y * e⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_twoResidual (blkE T L) he) y).1 hy
    · rw [map_mul, map_mul, map_inv]
      have h1 : (QuotientGroup.mk' (gnC T)) e = (g : X ⧸ gnC T) := hge
      have h2 : (QuotientGroup.mk' (gnC T)) y = (n : X ⧸ gnC T) := hyn
      rw [h1, h2]
      rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((gnImg T (blkY T L)).subgroupOf L) with h | h
  · exfalso
    apply not_isPGroup_two_alt7
    have hL2 : IsPGroup 2 ↥L := by
      intro l
      obtain ⟨e, he, hel⟩ : (l : X ⧸ gnC T) ∈ gnImg T (blkE T L) := by rw [hE]; exact l.2
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (blkE T L) e he
      refine ⟨k, ?_⟩
      have hmem : (l ^ 2 ^ k : ↥L) ∈ (gnImg T (blkY T L)).subgroupOf L :=
        Subgroup.mem_subgroupOf.2 ⟨e ^ 2 ^ k, hk, by rw [map_pow, hel]; rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    exact hL2.of_equiv eL
  · intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ (gnImg T (blkY T L)).subgroupOf L := by rw [h]; trivial
    exact Subgroup.mem_subgroupOf.1 this

end Image

section Subnormal

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

theorem isSubnormal_comap' {X Y : Type*} [Group X] [Group Y] {A B : Subgroup Y}
    (h : IsSubnormal A B) (f : X →* Y) : IsSubnormal (A.comap f) (B.comap f) :=
  h.comap f

theorem isSubnormal_subgroupOf'' {G : Type*} [Group G] {A B : Subgroup G} (h : IsSubnormal A B) :
    (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

omit [Finite X] in
theorem preL_normalizer_blkE (g : X) (hg : g ∈ preL T L) : g ∈ Subgroup.normalizer (blkE T L : Set X) :=
  have := normal_gnD T
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer_of_normal (Subgroup.mem_top g), Subgroup.le_normalizer hg⟩

omit [Finite X] in
theorem isSubnormal_blkY (hL : IsComponentOf L ⊤) : IsSubnormal (blkY T L) ⊤ := by
  have h1 : IsSubnormal (preL T L) ⊤ := by
    have := isSubnormal_comap' hL.2.1 (QuotientGroup.mk' (gnC T))
    rwa [Subgroup.comap_top] at this
  refine IsSubnormal.step blkY_le_blkE ?_ (IsSubnormal.step blkE_le_preL ?_ h1)
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer blkY_le_blkE]
    exact le_normalizer_twoResidual _
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer blkE_le_preL]
    exact fun g hg => preL_normalizer_blkE g hg

omit [Finite X] in
theorem isSubnormal_blkY' (hL : IsComponentOf L ⊤) :
    ((blkY T L).subgroupOf (⊤ : Subgroup X)).IsSubnormal :=
  isSubnormal_subgroupOf'' (isSubnormal_blkY hL)

end Subnormal

section PCore

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

theorem blkY_inf_gnC_le (hX : GNSetting X T) : blkY T L ⊓ gnC T ≤ pCoreOf 2 (blkY T L) := by
  have hQ2 : IsPGroup 2 (pCoreOf 2 (⊤ : Subgroup X)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
  have hle : blkY T L ⊓ gnC T ≤ pCoreOf 2 (⊤ : Subgroup X) :=
    (le_inf (inf_le_left.trans (blkY_le_blkE.trans blkE_le_gnD)) inf_le_right).trans
      (centralizer_quot_inf_le hX)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ (hQ2.to_le hle)
  intro g hg
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hg, Subgroup.le_normalizer_of_normal (Subgroup.mem_top g)⟩

theorem pCoreOf_blkY_le_gnC (eL : ↥L ≃* alternatingGroup (Fin 7))
    (hD : ¬ gnD T ⊓ preL T L ≤ gnC T) : pCoreOf 2 (blkY T L) ≤ gnC T := by
  have := isSimpleGroupAlt7
  have : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hY := gnImg_blkY eL hD
  have hR2 : IsPGroup 2 (pCoreOf 2 (blkY T L)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRL : gnImg T (pCoreOf 2 (blkY T L)) ≤ L :=
    (Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).trans hY.le
  have hSn : ((gnImg T (pCoreOf 2 (blkY T L))).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : (g : X ⧸ gnC T) ∈ gnImg T (blkY T L) := by rw [hY]; exact g.2
    obtain ⟨y, hy, hgy⟩ := hg
    obtain ⟨r, hr, hrn⟩ := Subgroup.mem_subgroupOf.1 hn
    refine Subgroup.mem_subgroupOf.2 ⟨y * r * y⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (blkY T L) hy) r).1 hr
    · rw [map_mul, map_mul, map_inv]
      have h1 : (QuotientGroup.mk' (gnC T)) y = (g : X ⧸ gnC T) := hgy
      have h2 : (QuotientGroup.mk' (gnC T)) r = (n : X ⧸ gnC T) := hrn
      rw [h1, h2]
      rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((gnImg T (pCoreOf 2 (blkY T L))).subgroupOf L) with h | h
  · intro r hr
    have hmem : (⟨(r : X ⧸ gnC T), hRL ⟨r, hr, rfl⟩⟩ : ↥L) ∈
        (gnImg T (pCoreOf 2 (blkY T L))).subgroupOf L :=
      Subgroup.mem_subgroupOf.2 ⟨r, hr, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff r).1 (congrArg Subtype.val hmem)
  · exfalso
    apply not_isPGroup_two_alt7
    have hL2 : IsPGroup 2 ↥L := by
      intro l
      have hmem : (l : ↥L) ∈ (gnImg T (pCoreOf 2 (blkY T L))).subgroupOf L := by rw [h]; trivial
      obtain ⟨r, hr, hrl⟩ := Subgroup.mem_subgroupOf.1 hmem
      obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h3 : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h4 : (QuotientGroup.mk' (gnC T)) r = (l : X ⧸ gnC T) := hrl
      show ((l ^ 2 ^ k : ↥L) : X ⧸ gnC T) = 1
      rw [Subgroup.coe_pow, ← h4, ← map_pow, h3, map_one]
    exact hL2.of_equiv eL

theorem pCoreOf_blkY_eq (hX : GNSetting X T) (eL : ↥L ≃* alternatingGroup (Fin 7))
    (hD : ¬ gnD T ⊓ preL T L ≤ gnC T) : pCoreOf 2 (blkY T L) = blkY T L ⊓ gnC T :=
  le_antisymm (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (pCoreOf_blkY_le_gnC eL hD))
    (blkY_inf_gnC_le hX)

end PCore

section Generic

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem noPQuotient_of_twoResidual_eq {K : Subgroup X} (hK : twoResidual K = K)
    (N' : Subgroup ↥K) [hNn : N'.Normal] (hN' : IsPGroup 2 (↥K ⧸ N')) : N' = ⊤ := by
  have hmap : N'.map K.subtype ≤ K := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hn : K ≤ Subgroup.normalizer ((N'.map K.subtype : Subgroup X) : Set X) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, hNn.conj_mem y hy _, ?_⟩
      simp
    · rintro ⟨y, hy, hyx⟩
      have h1 : (⟨k, hk⟩ : ↥K)⁻¹ * y * (⟨k, hk⟩ : ↥K)⁻¹⁻¹ ∈ N' := hNn.conj_mem y hy _
      rw [inv_inv] at h1
      refine ⟨_, h1, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      have hyx' : (y : X) = k * x * k⁻¹ := hyx
      rw [hyx']
      group
  have h2 : ∀ y ∈ K, ∃ k : ℕ, y ^ 2 ^ k ∈ N'.map K.subtype := by
    intro y hy
    obtain ⟨k, hk⟩ := hN' (QuotientGroup.mk ⟨y, hy⟩)
    refine ⟨k, ⟨⟨y, hy⟩ ^ 2 ^ k, ?_, rfl⟩⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    exact hk
  have h3 : twoResidual K ≤ N'.map K.subtype := twoResidual_le_of_isTwoQuotient hmap hn h2
  rw [hK] at h3
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := h3 x.2
  have : y = x := Subtype.ext hyx
  rwa [this] at hy

omit [Finite X] in
theorem mem_pCore_iff_mem_pCoreOf (H : Subgroup X) (y : ↥H) :
    y ∈ CFSG.pCore 2 ↥H ↔ (y : X) ∈ pCoreOf 2 H := by
  exact ⟨fun h => ⟨y, h, rfl⟩, fun ⟨z, hz, e⟩ => (Subtype.ext e) ▸ hz⟩

end Generic

section Alt7Facts

theorem exists_nonComm_alt7 :
    ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩, ?_⟩
  intro h
  have := congrArg Subtype.val h
  revert this
  decide

theorem exists_ne_one_alt7 : ∃ a : alternatingGroup (Fin 7), a ≠ 1 := by
  obtain ⟨a, b, h⟩ := exists_nonComm_alt7
  by_contra hcon
  push Not at hcon
  exact h (by rw [hcon a, hcon b])

theorem isQuasisimple_of_equiv_alt7 {Q : Type*} [Group Q] (e : Q ≃* alternatingGroup (Fin 7)) :
    CFSG.IsQuasisimple Q := by
  have hs7 := isSimpleGroupAlt7
  have hs : IsSimpleGroup Q := e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := exists_nonComm_alt7
  have hnc : ∃ x y : Q, x * y ≠ y * x := ⟨e.symm a, e.symm b, fun h => hab (by
    have := congrArg e h
    simpa using this)⟩
  have hperf : Group.IsPerfect Q := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have : ⁅x, y⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
        (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact ⟨h⟩
  have hc : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      exact hxy ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y)) x)
  let e2 : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨hperf, e2.isSimpleGroup, ?_⟩
  obtain ⟨x, y, hxy⟩ := hnc
  exact ⟨e2.symm x, e2.symm y, fun h => hxy (by simpa using congrArg e2 h)⟩

end Alt7Facts

section AltHeartFacts

theorem altHeart_add_self {n : ℕ} (a : altHeart n) : a + a = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  have hx : x + x = 0 := Subtype.ext (funext fun i => by
    have : ∀ t : ZMod 2, t + t = 0 := by decide
    exact this _)
  rw [← QuotientAddGroup.mk_add, hx]
  rfl

theorem exists_ne_zero_altHeart : ∃ a : altHeart 7, a ≠ 0 := by
  refine ⟨QuotientAddGroup.mk (pairEW (0 : Fin 7) 1), fun h => ?_⟩
  have hm : pairEW (0 : Fin 7) 1 ∈ evenWeightOnes 7 := (QuotientAddGroup.eq_zero_iff _).1 h
  obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hm
  have h0 := hc 0
  have h2 := hc 2
  rw [pairEW_apply] at h0 h2
  simp at h0 h2
  exact absurd (h0.trans h2.symm) (by decide)

end AltHeartFacts

section Module

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

@[expose] def blkN (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : Subgroup X :=
  ⁅gnV T, preL T L⁆

structure SixData (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) where
  hX : GNSetting X T
  hL : IsComponentOf L ⊤
  eL : ↥L ≃* alternatingGroup (Fin 7)
  hD : ¬ gnD T ⊓ preL T L ≤ gnC T
  hC : blkN T L ⊓ Subgroup.centralizer (preL T L : Set X) = ⊥
  φ : ↥(blkN T L) →* Multiplicative (altHeart 7)
  hφ : Function.Bijective φ
  hφe : ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L) (u v : ↥(blkN T L)),
    (v : X) = l * u * l⁻¹ →
      Multiplicative.toAdd (φ v) =
        altAct (eL ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin 7))
          (Multiplicative.toAdd (φ u))

namespace SixData

variable (S : SixData T L)

omit [Finite X] S in
theorem blkN_le_gnV : blkN T L ≤ gnV T :=
  have := normal_gnV T
  Subgroup.commutator_le_left _ _

include S in
theorem gnV_le_gnC' : gnV T ≤ gnC T := (gnV_le_pCoreOf S.hX).trans (pCoreOf_le_gnC S.hX)

include S in
theorem blkN_le_gnC : blkN T L ≤ gnC T := blkN_le_gnV.trans S.gnV_le_gnC'

omit [Finite X] in
theorem preL_le_normalizer_blkN : preL T L ≤ Subgroup.normalizer (blkN T L : Set X) :=
  Subgroup.normalizer_commutator_ge_right _ _

include S in
theorem exists_mul {x : X} (hx : x ∈ preL T L) : ∃ y ∈ blkY T L, ∃ c ∈ gnC T, x = y * c := by
  have h1 : (x : X ⧸ gnC T) ∈ gnImg T (blkY T L) := by
    rw [gnImg_blkY S.eL S.hD]; exact hx
  obtain ⟨y, hy, hyx⟩ := h1
  refine ⟨y, hy, y⁻¹ * x, ?_, by group⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have : (y : X ⧸ gnC T) = (x : X ⧸ gnC T) := hyx
  rw [this, inv_mul_cancel]

include S in
theorem blkN_inf_centralizer_blkY : blkN T L ⊓ Subgroup.centralizer (blkY T L : Set X) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro n ⟨hnN, hnY⟩
  have h1 : n ∈ blkN T L ⊓ Subgroup.centralizer (preL T L : Set X) := by
    refine ⟨hnN, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro x hx
    obtain ⟨y, hy, c, hc, rfl⟩ := S.exists_mul hx
    have hcn : n * c = c * n :=
      Subgroup.mem_centralizer_iff.1 hc n (blkN_le_gnV hnN)
    have hyn : y * n = n * y := Subgroup.mem_centralizer_iff.1 hnY y hy
    calc y * c * n = y * (c * n) := by group
      _ = y * (n * c) := by rw [← hcn]
      _ = (y * n) * c := by group
      _ = (n * y) * c := by rw [hyn]
      _ = n * (y * c) := by group
  rw [S.hC] at h1
  exact h1

include S in
theorem gnV_le_normalizer_blkY : gnV T ≤ Subgroup.normalizer (blkY T L : Set X) := by
  have := normal_gnV T
  have hQ2 : IsPGroup 2 (gnV T) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup X)).to_le (gnV_le_pCoreOf S.hX)
  exact le_normalizer_of_isSubnormal_of_odd (H := ⊤) (K := blkY T L) (R := gnV T) le_top
    (isSubnormal_blkY' S.hL) (le_closure_odd_of_twoResidual_eq (twoResidual_twoResidual _))
    le_top (fun g hg => Subgroup.le_normalizer_of_normal hg) hQ2

include S in
theorem comm_blkN_blkY_le : ⁅blkN T L, blkY T L⁆ ≤ blkY T L :=
  (Subgroup.commutator_mono blkN_le_gnV le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_right.1 S.gnV_le_normalizer_blkY)

omit [Finite X] S in
theorem comm_blkN_blkY_le_blkN [Finite X] : ⁅blkN T L, blkY T L⁆ ≤ blkN T L :=
  Subgroup.le_normalizer_iff_commutator_le_left.1
    ((blkY_le_blkE.trans blkE_le_preL).trans preL_le_normalizer_blkN)

include S in
theorem eq_bot_or_eq_blkN {W : Subgroup X} (hW : W ≤ blkN T L)
    (hinv : ∀ y ∈ blkY T L, ∀ w ∈ W, y * w * y⁻¹ ∈ W) : W = ⊥ ∨ W = blkN T L := by
  let U : AddSubgroup (altHeart 7) :=
    { carrier := {a | ∃ w : ↥(blkN T L), (w : X) ∈ W ∧ Multiplicative.toAdd (S.φ w) = a}
      zero_mem' := ⟨1, W.one_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
        exact ⟨w₁ * w₂, W.mul_mem hw₁ hw₂, by simp⟩
      neg_mem' := by
        rintro _ ⟨w, hw, rfl⟩
        exact ⟨w⁻¹, W.inv_mem hw, by simp⟩ }
  have hU : ∀ σ ∈ alternatingGroup (Fin 7), ∀ x : evenWeight 7,
      (QuotientAddGroup.mk x : altHeart 7) ∈ U →
        (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart 7) ∈ U := by
    intro σ hσ x hx
    obtain ⟨w, hwW, hwx⟩ := hx
    obtain ⟨l0, hl0⟩ : ∃ l0 : ↥L, S.eL l0 = ⟨σ, hσ⟩ := S.eL.surjective ⟨σ, hσ⟩
    obtain ⟨y, hy, hyl⟩ : (l0 : X ⧸ gnC T) ∈ gnImg T (blkY T L) := by
      rw [gnImg_blkY S.eL S.hD]; exact l0.2
    have hyn : y ∈ Subgroup.normalizer (blkN T L : Set X) :=
      preL_le_normalizer_blkN (blkE_le_preL (blkY_le_blkE hy))
    have hvmem : y * (w : X) * y⁻¹ ∈ blkN T L :=
      (Subgroup.mem_normalizer_iff.1 hyn w).1 w.2
    refine ⟨⟨y * w * y⁻¹, hvmem⟩, hinv y hy w hwW, ?_⟩
    have hl : QuotientGroup.mk' (gnC T) y ∈ L := by rw [hyl]; exact l0.2
    have h3 := S.hφe y hl w ⟨y * w * y⁻¹, hvmem⟩ rfl
    rw [h3]
    have h1 : (⟨QuotientGroup.mk' (gnC T) y, hl⟩ : ↥L) = l0 := Subtype.ext hyl
    rw [h1, hl0, hwx]
    rfl
  rcases altHeart_irreducible (by norm_num) U hU with h | h
  · left
    refine le_bot_iff.1 fun w hw => ?_
    have hwN := hW hw
    have h4 : Multiplicative.toAdd (S.φ ⟨w, hwN⟩) ∈ U := ⟨⟨w, hwN⟩, hw, rfl⟩
    rw [h, AddSubgroup.mem_bot] at h4
    have h1 : S.φ ⟨w, hwN⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      simpa using h4
    have h2 : (⟨w, hwN⟩ : ↥(blkN T L)) = 1 := S.hφ.1 (h1.trans (map_one _).symm)
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h2
  · right
    refine le_antisymm hW fun n hn => ?_
    have h4 : Multiplicative.toAdd (S.φ ⟨n, hn⟩) ∈ U := by rw [h]; trivial
    obtain ⟨w, hwW, hwe⟩ := h4
    have h5 : w = ⟨n, hn⟩ := S.hφ.1 (Multiplicative.toAdd.injective hwe)
    subst h5
    exact hwW

include S in
theorem blkN_ne_bot : blkN T L ≠ ⊥ := by
  intro h
  obtain ⟨a, ha⟩ := exists_ne_zero_altHeart
  obtain ⟨n, hn⟩ := S.hφ.2 (Multiplicative.ofAdd a)
  have h1 : (n : X) = 1 := Subgroup.mem_bot.1 (h.le n.2)
  have h2 : n = 1 := Subtype.ext h1
  apply ha
  have h3 : S.φ n = Multiplicative.ofAdd a := hn
  rw [h2, map_one] at h3
  exact (congrArg Multiplicative.toAdd h3).symm

include S in
theorem blkN_eq_comm : ⁅blkN T L, blkY T L⁆ = blkN T L := by
  rcases S.eq_bot_or_eq_blkN (W := ⁅blkN T L, blkY T L⁆) comm_blkN_blkY_le_blkN
      (fun y hy w hw => (Subgroup.mem_normalizer_iff.1
        (Subgroup.normalizer_commutator_ge_right (blkN T L) (blkY T L) hy) w).1 hw) with h | h
  · exfalso
    apply S.blkN_ne_bot
    have h1 : blkN T L ≤ Subgroup.centralizer (blkY T L : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    exact le_bot_iff.1 (le_trans (le_inf le_rfl h1) S.blkN_inf_centralizer_blkY.le)
  · exact h

include S in
theorem blkN_le_blkY : blkN T L ≤ blkY T L :=
  calc blkN T L = ⁅blkN T L, blkY T L⁆ := S.blkN_eq_comm.symm
    _ ≤ blkY T L := S.comm_blkN_blkY_le

include S in
theorem blkN_le_blkYC : blkN T L ≤ blkY T L ⊓ gnC T := le_inf S.blkN_le_blkY S.blkN_le_gnC

include S in
theorem blockQ_blkY : blockQ (blkY T L) = blkY T L ⊓ gnC T := pCoreOf_blkY_eq S.hX S.eL S.hD

include S in
theorem blockU_blkY : blockU (blkY T L) = blkN T L := by
  apply le_antisymm
  · show ⁅blockQ (blkY T L), blkY T L⁆ ≤ blkN T L
    rw [S.blockQ_blkY]
    have hQ2 : IsPGroup 2 (pCoreOf 2 (⊤ : Subgroup X)) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
    have hRQ : blkY T L ⊓ gnC T ≤ pCoreOf 2 (⊤ : Subgroup X) :=
      (le_inf (inf_le_left.trans (blkY_le_blkE.trans blkE_le_gnD)) inf_le_right).trans
        (centralizer_quot_inf_le S.hX)
    have hR2 : IsPGroup 2 (blkY T L ⊓ gnC T : Subgroup X) := hQ2.to_le hRQ
    have hYR : blkY T L ≤ Subgroup.normalizer ((blkY T L ⊓ gnC T : Subgroup X) : Set X) :=
      fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, Subgroup.le_normalizer_of_normal (Subgroup.mem_top g)⟩
    have hcop := commutator_le_commutator_commutator_of_odd hR2 hYR
      (le_closure_odd_of_twoResidual_eq (twoResidual_twoResidual (blkE T L)))
    have hQV : ⁅pCoreOf 2 (⊤ : Subgroup X), blkY T L⁆ ≤ gnV T :=
      le_gnD_iff.1 (blkY_le_blkE.trans blkE_le_gnD)
    have h1 : ⁅blkY T L ⊓ gnC T, blkY T L⁆ ≤ gnV T :=
      (Subgroup.commutator_mono hRQ le_rfl).trans hQV
    refine hcop.trans ((Subgroup.commutator_mono h1 le_rfl).trans ?_)
    exact Subgroup.commutator_mono le_rfl (blkY_le_blkE.trans blkE_le_preL)
  · calc blkN T L = ⁅blkN T L, blkY T L⁆ := S.blkN_eq_comm.symm
      _ ≤ ⁅blkY T L ⊓ gnC T, blkY T L⁆ := Subgroup.commutator_mono S.blkN_le_blkYC le_rfl
      _ = blockU (blkY T L) := by rw [blockU, S.blockQ_blkY]

include S in
theorem blockZ_blkY : blockZ (blkY T L) = ⊥ := by
  show blockU (blkY T L) ⊓ Subgroup.centralizer (blkY T L : Set X) = ⊥
  rw [S.blockU_blkY]
  exact S.blkN_inf_centralizer_blkY

include S in
theorem charTwo_blkY : CharTwo (blkY T L) := by
  intro y hy
  obtain ⟨hyY, hyc⟩ := hy
  have hR : pCoreOf 2 (blkY T L) = blkY T L ⊓ gnC T := pCoreOf_blkY_eq S.hX S.eL S.hD
  have hcomm : ∀ n ∈ blkN T L, n * y = y * n := fun n hn => by
    have hn' : n ∈ pCoreOf 2 (blkY T L) := by rw [hR]; exact S.blkN_le_blkYC hn
    exact Subgroup.mem_centralizer_iff.1 hyc n hn'
  have hl : QuotientGroup.mk' (gnC T) y ∈ L := mk_mem_of_mem_blkY hyY
  have h1 : (S.eL ⟨QuotientGroup.mk' (gnC T) y, hl⟩ : Equiv.Perm (Fin 7)) = 1 := by
    refine perm_eq_one_of_altHeart_fixed (by norm_num) _ fun x => ?_
    obtain ⟨n, hn⟩ := S.hφ.2 (Multiplicative.ofAdd (QuotientAddGroup.mk x : altHeart 7))
    have hn' : Multiplicative.toAdd (S.φ n) = (QuotientAddGroup.mk x : altHeart 7) :=
      congrArg Multiplicative.toAdd hn
    have h2 := S.hφe y hl n n (by
      have := hcomm n n.2
      calc (n : X) = (n * y) * y⁻¹ := by group
        _ = (y * n) * y⁻¹ := by rw [this])
    rw [hn'] at h2
    exact h2.symm
  have h2 : S.eL ⟨QuotientGroup.mk' (gnC T) y, hl⟩ = 1 := Subtype.ext h1
  have h3 : (⟨QuotientGroup.mk' (gnC T) y, hl⟩ : ↥L) = 1 := S.eL.map_eq_one_iff.1 h2
  have h4 : QuotientGroup.mk' (gnC T) y = 1 := congrArg Subtype.val h3
  rw [hR]
  exact ⟨hyY, (QuotientGroup.eq_one_iff y).1 h4⟩

include S in
theorem blockU_le_centralizer_blkY :
    blockU (blkY T L) ≤ blockQ (blkY T L) ⊓ Subgroup.centralizer (blockQ (blkY T L) : Set X) := by
  rw [S.blockU_blkY, S.blockQ_blkY]
  refine le_inf S.blkN_le_blkYC ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact (Subgroup.mem_centralizer_iff.1 hr.2 x (blkN_le_gnV hx)).symm

include S in
theorem sq_eq_one_of_mem_blkN {x : X} (hx : x ∈ blkN T L) : x ^ 2 = 1 := by
  have h1 : S.φ ⟨x, hx⟩ * S.φ ⟨x, hx⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    exact altHeart_add_self _
  have h2 : (⟨x, hx⟩ : ↥(blkN T L)) * ⟨x, hx⟩ = 1 := S.hφ.1 (by rw [map_mul, map_one, h1])
  rw [sq]
  exact congrArg Subtype.val h2

include S in
theorem irreducible_blkY {W : Subgroup X} (_hZ : blockZ (blkY T L) ≤ W) (hU : W ≤ blockU (blkY T L))
    (hn : blkY T L ≤ Subgroup.normalizer (W : Set X)) :
    W = blockZ (blkY T L) ∨ W = blockU (blkY T L) := by
  rw [S.blockZ_blkY]
  rw [S.blockU_blkY] at hU ⊢
  exact S.eq_bot_or_eq_blkN hU fun y hy w hw => (Subgroup.mem_normalizer_iff.1 (hn hy) w).1 hw

@[expose] def alphaY (S : SixData T L) : ↥(blkY T L) →* alternatingGroup (Fin 7) :=
  S.eL.toMonoidHom.comp (((QuotientGroup.mk' (gnC T)).comp (blkY T L).subtype).codRestrict L
    (fun y => mk_mem_of_mem_blkY y.2))

include S in
theorem alphaY_surjective : Function.Surjective (alphaY S) := by
  intro a
  obtain ⟨y, hy, hyl⟩ : ((S.eL.symm a : ↥L) : X ⧸ gnC T) ∈ gnImg T (blkY T L) := by
    rw [gnImg_blkY S.eL S.hD]; exact (S.eL.symm a).2
  refine ⟨⟨y, hy⟩, ?_⟩
  show S.eL ⟨QuotientGroup.mk' (gnC T) y, _⟩ = a
  have h1 : (⟨QuotientGroup.mk' (gnC T) y, mk_mem_of_mem_blkY hy⟩ : ↥L) =
      S.eL.symm a := Subtype.ext hyl
  rw [h1]
  exact S.eL.apply_symm_apply a

include S in
theorem alphaY_ker : (alphaY S).ker = CFSG.pCore 2 ↥(blkY T L) := by
  ext y
  have hl : QuotientGroup.mk' (gnC T) (y : X) ∈ L := mk_mem_of_mem_blkY y.2
  have key : alphaY S y = 1 ↔ QuotientGroup.mk' (gnC T) (y : X) = 1 := by
    constructor
    · intro h
      have h2 : S.eL ⟨QuotientGroup.mk' (gnC T) (y : X), hl⟩ = 1 := h
      exact congrArg Subtype.val (S.eL.map_eq_one_iff.1 h2)
    · intro h
      have h3 : (⟨QuotientGroup.mk' (gnC T) (y : X), hl⟩ : ↥L) = 1 := Subtype.ext h
      show S.eL ⟨QuotientGroup.mk' (gnC T) (y : X), hl⟩ = 1
      rw [h3, map_one]
  have key2 : QuotientGroup.mk' (gnC T) (y : X) = 1 ↔ (y : X) ∈ gnC T :=
    QuotientGroup.eq_one_iff (y : X)
  rw [MonoidHom.mem_ker, key, key2, mem_pCore_iff_mem_pCoreOf, pCoreOf_blkY_eq S.hX S.eL S.hD]
  exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩

include S in
theorem isShort2_aux_quasisimple :
    CFSG.IsQuasisimple (↥(blkY T L) ⧸ CFSG.pCore 2 ↥(blkY T L)) := by
  let e : (↥(blkY T L) ⧸ CFSG.pCore 2 ↥(blkY T L)) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq (alphaY_ker S).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (alphaY_surjective S))
  exact isQuasisimple_of_equiv_alt7 e

include S in
theorem isShort2_blkY : IsShort2 (blkY T L) := by
  refine ⟨fun N [N.Normal] hN => noPQuotient_of_twoResidual_eq (K := blkY T L)
      (twoResidual_twoResidual (blkE T L)) N hN, S.charTwo_blkY,
    ⟨S.blockU_le_centralizer_blkY, fun x hx => ?_⟩, Or.inl S.isShort2_aux_quasisimple, ?_, ?_⟩
  · rw [S.blockU_blkY] at hx
    exact S.sq_eq_one_of_mem_blkN hx
  · rw [S.blockZ_blkY, S.blockU_blkY]
    exact bot_lt_iff_ne_bot.2 S.blkN_ne_bot
  · exact fun W hZ hU hn => S.irreducible_blkY hZ hU hn

include S in
theorem isAltNatural_blkY : IsAltNaturalType (blkY T L) 7 := by
  have hU := S.blockU_blkY
  refine ⟨alphaY S, alphaY_surjective S, alphaY_ker S,
    S.φ.comp (Subgroup.inclusion hU.le), ?_, ?_, ?_⟩
  · intro a
    obtain ⟨n, hn⟩ := S.hφ.2 a
    exact ⟨⟨n.1, hU.ge n.2⟩, hn⟩
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, S.blockZ_blkY, Subgroup.mem_bot]
    constructor
    · intro h
      have h0 : S.φ (Subgroup.inclusion hU.le u) = S.φ 1 := by
        rw [map_one]; exact h
      have h1 : Subgroup.inclusion hU.le u = 1 := S.hφ.1 h0
      exact congrArg Subtype.val h1
    · intro h
      have h1 : Subgroup.inclusion hU.le u = 1 := Subtype.ext h
      show S.φ (Subgroup.inclusion hU.le u) = 1
      rw [h1, map_one]
  · intro ℓ u v huv x hx
    have hl : QuotientGroup.mk' (gnC T) (ℓ : X) ∈ L := mk_mem_of_mem_blkY ℓ.2
    have h1 := S.hφe (ℓ : X) hl (Subgroup.inclusion hU.le u) (Subgroup.inclusion hU.le v)
      (by simpa using huv)
    show Multiplicative.toAdd (S.φ (Subgroup.inclusion hU.le v)) = _
    rw [h1]
    have hu : Multiplicative.toAdd (S.φ (Subgroup.inclusion hU.le u)) = (x : altHeart 7) := hx
    rw [hu]
    rfl

include S in
theorem false_of_blkY : False := by
  have hblock : IsBlock2 (⊤ : Subgroup X) (blkY T L) :=
    ⟨S.isShort2_blkY, le_top, isSubnormal_blkY' S.hL⟩
  have hchi : IsChiBlockGN (⊤ : Subgroup X) (blkY T L) :=
    ⟨hblock, Or.inr ⟨7, by decide, by norm_num,
      isAltType_of_isAltNaturalType (by decide) S.isAltNatural_blkY⟩⟩
  have hnotC : ¬ blkY T L ≤ gnC T := by
    intro h
    obtain ⟨a, ha⟩ := exists_ne_one_alt7
    obtain ⟨y, hy, hyl⟩ : ((S.eL.symm a : ↥L) : X ⧸ gnC T) ∈ gnImg T (blkY T L) := by
      rw [gnImg_blkY S.eL S.hD]; exact (S.eL.symm a).2
    have h1 : QuotientGroup.mk' (gnC T) y = 1 := (QuotientGroup.eq_one_iff y).2 (h hy)
    have h2 : ((S.eL.symm a : ↥L) : X ⧸ gnC T) = 1 := hyl.symm.trans h1
    have h3 : S.eL.symm a = 1 := Subtype.ext h2
    exact ha (by simpa using congrArg S.eL h3)
  refine false_of_block_subnormal S.hX le_top hchi hnotC ?_
  rw [gnImg_blkY S.eL S.hD]
  exact S.hL.2.1

end SixData

theorem false_of_gnD_alt7 {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤) (eL : ↥L ≃* alternatingGroup (Fin 7))
    (hC : ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
      Subgroup.centralizer ((L.comap (QuotientGroup.mk' (gnC T)) : Subgroup X) : Set X) = ⊥)
    (φ : ↥⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (altHeart 7))
    (hφ : Function.Bijective φ)
    (hφe : ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L)
      (u v : ↥⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆), (v : X) = l * u * l⁻¹ →
      Multiplicative.toAdd (φ v) =
        altAct (eL ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin 7))
          (Multiplicative.toAdd (φ u)))
    (hD : ¬ gnD T ⊓ L.comap (QuotientGroup.mk' (gnC T)) ≤ gnC T) : False :=
  SixData.false_of_blkY ⟨hX, hL, eL, hD, hC, φ, hφ, hφe⟩

end Module

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
