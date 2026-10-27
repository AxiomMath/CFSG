module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupRankOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentActionBasic
public import CFSG.LocalAnalysis.ComponentInitial.CyclicIndexTwoRank
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open Subgroup
open scoped commutatorElement

namespace Lemma35

theorem isSmallDihedralSimple_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSmallDihedralSimple X) : IsSmallDihedralSimple Y := by
  rcases h with ⟨⟨e'⟩⟩ | ⟨p, f, hpf, hadm, K, hK1, hK2, hcard, ⟨e'⟩⟩
  · exact Or.inl ⟨e.symm.trans e'⟩
  · exact Or.inr ⟨p, f, hpf, hadm, K, hK1, hK2, hcard, ⟨e.symm.trans e'⟩⟩

theorem pRank_le_two_of_dihedral {X : Type*} [Group X] [Finite X] (h : HasDihedralSylowTwo X) :
    Open.pRank 2 (⊤ : Subgroup X) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, n, hn, ⟨e⟩⟩ := h
  set m := 2 ^ (n - 1) with hm
  have : NeZero m := ⟨by positivity⟩
  set R : Subgroup (S : Subgroup X) := zpowers (e.symm (DihedralGroup.r 1)) with hR
  have hRcard : Nat.card R = m := by
    rw [hR, Nat.card_zpowers, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hScard : Nat.card (S : Subgroup X) = 2 * m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hRind : R.index ≤ 2 := by
    have h1 := R.index_mul_card
    rw [hRcard, hScard] at h1
    have hm0 : 0 < m := by positivity
    have : R.index * m = 2 * m := h1
    exact (Nat.eq_of_mul_eq_mul_right hm0 this).le
  have h1 : CFSG.pRank 2 (S : Subgroup X) ≤ 2 :=
    LocalAnalysis.ComponentInitial.cyclic_index_two_rank_bound (H := R) inferInstance hRind
  rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h1
  rw [← (SectionRank.pRank_sylow S).1]
  exact h1

variable {G : Type*} [Group G]

theorem isElemAbelian_of_le {E W : Subgroup G} (hE : Open.IsElemAbelian 2 E) (hWE : W ≤ E) :
    Open.IsElemAbelian 2 W := CFSG.Open.IsElemAbelian.mono hE hWE

theorem exists_fourGroup_of_mem [Finite G] {E : Subgroup G} (hE : Open.IsElemAbelian 2 E)
    (hE8 : Nat.card E = 2 ^ 3) {e : G} (he : e ∈ E) :
    ∃ W : Subgroup G, W ≤ E ∧ IsFourGroup W ∧ e ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK4, heK⟩ : ∃ K : Subgroup E, Nat.card K = 2 ^ 2 ∧ (⟨e, he⟩ : E) ∈ K := by
    by_cases he1 : e = 1
    · obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2
        (by rw [hE8]; norm_num : 2 ^ 2 ∣ Nat.card E)
      refine ⟨K, hK, ?_⟩
      have : (⟨e, he⟩ : E) = 1 := Subtype.ext he1
      rw [this]
      exact one_mem K
    · have hord : Nat.card (zpowers (⟨e, he⟩ : E)) = 2 ^ 1 := by
        rw [Nat.card_zpowers, pow_one]
        apply orderOf_eq_prime
        · exact Subtype.ext (hE.2 e he)
        · intro h1
          exact he1 (congrArg Subtype.val h1)
      obtain ⟨K, hK, hle⟩ := Sylow.exists_subgroup_card_pow_succ
        (by rw [hE8]; norm_num : 2 ^ (1 + 1) ∣ Nat.card E) hord
      exact ⟨K, hK, hle (mem_zpowers _)⟩
  refine ⟨K.map E.subtype, map_subtype_le K, ⟨isElemAbelian_of_le hE (map_subtype_le K), ?_⟩,
    ⟨⟨e, he⟩, heK, rfl⟩⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hK4]
  norm_num

theorem inf_centralizer_le_centralizerJoin {W L : Subgroup G} {a : G} (haW : a ∈ W)
    (ha1 : a ≠ 1) : L ⊓ centralizer ({a} : Set G) ≤ centralizerJoin W L :=
  le_iSup_of_le a (le_iSup_of_le haW (le_iSup_of_le ha1 le_rfl))

theorem centralizer_image_eq_bot {H : Type*} [Group H] (L : Subgroup H) [L.Normal]
    [Group.IsPerfect L] :
    centralizer ((L.map (QuotientGroup.mk' (centralizer (L : Set H)))) :
      Set (H ⧸ centralizer (L : Set H))) = ⊥ := by
  set C := centralizer (L : Set H) with hC
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  rw [mem_bot, QuotientGroup.eq_one_iff]
  have hcomm : ∀ g ∈ zpowers h, ∀ l ∈ L, ⁅g, l⁆ ∈ C := by
    intro g hg l hl
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    have hk : (QuotientGroup.mk (h ^ k) : H ⧸ C) ∈
        centralizer ((L.map (QuotientGroup.mk' C)) : Set (H ⧸ C)) := by
      rw [QuotientGroup.mk_zpow]
      exact zpow_mem hx k
    have hlN : (QuotientGroup.mk l : H ⧸ C) ∈ L.map (QuotientGroup.mk' C) := ⟨l, hl, rfl⟩
    have h1 := (mem_centralizer_iff.1 hk) _ hlN
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      ← h1]
    group
  have h1 : ⁅zpowers h, L⁆ ≤ C := (commutator_le).2 hcomm
  have h2 : ⁅⁅zpowers h, L⁆, L⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine (commutator_mono h1 le_rfl).trans ?_
    rw [commutator_le]
    intro c hc l hl
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact ((mem_centralizer_iff.1 hc) l hl).symm
  have h3 := AschbacherComponentAction.perfect_three_subgroup_action L (zpowers h) h2
  rw [commutator_eq_bot_iff_le_centralizer] at h3
  exact h3 (mem_zpowers h)

noncomputable def imageEquiv {H : Type*} [Group H] (L : Subgroup H) [L.Normal] :
    (L.map (QuotientGroup.mk' (centralizer (L : Set H))) : Subgroup _) ≃* L ⧸ center L := by
  let g : L →* H ⧸ centralizer (L : Set H) :=
    (QuotientGroup.mk' (centralizer (L : Set H))).comp L.subtype
  have hgker : g.ker = center L := by
    ext l
    rw [MonoidHom.mem_ker, mem_center_iff]
    change (QuotientGroup.mk (l : H) : H ⧸ centralizer (L : Set H)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, mem_centralizer_iff]
    constructor
    · intro hl m
      exact Subtype.ext (hl m m.2)
    · intro hl m hm
      exact congrArg Subtype.val (hl ⟨m, hm⟩)
  have hgrange : g.range = L.map (QuotientGroup.mk' (centralizer (L : Set H))) := by
    rw [MonoidHom.range_comp, range_subtype]
  exact (MulEquiv.subgroupCongr hgrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange g).symm.trans (QuotientGroup.quotientMulEquivOfEq hgker))

theorem isElemAbelian_map {H X : Type*} [Group H] [Group X] {E : Subgroup H}
    (hE : Open.IsElemAbelian 2 E) (f : H →* X) : Open.IsElemAbelian 2 (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map hE _

theorem core (hK : AschbacherKnownGroupFacts) {H : Type} [Group H] [Finite H]
    (L : Subgroup H) [L.Normal] (hLq : Open.IsQuasisimple L)
    (hD : HasDihedralSylowTwo (L ⧸ center L)) (hZ : (Nat.card (center L)).factorization 2 ≤ 1) :
    (∀ U : Subgroup H, IsFourGroup U → ¬ L ≤ centralizerJoin U L →
      IsSmallDihedralSimple (L ⧸ center L) ∧ U ≤ L ⊔ centralizer (L : Set H)) ∧
    (IsSmallDihedralSimple (L ⧸ center L) →
      ∀ (X : Subgroup (H ⧸ centralizer (L : Set H))) (k : ℕ), 1 ≤ k →
        Nonempty (X ≃* QuaternionGroup (2 ^ k)) →
        Open.pRank 2 (centralizer (X : Set (H ⧸ centralizer (L : Set H)))) ≤ 1) ∧
    (∀ V : Subgroup H, 3 ≤ Open.pRank 2 V →
      ∃ W : Subgroup H, W ≤ V ∧ IsFourGroup W ∧ L ≤ centralizerJoin W L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect L := ⟨hLq.1⟩
  have hNorm : normalizer (L : Set H) = ⊤ := normalizer_eq_top L
  have h12 : ∀ U : Subgroup H, IsFourGroup U → ¬ L ≤ centralizerJoin U L →
      IsSmallDihedralSimple (L ⧸ center L) ∧ U ≤ L ⊔ centralizer (L : Set H) :=
    fun U hU hgen => hK.dihedral_cover_generation H L U hLq hD hZ (hNorm ▸ le_top) hU hgen
  set C := centralizer (L : Set H) with hC
  set N := L.map (QuotientGroup.mk' C) with hN
  have hNn : N.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective C)
  have hNC : centralizer (N : Set (H ⧸ C)) = ⊥ := centralizer_image_eq_bot L
  have hNrank : Open.pRank 2 N ≤ 2 := by
    rw [SectionRank.pRank_eq_pRank_top_subgroup,
      SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (imageEquiv L)]
    exact pRank_le_two_of_dihedral hD
  refine ⟨h12, fun hsmall X k hk hX => ?_, fun V hV => ?_⟩
  · exact hK.small_aut_quaternion (H ⧸ C) N hNn hNC
      (isSmallDihedralSimple_of_mulEquiv (imageEquiv L).symm hsmall) X k hk hX
  · obtain ⟨E, hEV, hE, hE8⟩ := SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) hV
    by_contra hcon
    push Not at hcon
    have hEsub : E ≤ L ⊔ C := by
      intro e he
      obtain ⟨W, hWE, hW, heW⟩ := exists_fourGroup_of_mem hE hE8 he
      exact (h12 W hW (hcon W (hWE.trans hEV) hW)).2 heW
    obtain ⟨a, haE, ha1, haC⟩ : ∃ a ∈ E, a ≠ 1 ∧ a ∈ C := by
      by_contra hno
      push Not at hno
      have hinj : Function.Injective ((QuotientGroup.mk' C).comp E.subtype) := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro x hx
        rw [MonoidHom.mem_ker] at hx
        have hxC : (x : H) ∈ C := (QuotientGroup.eq_one_iff _).1 hx
        rw [mem_bot]
        by_contra hx1
        exact hno x x.2 (fun h => hx1 (Subtype.ext h)) hxC
      have hmapN : E.map (QuotientGroup.mk' C) ≤ N := by
        calc E.map (QuotientGroup.mk' C) ≤ (L ⊔ C).map (QuotientGroup.mk' C) := map_mono hEsub
          _ = N := by rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
      have hrange : ((QuotientGroup.mk' C).comp E.subtype).range = E.map (QuotientGroup.mk' C) := by
        rw [MonoidHom.range_comp, range_subtype]
      have hmapcard : Nat.card (E.map (QuotientGroup.mk' C)) = 2 ^ 3 := by
        rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hE8]
      have := SectionRank.le_pRank (by norm_num) hmapN (isElemAbelian_map hE _) hmapcard
      omega
    obtain ⟨W, hWE, hW, haW⟩ := exists_fourGroup_of_mem hE hE8 haE
    apply hcon W (hWE.trans hEV) hW
    intro l hl
    refine inf_centralizer_le_centralizerJoin haW ha1 (mem_inf.2 ⟨hl, ?_⟩)
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 haC) l hl

end Lemma35

theorem lemma_3_5 (hK : AschbacherKnownGroupFacts) {H : Type} [Group H] [Finite H]
    (L U : Subgroup H) [L.Normal] (hLq : Open.IsQuasisimple L) (hr : Open.pRank 2 L ≤ 1)
    (hU : IsFourGroup U) (hgen : ¬ L ≤ centralizerJoin U L) :
    IsSmallDihedralSimple (L ⧸ center L) ∧ U ≤ L ⊔ centralizer (L : Set H) ∧
    (∀ (X : Subgroup (H ⧸ centralizer (L : Set H))) (k : ℕ), 1 ≤ k →
      Nonempty (X ≃* QuaternionGroup (2 ^ k)) →
      Open.pRank 2 (centralizer (X : Set (H ⧸ centralizer (L : Set H)))) ≤ 1) ∧
    (∀ V : Subgroup H, 3 ≤ Open.pRank 2 V →
      ∃ W : Subgroup H, W ≤ V ∧ IsFourGroup W ∧ L ≤ centralizerJoin W L) := by
  have hr' : Open.pRank 2 (⊤ : Subgroup L) ≤ 1 := by
    rw [← SectionRank.pRank_eq_pRank_top_subgroup]
    exact hr
  obtain ⟨hD, hZ⟩ := rankOne_quotient_center hLq hr'
  obtain ⟨h12, h3, h4⟩ := Lemma35.core hK L hLq hD hZ
  obtain ⟨h1, h2⟩ := h12 U hU hgen
  exact ⟨h1, h2, h3 h1, h4⟩

theorem lemma_3_6 (hK : AschbacherKnownGroupFacts) {H : Type} [Group H] [Finite H]
    (L U : Subgroup H) [L.Normal] (hLq : Open.IsQuasisimple L) (hd : HasDihedralSylowTwo L)
    (hU : IsFourGroup U) (hgen : ¬ L ≤ centralizerJoin U L) :
    (Nat.card (center L)).factorization 2 = 0 ∧
    IsSmallDihedralSimple (L ⧸ center L) ∧ U ≤ L ⊔ centralizer (L : Set H) ∧
    (∀ (X : Subgroup (H ⧸ centralizer (L : Set H))) (k : ℕ), 1 ≤ k →
      Nonempty (X ≃* QuaternionGroup (2 ^ k)) →
      Open.pRank 2 (centralizer (X : Set (H ⧸ centralizer (L : Set H)))) ≤ 1) ∧
    (∀ V : Subgroup H, 3 ≤ Open.pRank 2 V →
      ∃ W : Subgroup H, W ≤ V ∧ IsFourGroup W ∧ L ≤ centralizerJoin W L) := by
  obtain ⟨hD, hZ⟩ := dihedral_quotient_center hLq hd
  obtain ⟨h12, h3, h4⟩ := Lemma35.core hK L hLq hD (by omega)
  obtain ⟨h1, h2⟩ := h12 U hU hgen
  exact ⟨hZ, h1, h2, h3 h1, h4⟩

end CFSG.ComponentClassification.AschbacherKnownGroup
