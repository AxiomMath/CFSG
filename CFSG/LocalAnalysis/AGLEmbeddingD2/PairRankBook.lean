module

public import CFSG.LocalAnalysis.AGLEmbedding.MovedComponents
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G]

theorem mem_barM_normalizer_of_mem_normalizer_barM {M S : Subgroup G} (hSM : S ≤ M)
    (hQS : pCoreOf 2 M ≤ S) {x : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hx : x ∈ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    x ∈ barM M (Subgroup.normalizer (S : Set G)) := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) x
  refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ?_)
  refine le_normalizer_of_forall_map_conj_le (fun g hg => ?_) (Subgroup.mem_zpowers (m : G))
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rintro _ ⟨s, hs, rfl⟩
  have hsb : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨s, hSM hs⟩ ∈ barM M S :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
  have hxk : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m ^ k ∈
      Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := Subgroup.zpow_mem _ hx k
  have hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (m ^ k * ⟨s, hSM hs⟩ * (m ^ k)⁻¹) ∈ barM M S := by
    rw [map_mul, map_mul, map_inv, map_zpow]
    exact (Subgroup.mem_normalizer_iff.mp hxk _).mp hsb
  have h2 := coe_mem_of_mk_mem_barM hQS _ hmk
  have e : (MulAut.conj ((m : G) ^ k)).toMonoidHom s =
      ((m ^ k * ⟨s, hSM hs⟩ * (m ^ k)⁻¹ : M) : G) := by
    change (m : G) ^ k * s * ((m : G) ^ k)⁻¹ = _
    push_cast
    rfl
  rw [e]
  exact h2

theorem mem_normalizer_of_map_conj_pow_eq {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    {u : X} (hu : IsPGroup 3 (Subgroup.zpowers u)) {a b : ℕ} (hab : a < b) (hb : b < a + 3)
    (he : L.map (MulAut.conj (u ^ a)).toMonoidHom = L.map (MulAut.conj (u ^ b)).toMonoidHom) :
    u ∈ Subgroup.normalizer (L : Set X) := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  have hd1 : 0 < d := by omega
  have hd3 : d < 3 := by omega
  have hmap : L.map (MulAut.conj (u ^ d)).toMonoidHom ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (MulAut.conj (u ^ (a + d))).toMonoidHom x ∈
        L.map (MulAut.conj (u ^ a)).toMonoidHom := by
      rw [he]; exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨w, hw, hw'⟩ := hx'
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at hw' ⊢
    have e : u ^ d * x * (u ^ d)⁻¹ =
        (u ^ a)⁻¹ * (u ^ (a + d) * x * (u ^ (a + d))⁻¹) * u ^ a := by
      rw [pow_add]; group
    rw [e, ← hw']
    have e2 : (u ^ a)⁻¹ * (u ^ a * w * (u ^ a)⁻¹) * u ^ a = w := by group
    rw [e2]; exact hw
  have hN : u ^ d ∈ Subgroup.normalizer (L : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hmap
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj (u ^ d)).injective).symm)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hu) ⟨u, Subgroup.mem_zpowers u⟩
  rw [Subgroup.orderOf_mk] at hk
  have hcop : d.gcd (orderOf u) = 1 := by
    rw [hk]
    apply Nat.Coprime.pow_right
    interval_cases d <;> norm_num
  exact (Subgroup.zpowers_le.mpr hN) (mem_zpowers_pow_iff.mpr hcop)

theorem isPGroup_zpowers_mk {M : Subgroup G} {y : G} (hyM : y ∈ M)
    (hy3 : IsPGroup 3 (Subgroup.zpowers y)) :
    IsPGroup 3 (Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩)) := by
  have h3 : IsPGroup 3 (Subgroup.zpowers (⟨y, hyM⟩ : ↥M)) := by
    intro g
    obtain ⟨k, hk⟩ := hy3 ⟨g, by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [← hn]; rfl⟩⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have := h3.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
  rwa [MonoidHom.map_zpowers] at this

theorem barM_not_commute {M L : Subgroup G} (hLM : L ≤ M) {y l : G} (hy : y ∈ L) (hl : l ∈ L)
    (hyl : y * l * y⁻¹ * l⁻¹ ∉ pCoreOf 2 M) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hLM hy⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLM hl⟩ ≠
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLM hl⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hLM hy⟩ := by
  intro he
  apply hyl
  set m : ↥M := ⟨y, hLM hy⟩ * ⟨l, hLM hl⟩ * (⟨y, hLM hy⟩)⁻¹ * (⟨l, hLM hl⟩)⁻¹
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m ∈ barM M (pCoreOf 2 M) := by
    have : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m = 1 := by
      simp only [m, map_mul, map_inv, he, mul_inv_cancel_right, mul_inv_cancel]
    rw [this]
    exact Subgroup.one_mem _
  exact coe_mem_of_mk_mem_barM le_rfl m h1

variable [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem AGLPair.mem_centralizer_of_centralizes_weakSBlocks (h : AGLPair p M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    {c : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hc : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      c ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    c ∈ Subgroup.centralizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  refine mem_centralizer_of_centralizes_moving_components (pCore_quotient_pCore_eq_bot' 2)
    ((pCoreOf_isPGroup 2 H).comap_subtype.map _)
    (fun Lbar hLbar => h86 G M (pCoreOf 2 H) h.isKGroup.1 h.asc81bHyp Lbar hLbar)
    (h.oddCore_le_centralizer h84 hD2) fun Lbar hLbar hnot => ?_
  obtain ⟨L, hL, hbar⟩ := exists_isTwoPrimeComponent hLbar
  have hw : IsWeakSBlock M (pCoreOf 2 H) L :=
    { toIsTwoPrimeComponent := hL
      not_le_normalizer := fun hLS => hnot (hbar ▸ barM_le_normalizer_barM hLS) }
  exact hbar ▸ hc L hw

theorem AGLPair.mem_barM_normalizer_of_centralizes_weakSBlocks (h : AGLPair p M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    {c : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hc : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      c ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    c ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
  mem_barM_normalizer_of_mem_normalizer_barM h.twoCore_le h.twoCore_M_le
    (Subgroup.centralizer_le_normalizer _
      (h.mem_centralizer_of_centralizes_weakSBlocks h84 h86 hD2 hc))


theorem AGLPair.exists_three_mem_barM_normalizer (h : AGLPair p M H R)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {c : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hc : IsComponentOf c ⊤) {z : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hzc : z ∈ c) (hz3 : IsPGroup 3 (Subgroup.zpowers z)) (hzZ : ∃ l ∈ c, z * l ≠ l * z) :
    ∃ y ∈ c, y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧
      IsPGroup 3 (Subgroup.zpowers y) ∧ ∃ l ∈ c, y * l ≠ l * y := by
  by_cases hcN : c ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set _)
  · exact ⟨z, hzc, mem_barM_normalizer_of_mem_normalizer_barM h.twoCore_le h.twoCore_M_le
      (hcN hzc), hz3, hzZ⟩
  · obtain ⟨L, hL, hbar⟩ := exists_isTwoPrimeComponent hc
    have hw : IsWeakSBlock M (pCoreOf 2 H) L :=
      { toIsTwoPrimeComponent := hL
        not_le_normalizer := fun hLS => hcN (hbar ▸ barM_le_normalizer_barM hLS) }
    obtain ⟨y, ⟨hyN, hyL⟩, hy3, l, hl, hyl⟩ := hthree L hw
    exact ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hL.le hyL⟩, hbar ▸ Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr hyL), Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr hyN), isPGroup_zpowers_mk _ hy3,
      ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hL.le hl⟩,
      hbar ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl),
      barM_not_commute hL.le hyL hl hyl⟩⟩

theorem AGLPair.pRank_barM_normalizer_le (h : AGLPair p M H R) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) :
    Open.pRank q (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G))) ≤ Open.pRank q H := by
  have e : barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) =
      barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ M) := by
    simp only [barM, Subgroup.inf_subgroupOf_right]
  rw [e]
  refine (pRank_barM_le hq hq2 M _ inf_le_right).trans ?_
  refine CFSG.PreuniquenessRankFour.Helpers.pRank_mono q hq ?_
  rw [h.normalizer_twoCore_H]
  exact inf_le_left

theorem AGLPair.mem_normalizer_weakSBlock_of_isPGroup (h : AGLPair 3 M H R)
    (hH : Open.pRank 3 H = 2)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {u : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hu : IsPGroup 3 (Subgroup.zpowers u)) :
    u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  by_contra hnot
  set Lb := barM M L
  obtain ⟨y, ⟨-, hyL⟩, hy3, l, hl, hyl⟩ := hthree L hL
  set yb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hL.le hyL⟩
  set lb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hL.le hl⟩
  have hybL : yb ∈ Lb := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL)
  have hlbL : lb ∈ Lb := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)
  have hybl : yb * lb ≠ lb * yb := barM_not_commute hL.le hyL hl hyl
  have hyb3 : IsPGroup 3 (Subgroup.zpowers yb) := isPGroup_zpowers_mk _ hy3
  let c : Fin 3 → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := fun i =>
    Lb.map (MulAut.conj (u ^ (i : ℕ))).toMonoidHom
  have hc : ∀ i, IsComponentOf (c i) ⊤ := fun i => isComponentOf_top_map_conj hL.component _
  have hinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact hnot (mem_normalizer_of_map_conj_pow_eq hu hlt (by omega) hij)
    · exact hnot (mem_normalizer_of_map_conj_pow_eq hu hlt (by omega) hij.symm)
  have hz : ∀ i : Fin 3, ∃ y' ∈ c i,
      y' ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧
        IsPGroup 3 (Subgroup.zpowers y') ∧ ∃ l' ∈ c i, y' * l' ≠ l' * y' := by
    intro i
    set g := u ^ (i : ℕ)
    refine h.exists_three_mem_barM_normalizer hthree (hc i)
      (Subgroup.mem_map_of_mem _ hybL) ?_ ⟨(MulAut.conj g).toMonoidHom lb,
        Subgroup.mem_map_of_mem _ hlbL, fun he => hybl ?_⟩
    · have := hyb3.map (MulAut.conj g).toMonoidHom
      rwa [MonoidHom.map_zpowers] at this
    · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at he
      have e1 : g * yb * g⁻¹ * (g * lb * g⁻¹) = g * (yb * lb) * g⁻¹ := by group
      have e2 : g * lb * g⁻¹ * (g * yb * g⁻¹) = g * (lb * yb) * g⁻¹ := by group
      rw [e1, e2] at he
      exact mul_left_cancel (mul_right_cancel he)
  choose y' hy'c hy'K hy'3 hy'Z using hz
  have hrank := le_pRank_of_components Nat.prime_three c hc hinj _ y' hy'K hy'c hy'3 hy'Z
  have hle := h.pRank_barM_normalizer_le Nat.prime_three (by decide)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hrank
  omega

end CFSG.AGLEmbeddingD2
