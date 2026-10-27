module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactSections3
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
import CFSG.LocalAnalysis.ComponentClassification.Components
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

section Quot

variable {p : ℕ} {N : Subgroup G}

theorem rankThreePrimeCore_eq_map_primeComplementCore (p : ℕ) (N : Subgroup G) :
    rankThreePrimeCore p N = (primeComplementCore (G := N) p).map N.subtype :=
  glbPrimeCore_eq_primeComplementCoreOf p N

theorem mem_rankThreePrimeCore_of_mk_eq_one {g : G} (hg : g ∈ N)
    (h : QuotientGroup.mk' (primeComplementCore (G := N) p) ⟨g, hg⟩ = 1) :
    g ∈ rankThreePrimeCore p N := by
  rw [rankThreePrimeCore_eq_map_primeComplementCore]
  exact ⟨⟨g, hg⟩, (QuotientGroup.eq_one_iff _).mp h, rfl⟩

theorem le_rankThreePrimeCore_of_map_mk_eq_bot {W : Subgroup G} (hWN : W ≤ N)
    (h : (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) = ⊥) :
    W ≤ rankThreePrimeCore p N := by
  rw [rankThreePrimeCore_eq_map_primeComplementCore, ← Subgroup.map_subgroupOf_eq_of_le hWN]
  refine Subgroup.map_mono ?_
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h

theorem primeComplementCore_le_subgroupOf_inf_of_coprime {M U : Subgroup G} (hp : p.Prime)
    (hUN : U ≤ N) (h : ∀ X : Subgroup G, ¬ p ∣ Nat.card X → U ≤ normalizer (X : Set G) → X ≤ M) :
    primeComplementCore (G := N) p ≤ (N ⊓ M).subgroupOf N := by
  rw [← glbPrimeCore_subgroupOf p N]
  exact glbPrimeCore_subgroupOf_le_inf (h _ ((Nat.Prime.coprime_iff_not_dvd hp).mp
    (glbPrimeCore_coprime p N)) (hUN.trans (le_normalizer_glbPrimeCore p N)))

omit [Finite G] in
theorem comap_map_mk_primeComplementCore_of_le {X : Subgroup N}
    (h : primeComplementCore (G := N) p ≤ X) :
    (X.map (QuotientGroup.mk' (primeComplementCore (G := N) p))).comap
      (QuotientGroup.mk' (primeComplementCore (G := N) p)) = X := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr h]

omit [Finite G] in
theorem map_mk_inf_ne_top {M : Subgroup G}
    (hOM : primeComplementCore (G := N) p ≤ (N ⊓ M).subgroupOf N) (hNM : ¬ N ≤ M) :
    ((N ⊓ M).subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ≠ ⊤ := by
  intro htop
  apply hNM
  have h := comap_map_mk_primeComplementCore_of_le hOM
  rw [htop, Subgroup.comap_top] at h
  intro g hg
  have hmem : (⟨g, hg⟩ : N) ∈ (N ⊓ M).subgroupOf N := h ▸ Subgroup.mem_top _
  exact (Subgroup.mem_subgroupOf.mp hmem).2

omit [Finite G] in
theorem not_map_mk_le_map_mk_inf {M L : Subgroup G}
    (hOM : primeComplementCore (G := N) p ≤ (N ⊓ M).subgroupOf N) (hLN : L ≤ N)
    (hLM : ¬ L ≤ M) :
    ¬ (L.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ≤
      ((N ⊓ M).subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) := by
  intro hle
  apply hLM
  have h := (Subgroup.map_le_iff_le_comap.mp hle).trans
    (comap_map_mk_primeComplementCore_of_le hOM).le
  intro l hl
  exact (Subgroup.mem_subgroupOf.mp (h (show (⟨l, hLN hl⟩ : N) ∈ L.subgroupOf N from hl))).2

theorem normalizer_le_map_mk_inf {M U : Subgroup G} (hp : p.Prime)
    (hOM : primeComplementCore (G := N) p ≤ (N ⊓ M).subgroupOf N) (hUN : U ≤ N)
    (hU : IsPGroup p U) (hnorm : ∀ D : Subgroup G, D ≤ U → D ≠ ⊥ → normalizer (D : Set G) ≤ M)
    {Dbar : Subgroup (N ⧸ primeComplementCore (G := N) p)}
    (hD : Dbar ≤ (U.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)))
    (hD1 : Dbar ≠ ⊥) :
    normalizer (Dbar : Set (N ⧸ primeComplementCore (G := N) p)) ≤
      ((N ⊓ M).subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) := by
  set O := primeComplementCore (G := N) p with hO
  obtain ⟨D, hDU, rfl⟩ : ∃ D ≤ U.subgroupOf N, D.map (QuotientGroup.mk' O) = Dbar :=
    ⟨_, inf_le_right, map_comap_inf_eq _ hD⟩
  have hDp : IsPGroup p D := hU.comap_subtype.to_le hDU
  have hDG : D.map N.subtype ≤ U := by
    refine (Subgroup.map_mono hDU).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hUN]
  have hD1' : D.map N.subtype ≠ ⊥ := by
    intro h
    apply hD1
    rw [(Subgroup.map_eq_bot_iff_of_injective D N.subtype_injective).mp h, Subgroup.map_bot]
  have hN := hnorm _ hDG hD1'
  have hNH : normalizer (D : Set N) ≤ (N ⊓ M).subgroupOf N := fun n hn =>
    Subgroup.mem_subgroupOf.mpr
      ⟨n.property, hN (Subgroup.le_normalizer_map N.subtype ⟨n, hn, rfl⟩)⟩
  exact le_map_of_comap_le (QuotientGroup.mk'_surjective O)
    ((comap_normalizer_map_le_sup hp O (primeComplementCore_coprime p) hDp).trans
      (sup_le hOM hNH))

theorem inf_eq_bot_of_coprime_of_isSimpleGroup {X : Type*} [Group X] [Finite X] (hp : p.Prime)
    (O : Subgroup X) [O.Normal] (hO : p.Coprime (Nat.card O)) {L : Subgroup X}
    (hL : IsSimpleGroup L) (hpL : p ∣ Nat.card L) : O ⊓ L = ⊥ := by
  rcases hL.eq_bot_or_eq_top_of_normal (O.subgroupOf L) with h | h
  · exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
  · exact absurd (Nat.Coprime.eq_one_of_dvd hO
      (hpL.trans (Subgroup.card_dvd_of_le (Subgroup.subgroupOf_eq_top.mp h)))) hp.one_lt.ne'

theorem nonempty_mulEquiv_map_mk_of_inf_eq_bot {X : Type*} [Group X] (O : Subgroup X) [O.Normal]
    {L : Subgroup X} (h : O ⊓ L = ⊥) : Nonempty (L ≃* L.map (QuotientGroup.mk' O)) := by
  refine ⟨MulEquiv.ofBijective ((QuotientGroup.mk' O).subgroupMap L)
    ⟨fun a b hab => ?_, (QuotientGroup.mk' O).subgroupMap_surjective L⟩⟩
  have h1 : QuotientGroup.mk' O (a : X) = QuotientGroup.mk' O (b : X) := congrArg Subtype.val hab
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  have h2 : (a : X)⁻¹ * b ∈ O ⊓ L := ⟨h1, L.mul_mem (L.inv_mem a.2) b.2⟩
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact Subtype.ext h2

theorem isSylowOf_map_mk_of_inf_eq_bot [Fact p.Prime] {U L : Subgroup G} (hLN : L ≤ N)
    (hUL : IsSylowOf p U L) (hinj : primeComplementCore (G := N) p ⊓ L.subgroupOf N = ⊥) :
    IsSylowOf p ((U.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)))
      ((L.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p))) := by
  set O := primeComplementCore (G := N) p with hO
  have hUN : U ≤ N := hUL.le.trans hLN
  obtain ⟨e⟩ := nonempty_mulEquiv_map_mk_of_inf_eq_bot O hinj
  have hU : Nat.card ((U.subgroupOf N).map (QuotientGroup.mk' O)) = Nat.card U := by
    rw [card_map_mk_of_isPGroup (T := U.subgroupOf N) Fact.out O (primeComplementCore_coprime p)
      hUL.isPGroup.comap_subtype]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv
  have hL : Nat.card ((L.subgroupOf N).map (QuotientGroup.mk' O)) = Nat.card L :=
    (Nat.card_congr e.toEquiv).symm.trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv)
  refine isSylowOf_of_card (Subgroup.map_mono fun u hu => hUL.le hu) ?_
  rw [hU, hL]
  exact hUL.card_eq

theorem map_mk_layer [Fact p.Prime] (hp5 : 5 ≤ p) {L U : Subgroup G} (hLN : L ≤ N)
    (e : L ≃* PSL(2, GaloisField p 2)) (hUL : IsSylowOf p U L) (hU : Nat.card U = p ^ 2) :
    primeComplementCore (G := N) p ⊓ L.subgroupOf N = ⊥ ∧
      Nonempty ((L.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ≃*
        PSL(2, GaloisField p 2)) ∧
      IsSylowOf p ((U.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)))
        ((L.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p))) := by
  have hK : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have : IsSimpleGroup PSL(2, GaloisField p 2) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; nlinarith)
  let eL : L.subgroupOf N ≃* PSL(2, GaloisField p 2) :=
    (Subgroup.subgroupOfEquivOfLe hLN).trans e
  have hpL : p ∣ Nat.card (L.subgroupOf N) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv]
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hUL.le)
    rw [hU]
    exact dvd_pow_self p two_ne_zero
  have hinj := inf_eq_bot_of_coprime_of_isSimpleGroup Fact.out _ (primeComplementCore_coprime p)
    eL.isSimpleGroup hpL
  obtain ⟨e₁⟩ := nonempty_mulEquiv_map_mk_of_inf_eq_bot _ hinj
  exact ⟨hinj, ⟨e₁.symm.trans eL⟩, isSylowOf_map_mk_of_inf_eq_bot hLN hUL hinj⟩

theorem isSylowOf_top_map_mk [Fact p.Prime] {U : Subgroup G} (hU : IsSylowOf p U N) :
    IsSylowOf p ((U.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p))) ⊤ := by
  obtain ⟨T, hT⟩ := hU.exists_sylow_eq_subgroupOf
  set S := T.mapSurjective (QuotientGroup.mk'_surjective (primeComplementCore (G := N) p))
  have hS : (S : Subgroup (N ⧸ primeComplementCore (G := N) p)) =
      (U.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) := by
    rw [Sylow.coe_mapSurjective, hT]
  rw [isSylowOf_iff, Subgroup.relIndex_top_right, ← hS]
  exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩

theorem coprime_card_map_of_isPGroup_two {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (hp : p.Prime) (hp2 : p ≠ 2) (f : X →* Y) {W : Subgroup X} (hW : IsPGroup 2 W) :
    Nat.Coprime p (Nat.card (W.map f)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hW.map f)
  rw [hn]
  exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right n

omit [Finite G] in
theorem map_subgroupOf_le_normalizer_map {Y : Type*} [Group Y] {U W : Subgroup G}
    (hUW : U ≤ normalizer (W : Set G)) (f : N →* Y) :
    (U.subgroupOf N).map f ≤ normalizer (((W.subgroupOf N).map f : Subgroup Y) : Set Y) := by
  refine le_trans (Subgroup.map_mono fun u hu => ?_) (Subgroup.le_normalizer_map f)
  rw [Subgroup.mem_normalizer_iff]
  intro w
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (hUW hu) w

end Quot

section QuotII

variable {p : ℕ} {N : Subgroup G}

theorem pRank_le_of_forall_isPGroup (hp : p.Prime) {k : ℕ}
    (h : ∀ Q : Subgroup G, IsPGroup p Q → CFSG.Open.pRank p Q ≤ k) (H : Subgroup G) :
    CFSG.Open.pRank p H ≤ k := by
  have : Fact p.Prime := ⟨hp⟩
  refine csSup_le' fun r hr => ?_
  obtain ⟨E, -, hE, hcard⟩ := hr
  exact (le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp E)
    ⟨E, le_rfl, hE, hcard⟩).trans (h E (IsPGroup.of_card hcard))

theorem pRank_top_quotient_le (hp : p.Prime) {k : ℕ}
    (h : ∀ Q : Subgroup G, IsPGroup p Q → CFSG.Open.pRank p Q ≤ k) :
    CFSG.Open.pRank p (⊤ : Subgroup (N ⧸ primeComplementCore (G := N) p)) ≤ k := by
  have h1 := pRank_map_mk_eq_pRank_map_subtype hp (primeComplementCore (G := N) p)
    (primeComplementCore_coprime p) ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
  rw [h1]
  exact pRank_le_of_forall_isPGroup hp h _

theorem isMulCommutative_sylow_quotient [Fact p.Prime]
    (h : ∀ Q : Subgroup G, IsPGroup p Q → IsMulCommutative Q)
    (S : Sylow p (N ⧸ primeComplementCore (G := N) p)) :
    IsMulCommutative (S : Subgroup (N ⧸ primeComplementCore (G := N) p)) := by
  obtain ⟨T, rfl⟩ := Sylow.mapSurjective_surjective
    (QuotientGroup.mk'_surjective (primeComplementCore (G := N) p)) p S
  have hT : IsMulCommutative ((T : Subgroup N).map N.subtype) := h _ (T.isPGroup'.map _)
  have hT' : IsMulCommutative (T : Subgroup N) := by
    have := Subgroup.comap_injective_isMulCommutative (H := (T : Subgroup N).map N.subtype)
      N.subtype_injective
    rwa [Subgroup.comap_map_eq_self_of_injective N.subtype_injective] at this
  rw [Sylow.coe_mapSurjective]
  infer_instance

omit [Finite G] in
theorem mk_mem_centralizer_map {O : Subgroup N} [O.Normal] {L : Subgroup G} {a : N}
    (ha : (a : G) ∈ centralizer (L : Set G)) :
    QuotientGroup.mk' O a ∈
      centralizer (((L.subgroupOf N).map (QuotientGroup.mk' O) : Subgroup (N ⧸ O)) :
        Set (N ⧸ O)) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨l, hl, rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext (mem_centralizer_iff.mp ha _ hl))

theorem centralizer_mk_le_map (hp : p.Prime) {a : N} (hao : orderOf a = p) :
    centralizer ({QuotientGroup.mk' (primeComplementCore (G := N) p) a} :
        Set (N ⧸ primeComplementCore (G := N) p)) ≤
      (centralizer ({a} : Set N)).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) := by
  set O := primeComplementCore (G := N) p with hO
  have ha : IsPGroup p (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
  intro y hy
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective O y
  have h1 : n ∈ (centralizer (((zpowers a).map (QuotientGroup.mk' O) : Subgroup (N ⧸ O)) :
      Set (N ⧸ O))).comap (QuotientGroup.mk' O) := by
    rw [Subgroup.mem_comap, MonoidHom.map_zpowers, zpowers_eq_closure, centralizer_closure]
    exact hy
  have h2 := Subgroup.mem_map_of_mem (QuotientGroup.mk' O)
    (comap_centralizer_map_le_sup hp O (primeComplementCore_coprime p) ha h1)
  rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' O).ge, bot_sup_eq,
    zpowers_eq_closure, centralizer_closure] at h2

theorem exists_perfect_le_map_eq {H Q : Type*} [Group H] [Finite H] [Group Q] (f : H →* Q)
    {K : Subgroup H} {J : Subgroup Q} (hJK : J ≤ K.map f) (hJ : ⁅J, J⁆ = J) :
    ∃ A ≤ K, A.map f = J ∧ ⁅A, A⁆ = A := by
  obtain ⟨A, -, hA⟩ := Finite.exists_le_minimal
    (p := fun A : Subgroup H => A ≤ K ∧ A.map f = J) (a := J.comap f ⊓ K)
    ⟨inf_le_right, map_comap_inf_eq f hJK⟩
  refine ⟨A, hA.prop.1, hA.prop.2, ?_⟩
  have hle : ⁅A, A⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
  refine le_antisymm hle (hA.le_of_le ⟨hle.trans hA.prop.1, ?_⟩ hle)
  rw [Subgroup.map_commutator, hA.prop.2, hJ]

theorem perfect_le_map_mk (hp : p.Prime) {a : N} (hao : orderOf a = p) {L : Subgroup G}
    (hperf : ∀ J : Subgroup G, J ≤ centralizer ({(a : G)} : Set G) → ⁅J, J⁆ = J → J ≤ L)
    (J : Subgroup (N ⧸ primeComplementCore (G := N) p))
    (hJ : J ≤ centralizer ({QuotientGroup.mk' (primeComplementCore (G := N) p) a} :
      Set (N ⧸ primeComplementCore (G := N) p))) (hJp : ⁅J, J⁆ = J) :
    J ≤ (L.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) := by
  obtain ⟨A, hAC, rfl, hAp⟩ :=
    exists_perfect_le_map_eq _ (hJ.trans (centralizer_mk_le_map hp hao)) hJp
  refine Subgroup.map_mono fun c hc => ?_
  refine hperf (A.map N.subtype) ?_ (by rw [← Subgroup.map_commutator, hAp]) ⟨c, hc, rfl⟩
  rintro _ ⟨d, hd, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
    (mem_centralizer_singleton_iff.mp (hAC hd)))

theorem centralizer_mk_le_normalizer_map (hp : p.Prime) {a : N} (hao : orderOf a = p)
    {L : Subgroup G} (hCL : centralizer ({(a : G)} : Set G) ≤ normalizer (L : Set G)) :
    centralizer ({QuotientGroup.mk' (primeComplementCore (G := N) p) a} :
        Set (N ⧸ primeComplementCore (G := N) p)) ≤
      normalizer (((L.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) :
        Subgroup (N ⧸ primeComplementCore (G := N) p)) :
          Set (N ⧸ primeComplementCore (G := N) p)) := by
  refine (centralizer_mk_le_map hp hao).trans (le_trans (Subgroup.map_mono fun c hc => ?_)
    (Subgroup.le_normalizer_map _))
  have hcG : (c : G) ∈ normalizer (L : Set G) := hCL (mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)))
  rw [Subgroup.mem_normalizer_iff]
  intro l
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp hcG l

theorem commutator_mem_rankThreePrimeCore {W L : Subgroup G} (hWN : W ≤ N) (hLN : L ≤ N)
    (h : (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ≤
      centralizer (((L.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) :
        Subgroup (N ⧸ primeComplementCore (G := N) p)) :
          Set (N ⧸ primeComplementCore (G := N) p))) :
    ∀ w ∈ W, ∀ l ∈ L, w⁻¹ * (l⁻¹ * w * l) ∈ rankThreePrimeCore p N := by
  intro w hw l hl
  have hc := mem_centralizer_iff.mp (h ⟨⟨w, hWN hw⟩, hw, rfl⟩) _ ⟨⟨l, hLN hl⟩, hl, rfl⟩
  refine mem_rankThreePrimeCore_of_mk_eq_one (N.mul_mem (N.inv_mem (hWN hw))
    (N.mul_mem (N.mul_mem (N.inv_mem (hLN hl)) (hWN hw)) (hLN hl))) ?_
  have he : (⟨w⁻¹ * (l⁻¹ * w * l), N.mul_mem (N.inv_mem (hWN hw))
      (N.mul_mem (N.mul_mem (N.inv_mem (hLN hl)) (hWN hw)) (hLN hl))⟩ : N) =
      (⟨w, hWN hw⟩ : N)⁻¹ * ((⟨l, hLN hl⟩ : N)⁻¹ * ⟨w, hWN hw⟩ * ⟨l, hLN hl⟩) := rfl
  rw [he, map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ _ (QuotientGroup.mk' _ _), ← hc,
    inv_mul_cancel_left, inv_mul_cancel]

theorem weaklyClosed_map_mk [Fact p.Prime] {a : N} (hao : orderOf a = p)
    (hab : ∀ S : Sylow p (N ⧸ primeComplementCore (G := N) p),
      IsMulCommutative (S : Subgroup (N ⧸ primeComplementCore (G := N) p)))
    (hweak : ∀ Q : Sylow p G, (a : G) ∈ (Q : Subgroup G) → ∀ g : G,
      (zpowers (a : G)).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup G) →
        (zpowers (a : G)).map (MulAut.conj g).toMonoidHom = zpowers (a : G))
    (Q : Sylow p (N ⧸ primeComplementCore (G := N) p))
    (haQ : QuotientGroup.mk' (primeComplementCore (G := N) p) a ∈
      (Q : Subgroup (N ⧸ primeComplementCore (G := N) p)))
    (g : N ⧸ primeComplementCore (G := N) p)
    (hg : (zpowers (QuotientGroup.mk' (primeComplementCore (G := N) p) a)).map
      (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup (N ⧸ primeComplementCore (G := N) p))) :
    (zpowers (QuotientGroup.mk' (primeComplementCore (G := N) p) a)).map
        (MulAut.conj g).toMonoidHom =
      zpowers (QuotientGroup.mk' (primeComplementCore (G := N) p) a) := by
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := N) p) g
  set O := primeComplementCore (G := N) p with hO
  have hcQ : QuotientGroup.mk' O g₁ * QuotientGroup.mk' O a * (QuotientGroup.mk' O g₁)⁻¹ ∈
      (Q : Subgroup (N ⧸ O)) := hg ⟨_, mem_zpowers _, rfl⟩
  set K : Subgroup N := (Q : Subgroup (N ⧸ O)).comap (QuotientGroup.mk' O) with hK
  have haK : (a : G) ∈ K.map N.subtype := ⟨a, haQ, rfl⟩
  have ha'K : (g₁ : G) * a * (g₁ : G)⁻¹ ∈ K.map N.subtype :=
    ⟨g₁ * a * g₁⁻¹, by simpa only [hK, SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv]
      using hcQ, rfl⟩
  have hpa : IsPGroup p (zpowers (a : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hao, pow_one])
  have hpa' : IsPGroup p (zpowers ((g₁ : G) * a * (g₁ : G)⁻¹)) := by
    have := hpa.map (MulAut.conj (g₁ : G)).toMonoidHom
    rwa [MonoidHom.map_zpowers] at this
  obtain ⟨T₁, hT₁⟩ := (hpa.comap_subtype (K := K.map N.subtype)).exists_le_sylow
  obtain ⟨T₂, hT₂⟩ := (hpa'.comap_subtype (K := K.map N.subtype)).exists_le_sylow
  set S₁ : Subgroup G := (T₁ : Subgroup (K.map N.subtype)).map (K.map N.subtype).subtype
  set S₂ : Subgroup G := (T₂ : Subgroup (K.map N.subtype)).map (K.map N.subtype).subtype
  have hS₁ : IsSylowOf p S₁ (K.map N.subtype) := ⟨T₁, rfl⟩
  have hS₂ : IsSylowOf p S₂ (K.map N.subtype) := ⟨T₂, rfl⟩
  have h₁ : zpowers (a : G) ≤ S₁ := fun y hy => ⟨⟨y, zpowers_le.mpr haK hy⟩, hT₁ hy, rfl⟩
  have h₂ : zpowers ((g₁ : G) * a * (g₁ : G)⁻¹) ≤ S₂ := fun y hy =>
    ⟨⟨y, zpowers_le.mpr ha'K hy⟩, hT₂ hy, rfl⟩
  obtain ⟨k, hkK, hk⟩ := hS₁.exists_mem_conj hS₂
  have hk1 : k⁻¹ * ((g₁ : G) * a * (g₁ : G)⁻¹) * k ∈ S₁ := (hk _).mp (h₂ (mem_zpowers _))
  obtain ⟨Q₀, hQ₀⟩ := hS₁.isPGroup.exists_le_sylow
  have hconj : (MulAut.conj (k⁻¹ * (g₁ : G))).toMonoidHom (a : G) =
      k⁻¹ * ((g₁ : G) * a * (g₁ : G)⁻¹) * k := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hw := hweak Q₀ (hQ₀ (h₁ (mem_zpowers _))) (k⁻¹ * g₁) (by
    rw [MonoidHom.map_zpowers, zpowers_le, hconj]
    exact hQ₀ hk1)
  have hmem : k⁻¹ * ((g₁ : G) * a * (g₁ : G)⁻¹) * k ∈ zpowers (a : G) := by
    rw [← hconj, ← hw]
    exact Subgroup.mem_map_of_mem _ (mem_zpowers _)
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hmem
  obtain ⟨kN, hkN, rfl⟩ := hkK
  have hmN : kN⁻¹ * (g₁ * a * g₁⁻¹) * kN = a ^ m := Subtype.ext (by simpa using hm.symm)
  have : IsMulCommutative (Q : Subgroup (N ⧸ O)) := hab Q
  have hkQ : QuotientGroup.mk' O kN ∈ (Q : Subgroup (N ⧸ O)) := hkN
  have hcomm := setLike_mul_comm hkQ hcQ
  have hcm : QuotientGroup.mk' O g₁ * QuotientGroup.mk' O a * (QuotientGroup.mk' O g₁)⁻¹ =
      QuotientGroup.mk' O a ^ m := by
    have h := congrArg (QuotientGroup.mk' O) hmN
    rwa [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow, mul_assoc, ← hcomm,
      inv_mul_cancel_left] at h
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [MonoidHom.map_zpowers, zpowers_le]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hcm]
    exact zpow_mem (mem_zpowers _) m
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]

end QuotII

section Sections

theorem notSecExcl3_of_mulEquiv_section {X Q : Type} [Group X] [Group Q]
    (hX : NoExcludedSection3 X) (H₀ : Subgroup X) (N₀ : Subgroup H₀) [N₀.Normal]
    (e : H₀ ⧸ N₀ ≃* Q) (K : Subgroup Q) (hK : CFSG.Open.IsQuasisimple K) :
    NotSecExcl3 (K ⧸ center K) := by
  let φ := e.symm.subgroupMap K
  exact notSecExcl3_of_mulEquiv (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ))
    (hX H₀ N₀ _ (CFSG.ComponentClassification.Components.quasisimple_of_equiv φ.symm hK))

omit [Finite G] in
theorem noExcludedSection3_quotient (hG : NoExcludedSection3 G) (N : Subgroup G)
    (O : Subgroup N) [O.Normal] : NoExcludedSection3 (N ⧸ O) := by
  intro H N' _ K hK
  let H₀ : Subgroup G := (H.comap (QuotientGroup.mk' O)).map N.subtype
  let ι := (H.comap (QuotientGroup.mk' O)).equivMapOfInjective N.subtype N.subtype_injective
  let ψ : H₀ →* H ⧸ N' := (QuotientGroup.mk' N').comp
    (((QuotientGroup.mk' O).subgroupComap H).comp ι.symm.toMonoidHom)
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective N').comp
    (((QuotientGroup.mk' O).subgroupComap_surjective H (QuotientGroup.mk'_surjective O)).comp
      ι.symm.surjective)
  exact notSecExcl3_of_mulEquiv_section hG H₀ ψ.ker
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ) K hK

end Sections

end CFSG.LocalAnalysis.RankThreeTheoremC
