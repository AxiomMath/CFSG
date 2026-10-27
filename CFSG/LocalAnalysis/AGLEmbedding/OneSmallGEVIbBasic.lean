module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem blockType_ib {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    (IsOrthogonalTwo ↥(barM M L) ∨ ∃ m : ℕ, Nonempty (↥(barM M L) ≃* alternatingGroup (Fin m)) ∨
        Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m))) ∨
      (IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
        IsParabolicTwo (barM M L) (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ∧
        barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≠ barM M L ∧
        ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsSylowTwoOf T (barM M L) →
          barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≠
            barM M L ⊓ Subgroup.normalizer (T : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := by
  have hn1 := h.nineThree_not_one h85 hD2 hL
  rcases h.nineThree h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hn1.1
  · exact Or.inr ⟨h2.1, h2.2.1, h.barM_ne_of_isWeakSBlock hL,
      ne_inf_normalizer_of_nineThreeTwo h2 (hn1.2 h2)⟩
  · exact Or.inl (Or.inl h3.2.1)
  · exact Or.inl (Or.inr ⟨6, Or.inr h4.2.2.1⟩)
  · exact Or.inl (Or.inr ⟨7, Or.inl h5.2.1⟩)
  · obtain ⟨-, n, he, -⟩ := h6
    exact Or.inl (Or.inr ⟨2 * n, Or.inr he⟩)
  · obtain ⟨-, n, he, -⟩ := h7
    exact Or.inl (Or.inr ⟨4 * n, Or.inl he⟩)
  · obtain ⟨-, N, r, -, -, -, -, -, he, -⟩ := h8
    exact Or.inl (Or.inr ⟨N, Or.inl he⟩)

omit [Finite G] in
theorem barM_inf_eq {M S L : Subgroup G} (hQS : pCoreOf 2 M ≤ S) :
    barM M (S ⊓ L) = barM M S ⊓ barM M L := by
  refine le_antisymm (le_inf (barM_mono inf_le_left) (barM_mono inf_le_right)) ?_
  rintro x ⟨⟨s, hs, rfl⟩, ⟨l, hl, hlx⟩⟩
  have hq : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (s⁻¹ * l) = 1 := by
    rw [map_mul, map_inv, hlx, inv_mul_cancel]
  have hqS : ((s⁻¹ * l : ↥M) : G) ∈ S := hQS (coe_mem_pCoreOf_two_of_mk_eq_one _ hq)
  have hlS : (l : G) ∈ S := by
    have h1 := S.mul_mem (Subgroup.mem_subgroupOf.mp hs) hqS
    simpa using h1
  exact ⟨l, Subgroup.mem_subgroupOf.mpr ⟨hlS, Subgroup.mem_subgroupOf.mp hl⟩, hlx⟩

theorem isSolvable_outer_of_component {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hSch : KFactCatalogSchreier) (hL : IsComponentOf L ⊤)
    (hcat : IsCatalogGroup (↥L ⧸ Subgroup.center ↥L)) : Group.IsSolvable (Outer ↥L) := by
  obtain ⟨-, -, hcomm, hsimp⟩ := hL
  have hperf : Group.IsPerfect ↥L := Group.isPerfect_def.2 hcomm
  have hnab : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hle : commutator ↥L ≤ Subgroup.center ↥L := by
      rw [commutator_def]
      refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (h _ _)
    have hZ : Subgroup.center ↥L = ⊤ := top_unique (hcomm ▸ hle)
    obtain ⟨a, b, hab⟩ := (hsimp.toNontrivial).exists_pair_ne
    apply hab
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    rw [QuotientGroup.eq, hZ]
    exact Subgroup.mem_top _
  have : Group.IsSolvable (Outer (↥L ⧸ Subgroup.center ↥L)) := hSch _ hsimp hnab hcat
  exact ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient ↥L

structure D1IbCore (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (z : G) : Prop where
  data : D1OneSmallData p P M H R Rbar K
  elt : D1SmallCZElt p H R K z
  b0 : D1CzB0 p R z
  cz_le : Subgroup.centralizer ({z} : Set G) ≤ H
  five_le : 5 ≤ p
  not_fi22 : ¬ (p = 5 ∧ IsFi22 K)
  phase : D1PhaseThree p P M H R
  dec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i
  exp : ∀ r ∈ R, r ^ p = 1
  perf : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
    ¬ p ^ 2 ∣ Nat.card V
  uniq : ∀ L₁ L₂ : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L₁ →
    IsWeakSBlock M (pCoreOf 2 H) L₂ → barM M L₁ = barM M L₂
  cover : ∃ U : Subgroup G, U ≤ H ⊓ M ∧ ⁅U, U⁆ = U ∧ z ∈ U

theorem D1IbConfig.toIbCore {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}
    (hc : D1IbConfig p P M H R Rbar K z) : D1IbCore p P M H R Rbar K z :=
  ⟨hc.data, hc.elt, hc.b0, hc.cz_le, hc.five_le, hc.not_fi22, hc.phase, hc.dec, hc.exp, hc.perf,
    hc.uniq, hc.cover⟩

theorem D1IbCore.toIbConfig {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}
    (hc : D1IbCore p P M H R Rbar K z)
    (hT : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)) = p ^ 2) : D1IbConfig p P M H R Rbar K z :=
  ⟨hc.data, hc.elt, hc.b0, hc.cz_le, hc.five_le, hc.not_fi22, hc.phase, hc.dec, hc.exp, hT, hc.perf,
    hc.uniq, hc.cover⟩

namespace D1IbCore

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem prime (hc : D1IbCore p P M H R Rbar K z) : p.Prime := hc.data.cfg.red.prime

theorem mem_M (hc : D1IbCore p P M H R Rbar K z) : z ∈ M := hc.phase.le_M hc.elt.1

theorem le_centralizer (hc : D1IbCore p P M H R Rbar K z) :
    R ≤ Subgroup.centralizer ({z} : Set G) :=
  hc.data.le_centralizer_czElt hc.elt

theorem coprime_twoCore (hc : D1IbCore p P M H R Rbar K z) :
    p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
  rw [hk]
  exact ((Nat.coprime_primes hc.prime Nat.prime_two).mpr hc.data.cfg.red.ne_two).pow_right k

theorem zbar_pow (hc : D1IbCore p P M H R Rbar K z) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ^ p = 1 := by
  have : (⟨z, hc.mem_M⟩ : M) ^ p = 1 :=
    Subtype.ext (by simp [← hc.elt.2.1, pow_orderOf_eq_one])
  rw [← map_pow, this, map_one]

theorem isPGroup_zpowers (hc : D1IbCore p P M H R Rbar K z) :
    IsPGroup p (Subgroup.zpowers z) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc.elt.2.1, pow_one])

theorem zbar_mem_normalizer (hc : D1IbCore p P M H R Rbar K z) (hB : D1IbBlockInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  mem_normalizer_barM hc.mem_M (hc.phase.mem_normalizer_block_of_five hc.data.cfg.ind hB.h85
    hB.h86 hB.h93 hB.hD2 hB.hK2 hB.hC3 hB.hK5 hc.five_le ⟨hc.elt.2.2.1, hc.mem_M⟩ hc.elt.2.1 hL)

theorem zbar_fixed_le (hc : D1IbCore p P M H R Rbar K z) (L : Subgroup G) :
    ∀ l ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * l *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩)⁻¹ = l →
      l ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) :=
  hc.phase.fixed_le_barM_normalizer_inf hc.prime hc.data.cfg.red.ne_two hc.mem_M
    hc.isPGroup_zpowers hc.cz_le

theorem zbar_not_mem_centralizer (hc : D1IbCore p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  intro hzc
  apply hc.phase.barM_ne_of_isWeakSBlock hL
  refine le_antisymm (barM_mono inf_le_right) fun l hl => hc.zbar_fixed_le L l hl ?_
  rw [← Subgroup.mem_centralizer_iff.mp hzc l hl, mul_inv_cancel_right]

theorem perf_block (hc : D1IbCore p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    IbPerfectSections p (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) := by
  intro V hV hVp
  refine hc.perf V (hV.trans (barM_mono ?_)) hVp
  rw [hc.phase.normalizer_twoCore_H]
  exact inf_le_inf_left H hL.le

theorem mem_normalizer_of_mem (hc : D1IbCore p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {n : G} (hnH : n ∈ H) (hnM : n ∈ M) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hnM⟩ ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hnS : n ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    rw [hc.phase.normalizer_twoCore_H]
    exact hnH
  have heq := hc.uniq _ _ (hL.map_conj hnM hnS) hL
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨m, hm, rfl⟩ := hx
  rw [← heq]
  have hmem : ⟨n, hnM⟩ * m * ⟨n, hnM⟩⁻¹ ∈
      (L.map (MulAut.conj n).toMonoidHom).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr ⟨(m : G), Subgroup.mem_subgroupOf.mp hm,
      by simp [MulAut.conj_apply]⟩
  exact ⟨_, hmem, by simp only [map_mul, map_inv]⟩

theorem mem_normalizer_of_commute (hc : D1IbCore p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {y : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hy : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * y) :
    y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  have hzMp : IsPGroup p (Subgroup.zpowers (⟨z, hc.mem_M⟩ : ↥M)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact hc.elt.2.1
  obtain ⟨g, hg, hgy⟩ := exists_mem_centralizer_mk_eq hp (CFSG.pCore 2 ↥M) hc.coprime_twoCore
    hzMp (Subgroup.mem_centralizer_singleton_iff.mpr hy)
  have hgz : (g : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
  rw [← hgy]
  exact hc.mem_normalizer_of_mem hL (hc.cz_le hgz) g.2

theorem exists_cover_block (hc : D1IbCore p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
      V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      V ≤ Subgroup.normalizer (barM M (pCoreOf 2 H ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈ V := by
  obtain ⟨U, hUHM, hUp, hzU⟩ := hc.cover
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hUM : U ≤ M := hUHM.trans inf_le_right
  set V := barM M U
  have hVp : ⁅V, V⁆ = V := by
    have h1 : ⁅U.subgroupOf M, U.subgroupOf M⁆ = U.subgroupOf M := by
      apply Subgroup.map_injective M.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUM, hUp]
    change ⁅(U.subgroupOf M).map mkM, (U.subgroupOf M).map mkM⁆ = (U.subgroupOf M).map mkM
    rw [← Subgroup.map_commutator, h1]
  have hVL : V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨u, hu, rfl⟩
    have huHM := hUHM (Subgroup.mem_subgroupOf.mp hu)
    exact hc.mem_normalizer_of_mem hL huHM.1 u.2
  have hVS : V ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨u, hu, rfl⟩
    have huHM := hUHM (Subgroup.mem_subgroupOf.mp hu)
    have huN : (u : G) ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
      rw [hc.phase.normalizer_twoCore_H]
      exact huHM.1
    exact mem_normalizer_barM u.2 huN
  have hinf := barM_inf_eq (L := L) (hc.phase.twoCore_M_le hc.phase.twoCore_inf)
  refine ⟨V, hVp, hVL, ?_, ⟨⟨z, hc.mem_M⟩, Subgroup.mem_subgroupOf.mpr hzU, rfl⟩⟩
  rw [hinf]
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxS, hxL⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hVS hv) x).mp hxS,
      (Subgroup.mem_normalizer_iff.mp (hVL hv) x).mp hxL⟩
  · rintro ⟨hxS, hxL⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hVS hv) x).mpr hxS,
      (Subgroup.mem_normalizer_iff.mp (hVL hv) x).mpr hxL⟩

theorem zbar_mem_sup (hc : D1IbCore p P M H R Rbar K z) (hB : D1IbBlockInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hN := hc.zbar_mem_normalizer hB hL
  obtain ⟨V, hVp, hVL, -, hzV⟩ := hc.exists_cover_block hL
  rcases blockType_ib hc.phase hB.h85 hB.h93 hB.hD2 hL with htype | ⟨hcl, -, -, -⟩
  · exact hB.hOP _ (barM M L) hL.component p hc.prime hc.five_le htype _ hN hc.zbar_pow
  rcases hcl with ⟨d, -, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩ | ⟨d, -, ⟨e⟩⟩
  · exact perfect_le_sup_centralizer_of_outer
      (isSolvable_outer_of_component hB.hSch hL.component ⟨_, ⟨e⟩⟩) hVp hVL hzV
  · exact hB.hOP _ (barM M L) hL.component p hc.prime hc.five_le (Or.inr ⟨n, Or.inr ⟨e⟩⟩) _
      hN hc.zbar_pow
  · exact perfect_le_sup_centralizer_of_outer
      (isSolvable_outer_of_component hB.hSch hL.component ⟨_, ⟨e⟩⟩) hVp hVL hzV

end D1IbCore

namespace D1IbConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem prime (hc : D1IbConfig p P M H R Rbar K z) : p.Prime :=
  hc.toIbCore.prime

theorem mem_M (hc : D1IbConfig p P M H R Rbar K z) : z ∈ M :=
  hc.toIbCore.mem_M

theorem le_centralizer (hc : D1IbConfig p P M H R Rbar K z) :
    R ≤ Subgroup.centralizer ({z} : Set G) :=
  hc.toIbCore.le_centralizer

theorem card_d1LiftX (hc : D1IbConfig p P M H R Rbar K z) :
    Nat.card (d1LiftX p H R K) = p ^ 2 ∧ z ∉ d1LiftX p H R K := by
  obtain ⟨hzT, hT⟩ := hc.data.d1LiftX_facts hc.elt
  exact ⟨hT.trans hc.card_T, hzT⟩

theorem coprime_twoCore (hc : D1IbConfig p P M H R Rbar K z) :
    p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) :=
  hc.toIbCore.coprime_twoCore

theorem zbar_pow (hc : D1IbConfig p P M H R Rbar K z) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ^ p = 1 :=
  hc.toIbCore.zbar_pow

theorem zbar_not_mem_centralizer (hc : D1IbConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  hc.toIbCore.zbar_not_mem_centralizer hL

theorem perf_block (hc : D1IbConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    IbPerfectSections p (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) :=
  hc.toIbCore.perf_block hL

theorem mem_normalizer_of_commute (hc : D1IbConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {y : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hy : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * y) :
    y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  hc.toIbCore.mem_normalizer_of_commute hL hy

theorem zbar_mem_sup (hc : D1IbConfig p P M H R Rbar K z) (hB : D1IbBlockInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  hc.toIbCore.zbar_mem_sup hB hL

end D1IbConfig

end CFSG.AGLEmbedding
