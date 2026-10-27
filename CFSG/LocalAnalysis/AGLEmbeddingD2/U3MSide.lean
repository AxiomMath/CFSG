module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Blocks
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisTools
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreHeis
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

open scoped commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

namespace CFSG.AGLEmbeddingD2

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem card_barM_of_isPGroup (h : AGLPair p M H R) {U : Subgroup G} (hUM : U ≤ M)
    (hU : IsPGroup p U) : Nat.card (barM M U) = Nat.card U :=
  CFSG.AGLEmbedding.card_barM_of_isPGroup h.prime h.ne_two hUM hU

theorem pow_notMem_normalizer_barM_of_le (h : AGLPair p M H R) {U Z : Subgroup G} (hUM : U ≤ M)
    (hU : IsPGroup p U) (hZU : Z ≤ U) {t : G} (htM : t ∈ M)
    (htU : t ∈ Subgroup.normalizer (U : Set G)) {m : ℕ}
    (horb : ∀ k, 0 < k → k < m → ∀ F : Subgroup G, Z ≤ F → F ≤ U → F.relIndex U = p →
      t ^ k ∉ Subgroup.normalizer (F : Set G))
    {k : ℕ} (hk0 : 0 < k) (hkm : k < m) {F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hZF : barM M Z ≤ F) (hFU : F ≤ barM M U) (hidx : F.relIndex (barM M U) = p) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ^ k ∉ Subgroup.normalizer (F : Set _) := by
  intro hgF
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have htk : mk ⟨t, htM⟩ ^ k = mk ⟨t ^ k, M.pow_mem htM k⟩ := by
    rw [← map_pow]
    rfl
  rw [htk] at hgF
  set F₁ : Subgroup G := U ⊓ (F.comap mk).map M.subtype with hF₁
  have hgF₁ : t ^ k ∈ Subgroup.normalizer (F₁ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.pow_mem _ htU k,
      Subgroup.le_normalizer_map M.subtype
        (Subgroup.mem_map_of_mem _ (Subgroup.le_normalizer_comap mk hgF))⟩
  have hmem : ∀ (x : G) (hx : x ∈ U), x ∈ F₁ ↔ mk ⟨x, hUM hx⟩ ∈ F := by
    intro x hx
    refine ⟨fun h => ?_, fun h => ⟨hx, ⟨x, hUM hx⟩, h, rfl⟩⟩
    obtain ⟨m, hm, hmx⟩ := h.2
    have : m = ⟨x, hUM hx⟩ := Subtype.ext hmx
    rw [← this]
    exact hm
  have hF₁U : F₁ ≤ U := inf_le_left
  have hZF₁ : Z ≤ F₁ := fun z hz => (hmem z (hZU hz)).mpr
    (hZF (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hz)))
  have hbar : barM M F₁ = F := by
    refine le_antisymm ?_ fun σ hσ => ?_
    · rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
      exact (hmem x (hF₁U (Subgroup.mem_subgroupOf.mp hx))).mp (Subgroup.mem_subgroupOf.mp hx)
    · obtain ⟨⟨x, hxM⟩, hx, rfl⟩ := hFU hσ
      exact ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr
        ((hmem x (Subgroup.mem_subgroupOf.mp hx)).mpr hσ), rfl⟩
  have hcard : Nat.card F₁ = Nat.card F := by
    rw [← hbar]
    exact (h.card_barM_of_isPGroup (hF₁U.trans hUM) (hU.to_le hF₁U)).symm
  have hrel : F₁.relIndex U = p := by
    have h1 := Subgroup.relIndex_mul_card F (barM M U)
    have h2 := Subgroup.relIndex_mul_card F₁ U
    rw [inf_eq_left.mpr hFU, hidx, h.card_barM_of_isPGroup hUM hU] at h1
    rw [inf_eq_left.mpr hF₁U, hcard] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h2.trans h1.symm)
  exact horb k hk0 hkm F₁ hZF₁ hF₁U hrel hgF₁

end AGLPair

section Preimage

variable {G : Type} [Group G] {p : ℕ} {M : Subgroup G}

theorem le_pCorePreimage_of_barM_le {X : Subgroup G} (hXM : X ≤ M)
    (hX : barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)) : X ≤ pCorePreimage p M :=
  fun x hx => ⟨⟨x, hXM hx⟩, hX (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)), rfl⟩

theorem barM_sup_twoCore {Z : Subgroup G} (hZM : Z ≤ M) :
    barM M (Z ⊔ pCoreOf 2 M) = barM M Z := by
  have hQM : pCoreOf 2 M ≤ M := pCoreOf_le 2 M
  have hQ : barM M (pCoreOf 2 M) = ⊥ := by
    rw [barM, Subgroup.map_eq_bot_iff]
    intro q hq
    exact (mk_eq_one_iff_coe_mem_pCoreOf q).mpr (Subgroup.mem_subgroupOf.mp hq)
  unfold barM at hQ ⊢
  rw [Subgroup.subgroupOf_sup hZM hQM, Subgroup.map_sup, hQ, sup_bot_eq]

end Preimage

namespace D2HeisDataCore

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R Z : Subgroup G}

theorem Z_le_R (h : D2HeisDataCore p M H R Z) : Z ≤ R :=
  h.heis.2.1 ▸ Subgroup.commutator_le_self R

theorem Z_le_M (h : D2HeisDataCore p M H R Z) : Z ≤ M :=
  h.Z_le_R.trans h.pair.le_M

theorem conj_mem_Z (h : D2HeisDataCore p M H R Z) {g : G} (hg : ∀ x ∈ R, g * x * g⁻¹ ∈ R) :
    ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
  intro z hz
  rw [← h.heis.2.1] at hz ⊢
  have hmap : (⁅R, R⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ ⁅R, R⁆ := by
    rw [Subgroup.map_commutator]
    have hR : R.map (MulAut.conj g).toMonoidHom ≤ R := by
      rintro _ ⟨x, hx, rfl⟩
      exact hg x hx
    exact Subgroup.commutator_mono hR hR
  exact hmap ⟨z, hz, by simp [MulAut.conj_apply]⟩

theorem mul_comm_of_mem_Z (h : D2HeisDataCore p M H R Z) : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z := by
  have hp : p.Prime := h.pair.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent R := h.pair.isPGroup_R.isNilpotent
  have hZR := h.Z_le_R
  set Z' : Subgroup R := Z.subgroupOf R with hZ'
  have hZ'n : Z'.Normal := ⟨fun n hn g => by
    show ((g * n * g⁻¹ : R) : G) ∈ Z
    have : ((g * n * g⁻¹ : R) : G) = (g : G) * (n : G) * (g : G)⁻¹ := rfl
    rw [this]
    exact h.conj_mem_Z (fun x hx => R.mul_mem (R.mul_mem g.2 hx) (R.inv_mem g.2)) _ hn⟩
  have hcard : Nat.card Z' = p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv).trans h.heis.1
  have hZ'ne : Z' ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    exact hp.one_lt.ne hcard
  have hint := Group.IsNilpotent.inf_center_ne_bot_of_normal hZ'ne
  have hdvd : Nat.card (Z' ⊓ Subgroup.center R : Subgroup R) ∣ p :=
    hcard ▸ Subgroup.card_dvd_of_le inf_le_left
  have hle : Z' ⊓ Subgroup.center R = Z' := by
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hint
    · exact Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hcard])
  intro z hz r hr
  have hzc : (⟨z, hZR hz⟩ : R) ∈ Z' ⊓ Subgroup.center R := by
    rw [hle]
    exact Subgroup.mem_subgroupOf.mpr hz
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc.2 ⟨r, hr⟩)).symm

theorem card_barM_Z (h : D2HeisDataCore p M H R Z) : Nat.card (barM M Z) = p := by
  rw [h.pair.card_barM_of_isPGroup h.Z_le_M (h.pair.isPGroup_R.to_le h.Z_le_R)]
  exact h.heis.1

theorem commutator_barM (h : D2HeisDataCore p M H R Z) : ⁅barM M R, barM M R⁆ = barM M Z := by
  have h1 : ⁅R.subgroupOf M, R.subgroupOf M⁆ = Z.subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h.pair.le_M, h.heis.2.1,
      Subgroup.map_subgroupOf_eq_of_le h.Z_le_M]
  unfold barM
  rw [← Subgroup.map_commutator, h1]

theorem pow_barM (h : D2HeisDataCore p M H R Z) : ∀ r ∈ barM M R, r ^ p = 1 := by
  rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
  have hxp := h.heis.2.2 x (Subgroup.mem_subgroupOf.mp hx)
  have h1 : (⟨x, hxM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hxp)
  rw [← map_pow, h1, map_one]

theorem lines_barM (h : D2HeisDataCore p M H R Z) :
    ∃ t : ↥M ⧸ CFSG.pCore 2 ↥M,
      t ∈ Subgroup.normalizer (barM M R : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      ∃ m lam : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧
      (∀ x ∈ barM M R, ∃ z ∈ barM M Z, t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
      ∀ k : ℕ, 0 < k → k < m →
        ∀ F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), barM M Z ≤ F → F ≤ barM M R →
          F.relIndex (barM M R) = p → t ^ k ∉ Subgroup.normalizer (F : Set _) := by
  obtain ⟨t, htK, htN, m, lam, -, hm, hlam, -, hscal, -, hline⟩ := h.lines
  have htM : t ∈ M := htK.2
  refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩, mem_normalizer_barM htM htN, m, lam, hm,
    hlam, ?_, fun k hk0 hkm F hZF hFR hidx => ?_⟩
  · rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
    obtain ⟨z, hz, hxz⟩ := hscal x (Subgroup.mem_subgroupOf.mp hx)
    have hzM : z ∈ M := h.Z_le_M hz
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hz), ?_⟩
    have h1 : (⟨t, htM⟩ : M) ^ m * ⟨x, hxM⟩ * ((⟨t, htM⟩ : M) ^ m)⁻¹ =
        ⟨x, hxM⟩ ^ lam * ⟨z, hzM⟩ := Subtype.ext (by simpa using hxz)
    simpa only [map_mul, map_inv, map_pow] using congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) h1
  · exact h.pair.pow_notMem_normalizer_barM_of_le h.pair.le_M h.pair.isPGroup_R h.Z_le_R htM htN
      hline hk0 hkm hZF hFR hidx

theorem false_of_oddCore_not_centralized (h : D2HeisDataCore p M H R Z) (hD1 : D1For G)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) (hp5 : 5 ≤ p) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hsp : s ≠ p)
    (hns : ¬ barM M R ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)) :
    False := by
  have hp : p.Prime := h.pair.prime
  have := Fact.mk hs
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  obtain ⟨t, htR, m, lam, hm, hlam, hscal, hline⟩ := h.lines_barM
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  have hrank : 4 ≤ Open.pRank s Sg :=
    stmtOddCoreRankHeis hs hs2 hp hp5 hm hsp Sg (barM M R) (barM M Z) t lam
      CFSG.pCore_isPGroup (le_top.trans hSgN) h.card_barM_Z h.commutator_barM h.pow_barM
      (hSgN (Subgroup.mem_top _)) htR hlam hscal hline hns
  have hSgK : Sg ≤ barM M (H ⊓ M) :=
    h.pair.le_barM_inf_of_le_centralizer
      ((pCore_le_pPrimeCore_two hs hs2).trans (h.pair.oddCore_le_centralizer h84 hD2))
  have h4 : 4 ≤ Open.pRank s (H ⊓ M) :=
    hrank.trans ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono s hs hSgK).trans
      (pRank_barM_le hs hs2 M (H ⊓ M) inf_le_right))
  exact h.pair.false_of_four_le_pRank hD1 hs hs2 h4

theorem le_centralizer_oddCore (h : D2HeisDataCore p M H R Z) (hD1 : D1For G)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) (hp5 : 5 ≤ p) : ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p →
      barM M R ≤ Subgroup.centralizer
        ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) :=
  fun _ hs hs2 hsp => by_contra fun hns =>
    h.false_of_oddCore_not_centralized hD1 h84 hD2 hp5 hs hs2 hsp hns

theorem pCore_eq_bot_or_le (h : D2HeisDataCore p M H R Z) (h84 : Asc81bEightFour)
    (hD2 : NoXBlockFor G) :
    CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ ∨
      barM M Z ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
  have : Fact p.Prime := ⟨h.pair.prime⟩
  exact h.pair.toTwoLocalPhaseThree.pCore_eq_bot_or_le h.pair.isKGroup.1 h.pair.ne_two
    h.normal_dichotomy h84 hD2

theorem le_pCore_of_le_centralizer_pCore (h : D2HeisDataCore p M H R Z) (hD1 : D1For G)
    (hp5 : 5 ≤ p) (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G)
    (hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M R ≤ Subgroup.centralizer (Lbar : Set _))
    (hcp : barM M R ≤ Subgroup.centralizer
      ((CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)) :
    barM M R ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
  have hRp : IsPGroup p (barM M R) := h.pair.isPGroup_R.comap_subtype.map _
  refine le_pCore_of_le_centralizer_components hRp hcomp fun l hl => ?_
  by_cases hl2 : l = 2
  · rw [hl2, pCore_quotient_pCore_eq_bot']
    exact Subgroup.le_centralizer_iff.mp bot_le
  by_cases hlp : l = p
  · rw [hlp]
    exact hcp
  exact h.le_centralizer_oddCore hD1 h84 hD2 hp5 l hl hl2 hlp

theorem le_pCore_of_components (h : D2HeisDataCore p M H R Z) (hD1 : D1For G) (hp5 : 5 ≤ p)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G)
    (hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M R ≤ Subgroup.centralizer (Lbar : Set _)) :
    barM M R ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
  have hcen := h.le_pCore_of_le_centralizer_pCore hD1 hp5 h84 hD2 hcomp
  rcases h.pCore_eq_bot_or_le h84 hD2 with hOp | hZb
  · refine hcen ?_
    rw [hOp]
    exact Subgroup.le_centralizer_iff.mp bot_le
  · have hZY : Z ≤ pCorePreimage p M := le_pCorePreimage_of_barM_le h.Z_le_M hZb
    rcases h.irred (R ⊓ pCorePreimage p M) (le_inf h.Z_le_R hZY) inf_le_left
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hg.2, le_normalizer_pCorePreimage p M hg.1.2⟩) with hV | hV
    · have hYeq : pCorePreimage p M = Z ⊔ pCoreOf 2 M := by
        have := h.pair.inf_sup_twoCore_eq h84 hD2
        rw [hV] at this
        exact this.symm
      have hbar : CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) = barM M Z := by
        rw [← barM_sup_twoCore h.Z_le_M, ← hYeq]
        exact (barM_preimage _).symm
      refine hcen ?_
      rw [hbar]
      intro x hxR
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨⟨z, hzM⟩, hz, rfl⟩
      obtain ⟨⟨x, hxM⟩, hx, rfl⟩ := hxR
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (h.mul_comm_of_mem_Z z (Subgroup.mem_subgroupOf.mp hz) x
        (Subgroup.mem_subgroupOf.mp hx)))
    · exact barM_le_of_le_preimage (inf_eq_left.mp hV)

theorem normal_sup_of_components (h : D2HeisDataCore p M H R Z) (hD1 : D1For G) (hp5 : 5 ≤ p)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G)
    (hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M R ≤ Subgroup.centralizer (Lbar : Set _)) :
    ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal :=
  h.pair.normal_sup_of_le_pCore h84 hD2 (h.le_pCore_of_components hD1 hp5 h84 hD2 hcomp)

end D2HeisDataCore

theorem D2Escape.normal_sup_of_u3 {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {M A H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKU : UnitaryBorelKFacts)
    (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hglob : AGLGlobal G) (hD1 : D1For G) (hD2G : NoXBlockFor G) (hesc : D2Escape p P M A H R)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1)
    (e : K ≃* CatGroup d) (hp5 : 5 ≤ p) : ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal := by
  have hdata := hesc.heisData_of_u3 hKU hglob hRbar hK hd hn e
  have hRK : (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ≤ K := by
    rw [← hRbar]
    exact hK.sylow_le_of_u3 hd hn e
  refine hdata.normal_sup_of_components hD1 hp5 h84 hD2G fun Lbar hLbar => ?_
  obtain ⟨L, hL2, hbar, hL⟩ := hdata.pair.exists_weakSBlock_or_le_inf hLbar
  rw [← hbar]
  rcases hL with hblock | hle
  · exact hdata.barM_le_centralizer_of_weakSBlock hD1 h84 h85 h86 h93 hD2G hK2 hC3 hK5 hKin hKP
      hC3p hK5p hp5 hblock
  · exact hesc.barM_le_centralizer_of_le_inf_of_simple hdata.pair hdata.perfect_le hK le_rfl hRK
      hD1 hp5 hα hSch hL2 hle

@[expose] def D2U3MSide : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (P : Sylow p G) (M A H R : Subgroup G),
      D2Escape p P M A H R → D2EscapeMax p P M R → p ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      ∀ d : TauCeti.ValidLieTypeIndex, IsUnitaryIndex p d → d.1.fieldExponent = 1 →
      Nonempty (K ≃* CatGroup d) → ((R ⊔ pCoreOf 2 M).subgroupOf M).Normal

theorem d2U3MSide_of (hKU : UnitaryBorelKFacts) (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime) : D2U3MSide := by
  intro G _ _ hglob hD1 p _ hp5 P M A H R hesc _ _ Rbar K hRbar hK d hd hn ⟨e⟩
  exact hesc.normal_sup_of_u3 hKU hα hSch h84 h85 h86 h93 hK2 hC3 hK5 hKin hKP hC3p hK5p
    hglob.toAGLGlobal hD1 (hD2.noXBlockFor hglob.toD1Global) hRbar hK hd hn e hp5

end CFSG.AGLEmbeddingD2
