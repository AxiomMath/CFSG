module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieceBlocksAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocksAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbPerf
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbLinTwoData
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBarM

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace SPLMSide

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem isClassicalTwoOrG2_of_isOrthogonalTwo {Y : Type} [Group Y] (h : IsOrthogonalTwo Y) :
    IsClassicalTwoOrG2 Y := by
  rcases h with ⟨d, ⟨m, q, hq, hd⟩, hY⟩ | hA
  · have hq2 : q.p = 2 := by
      have hqe : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq
      have h1 : q.p ∣ 2 := hqe ▸ dvd_pow_self q.p q.exponent_pos.ne'
      exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp h1
    refine Or.inl ⟨d, ?_, hY⟩
    rcases hd with hd | hd | ⟨-, hd⟩ <;> rw [hd] <;> exact hq2
  · exact Or.inr (Or.inl hA)

theorem isSPLBlockType_of_weakSBlock (h3 : D1PhaseThree p P M H R) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    IsSPLBlockType p (barM M L) := by
  have hq := hL.component.2.2
  have hperf : Group.IsPerfect ↥(barM M L) := ⟨hq.1⟩
  have hnab : ∃ a b : ↥(barM M L), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L)) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L)) b
    exact ⟨a', b', fun h' => hab (by rw [← map_mul, ← map_mul, h'])⟩
  have e₀ : Subgroup.center ↥(barM M L) = ⊥ →
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* ↥(barM M L)) := fun hZ =>
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩
  have halt : ∀ n : ℕ, Nonempty (↥(barM M L) ≃* alternatingGroup (Fin n)) →
      IsSPLBlockType p (barM M L) := by
    rintro n ⟨φ⟩
    obtain ⟨e⟩ := e₀ (center_eq_bot_of_mulEquiv_alternating hnab φ)
    exact Or.inr (Or.inl ⟨n, ⟨e.trans φ⟩⟩)
  rcases h3.nineThree h93 hL with h1 | h2 | h3' | h4 | h5 | h6 | h7 | h8
  · exact (hD2 G h3.glob M L h3.maxTwoLocal_M hL.le hL.subnormal h1).elim
  · exact Or.inl h2.1
  · obtain ⟨e⟩ := e₀ (center_eq_bot_of_isOrthogonalTwo hperf hnab h3'.2.1)
    exact Or.inl (isClassicalTwoOrG2_of_isOrthogonalTwo (IsOrthogonalTwo.of_mulEquiv e h3'.2.1))
  · exact Or.inr (Or.inl ⟨6, h4.2.2.1⟩)
  · exact halt 7 h5.2.1
  · obtain ⟨-, n, hn, -⟩ := h6
    exact Or.inr (Or.inl ⟨2 * n, hn⟩)
  · obtain ⟨-, n, hn, -⟩ := h7
    exact halt (4 * n) hn
  · obtain ⟨-, N, r, -, -, -, -, -, hN, -⟩ := h8
    exact halt N hN

theorem isSPLBlockType_of_le_inf (D : D1SPLPairData p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) (hle : L ≤ H ⊓ M) : IsSPLBlockType p (barM M L) := by
  have hp := D.data.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := D.data.cfg.red.ne_two
  have hD : ∀ T : Sylow p ↥K, SmallRankOneData p ↥K T := by
    intro T
    rcases D.family with h | ⟨rfl, h⟩
    · exact smallRankOneData_of_isSmallLinTwo hp2 h T
    · exact smallRankOneData_of_altSix h T
  obtain ⟨T₁, hT₁, -⟩ := D.data.exists_sylow
  have hLN : L ≤ d1PlusCore p H K :=
    le_d1PlusCore_of_map_le (hle.trans inf_le_left)
      (D.data.le_centralizer_of_perfect hT₁ (kFactUPrime_of_data hp hD) (hD T₁).outer
        (isSolvable_glbCore_of_data hp (hD T₁))
        (Subgroup.map_mono (Subgroup.subgroupOf_mono H hle))
        (commutator_map_eq_self (hle.trans inf_le_left) hL.perfect))
  let f : ↥(L.subgroupOf M) →* ↥(barM M L) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).subgroupMap (L.subgroupOf M)
  have hfs : Function.Surjective f := (QuotientGroup.mk' _).subgroupMap_surjective _
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥(L.subgroupOf M)) := inferInstance
  refine Or.inr (Or.inr ⟨Q.mapSurjective hfs, ?_⟩)
  set U : Subgroup G := ((Q : Subgroup _).map (L.subgroupOf M).subtype).map M.subtype
  have hUL : U ≤ L := by
    rintro _ ⟨_, ⟨q, -, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.mp q.2
  have hUp : IsPGroup p U := (Q.isPGroup'.map _).map _
  have : IsCyclic U := D.data.isCyclic_of_le_d1PlusCore (hUL.trans hLN) hUp
  let e : (Q : Subgroup ↥(L.subgroupOf M)) ≃* U :=
    ((Q : Subgroup _).equivMapOfInjective _ (L.subgroupOf M).subtype_injective).trans
      (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective)
  have : IsCyclic (Q : Subgroup ↥(L.subgroupOf M)) :=
    isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  rw [Sylow.coe_mapSurjective]
  exact isCyclic_of_surjective (f.subgroupMap Q) (f.subgroupMap_surjective Q)

end SPLMSide

theorem d1SPLPieceBlocks_of (hFi : KFactSPLNotFi22) (hUP : KFactUPrimeSmall)
    (hSTO : KFactSmallThreeOrders) (hKU2 : KFactUnitarySylowStructure)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (h93 : Asc81bNineThree) : D1SPLPieceBlocks := by
  intro G _ _ p P M H R Rbar K z D
  have hp := D.data.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := D.data.cfg.red.ne_two
  obtain ⟨h3, hXab, hXY, hYeq⟩ := SPLMSide.pairData_pCorePreimage_facts hFi hUP hSTO hKU2 h84
    hD2 D
  have hXM : d1LiftX p H R K ≤ M := hXY.trans (pCorePreimage_le p M)
  have hpc := SPLMSide.pCore_eq_barM_of_sup_eq hXM hYeq
  obtain ⟨hXel, hXcard⟩ := SPLMSide.isElemAbelian_card_liftX D hXab
  have hXp : IsPGroup p (d1LiftX p H R K) := D.data.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)
  refine ⟨hpc, isElemAbelian_barM hXel, (card_barM_of_isPGroup hp hp2 hXM hXp).trans hXcard,
    fun Λ hΛ x hx a ha => ?_, fun Λ hΛ φ hφ hc hpk => ?_,
    fun Λ hΛ => SPLMSide.isCatalogGroup_component_of_phaseThree h3 hΛ, fun Λ hΛ _ => ?_⟩
  · rw [← hpc] at hx
    exact SPLMSide.commute_of_mem_pCore_of_isComponent hΛ hx ha
  · rw [← hpc]
    exact SPLMSide.mem_pCore_of_mem_center_isComponent hΛ hφ hc hpk
  · obtain ⟨L, hL2, rfl, hw | hle⟩ :=
      h3.exists_weakSBlock_or_le_inf ((CFSG.isComponent_iff_open Λ).mp hΛ)
    · exact SPLMSide.isSPLBlockType_of_weakSBlock h3 h93 hD2 hw
    · exact SPLMSide.isSPLBlockType_of_le_inf D hL2 hle

end CFSG.AGLEmbedding
