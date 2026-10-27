module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGTwoModel
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoBlock

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo

open CFSG.Open CFSG.AGLEmbedding CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement


theorem exists_mulEquiv_g2_of_isLieOf (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type}
    [Group Y] [Finite Y] (hY : Open.IsQuasisimple Y) (hodd : Odd (Nat.card (Subgroup.center Y)))
    (hG : IsLieOf IdxG2 (Y ⧸ Subgroup.center Y)) :
    ∃ f : ℕ, 2 ≤ f ∧ Nonempty (Y ≃* AdjointQuotient .G2 (GaloisField 2 f)) := by
  have : Group.IsPerfect Y := Group.isPerfect_def.mpr hY.1
  have hZ : Nat.card (Subgroup.center Y) = 1 := by
    obtain ⟨d, hPd, ⟨e⟩⟩ := hG
    obtain ⟨hd, hA, h2A⟩ := ToralCensus.rest_index (P := IdxG2) (Or.inr (Or.inr (Or.inr rfl))) hPd
    exact ToralCensus.card_center_eq_one_of_index hGA d hd hA h2A e hodd
  have e₂ : Y ≃* Y ⧸ Subgroup.center Y := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.eq_bot_of_card_eq _ hZ).symm)
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hG
  cases d with
  | G2 q =>
    change q.p = 2 at hd
    have hK : Nat.card (GaloisField 2 q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card 2 q.exponent q.exponent_pos.ne', hd]
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField 2 q.exponent) hK
    have hq3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hf : 2 ≤ q.exponent := by
      by_contra hf
      have : q.exponent = 1 := by have := q.exponent_pos; omega
      rw [TauCeti.PrimePower.card_def, hd, this] at hq3
      omega
    exact ⟨q.exponent, hf, ⟨e₂.trans (e.trans b.symm)⟩⟩
  | _ => exact hd.elim

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem commutator_mem_pCoreOf_of_eq_normalizer {G : Type} [Group G] [Finite G] {Y P : Subgroup G}
    (hPY : P ≤ Y) (e : ↥Y ≃* AdjointQuotient .G2 K) (T : Sylow 2 ↥Y)
    (hJ : P.subgroupOf Y = Subgroup.normalizer ((T : Subgroup ↥Y) : Set ↥Y)) {x y : G}
    (hx : x ∈ P) (hy : y ∈ P) : x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 P := by
  haveI : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 _
  have h := borelQuotient_g2 e
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient (g2Datum K) (weylElement .G2 K) (torus (τ := .G2) K) π'
      (Nat.card K - 1) :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT, ← hJ] at hNπ
  set T' : Subgroup G := (T : Subgroup ↥Y).map Y.subtype with hT'def
  have hT'P : T' ≤ P := by
    rintro _ ⟨t, ht, rfl⟩
    have : t ∈ P.subgroupOf Y := hJ ▸ Subgroup.le_normalizer ht
    exact Subgroup.mem_subgroupOf.1 this
  have hT'N : ∀ a ∈ P, ∀ n ∈ T', a * n * a⁻¹ ∈ T' := by
    rintro a ha _ ⟨t, ht, rfl⟩
    have haN : (⟨a, hPY ha⟩ : ↥Y) ∈ Subgroup.normalizer ((T : Subgroup ↥Y) : Set ↥Y) :=
      hJ ▸ Subgroup.mem_subgroupOf.2 ha
    exact ⟨_, (Subgroup.mem_normalizer_iff.1 haN t).1 ht, by simp⟩
  have hT'2 : IsPGroup 2 T' := T.isPGroup'.map Y.subtype
  have hT'O : T' ≤ CFSG.Open.pCoreOf 2 P := le_pCoreOf hT'P hT'N hT'2
  have hxJ : (⟨x, hPY hx⟩ : ↥Y) ∈ (borel (g2Datum K) (torus (τ := .G2) K)).map π' :=
    hNπ ▸ (Subgroup.mem_subgroupOf.2 hx : (⟨x, hPY hx⟩ : ↥Y) ∈ P.subgroupOf Y)
  have hyJ : (⟨y, hPY hy⟩ : ↥Y) ∈ (borel (g2Datum K) (torus (τ := .G2) K)).map π' :=
    hNπ ▸ (Subgroup.mem_subgroupOf.2 hy : (⟨y, hPY hy⟩ : ↥Y) ∈ P.subgroupOf Y)
  obtain ⟨b₁, hb₁, hb₁e⟩ := hxJ
  obtain ⟨b₂, hb₂, hb₂e⟩ := hyJ
  have hcomm : ⁅b₁, b₂⁆ ∈ posUnipotent (g2Datum K) :=
    CFSG.AGLEmbedding.LeviBlock.commutator_mem_of_mem_torus_sup
      ((le_sup_left (b := posUnipotent (g2Datum K))).trans
        (borel_le_normalizer_posUnipotent hQ.ct))
      (fun _ ha _ hb => hQ.torus_mul_comm ha hb) hb₁ hb₂
  have himg : π' ⁅b₁, b₂⁆ ∈ (T : Subgroup ↥Y) := hT ▸ ⟨_, hcomm, rfl⟩
  rw [map_commutatorElement, hb₁e, hb₂e] at himg
  apply hT'O
  refine ⟨_, himg, ?_⟩
  simp [commutatorElement_def]

theorem exists_node_of_parabolic {G : Type} [Group G] [Finite G] {Y P : Subgroup G}
    (e : ↥Y ≃* AdjointQuotient .G2 K) (hpar : IsParabolicTwo Y P) (hne : P ≠ Y)
    (hna : ∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ CFSG.Open.pCoreOf 2 P) :
    ∃ π' : ↥(adjointGroup .G2 K) →* ↥Y,
      BorelQuotient (g2Datum K) (weylElement .G2 K) (torus (τ := .G2) K) π' (Nat.card K - 1) ∧
      borel (g2Datum K) (torus (τ := .G2) K) ≤ (P.subgroupOf Y).comap π' ∧
      ∃ i, negIndices (g2Datum K) ((P.subgroupOf Y).comap π') = {i} := by
  obtain ⟨hPY, T, ⟨hTY, hT2, hTi⟩, hNP⟩ := hpar
  let T' : Sylow 2 ↥Y := (hT2.comap_subtype (K := Y)).toSylow hTi
  have hT'mem : ∀ t : ↥Y, t ∈ (T' : Subgroup ↥Y) ↔ (t : G) ∈ T := fun t => Iff.rfl
  have hNT : ∀ x : ↥Y, x ∈ Subgroup.normalizer ((T' : Subgroup ↥Y) : Set ↥Y) →
      (x : G) ∈ Y ⊓ Subgroup.normalizer (T : Set G) := fun x hx =>
    ⟨x.2, Subgroup.mem_normalizer_fintype fun t ht => by
      have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨t, hTY ht⟩).1 ((hT'mem _).2 ht)
      simpa [hT'mem] using h2⟩
  have hNJ : Subgroup.normalizer ((T' : Subgroup ↥Y) : Set ↥Y) ≤ P.subgroupOf Y :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hNP (hNT x hx))
  have hJN : P.subgroupOf Y ≠ Subgroup.normalizer ((T' : Subgroup ↥Y) : Set ↥Y) := by
    intro hJ
    obtain ⟨x, hx, y, hy, hxy⟩ := hna
    exact hxy (commutator_mem_pCoreOf_of_eq_normalizer hPY e T' hJ hx hy)
  have hJtop : P.subgroupOf Y ≠ ⊤ := by
    intro he
    refine hne (le_antisymm hPY fun l hl => ?_)
    have : (⟨l, hl⟩ : ↥Y) ∈ P.subgroupOf Y := he ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  exact CFSG.AGLEmbedding.LeviBlock.exists_single_node_g2 e T' hNJ hJN hJtop

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo
