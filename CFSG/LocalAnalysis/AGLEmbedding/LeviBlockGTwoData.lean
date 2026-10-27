module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeG2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTits
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeG2
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoNode
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2

public section

namespace CFSG.AGLEmbedding.LeviBlock

open CFSG.Open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.ToralCensus CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem ordA_one_eq_two_pow {f : ℕ} (hf : 1 ≤ f) :
    ordA 1 (2 ^ f) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have h1 : Nat.gcd (1 + 1) (2 ^ f - 1) = 1 := Nat.coprime_two_left.mpr
    (Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one)
  rw [ordA, h1, Nat.div_one]
  simp

theorem sl2Block_facts {k : Type} [Field k] [Finite k] [CharP k 2] (h4 : 4 ≤ Nat.card k)
    {S : Type} [Group S] (e : Matrix.SpecialLinearGroup (Fin 2) k ≃* S) :
    CFSG.Open.IsQuasisimple S ∧ Subgroup.center S = ⊥ ∧
      Nat.card S = Nat.card k * (Nat.card k ^ 2 - 1) := by
  have hZ := sl2_center_eq_bot (k := k)
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k) := sl2_isSimpleGroup h4
  have hq : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) k) :=
    ⟨(sl2_isPerfect h4).commutator_eq_top,
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  refine ⟨isQuasisimple_of_mulEquiv e hq, ?_, ?_⟩
  · rw [← map_center_mulEquiv e, hZ, Subgroup.map_bot]
  · rw [← Nat.card_congr e.toEquiv, card_sl2]

theorem exists_sylow_le_subgroupOf_of_compParab {Y : Type} [Group Y] [Finite Y]
    {L P : Subgroup Y} (hCP : CompParab L P) :
    ∃ T : Sylow 2 ↥L, Subgroup.normalizer ((T : Subgroup ↥L) : Set ↥L) ≤ P.subgroupOf L ∧
      P.subgroupOf L ≠ Subgroup.normalizer ((T : Subgroup ↥L) : Set ↥L) ∧
      P.subgroupOf L ≠ ⊤ := by
  obtain ⟨hPL, T, ⟨hTL, hT2, hTi⟩, hNP⟩ := hCP.parab
  let T' : Sylow 2 ↥L := (hT2.comap_subtype (K := L)).toSylow hTi
  have hT'mem : ∀ t : ↥L, t ∈ (T' : Subgroup ↥L) ↔ (t : Y) ∈ T := fun t => Iff.rfl
  have hNT : ∀ x : ↥L, x ∈ Subgroup.normalizer ((T' : Subgroup ↥L) : Set ↥L) →
      (x : Y) ∈ L ⊓ Subgroup.normalizer (T : Set Y) := fun x hx =>
    ⟨x.2, Subgroup.mem_normalizer_fintype fun t ht => by
      have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨t, hTL ht⟩).1 ((hT'mem _).2 ht)
      simpa [hT'mem] using h2⟩
  refine ⟨T', fun x hx => Subgroup.mem_subgroupOf.2 (hNP (hNT x hx)), fun he => ?_, fun he => ?_⟩
  · refine hCP.ne_borel T ⟨hTL, hT2, hTi⟩ (le_antisymm (fun y hy => ?_) hNP)
    have hy' : (⟨y, hPL hy⟩ : ↥L) ∈ P.subgroupOf L := Subgroup.mem_subgroupOf.2 hy
    rw [he] at hy'
    exact hNT _ hy'
  · refine hCP.ne_top (le_antisymm hPL fun l hl => ?_)
    have : (⟨l, hl⟩ : ↥L) ∈ P.subgroupOf L := he ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this

section G2

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem nonempty_sl2_mulEquiv_rankOne_g2 (i : Fin (Tag.rank .G2)) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(rankOne (g2Datum F).rootGroup i)) := by
  obtain ⟨φ, hφ, hx, hy⟩ := g2_exists_sl2_hom (K := F) i
  have hr := rankOne_eq_range_of_sl2
    (adjDatum_isParametrization (F := rootOperatorFamily .G2) (K := F)
      (RootSystem.ofCartan (g2Datum F).isFiniteType (g2Datum F).divisible)
      (adjDatum_roots (rootOperatorFamily .G2) F))
    (fun c => (hx c).trans (xPar_simple i c).symm)
    (fun c => (hy c).trans (xPar_neg_simple i c).symm)
  exact ⟨(MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hr.symm)⟩


theorem exists_mulEquiv_g2 (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] {L P : Subgroup Y} (hCP : CompParab L P)
    (hG : IsLieOf IdxG2 (↥L ⧸ Subgroup.center ↥L)) :
    ∃ f : ℕ, 2 ≤ f ∧ Nonempty (↥L ≃* AdjointQuotient .G2 (GaloisField 2 f)) := by
  have hq : CFSG.Open.IsQuasisimple ↥L := hCP.comp.2.2
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  have hZ : Nat.card (Subgroup.center ↥L) = 1 := by
    obtain ⟨d, hPd, ⟨e⟩⟩ := hG
    obtain ⟨hd, hA, h2A⟩ := rest_index (P := IdxG2) (Or.inr (Or.inr (Or.inr rfl))) hPd
    exact card_center_eq_one_of_index hGA d hd hA h2A e hCP.odd
  have e₂ : ↥L ≃* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.quotientBot.symm.trans
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

theorem exists_single_node_g2 {X : Type} [Group X] [Finite X] (e : X ≃* AdjointQuotient .G2 F)
    (T : Sylow 2 X) {J : Subgroup X} (hNJ : Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ J)
    (hJN : J ≠ Subgroup.normalizer ((T : Subgroup X) : Set X)) (hJtop : J ≠ ⊤) :
    ∃ π' : ↥(adjointGroup .G2 F) →* X,
      BorelQuotient (g2Datum F) (weylElement .G2 F) (torus (τ := .G2) F) π' (Nat.card F - 1) ∧
      borel (g2Datum F) (torus (τ := .G2) F) ≤ J.comap π' ∧
      ∃ i, negIndices (g2Datum F) (J.comap π') = {i} := by
  have : Finite ↥(adjointGroup .G2 F) := generated_group_finite .G2 _
  have h := borelQuotient_g2 e
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient (g2Datum F) (weylElement .G2 F) (torus (τ := .G2) F) π'
      (Nat.card F - 1) :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel (g2Datum F) (torus (τ := .G2) F)).map π' ≤ J := hNπ ▸ hNJ
  have hBA : borel (g2Datum F) (torus (τ := .G2) F) ≤ J.comap π' := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hne : J.comap π' ≠ borel (g2Datum F) (torus (τ := .G2) F) := by
    intro he
    apply hJN
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i, hi⟩ := negIndices_nonempty_of_ne hQ.ct hQ.extras hBA hne
  obtain ⟨k, hk⟩ := LieOut.exists_node_not_mem_negIndices hQ hBJ hJtop
  obtain ⟨-, hrest⟩ := g2_nodes (fun e : i = k => hk (e ▸ hi))
  refine ⟨π', hQ, hBA, i, ?_⟩
  ext c
  exact ⟨fun hc => hrest c fun e => hk (e ▸ hc), fun hc => hc ▸ hi⟩

theorem exists_leviData_g2 (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] {L P : Subgroup Y} (hCP : CompParab L P)
    (hG : IsLieOf IdxG2 (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (K : Type) (_ : Group K) (_ : Finite K) (ρ : K →* ↥L) (G : Type) (_ : Group G)
      (_ : Finite G) (S : Subgroup G) (β : ↥((P.subgroupOf L).comap ρ) →* (Fin 1 → G)) (f : ℕ),
      Function.Surjective ρ ∧ IsPGroup 2 β.ker ∧ Subgroup.pi Set.univ (fun _ => S) ≤ β.range ∧
      ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ (fun _ => S) ∧ CFSG.Open.IsQuasisimple ↥S ∧
      Subgroup.center ↥S = ⊥ ∧ Nat.card ↥S = ordA 1 (2 ^ f) := by
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_mulEquiv_g2 hGA hCP hG
  obtain ⟨T, hNT, hne, htop⟩ := exists_sylow_le_subgroupOf_of_compParab hCP
  obtain ⟨π', hQ, hBA, i, hI⟩ := exists_single_node_g2 e T hNT hne htop
  have : Finite ↥(adjointGroup .G2 (GaloisField 2 f)) := generated_group_finite .G2 _
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨eL⟩ := nonempty_sl2_mulEquiv_rankOne_g2 (F := GaloisField 2 f) i
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    sl2_isSimpleGroup h4
  have : IsSimpleGroup ↥(rankOne (g2Datum (GaloisField 2 f)).rootGroup i) := eL.symm.isSimpleGroup
  have hnc : ∃ a b : ↥(rankOne (g2Datum (GaloisField 2 f)).rootGroup i), a * b ≠ b * a :=
    ⟨eL (sl2Upper 1 * sl2Lower 1), eL (sl2Upper 1), fun h =>
      sl2_upper_lower_not_commute (eL.injective (by simpa [map_mul] using h))⟩
  obtain ⟨G, _, _, S, β, hker, hpi, hcomm, ⟨eS⟩⟩ :=
    exists_leviData_of_negIndices_eq hQ hBA hI (rankOne_inf_posUnipotentExcept_eq_bot hQ i hnc)
  obtain ⟨hqs, hZ, hcard⟩ := sl2Block_facts h4 (eL.trans eS)
  exact ⟨_, inferInstance, inferInstance, π', G, inferInstance, inferInstance, S, β, f, hQ.surj,
    hker, hpi, hcomm, hqs, hZ, by rw [hcard, hF, ordA_one_eq_two_pow (by omega)]⟩

end G2

end CFSG.AGLEmbedding.LeviBlock
