module

public import CFSG.ClassicalInvolution.WeakCT.UnitaryEightCharts
import CFSG.ClassicalInvolution.WeakCT.SpCharts
import CFSG.ClassicalInvolution.WeakCT.TwistedRankOne
import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.ClassicalInvolution.WeakCT

open Matrix CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT.UnitaryEight
open CFSG.RankThree.PartTwo.CTU6 (embSU4 embSU4_injective embSU4_comp_sbEmb lbSU4 su4Model
  exists_su4Mu_ne rS0 rS1 rS0_injective rS1_injective short_upper_mem short_lower_mem
  short_param_upper short_param_lower commute_rS0_rL rootMatrix_mul_longRootMatrix_comm
  commute_of_mat_comm)
open CFSG.RankThree.PartOne.CTP (center_sl2_eq_bot_of_two_eq_zero sbEmb)
open CFSG.LieType.Steinberg (fixedSubfield)
open CFSG.Timmesfeld (tv LeviEmbedding)
open scoped MatrixGroups

section Model

variable {F : Type} [Field F] (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)

theorem embSL4_blockSL3_comp_blk_zero (k : Fin 3) (hk : (k : ℕ) + 1 < 3) :
    ((embSL4 σ hσ).comp (blockSL3 F 3 k hk)).comp (blk F 0) = rS8 σ hσ k := by
  rw [MonoidHom.comp_assoc]
  exact congrArg (embSL4 σ hσ).comp (blockSL3_comp_left 3 k hk)

theorem embSL4_blockSL3_comp_blk_one (k : Fin 3) (hk : (k : ℕ) + 1 < 3) :
    ((embSL4 σ hσ).comp (blockSL3 F 3 k hk)).comp (blk F 1) = rS8 σ hσ ⟨k + 1, hk⟩ := by
  rw [MonoidHom.comp_assoc]
  exact congrArg (embSL4 σ hσ).comp (blockSL3_comp_right 3 k hk)

theorem embSU6_embSU4_comp_sbEmb :
    ((embSU6 σ).comp (embSU4 σ)).comp (sbEmb σ hσ) = rS8 σ hσ 2 := by
  rw [MonoidHom.comp_assoc, embSU4_comp_sbEmb]
  exact embSU6_comp_rS1 σ hσ

theorem commute_rS8_zero_two (a b : SL(2, F)) : Commute (rS8 σ hσ 0 a) (rS8 σ hσ 2 b) := by
  show embSL4 σ hσ (blockSL2 F 3 0 a) * embSL4 σ hσ (blockSL2 F 3 2 b) =
    embSL4 σ hσ (blockSL2 F 3 2 b) * embSL4 σ hσ (blockSL2 F 3 0 a)
  rw [← map_mul, ← map_mul, blockSL2_comm 3 0 2 (by decide) a b]

end Model

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

theorem commute_rS8_one_rL8 (hK : Nat.card K = (2 ^ f) ^ 2) (a : SL(2, K))
    (b : SL(2, fixedSubfield K 2 f)) :
    Commute (rS8 _ (unitaryInvolution_involutive hK) 1 a) (rL8 K f b) := by
  refine commute_of_tv₂ _ _ (fun c d => ⟨?_, ?_, ?_, ?_⟩) a b
  · rw [rS8_tv01, rL8_tv01]
    refine commute_of_mat_comm ?_
    rw [coe_rootHom, coe_longRootHom]
    exact rootMatrix_mul_longRootMatrix_comm _ _ (by decide) (by decide) (by decide) (by decide)
  · rw [rS8_tv01, rL8_tv10]
    refine commute_of_mat_comm ?_
    rw [coe_rootHom, coe_longRootHom]
    exact rootMatrix_mul_longRootMatrix_comm _ _ (by decide) (by decide) (by decide) (by decide)
  · rw [rS8_tv10, rL8_tv01]
    refine commute_of_mat_comm ?_
    rw [coe_rootHom, coe_longRootHom]
    exact rootMatrix_mul_longRootMatrix_comm _ _ (by decide) (by decide) (by decide) (by decide)
  · rw [rS8_tv10, rL8_tv10]
    refine commute_of_mat_comm ?_
    rw [coe_rootHom, coe_longRootHom]
    exact rootMatrix_mul_longRootMatrix_comm _ _ (by decide) (by decide) (by decide) (by decide)

theorem weakCT_unitary_eight_even (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) {X : Type}
    [Group X] (U : Fin 4 → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hc02 : ∀ u ∈ U 0, ∀ v ∈ U 2, u * v = v * u) (hc03 : ∀ u ∈ U 0, ∀ v ∈ U 3, u * v = v * u)
    (hc13 : ∀ u ∈ U 1, ∀ v ∈ U 3, u * v = v * u)
    (hpair01 : ∃ W, LinearBlockStandardPair K W (U 0) (U 1))
    (hpair12 : ∃ W, LinearBlockStandardPair K W (U 1) (U 2))
    (htw : ∃ W, (su4Model hK).StandardPair W (U 3) (U 2)) :
    ∃ Ψ : SU (unitaryInvolution K 2 f) 8 →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (SU (unitaryInvolution K 2 f) 8)).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .PSU 8 2 f ∧
      ∀ k, (CurtisTits.rankOne (rootDatum hK 8).rootGroup k).map Ψ = U k := by
  classical
  have hσ := unitaryInvolution_involutive hK
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; nlinarith
  obtain ⟨_, θ₁, -, -, -, hs, hU3, hU2⟩ := htw
  let P := su4Model hK
  have hμ : ∃ s, P.mu s ≠ 1 := exists_su4Mu_ne hK hf
  have hlU : (θ₁.comp P.lb).range = U 3 := by rw [MonoidHom.range_comp]; exact hU3
  let US : Fin 3 → Subgroup X := fun i => U ⟨i.val, by omega⟩
  have hcommS : ∀ i j : Fin 3, i ≠ j → ¬ edgeUp 3 i j → ¬ edgeUp 3 j i →
      ∀ u ∈ US i, ∀ v ∈ US j, u * v = v * u := by
    intro i j hne h1 h2 u hu v hv
    have h3 : i.val ≠ j.val := fun h => hne (Fin.ext h)
    simp only [edgeUp] at h1 h2
    have hi := i.2
    have hj := j.2
    rcases (by omega : (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0)) with
      ⟨hi0, hj2⟩ | ⟨hi2, hj0⟩
    · obtain rfl : i = 0 := Fin.ext hi0
      obtain rfl : j = 2 := Fin.ext hj2
      exact hc02 u hu v hv
    · obtain rfl : i = 2 := Fin.ext hi2
      obtain rfl : j = 0 := Fin.ext hj0
      exact (hc02 v hv u hu).symm
  have hpairS : ∀ i j : Fin 3, edgeUp 3 i j →
      ∃ W, LinearBlockStandardPair K W (US i) (US j) := by
    intro i j hij
    simp only [edgeUp] at hij
    have hj := j.2
    rcases (by omega : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 2)) with
      ⟨hi0, hj1⟩ | ⟨hi1, hj2⟩
    · obtain rfl : i = 0 := Fin.ext hi0
      obtain rfl : j = 1 := Fin.ext hj1
      exact hpair01
    · obtain rfl : i = 1 := Fin.ext hi1
      obtain rfl : j = 2 := Fin.ext hj2
      exact hpair12
  have hsU : (θ₁.comp P.sb).range = US ⟨3 - 1, by omega⟩ := by
    rw [MonoidHom.range_comp]
    exact hU2
  have hVS : ∀ q : Fin 3, (edgeUp 3 ⟨3 - 1, by omega⟩ q ∨ edgeUp 3 q ⟨3 - 1, by omega⟩) →
      ∀ x ∈ (θ₁.comp P.lb).range, ∀ y ∈ US q, x * y = y * x := by
    intro q hq x hx y hy
    have hq1 : q = 1 := Fin.ext (by
      have := q.2
      simp only [edgeUp] at hq
      simp only [Fin.val_one]
      omega)
    subst hq1
    rw [hlU] at hx
    exact (hc13 y hy x hx).symm
  obtain ⟨ρS, hρS₁, hρSU, hρSψ⟩ := exists_frame_of_tree_short P hμ hK4
    (rootedTree_edgeUp_last (m := 3) (by norm_num)) ⟨1, Or.inr rfl⟩ hcommS hpairS hs hsU hVS
  let D := rootDatum hK 8
  have upS : ∀ (k : Fin 3) (c : K),
      rS8 _ hσ k (tv 0 1 c) ∈ D.rootGroup (Pi.single (nS k) 1) := fun k c => by
    rw [rS8_tv01]
    exact short_upper_mem hσ (nS_succ_lt k) c
  have loS : ∀ (k : Fin 3) (c : K),
      rS8 _ hσ k (tv 1 0 c) ∈ D.rootGroup (-Pi.single (nS k) 1) := fun k c => by
    rw [rS8_tv10]
    exact short_lower_mem hσ (nS_succ_lt k) c
  have puS : ∀ (k : Fin 3), ∀ g ∈ D.rootGroup (Pi.single (nS k) 1),
      ∃ c, rS8 _ hσ k (tv 0 1 c) = g := fun k =>
    short_param_upper hσ (nS_succ_lt k) (rS8 _ hσ k) (rS8_tv01 _ hσ k)
  have plS : ∀ (k : Fin 3), ∀ g ∈ D.rootGroup (-Pi.single (nS k) 1),
      ∃ c, rS8 _ hσ k (tv 1 0 c) = g := fun k =>
    short_param_lower hσ (nS_succ_lt k) (rS8 _ hσ k) (rS8_tv10 _ hσ k)
  let nd : ∀ k : Fin D.rank, NodeData D X k (U k) := fun k =>
    match k with
    | ⟨0, _⟩ => NodeData.ofParam (rS8 _ hσ 0) (ρS 0) (hρSU 0).2 (rS8_injective _ hσ 0) (upS 0)
        (loS 0) (puS 0) (plS 0)
    | ⟨1, _⟩ => NodeData.ofParam (rS8 _ hσ 1) (ρS 1) (hρSU 1).2 (rS8_injective _ hσ 1) (upS 1)
        (loS 1) (puS 1) (plS 1)
    | ⟨2, _⟩ => NodeData.ofParam (rS8 _ hσ 2) (ρS 2) (hρSU 2).2 (rS8_injective _ hσ 2) (upS 2)
        (loS 2) (puS 2) (plS 2)
    | ⟨3, _⟩ => NodeData.ofParam (rL8 K f) (θ₁.comp P.lb) hlU rL8_injective (rL8_upper_mem hK)
        (rL8_lower_mem hK) (rL8_param_upper hK) (rL8_param_lower hK)
    | ⟨n + 4, h⟩ => absurd h (by change ¬ n + 4 < 4; omega)
  have P0 : (nd n0).IsParam (rS8 _ hσ 0) (ρS 0) :=
    NodeData.ofParam_isParam (hρSU 0).2 (rS8_injective _ hσ 0) (upS 0) (loS 0) (puS 0) (plS 0)
  have P1 : (nd n1).IsParam (rS8 _ hσ 1) (ρS 1) :=
    NodeData.ofParam_isParam (hρSU 1).2 (rS8_injective _ hσ 1) (upS 1) (loS 1) (puS 1) (plS 1)
  have P2 : (nd n2).IsParam (rS8 _ hσ 2) (ρS 2) :=
    NodeData.ofParam_isParam (hρSU 2).2 (rS8_injective _ hσ 2) (upS 2) (loS 2) (puS 2) (plS 2)
  have P3 : (nd n3).IsParam (rL8 K f) (θ₁.comp P.lb) :=
    NodeData.ofParam_isParam hlU rL8_injective (rL8_upper_mem hK) (rL8_lower_mem hK)
      (rL8_param_upper hK) (rL8_param_lower hK)
  have hnt : ∃ k, ∃ g, (nd k).ψp g ≠ 1 := by
    refine ⟨n0, ⟨rS8 _ hσ 0 (tv 0 1 1), upS 0 1⟩, ?_⟩
    rw [P0.ψp_eq 1]
    intro h
    exact tv_zero_one_one_ne_one ((hρSU 0).1 (h.trans (map_one _).symm))
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 8 2 f :=
    ⟨Nat.prime_two, by omega, by norm_num, fun h => by
      have := congrArg Prod.fst h
      simp at this⟩
  have hCT : CurtisTits.CurtisTitsConclusion.{0} D .PSU 8 2 f :=
    CurtisTits.curtisTitsConclusion_unitary hadm hK
  have hL := CFSG.Timmesfeld.leviConePresented_unitary hK (n := 8) (by norm_num)
  have hdiv : D.divisible = ∅ := by
    change Unitary.divisible 8 = ∅
    simp only [Unitary.divisible, show Even 8 from ⟨4, rfl⟩, ↓reduceIte]
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hK
  have hCTG := isCTGroupDatum hK 8 (by norm_num) ζ hζ
  have hZ : ∀ {F₂ : Type} [Field F₂] (r₂ : SL(2, F₂) →* SU (unitaryInvolution K 2 f) 8)
      (k : Fin 3) (a : SL(2, K)) (b : SL(2, F₂)), a ∈ Subgroup.center SL(2, K) →
      b ∈ Subgroup.center SL(2, F₂) → rS8 _ hσ k a = r₂ b → rS8 _ hσ k a = 1 := by
    intro F₂ _ r₂ k a b ha _ _
    rw [center_sl2_eq_bot_of_two_eq_zero (CharTwo.two_eq_zero (R := K)), Subgroup.mem_bot] at ha
    rw [ha, map_one]
  have mS : ∀ (k : Fin 3) (a : SL(2, K)), ρS k a ∈ US k := fun k a => by
    have h : ρS k a ∈ (ρS k).range := ⟨a, rfl⟩
    rw [(hρSU k).2] at h
    exact h
  have hloc : ∀ i j : Fin D.rank, i ≤ j →
      ∃ (E : LeviEmbedding D i j) (φE : E.L →* X), ∀ k, (k = i ∨ k = j) →
      (∀ g : D.rootGroup (Pi.single k 1), φE (E.preimage g) = (nd k).ψp g) ∧
        ∀ g : D.rootGroup (-Pi.single k 1), φE (E.preimage g) = (nd k).ψm g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | (exfalso; revert hij; simp [Fin.le_def]; done) | skip
    · exact exists_levi_node hdiv hCTG nd P0 (rS8_injective _ hσ 0)
    ·
      obtain ⟨ψ, hψ0, hψ1⟩ := hρSψ 0 1 rfl
      exact exists_levi_of_model hdiv hCTG nd P0 P1
        ((embSL4 _ hσ).comp (blockSL3 K 3 0 (by decide)))
        ((embSL4_injective _ hσ).comp (blockSL3_injective 3 0 (by decide))) (blk K 0) (blk K 1)
        (embSL4_blockSL3_comp_blk_zero _ hσ 0 (by decide))
        (embSL4_blockSL3_comp_blk_one _ hσ 0 (by decide)) ψ hψ0 hψ1
    ·
      exact exists_levi_orth hdiv hCTG nd P0 P2 (rS8_injective _ hσ 0) (rS8_injective _ hσ 2)
        (commute_rS8_zero_two _ hσ) (hZ _ 0) (fun a b => hc02 _ (mS 0 a) _ (mS 2 b))
    ·
      exact exists_levi_orth hdiv hCTG nd P0 P3 (rS8_injective _ hσ 0) rL8_injective
        (commute_rS8_zero_rL8 hK) (hZ _ 0) (fun a b => hc03 _ (mS 0 a) _ (hlU ▸ ⟨b, rfl⟩))
    · exact exists_levi_node hdiv hCTG nd P1 (rS8_injective _ hσ 1)
    ·
      obtain ⟨ψ, hψ0, hψ1⟩ := hρSψ 1 2 rfl
      exact exists_levi_of_model hdiv hCTG nd P1 P2
        ((embSL4 _ hσ).comp (blockSL3 K 3 1 (by decide)))
        ((embSL4_injective _ hσ).comp (blockSL3_injective 3 1 (by decide))) (blk K 0) (blk K 1)
        (embSL4_blockSL3_comp_blk_zero _ hσ 1 (by decide))
        (embSL4_blockSL3_comp_blk_one _ hσ 1 (by decide)) ψ hψ0 hψ1
    ·
      exact exists_levi_orth hdiv hCTG nd P1 P3 (rS8_injective _ hσ 1) rL8_injective
        (commute_rS8_one_rL8 hK) (hZ _ 1) (fun a b => hc13 _ (mS 1 a) _ (hlU ▸ ⟨b, rfl⟩))
    · exact exists_levi_node hdiv hCTG nd P2 (rS8_injective _ hσ 2)
    ·
      exact exists_levi_of_model hdiv hCTG nd P2 P3 ((embSU6 _).comp (embSU4 _))
        ((embSU6_injective _).comp (embSU4_injective _)) (sbEmb _ hσ) (lbSU4 K f)
        (embSU6_embSU4_comp_sbEmb _ hσ) rfl θ₁ hρS₁.symm rfl
    · exact exists_levi_node hdiv hCTG nd P3 rL8_injective
  exact weakCT_of_twisted_nodes hCT hL hdiv hgen nd hnt hloc

theorem weakCT_unitary_eight_even_of_charts_with_long_root (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    {G : Type} [Group G] (φ : SL(4, K) →* G) (hφ : φ.ker ≤ Subgroup.center SL(4, K))
    (κ : SU (unitaryInvolution K 2 f) 6 →* G)
    (hκ : κ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) 6))
    (h1 : (φ.comp (blockSL2 K 3 1)).range =
      (κ.comp (rS0 _ (unitaryInvolution_involutive hK))).range)
    (h2 : (φ.comp (blockSL2 K 3 2)).range =
      (κ.comp (rS1 _ (unitaryInvolution_involutive hK))).range)
    (hcross : ∀ x ∈ (φ.comp (blockSL2 K 3 0)).range,
      ∀ y ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL K f)).range, x * y = y * x) :
    ∃ Ψ : SU (unitaryInvolution K 2 f) 8 →* G,
      Ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) 8) ∧
        Ψ.range = φ.range ⊔ κ.range ∧
      (CurtisTits.rankOne (rootDatum hK 8).rootGroup (⟨3, by change 3 < 4; decide⟩ : Fin (rootDatum hK 8).rank)).map Ψ =
        (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL K f)).range := by
  classical
  have hσ : ∀ c, unitaryInvolution K 2 f (unitaryInvolution K 2 f c) = c :=
    unitaryInvolution_involutive hK
  set X : Subgroup G := φ.range ⊔ κ.range with hX
  let φ' : SL(4, K) →* X := φ.codRestrict X fun A => Subgroup.mem_sup_left ⟨A, rfl⟩
  let κ' : SU (unitaryInvolution K 2 f) 6 →* X :=
    κ.codRestrict X fun A => Subgroup.mem_sup_right ⟨A, rfl⟩
  have hφ' : X.subtype.comp φ' = φ := MonoidHom.ext fun _ => rfl
  have hκ' : X.subtype.comp κ' = κ := MonoidHom.ext fun _ => rfl
  have hφk : φ'.ker ≤ Subgroup.center SL(4, K) := by
    rw [MonoidHom.ker_codRestrict]
    exact hφ
  have hκk : κ'.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) 6) := by
    rw [MonoidHom.ker_codRestrict]
    exact hκ
  have h1' : (φ'.comp (blockSL2 K 3 1)).range = (κ'.comp (rS0 _ hσ)).range := by
    apply Subgroup.map_injective X.subtype_injective
    rw [MonoidHom.map_range, MonoidHom.map_range, ← MonoidHom.comp_assoc,
      ← MonoidHom.comp_assoc, hφ', hκ']
    exact h1
  have h2' : (φ'.comp (blockSL2 K 3 2)).range = (κ'.comp (rS1 _ hσ)).range := by
    apply Subgroup.map_injective X.subtype_injective
    rw [MonoidHom.map_range, MonoidHom.map_range, ← MonoidHom.comp_assoc,
      ← MonoidHom.comp_assoc, hφ', hκ']
    exact h2
  have hker4 : (κ'.comp (embSU4 _)).ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) 4) := by
    intro x hx
    have hz : embSU4 _ x ∈ Subgroup.center (SU (unitaryInvolution K 2 f) 6) :=
      hκk (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx))
    refine Subgroup.mem_center_iff.mpr fun y => embSU4_injective _ ?_
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hz _
  have hinj : ∀ {F₂ : Type} [Field F₂], (2 : F₂) = 0 →
      ∀ r : SL(2, F₂) →* SU (unitaryInvolution K 2 f) 6, Function.Injective r →
        Function.Injective (κ'.comp r) := by
    intro F₂ _ h2F r hr
    refine (injective_iff_map_eq_one _).mpr fun a ha => ?_
    have hz : r a ∈ Subgroup.center (SU (unitaryInvolution K 2 f) 6) :=
      hκk (MonoidHom.mem_ker.mpr ha)
    have hc : a ∈ Subgroup.center SL(2, F₂) := Subgroup.mem_center_iff.mpr fun b =>
      hr (by rw [map_mul, map_mul]; exact Subgroup.mem_center_iff.mp hz (r b))
    rw [center_sl2_eq_bot_of_two_eq_zero h2F, Subgroup.mem_bot] at hc
    exact hc
  let U : Fin 4 → Subgroup X := fun k =>
    match k with
    | ⟨0, _⟩ => (φ'.comp (blockSL2 K 3 0)).range
    | ⟨1, _⟩ => (φ'.comp (blockSL2 K 3 1)).range
    | ⟨2, _⟩ => (φ'.comp (blockSL2 K 3 2)).range
    | ⟨3, _⟩ => (κ'.comp (CFSG.RankThree.PartTwo.CTU6.rL K f)).range
    | ⟨n + 4, h⟩ => absurd h (by omega)
  have hpair := exists_linearBlockStandardPair_of_blockSL2_frame (r := 2) φ' hφk U
    (fun k => by fin_cases k <;> rfl)
  have htw : ∃ W, (su4Model hK).StandardPair W (U 3) (U 2) := by
    refine ⟨(κ'.comp (embSU4 _)).range, κ'.comp (embSU4 _), rfl, hker4, ?_, ?_, ?_, ?_⟩
    · change Function.Injective (κ'.comp (CFSG.RankThree.PartTwo.CTU6.rL K f))
      exact hinj (CharTwo.two_eq_zero (R := fixedSubfield K 2 f)) _
        CFSG.RankThree.PartTwo.CTU6.rL_injective
    · change Function.Injective ((κ'.comp (embSU4 _)).comp (sbEmb _ hσ))
      rw [MonoidHom.comp_assoc, embSU4_comp_sbEmb]
      exact hinj (CharTwo.two_eq_zero (R := K)) _ (rS1_injective hσ)
    · change (lbSU4 K f).range.map (κ'.comp (embSU4 _)) =
        (κ'.comp (CFSG.RankThree.PartTwo.CTU6.rL K f)).range
      rw [MonoidHom.map_range]
      rfl
    · change (sbEmb _ hσ).range.map (κ'.comp (embSU4 _)) = (φ'.comp (blockSL2 K 3 2)).range
      rw [MonoidHom.map_range, MonoidHom.comp_assoc, embSU4_comp_sbEmb]
      exact h2'.symm
  have hc02 : ∀ u ∈ U 0, ∀ v ∈ U 2, u * v = v * u := by
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    show φ' (blockSL2 K 3 0 A) * φ' (blockSL2 K 3 2 B) =
      φ' (blockSL2 K 3 2 B) * φ' (blockSL2 K 3 0 A)
    rw [← map_mul, ← map_mul, blockSL2_comm 3 0 2 (by decide) A B]
  have hc03 : ∀ u ∈ U 0, ∀ v ∈ U 3, u * v = v * u := by
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact Subtype.ext (hcross _ ⟨A, rfl⟩ _ ⟨B, rfl⟩)
  have hc13 : ∀ u ∈ U 1, ∀ v ∈ U 3, u * v = v * u := by
    intro u hu v hv
    change u ∈ (φ'.comp (blockSL2 K 3 1)).range at hu
    rw [h1'] at hu
    obtain ⟨A, rfl⟩ := hu
    obtain ⟨B, rfl⟩ := hv
    show κ' (rS0 _ hσ A) * κ' (CFSG.RankThree.PartTwo.CTU6.rL K f B) =
      κ' (CFSG.RankThree.PartTwo.CTU6.rL K f B) * κ' (rS0 _ hσ A)
    rw [← map_mul, ← map_mul, (commute_rS0_rL hK A B).eq]
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hK
  have hdiv6 : (rootDatum hK 6).divisible = ∅ := by
    change Unitary.divisible 6 = ∅
    simp only [Unitary.divisible, show Even 6 from ⟨3, rfl⟩, ↓reduceIte]
  have hgen6 := iSup_rankOne_eq_top_of_ct (isCTGroupDatum hK 6 (by norm_num) ζ hζ) hdiv6
  have hle1 : φ'.range ≤ ⨆ k, U k := by
    rw [MonoidHom.range_eq_map, ← iSup_range_blockSL2 (K := K) 3, Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [MonoidHom.map_range]
    fin_cases k
    · exact le_iSup U 0
    · exact le_iSup U 1
    · exact le_iSup U 2
  have hle2 : κ'.range ≤ ⨆ k, U k := by
    rw [MonoidHom.range_eq_map, ← hgen6, Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    fin_cases k
    · refine (Subgroup.map_mono (rankOne_six_zero_le_range hK)).trans ?_
      rw [MonoidHom.map_range, ← h1']
      exact le_iSup U 1
    · refine (Subgroup.map_mono (rankOne_six_one_le_range hK)).trans ?_
      rw [MonoidHom.map_range, ← h2']
      exact le_iSup U 2
    · refine (Subgroup.map_mono (rankOne_six_long_le_range hK)).trans ?_
      rw [MonoidHom.map_range]
      exact le_iSup U 3
  have htop : φ'.range ⊔ κ'.range = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_range, MonoidHom.map_range, hφ', hκ', Subgroup.map_top,
      Subgroup.range_subtype]
  have hgen : ⨆ k, U k = ⊤ := eq_top_iff.mpr (by rw [← htop]; exact sup_le hle1 hle2)
  obtain ⟨Ψ, hsurj, hker, -, -, -, hnodes⟩ := weakCT_unitary_eight_even hK hf U hgen hc02 hc03 hc13
    (hpair 0 1 rfl (by decide)) (hpair 1 2 rfl (by decide)) htw
  refine ⟨X.subtype.comp Ψ, fun g hg => hker (Subtype.ext (MonoidHom.mem_ker.mp hg)), ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [← Subgroup.map_map, hnodes]
    change (κ'.comp (CFSG.RankThree.PartTwo.CTU6.rL K f)).range.map X.subtype =
      (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL K f)).range
    rw [MonoidHom.map_range, ← MonoidHom.comp_assoc, hκ']

theorem weakCT_unitary_eight_even_of_charts (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    {G : Type} [Group G] (φ : SL(4, K) →* G) (hφ : φ.ker ≤ Subgroup.center SL(4, K))
    (κ : SU (unitaryInvolution K 2 f) 6 →* G)
    (hκ : κ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) 6))
    (h1 : (φ.comp (blockSL2 K 3 1)).range =
      (κ.comp (rS0 _ (unitaryInvolution_involutive hK))).range)
    (h2 : (φ.comp (blockSL2 K 3 2)).range =
      (κ.comp (rS1 _ (unitaryInvolution_involutive hK))).range)
    (hcross : ∀ x ∈ (φ.comp (blockSL2 K 3 0)).range,
      ∀ y ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL K f)).range, x * y = y * x) :
    ∃ Ψ : SU (unitaryInvolution K 2 f) 8 →* G,
      Ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) 8) ∧
        Ψ.range = φ.range ⊔ κ.range := by
  obtain ⟨Ψ, hker, hrange, -⟩ :=
    weakCT_unitary_eight_even_of_charts_with_long_root hK hf φ hφ κ hκ h1 h2 hcross
  exact ⟨Ψ, hker, hrange⟩

end CFSG.ClassicalInvolution.WeakCT

end
