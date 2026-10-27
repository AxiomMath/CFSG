module

public import CFSG.ClassicalInvolution.WeakCT.UnitaryEightNodes
import CFSG.ClassicalInvolution.WeakCT.TwistedRankOne
import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.ClassicalInvolution.WeakCT

open Matrix CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.WeakCT.UnitaryEight
open CFSG.RankThree.PartTwo.CTU6 (embSL3 rS0 rS1 rS0_injective rS1_injective short_upper_mem
  short_lower_mem short_param_upper short_param_lower rS0_tv01 rS0_tv10 rS1_tv01 rS1_tv10 k0 k1 k2)
open CFSG.LieType.Steinberg (fixedSubfield)
open CFSG.Timmesfeld (tv LeviEmbedding)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

omit [Finite K] in
theorem center_SL4_eq_bot_of_charTwo : Subgroup.center SL(4, K) = ⊥ := by
  refine eq_bot_iff.2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have h1 : (r - 1) ^ (2 ^ 2) = 0 := by
    rw [sub_pow_char_pow, one_pow]
    norm_num [hr]
  have hr1 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h1)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp

theorem rankOne_six_zero_le_range (hK : Nat.card K = (2 ^ f) ^ 2) :
    CurtisTits.rankOne (rootDatum hK 6).rootGroup k0 ≤
      (rS0 (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range := by
  have hσ := unitaryInvolution_involutive hK
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨c, rfl⟩ := short_param_upper hσ (k := k0) (by decide) _ (rS0_tv01 hσ) g hg
    exact ⟨_, rfl⟩
  · obtain ⟨c, rfl⟩ := short_param_lower hσ (k := k0) (by decide) _ (rS0_tv10 hσ) g hg
    exact ⟨_, rfl⟩

theorem rankOne_six_one_le_range (hK : Nat.card K = (2 ^ f) ^ 2) :
    CurtisTits.rankOne (rootDatum hK 6).rootGroup k1 ≤
      (rS1 (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range := by
  have hσ := unitaryInvolution_involutive hK
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨c, rfl⟩ := short_param_upper hσ (k := k1) (by decide) _ (rS1_tv01 hσ) g hg
    exact ⟨_, rfl⟩
  · obtain ⟨c, rfl⟩ := short_param_lower hσ (k := k1) (by decide) _ (rS1_tv10 hσ) g hg
    exact ⟨_, rfl⟩

theorem rankOne_six_long_le_range (hK : Nat.card K = (2 ^ f) ^ 2) :
    CurtisTits.rankOne (rootDatum hK 6).rootGroup k2 ≤
      (CFSG.RankThree.PartTwo.CTU6.rL K f).range := by
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨c, rfl⟩ := CFSG.RankThree.PartTwo.CTU6.rL_param_upper hK g hg
    exact ⟨_, rfl⟩
  · obtain ⟨c, rfl⟩ := CFSG.RankThree.PartTwo.CTU6.rL_param_lower hK g hg
    exact ⟨_, rfl⟩

theorem agree_of_blocks (hK : Nat.card K = (2 ^ f) ^ 2) {G : Type} [Group G]
    (φ : SL(4, K) →* G) (κ : SU (unitaryInvolution K 2 f) 6 →* G)
    (h1 : φ.comp (blockSL2 K 3 1) = κ.comp (rS0 _ (unitaryInvolution_involutive hK)))
    (h2 : φ.comp (blockSL2 K 3 2) = κ.comp (rS1 _ (unitaryInvolution_involutive hK))) :
    φ.comp (blockSL K 4 3 1 (by norm_num)) =
      κ.comp (embSL3 _ (unitaryInvolution_involutive hK)) := by
  have hle : (⊤ : Subgroup SL(3, K)) ≤ (φ.comp (blockSL K 4 3 1 (by norm_num))).eqLocus
      (κ.comp (embSL3 _ (unitaryInvolution_involutive hK))) := by
    rw [← iSup_range_blockSL2 (K := K) 2]
    refine iSup_le fun k => ?_
    rintro _ ⟨A, rfl⟩
    fin_cases k
    · have e := DFunLike.congr_fun h1 A
      rw [← blockSL_four_comp_blk_zero] at e
      exact e
    · have e := DFunLike.congr_fun h2 A
      rw [← blockSL_four_comp_blk_one] at e
      exact e
  exact MonoidHom.ext fun A => hle (Subgroup.mem_top A)

theorem weakCT_unitary_eight_of_charts (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) {G : Type}
    [Group G] (φ : SL(4, K) →* G) (hφ : φ.ker ≤ Subgroup.center SL(4, K))
    (κ : SU (unitaryInvolution K 2 f) 6 →* G)
    (hagree : φ.comp (blockSL K 4 3 1 (by norm_num)) =
      κ.comp (embSL3 _ (unitaryInvolution_involutive hK)))
    (hcross : ∀ x ∈ (φ.comp (blockSL2 K 3 0)).range,
      ∀ y ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL K f)).range, x * y = y * x) :
    ∃ Ψ : SU (unitaryInvolution K 2 f) 8 →* G,
      Ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) 8) ∧ Ψ.range = φ.range ⊔ κ.range ∧
      Ψ.comp (embSL4 _ (unitaryInvolution_involutive hK)) = φ ∧ Ψ.comp (embSU6 _) = κ := by
  classical
  have hσ : ∀ c, unitaryInvolution K 2 f (unitaryInvolution K 2 f c) = c :=
    unitaryInvolution_involutive hK
  set X : Subgroup G := φ.range ⊔ κ.range with hX
  let φ' : SL(4, K) →* X := φ.codRestrict X fun A => Subgroup.mem_sup_left ⟨A, rfl⟩
  let κ' : SU (unitaryInvolution K 2 f) 6 →* X :=
    κ.codRestrict X fun A => Subgroup.mem_sup_right ⟨A, rfl⟩
  have hφ' : X.subtype.comp φ' = φ := MonoidHom.ext fun _ => rfl
  have hκ' : X.subtype.comp κ' = κ := MonoidHom.ext fun _ => rfl
  have hag1 : κ'.comp (rS0 _ hσ) = φ'.comp (blockSL2 K 3 1) := by
    refine MonoidHom.ext fun A => Subtype.ext ?_
    have h := DFunLike.congr_fun hagree (blk K 0 A)
    change κ (embSL3 _ hσ (blk K 0 A)) = φ (blockSL2 K 3 1 A)
    rw [← blockSL_four_comp_blk_zero]
    exact h.symm
  have hag2 : κ'.comp (rS1 _ hσ) = φ'.comp (blockSL2 K 3 2) := by
    refine MonoidHom.ext fun A => Subtype.ext ?_
    have h := DFunLike.congr_fun hagree (blk K 1 A)
    change κ (embSL3 _ hσ (blk K 1 A)) = φ (blockSL2 K 3 2 A)
    rw [← blockSL_four_comp_blk_one]
    exact h.symm
  let D := rootDatum hK 8
  let ρS : Fin 3 → (SL(2, K) →* X) := fun k => φ'.comp (blockSL2 K 3 k)
  let ρL : SL(2, fixedSubfield K 2 f) →* X := κ'.comp (CFSG.RankThree.PartTwo.CTU6.rL K f)
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
  let U : Fin D.rank → Subgroup X := fun k =>
    match k with
    | ⟨0, _⟩ => (ρS 0).range
    | ⟨1, _⟩ => (ρS 1).range
    | ⟨2, _⟩ => (ρS 2).range
    | ⟨3, _⟩ => ρL.range
    | ⟨n + 4, h⟩ => absurd h (by change ¬ n + 4 < 4; omega)
  let nd : ∀ k : Fin D.rank, NodeData D X k (U k) := fun k =>
    match k with
    | ⟨0, _⟩ => NodeData.ofParam (rS8 _ hσ 0) (ρS 0) rfl (rS8_injective _ hσ 0) (upS 0) (loS 0)
        (puS 0) (plS 0)
    | ⟨1, _⟩ => NodeData.ofParam (rS8 _ hσ 1) (ρS 1) rfl (rS8_injective _ hσ 1) (upS 1) (loS 1)
        (puS 1) (plS 1)
    | ⟨2, _⟩ => NodeData.ofParam (rS8 _ hσ 2) (ρS 2) rfl (rS8_injective _ hσ 2) (upS 2) (loS 2)
        (puS 2) (plS 2)
    | ⟨3, _⟩ => NodeData.ofParam (rL8 K f) ρL rfl rL8_injective (rL8_upper_mem hK)
        (rL8_lower_mem hK) (rL8_param_upper hK) (rL8_param_lower hK)
    | ⟨n + 4, h⟩ => absurd h (by change ¬ n + 4 < 4; omega)
  have P0 : (nd n0).IsParam (rS8 _ hσ 0) (ρS 0) :=
    NodeData.ofParam_isParam rfl (rS8_injective _ hσ 0) (upS 0) (loS 0) (puS 0) (plS 0)
  have P1 : (nd n1).IsParam (rS8 _ hσ 1) (ρS 1) :=
    NodeData.ofParam_isParam rfl (rS8_injective _ hσ 1) (upS 1) (loS 1) (puS 1) (plS 1)
  have P2 : (nd n2).IsParam (rS8 _ hσ 2) (ρS 2) :=
    NodeData.ofParam_isParam rfl (rS8_injective _ hσ 2) (upS 2) (loS 2) (puS 2) (plS 2)
  have P3 : (nd n3).IsParam (rL8 K f) ρL :=
    NodeData.ofParam_isParam rfl rL8_injective (rL8_upper_mem hK) (rL8_lower_mem hK)
      (rL8_param_upper hK) (rL8_param_lower hK)
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
  have hdiv6 : (rootDatum hK 6).divisible = ∅ := by
    change Unitary.divisible 6 = ∅
    simp only [Unitary.divisible, show Even 6 from ⟨3, rfl⟩, ↓reduceIte]
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hK
  have hCTG := isCTGroupDatum hK 8 (by norm_num) ζ hζ
  have hgen6 := iSup_rankOne_eq_top_of_ct (isCTGroupDatum hK 6 (by norm_num) ζ hζ) hdiv6
  have hle1 : φ'.range ≤ ⨆ k, U k := by
    rw [MonoidHom.range_eq_map, ← iSup_range_blockSL2 (K := K) 3, Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [MonoidHom.map_range]
    fin_cases k
    · exact le_iSup U n0
    · exact le_iSup U n1
    · exact le_iSup U n2
  have hle2 : κ'.range ≤ ⨆ k, U k := by
    rw [MonoidHom.range_eq_map, ← hgen6, Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    fin_cases k
    · refine (Subgroup.map_mono (rankOne_six_zero_le_range hK)).trans ?_
      rw [MonoidHom.map_range, hag1]
      exact le_iSup U n1
    · refine (Subgroup.map_mono (rankOne_six_one_le_range hK)).trans ?_
      rw [MonoidHom.map_range, hag2]
      exact le_iSup U n2
    · refine (Subgroup.map_mono (rankOne_six_long_le_range hK)).trans ?_
      rw [MonoidHom.map_range]
      exact le_iSup U n3
  have htop : φ'.range ⊔ κ'.range = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_range, MonoidHom.map_range, hφ', hκ', Subgroup.map_top,
      Subgroup.range_subtype]
  have hgen : ⨆ k, U k = ⊤ := eq_top_iff.mpr (by rw [← htop]; exact sup_le hle1 hle2)
  have hnt : ∃ k, ∃ g, (nd k).ψp g ≠ 1 := by
    refine ⟨n0, ⟨rS8 _ hσ 0 (tv 0 1 1), upS 0 1⟩, ?_⟩
    rw [P0.ψp_eq 1]
    intro h
    have h1 : φ (blockSL2 K 3 0 (tv 0 1 1)) = 1 := congrArg Subtype.val h
    have h2 := hφ (MonoidHom.mem_ker.mpr h1)
    rw [center_SL4_eq_bot_of_charTwo, Subgroup.mem_bot] at h2
    exact tv_zero_one_one_ne_one ((blockSL2_injective 3 0) (h2.trans (map_one _).symm))
  have hZ : ∀ (a : SL(2, K)) (b : SL(2, fixedSubfield K 2 f)), a ∈ Subgroup.center SL(2, K) →
      b ∈ Subgroup.center SL(2, fixedSubfield K 2 f) → rS8 _ hσ 0 a = rL8 K f b →
        rS8 _ hσ 0 a = 1 := by
    intro a b ha _ _
    rw [CFSG.RankThree.PartOne.CTP.center_sl2_eq_bot_of_two_eq_zero
      (CharTwo.two_eq_zero (R := K)), Subgroup.mem_bot] at ha
    rw [ha, map_one]
  have hcX : ∀ a b, Commute (ρS 0 a) (ρL b) := fun a b =>
    Subtype.ext (hcross _ ⟨a, rfl⟩ _ ⟨b, rfl⟩)
  have hloc : ∀ i j : Fin D.rank, i ≤ j →
      ∃ (E : LeviEmbedding D i j) (φE : E.L →* X), ∀ k, (k = i ∨ k = j) →
      (∀ g : D.rootGroup (Pi.single k 1), φE (E.preimage g) = (nd k).ψp g) ∧
        ∀ g : D.rootGroup (-Pi.single k 1), φE (E.preimage g) = (nd k).ψm g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | (exfalso; revert hij; simp [Fin.le_def]; done) | skip
    · exact exists_levi_node hdiv hCTG nd P0 (rS8_injective _ hσ 0)
    · exact exists_levi_of_model hdiv hCTG nd P0 P1 (embSL4 _ hσ) (embSL4_injective _ hσ)
        (blockSL2 K 3 0) (blockSL2 K 3 1) rfl rfl φ' rfl rfl
    · exact exists_levi_of_model hdiv hCTG nd P0 P2 (embSL4 _ hσ) (embSL4_injective _ hσ)
        (blockSL2 K 3 0) (blockSL2 K 3 2) rfl rfl φ' rfl rfl
    · exact exists_levi_orth hdiv hCTG nd P0 P3 (rS8_injective _ hσ 0) rL8_injective
        (commute_rS8_zero_rL8 hK) hZ hcX
    · exact exists_levi_node hdiv hCTG nd P1 (rS8_injective _ hσ 1)
    · exact exists_levi_of_model hdiv hCTG nd P1 P2 (embSL4 _ hσ) (embSL4_injective _ hσ)
        (blockSL2 K 3 1) (blockSL2 K 3 2) rfl rfl φ' rfl rfl
    · exact exists_levi_of_model hdiv hCTG nd P1 P3 (embSU6 _) (embSU6_injective _) (rS0 _ hσ)
        (CFSG.RankThree.PartTwo.CTU6.rL K f) (embSU6_comp_rS0 _ hσ) rfl κ' hag1 rfl
    · exact exists_levi_node hdiv hCTG nd P2 (rS8_injective _ hσ 2)
    · exact exists_levi_of_model hdiv hCTG nd P2 P3 (embSU6 _) (embSU6_injective _) (rS1 _ hσ)
        (CFSG.RankThree.PartTwo.CTU6.rL K f) (embSU6_comp_rS1 _ hσ) rfl κ' hag2 rfl
    · exact exists_levi_node hdiv hCTG nd P3 rL8_injective
  obtain ⟨Ψ, hsurj, hker, -, -, -, hpin⟩ :=
    weakCT_of_twisted_nodes_pinned hCT hL hdiv hgen nd hnt hloc
  have e0 := P0.comp_eq_of_rootGroup Ψ (hpin n0).2.1 (hpin n0).2.2
  have e1 := P1.comp_eq_of_rootGroup Ψ (hpin n1).2.1 (hpin n1).2.2
  have e2 := P2.comp_eq_of_rootGroup Ψ (hpin n2).2.1 (hpin n2).2.2
  have e3 := P3.comp_eq_of_rootGroup Ψ (hpin n3).2.1 (hpin n3).2.2
  have hres1 : Ψ.comp (embSL4 _ hσ) = φ' := by
    have hle : (⊤ : Subgroup SL(4, K)) ≤ (Ψ.comp (embSL4 _ hσ)).eqLocus φ' := by
      rw [← iSup_range_blockSL2 (K := K) 3]
      refine iSup_le fun k => ?_
      rintro _ ⟨A, rfl⟩
      fin_cases k
      · exact DFunLike.congr_fun e0 A
      · exact DFunLike.congr_fun e1 A
      · exact DFunLike.congr_fun e2 A
    exact MonoidHom.ext fun A => hle (Subgroup.mem_top A)
  have hres2 : Ψ.comp (embSU6 _) = κ' := by
    have hle : (⊤ : Subgroup (SU (unitaryInvolution K 2 f) 6)) ≤
        (Ψ.comp (embSU6 _)).eqLocus κ' := by
      rw [← hgen6]
      refine iSup_le fun k => ?_
      fin_cases k
      · refine (rankOne_six_zero_le_range hK).trans ?_
        rintro _ ⟨A, rfl⟩
        have e : (Ψ.comp (embSU6 _)).comp (rS0 _ hσ) = κ'.comp (rS0 _ hσ) := by
          rw [MonoidHom.comp_assoc, embSU6_comp_rS0, hag1]
          exact e1
        exact DFunLike.congr_fun e A
      · refine (rankOne_six_one_le_range hK).trans ?_
        rintro _ ⟨A, rfl⟩
        have e : (Ψ.comp (embSU6 _)).comp (rS1 _ hσ) = κ'.comp (rS1 _ hσ) := by
          rw [MonoidHom.comp_assoc, embSU6_comp_rS1, hag2]
          exact e2
        exact DFunLike.congr_fun e A
      · refine (rankOne_six_long_le_range hK).trans ?_
        rintro _ ⟨A, rfl⟩
        exact DFunLike.congr_fun e3 A
    exact MonoidHom.ext fun A => hle (Subgroup.mem_top A)
  refine ⟨X.subtype.comp Ψ, fun g hg => hker (Subtype.ext (MonoidHom.mem_ker.mp hg)), ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [MonoidHom.comp_assoc, hres1, hφ']
  · rw [MonoidHom.comp_assoc, hres2, hκ']

end CFSG.ClassicalInvolution.WeakCT

end
