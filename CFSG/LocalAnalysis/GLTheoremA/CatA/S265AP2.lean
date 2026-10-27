module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASpAct
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AP2Sp6
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ARank
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp6Lay
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnAPI
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutQuot
import CFSG.Milestones.ASVolI.A2OddAut
import CFSG.Milestones.ASVolI.F48.Core
import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec4.Item426A6
import CFSG.RankThree.PartTwo.Sec4.Statements423

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA S265
open CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine (spF2QTorus_holds)
open CFSG.RankThree.Classical (spEnd)
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exists_big_torus_of_sp6 {J D : Subgroup Ω} (hZ : Subgroup.center (PQuot 3 J) = ⊥)
    (hD : IsElemAbelian 3 D) (hDJ : D ≤ Subgroup.centralizer (J : Set Ω))
    (e : PSimple 3 J ≃* StatedSp 3 (ZMod 2)) :
    ∃ E : Subgroup Ω, E ≤ J ∧ IsElemAbelian 3 (E ⊔ D) ∧ 27 * Nat.card D ≤ Nat.card ↥(E ⊔ D) := by
  obtain ⟨Q, -, hQ⟩ := spF2QTorus_holds 3 (ZMod 2) (Nat.card_zmod 2) le_rfl
  obtain ⟨Q', -, hQ', hcardQ'⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) Q
  obtain ⟨E, hEJ, hED, hcard⟩ := exists_lift_sup hZ hD hDJ (hQ'.map e.symm.toMonoidHom)
  refine ⟨E, hEJ, hED, ?_⟩
  rw [hcard, Subgroup.card_map_of_injective e.symm.injective, hcardQ']
  exact Nat.mul_le_mul ((show 27 ≤ 3 ^ 3 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) hQ))
    le_rfl

private theorem mem_normalizer_sup_of_forall_conj {K L : Subgroup Ω} {g : Ω}
    (hK : ∀ x ∈ K, g * x * g⁻¹ ∈ K ⊔ L) (hL : ∀ x ∈ L, g * x * g⁻¹ ∈ K ⊔ L) :
    g ∈ Subgroup.normalizer ((K ⊔ L : Subgroup Ω) : Set Ω) := by
  have hle : K ⊔ L ≤ (K ⊔ L).comap (MulAut.conj g).toMonoidHom := sup_le hK hL
  exact Subgroup.mem_normalizer_fintype fun x hx => hle hx

theorem card_sup_le_rank_of_chevAut_eq_one {X J D E W : Subgroup Ω} (hJ : GLAPComponent 3 X J)
    (hDJ : D ≤ Subgroup.centralizer (J : Set Ω)) (hEJ : E ≤ J) (hED : IsElemAbelian 3 (E ⊔ D))
    (hW : W ≠ ⊥) (hW2 : IsPGroup 2 W) (hWN : W ≤ Subgroup.normalizer (J : Set Ω))
    (hDW : D ≤ Subgroup.normalizer (W : Set Ω))
    (hW1 : ∀ w (hw : w ∈ W), chevAut 3 J ⟨w, hWN hw⟩ = 1) :
    Nat.card ↥(E ⊔ D) ≤ 3 ^ GLATwoLocalRank 3 Ω := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOJ : GLAPPrimeCoreOf 3 J ≤ J := Subgroup.map_subtype_le _
  have hcent : ∀ w ∈ W, (⁅J, Subgroup.zpowers w⁆ : Subgroup Ω) ≤ GLAPPrimeCoreOf 3 J :=
    fun w hw => ((chevAut_eq_one_iff Nat.prime_three hJ (hWN hw)).mp (hW1 w hw)).2
  have hWO : W ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 J : Set Ω) := fun w hw => by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← CFSG.gLAPPrimeCoreOf_map_mulEquiv,
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hWN hw)]
  obtain ⟨M, hM⟩ : ∃ M : Subgroup Ω, M = GLAPPrimeCoreOf 3 J ⊔ W := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ := hW2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hW (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
  have h3M : ¬ 3 ∣ Nat.card M := by
    intro h
    have hc := card_sup_mul_card_inf_of_le_normalizer hWO
    rw [← hM] at hc
    have h3 : 3 ∣ Nat.card ↥(GLAPPrimeCoreOf 3 J) * 2 ^ k := by
      rw [← hk, ← hc]
      exact h.mul_right _
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact CFSG.LocalAnalysis.GLTheoremB.not_dvd_card_glaPPrimeCoreOf Nat.prime_three J h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
  have h2M : 2 ∣ Nat.card M := by
    have h := Subgroup.card_dvd_of_le (show W ≤ M by rw [hM]; exact le_sup_right)
    rw [hk] at h
    exact (dvd_pow_self 2 hk0).trans h
  have hDM : D ≤ Subgroup.normalizer (M : Set Ω) := fun d hd => by
    rw [hM]
    refine mem_normalizer_sup_of_forall_conj (fun o ho => ?_) (fun w hw => ?_)
    · have hc : o * d = d * o := Subgroup.mem_centralizer_iff.mp (hDJ hd) o (hOJ ho)
      rw [← hc, mul_inv_cancel_right]
      exact Subgroup.mem_sup_left ho
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hDW hd) w).mp hw)
  have hEM : E ≤ Subgroup.normalizer (M : Set Ω) := fun x hx => by
    rw [hM]
    refine mem_normalizer_sup_of_forall_conj (fun o ho => Subgroup.mem_sup_left ?_)
      (fun w hw => ?_)
    · exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LocalAnalysis.GLTheoremB.le_normalizer_glaPPrimeCoreOf 3 J (hEJ hx)) o).mp ho
    · have hc : ⁅x, w⁆ ∈ GLAPPrimeCoreOf 3 J :=
        hcent w hw (Subgroup.commutator_mem_commutator (hEJ hx) (Subgroup.mem_zpowers w))
      have heq : x * w * x⁻¹ = ⁅x, w⁆ * w := by rw [commutatorElement_def]; group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hw)
  obtain ⟨S, hS⟩ := CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup Nat.prime_three
    Nat.prime_two hED.isPGroup (sup_le hEM hDM) h3M
  exact T263.card_le_of_normalizes (fun h => Sylow.ne_bot_of_dvd_card S h2M
    ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h))
    (S.isPGroup'.map M.subtype) hED hS

private theorem chevAut_eq_one_of_sp6 {X J B D W : Subgroup Ω} (hN : NLAct 3 X J B D)
    (hB : IsElemAbelian 3 B) (hr : Nat.card B = 9 * Nat.card D)
    (e : PSimple 3 J ≃* StatedSp 3 (ZMod 2)) (hW2 : IsPGroup 2 W)
    (hWN : W ≤ Subgroup.normalizer (J : Set Ω)) (hBW : B ≤ Subgroup.normalizer (W : Set Ω)) :
    ∀ w (hw : w ∈ W), chevAut 3 J ⟨w, hWN hw⟩ = 1 := by
  obtain ⟨ψ, -, h2, h3⟩ := exists_spHom le_rfl e
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥B →* StatedSp 3 (ZMod 2), ∀ b, φ b = ψ (Subgroup.inclusion hN.norm b) :=
    ⟨ψ.comp (Subgroup.inclusion hN.norm), fun _ => rfl⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : ↥W →* StatedSp 3 (ZMod 2), ∀ w, χ w = ψ (Subgroup.inclusion hWN w) :=
    ⟨ψ.comp (Subgroup.inclusion hWN), fun _ => rfl⟩
  have hker : φ.ker = D.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ]
    exact (h2 (Subgroup.inclusion hN.norm b)).trans (hN.ker b b.2 (hN.norm b.2))
  have hAb : IsElemAbelian 3 φ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self B]
    exact (hB.subgroupOf B).map φ
  have h9 : Nat.card φ.range = 9 := by
    have hc : Nat.card φ.range * Nat.card D = Nat.card B := by
      rw [← Subgroup.card_ker_mul_card_range φ, hker, mul_comm,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN.le).toEquiv]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hc.trans hr)
  have hfix : ∀ s ∈ φ.range, s ≠ 1 →
      Module.finrank (ZMod 2) (LinearMap.ker (spEnd s - 1)) ≤ 2 := by
    rintro _ ⟨b, rfl⟩ hs
    have hbD : (b : Ω) ∉ D := fun hbD => hs (by
      rw [hφ]
      exact (h2 (Subgroup.inclusion hN.norm b)).2 ((hN.ker b b.2 (hN.norm b.2)).2 hbD))
    refine finrank_ker_le_two_of_layer_eq_bot_sp6 (hAb.2 _ ⟨b, rfl⟩) hs ?_
    rw [hφ]
    exact (h3 (Subgroup.inclusion hN.norm b)).2 (hN.layer b b.2 hbD (hN.norm b.2))
  have hTN : φ.range ≤ Subgroup.normalizer (χ.range : Set (StatedSp 3 (ZMod 2))) := by
    rintro _ ⟨b, rfl⟩
    refine Subgroup.mem_normalizer_fintype ?_
    rintro _ ⟨w, rfl⟩
    have hbw : (b : Ω) * w * (b : Ω)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hBW b.2) w).mp w.2
    refine MonoidHom.mem_range.mpr ⟨⟨_, hbw⟩, ?_⟩
    have hconj : Subgroup.inclusion hWN ⟨_, hbw⟩ = Subgroup.inclusion hN.norm b *
        Subgroup.inclusion hWN w * (Subgroup.inclusion hN.norm b)⁻¹ := Subtype.ext rfl
    rw [hφ, hχ, hχ, hconj, map_mul, map_mul, map_inv]
  have hTb := sp6_eq_bot_of_normalized_two_subgroup hAb h9 hfix
    (hW2.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective) hTN
  intro w hw
  have hmem : χ ⟨w, hw⟩ ∈ χ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  rw [hTb, Subgroup.mem_bot, hχ] at hmem
  exact (h2 _).1 hmem

theorem eq_bot_of_normalized_two_subgroup_of_nlAct {X J B D : Subgroup Ω} (hN : NLAct 3 X J B D)
    (hB : IsElemAbelian 3 B) (hDJ : D ≤ Subgroup.centralizer (J : Set Ω))
    (hZ : Subgroup.center (PQuot 3 J) = ⊥) (he : Nonempty (PSimple 3 J ≃* StatedSp 3 (ZMod 2)))
    (hr : Nat.card B = 9 * Nat.card D) (hrank : 3 ^ GLATwoLocalRank 3 Ω ≤ Nat.card B)
    (W : Subgroup Ω) (hW : IsPGroup 2 W) (hWN : W ≤ Subgroup.normalizer (J : Set Ω))
    (hBW : B ≤ Subgroup.normalizer (W : Set Ω)) : W = ⊥ := by
  obtain ⟨e⟩ := he
  by_contra hne
  obtain ⟨E, hEJ, hED, hEcard⟩ := exists_big_torus_of_sp6 hZ (hB.mono hN.le) hDJ e
  have hle := card_sup_le_rank_of_chevAut_eq_one hN.comp hDJ hEJ hED hne hW hWN
    (hN.le.trans hBW) (chevAut_eq_one_of_sp6 hN hB hr e hW hWN hBW)
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have := hle.trans hrank
  omega

end CFSG.LocalAnalysis.GLTheoremA.S265A
