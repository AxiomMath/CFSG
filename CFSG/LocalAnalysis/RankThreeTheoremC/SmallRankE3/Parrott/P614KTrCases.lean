module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts
import CFSG.GF2Type.Smith1979.W4InspSymOrth
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsOrth
import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsSL
import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsSp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614KTr

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts

section General

variable {G : Type*} [Group G] {K : Subgroup G}

theorem not_isSimpleGroup (hKn : K.Normal) (hKi : K.index = 2)
    (hKna : ∃ a b : K, a * b ≠ b * a) : ¬ IsSimpleGroup G := by
  intro hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · obtain ⟨a, b, hab⟩ := hKna
    have ha : (a : G) = 1 := Subgroup.mem_bot.mp (h.le a.2)
    have hb : (b : G) = 1 := Subgroup.mem_bot.mp (h.le b.2)
    exact hab (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, hb]))
  · rw [h, Subgroup.index_top] at hKi
    exact absurd hKi (by norm_num)

theorem rank2_top_of_mulEquiv {H : Type*} [Group H] (e : G ≃* H)
    (h : Rank2 (⊤ : Subgroup H)) : Rank2 (⊤ : Subgroup G) :=
  Rank2.map e.symm.toMonoidHom e.symm.injective (fun _ _ => Subgroup.mem_top _) h

theorem rank2_mono {H H' : Subgroup G} (hle : H ≤ H') (h : Rank2 H) : Rank2 H' :=
  Rank2.map (MonoidHom.id G) Function.injective_id (by rw [Subgroup.map_id]; exact hle) h

end General

section LinearSymplectic

variable {G : Type*} [Group G] {K : Subgroup G}

theorem not_statedSL {n : ℕ} (hn : 2 ≤ n) (e : G ≃* ↥(StatedSL n (ZMod 2))) (hKn : K.Normal)
    (hKi : K.index = 2) (hKna : ∃ a b : K, a * b ≠ b * a) : False := by
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    have hG : Nat.card G = 6 := by
      rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (mcltf_SLEquiv 2).toEquiv, mcltf_card_SL22]
    have hK : Nat.card K = 3 := by
      have hmul := K.card_mul_index
      rw [hKi, hG] at hmul
      omega
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI := isCyclic_of_prime_card hK
    obtain ⟨a, b, hab⟩ := hKna
    letI := IsCyclic.commGroup (α := K)
    exact hab (mul_comm a b)
  · haveI := mcltf_isSimpleGroup_SL h
    haveI : IsSimpleGroup ↥(StatedSL n (ZMod 2)) := (mcltf_SLEquiv n).symm.isSimpleGroup
    exact not_isSimpleGroup hKn hKi hKna e.isSimpleGroup

theorem rank2_perm_six : Rank2 (⊤ : Subgroup (Equiv.Perm (Fin 6))) := by
  refine ⟨Equiv.swap 0 2 * Equiv.swap 0 1, Subgroup.mem_top _, Equiv.swap 3 5 * Equiv.swap 3 4,
    Subgroup.mem_top _, by decide, by decide, by decide, by decide, ?_⟩
  exact not_mem_zpowers_of_pow_three (by decide) (by decide) (by decide) (by decide)

theorem rank2_perm {n : ℕ} (hn : 6 ≤ n) : Rank2 (⊤ : Subgroup (Equiv.Perm (Fin n))) :=
  Rank2.map (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hn))
    (Equiv.Perm.viaEmbeddingHom_injective _) (fun _ _ => Subgroup.mem_top _) rank2_perm_six

theorem not_statedSp {n : ℕ} (hn : 2 ≤ n) (e : G ≃* ↥(StatedSp n (ZMod 2))) (hKn : K.Normal)
    (hKi : K.index = 2) (hKna : ∃ a b : K, a * b ≠ b * a) (hr : ¬ Rank2 (⊤ : Subgroup G)) :
    False := by
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    exact hr (rank2_top_of_mulEquiv
      (e.trans (CFSG.QuasithinUnique.Bridge.Alt57Model.spEquivPerm (ZMod 2) (ZMod.card 2)))
      rank2_perm_six)
  · have hs := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 2) n
      (by omega) (Or.inr (Or.inr ⟨Nat.card_zmod 2, h⟩))
    haveI : IsSimpleGroup ↥(StatedSp n (ZMod 2)) := (mcltf_spProjEquiv n).isSimpleGroup
    exact not_isSimpleGroup hKn hKi hKna e.isSimpleGroup

end LinearSymplectic

section Orthogonal

open CFSG.LieType.Universal.Spin

theorem rank2_glaPlus {n : ℕ} (hn : 2 ≤ n) :
    Rank2 (⊤ : Subgroup ↥(GLAOrthGroup (GLAQPlus (ZMod 2) n))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  exact rank2_top_of_subgroup
    (rank2_mono (Subgroup.commutator_le_self _) (rank2_plus (m + 1) (by omega)))

theorem coe_quadMinus (m : ℕ) (b c : ZMod 2) :
    ⇑(quadMinus m (ZMod 2) b c) = StatedQuadMinus m (ZMod 2) b c := by
  funext v
  rw [quadMinus_apply]
  rfl

noncomputable def glaMinusEquiv (n : ℕ) :
    ↥(GLAOrthGroup (GLAQMinus n (1 : ZMod 2) 1)) ≃*
      ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus (n + 1) (ZMod 2) 1 1)) :=
  (mcltf_glaOrthEquiv (mcltf_coe_quadMinusGLA n 1 1)).trans
    (TauCeti.QuadraticMap.orthogonalGroupCongr (mcltf_minusIsometry n 1 1))

theorem rank2_glaMinus {n : ℕ} (hn : 2 ≤ n) :
    Rank2 (⊤ : Subgroup ↥(GLAOrthGroup (GLAQMinus n (1 : ZMod 2) 1))) := by
  have h1 : Rank2 (⊤ : Subgroup ↥(GLAOrthGroup (StatedQuadMinus (n + 1) (ZMod 2) 1 1))) :=
    rank2_top_of_subgroup (rank2_mono (Subgroup.commutator_le_self _) (rank2_minus n hn))
  exact rank2_top_of_mulEquiv
    ((glaMinusEquiv n).trans (mcltf_glaOrthEquiv (coe_quadMinus (n + 1) 1 1)).symm) h1

open CFSG.GroupTheory.WeirSylow CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth
  CFSG.GF2Type.Smith1979.W4Insp in
theorem nonempty_orthogonalGroup_quadMinus_two_equiv_perm :
    Nonempty (↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus (1 + 1) (ZMod 2) 1 1)) ≃*
      Equiv.Perm (Fin 5)) := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite (1 + 1) (ZMod 2) mcltf_irr
  have hdim := mcltf_finrank_quadMinus (m := 1 + 1) (by norm_num)
  have hminus := not_isPlusType_quadMinus (n := 1 + 1) (K := ZMod 2) (by norm_num) mcltf_irr
  obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff (n := 2) hQ
    (p4insporth_nondegenerate_quad p4insporth_symplectic5 (p4insporth_qN_add 5)) hdim
    (by rw [finrank_permCore_five]) (iff_of_false hminus p4insporth_not_plus5)
  have hι : ∀ x, p4insporth_qN 5 (e.toLinearEquiv x) = quadMinus (1 + 1) (ZMod 2) 1 1 x :=
    fun x => e.map_app x
  obtain ⟨e2⟩ := nonempty_mulEquiv_orthSub e.toLinearEquiv hι
  obtain ⟨e3⟩ := nonempty_mulEquiv_perm_five_orthSub
  exact ⟨(MulEquiv.subgroupCongr (orthogonalGroup_eq_orthSub _)).trans (e2.trans e3)⟩

theorem nonempty_glaMinus_one_equiv_perm :
    Nonempty (↥(GLAOrthGroup (GLAQMinus 1 (1 : ZMod 2) 1)) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨f⟩ := nonempty_orthogonalGroup_quadMinus_two_equiv_perm
  exact ⟨(glaMinusEquiv 1).trans f⟩

end Orthogonal

theorem perm_five_of_isMcLaughlinGroup {G : Type} [Group G] (hG : IsMcLaughlinGroup G)
    {K : Subgroup G} (hKn : K.Normal) (hKi : K.index = 2) (hKna : ∃ a b : K, a * b ≠ b * a)
    (hr : ¬ Rank2 (⊤ : Subgroup G)) : Nonempty (G ≃* Equiv.Perm (Fin 5)) := by
  rcases hG with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact (not_statedSL hn e hKn hKi hKna).elim
  · exact (not_statedSp hn e hKn hKi hKna hr).elim
  · exact (hr (rank2_top_of_mulEquiv e (rank2_glaPlus hn))).elim
  · rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      obtain ⟨f⟩ := nonempty_glaMinus_one_equiv_perm
      exact ⟨e.trans f⟩
    · exact (hr (rank2_top_of_mulEquiv e (rank2_glaMinus h))).elim
  · rcases Nat.lt_or_ge n 6 with h | h
    · obtain rfl : n = 5 := by omega
      exact ⟨e⟩
    · exact (hr (rank2_top_of_mulEquiv e (rank2_perm h))).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614KTr
