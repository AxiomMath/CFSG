module

public import CFSG.Quasithin.H13.U3L14B
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem Y_not_M_F4 (h1336 : A6.Stmt13_3_6_F4)
    (hY : oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ≠ ⊥) :
    ¬ oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ≤ normalizer (L : Set G) := by
  intro hYM
  have hN : oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ≤
      normalizer (V : Set G) ⊓ normalizer (L : Set G) := fun y hy =>
    ⟨S.YM_NV ⟨hy, hYM hy⟩, hYM hy⟩
  have h2 := (oTwoUpper_oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G))).symm
  have hNY := S.NY0_M hN Y_CV3 h2 (S.T_G1.trans G1_NY) S.Y_G1 hY
  have hG1 : A6.g1 T V ≤ normalizer (L : Set G) := G1_NY.trans hNY
  rcases h1336 G T L V S.h13 S.irr with h | ⟨h, -⟩
  · exact h hG1
  · exact h S.zv

theorem isPGroup_Y_inter_F4 (h1336 : A6.Stmt13_3_6_F4) {g : G} (hgL : g ∈ L)
    (hg2 : g ∈ normalizer (V₂ : Set G))
    (hgM : centralizer ((V₃ ⊔ V₃.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    IsPGroup 2 ↥(oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) ⊓
      (oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G))).map
        (MulAut.conj g).toMonoidHom) := by
  set Y := oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) with hYdef
  set Yg := Y.map (MulAut.conj g).toMonoidHom with hYgdef
  set M := normalizer (L : Set G) with hM

  have hYg3 : Yg ≤ centralizer ((V₃.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    intro x hx
    rw [mem_map_conj_iff] at hx
    rw [mem_centralizer_iff]
    intro w hw
    replace hw := mem_map_conj_iff.1 hw
    have h1 := (mem_centralizer_iff.1 (Y_CV3 hx)) _ hw
    calc w * x = g * ((g⁻¹ * w * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
      _ = x * w := by group
  have hinter : Y ⊓ Yg ≤ M := fun x hx =>
    hgM (mem_centralizer_sup (Y_CV3 hx.1) (hYg3 hx.2))

  set YM := oTwoUpper (Y ⊓ M) with hYM
  have hYMY : YM ≤ Y := (oTwoUpper_le _).trans inf_le_left
  have hYMM : YM ≤ M := (oTwoUpper_le _).trans inf_le_right
  have hYMN : YM ≤ normalizer (V : Set G) ⊓ M := fun y hy =>
    ⟨S.YM_NV ⟨hYMY hy, hYMM hy⟩, hYMM hy⟩
  have hYM2 : YM = oTwoUpper YM := (oTwoUpper_oTwoUpper _).symm
  have hTYM : T ≤ normalizer (YM : Set G) := fun t ht =>
    normalizer_le_normalizer_oTwoUpper _
      (mem_normalizer_inf (G1_NY (S.T_G1 ht)) (le_normalizer (S.T_L ht)))
  have hLYM := S.L_NY0 hYMN (hYMY.trans Y_CV3) hYM2 hTYM

  set Y₁ := oTwoUpper (Y ⊓ Yg) with hY₁
  have hYMYg : YM ≤ Yg := by
    intro x hx
    rw [mem_map_conj_iff]
    have h1 := (mem_normalizer_iff.1 (hLYM (inv_mem hgL)) x).1 hx
    have h2 : g⁻¹ * x * g ∈ YM := by simpa using h1
    exact hYMY h2
  have h1 : YM ≤ Y₁ := hYM2.le.trans (oTwoUpper_mono (le_inf hYMY hYMYg))
  have h2 : Y₁ ≤ YM := oTwoUpper_mono (le_inf inf_le_left hinter)
  have hY₁eq : Y₁ = YM := le_antisymm h2 h1
  by_cases hY : Y = ⊥
  · rw [hY, bot_inf_eq]
    exact IsPGroup.of_bot

  have hY₁ : Y₁ = ⊥ := by
    by_contra hne
    have hYMne : YM ≠ ⊥ := hY₁eq ▸ hne
    have hNM := S.NY0_M hYMN (hYMY.trans Y_CV3) hYM2 hTYM (hYMY.trans S.Y_G1) hYMne
    have hYN : Y ≤ normalizer (Y₁ : Set G) := fun y hy =>
      normalizer_le_normalizer_oTwoUpper _ (mem_normalizer_inf (le_normalizer hy) (S.Y_NYg hg2 hy))
    exact S.Y_not_M_F4 h1336 hY (hYN.trans (hY₁eq ▸ hNM))
  exact isPGroup_of_oTwoUpper_eq_bot hY₁

theorem stepB_F4 (h1336 : A6.Stmt13_3_6_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) :
    Group.IsSolvable ↥(oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G))) ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup G,
        E ≤ oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) →
          IsElemAbelian p E → Nat.card E ≤ p := by
  set Y := oTwoUpper (centralizer (conjClosure V₃ (A6.g1 T V) : Set G)) with hYdef
  have hbot : Y = ⊥ → Group.IsSolvable ↥Y ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup G,
      E ≤ Y → IsElemAbelian p E → Nat.card E ≤ p := by
    intro h
    refine ⟨?_, fun p hp _ E hE _ => ?_⟩
    · rw [isSolvable_iff_perfectCore_eq_bot, eq_bot_iff, h]
      exact perfectCore_le _
    · rw [h, le_bot_iff] at hE
      rw [hE, card_bot]
      exact hp.one_lt.le
  rcases S.bcase with hC | ⟨g, ⟨hgL, hg2⟩, hg3, hg1, hgM⟩
  · refine hbot ?_
    by_contra hY
    exact S.Y_not_M_F4 h1336 hY (Y_CV3.trans hC)
  by_cases hY : Y = ⊥
  · exact hbot hY
  have h2 := S.isPGroup_Y_inter_F4 h1336 hgL hg2 hgM
  refine ⟨?_, fun p hp hp2 E hEY hE => S.card_le_of_inter hg2 h2 hp hp2 hEY hE⟩

  by_contra hns
  have hK := S.h13.qtke
  have hs := S.h13.simple
  have hnab := S.h13.nonabelian

  have hYc : CharTwo Y := S.charTwo_G1.of_normal S.Y_G1 (normal_subgroupOf_of_le_normalizer G1_NY)
  have hO2Y : pCoreOf 2 Y ≠ ⊥ := by
    intro hb
    apply hY
    rw [eq_bot_iff]
    intro y hy
    have hyc : y ∈ centralizer (pCoreOf 2 Y : Set G) := by
      rw [hb, mem_centralizer_iff]
      intro h hh
      rw [show h = 1 from hh]
      group
    have := hYc ⟨hy, hyc⟩
    rw [hb] at this
    exact this
  have hspan := lemma_1_2_1_one hK hs hnab h39 hO2Y
  have hpc : perfectCore Y ≠ ⊥ := fun h => hns ((isSolvable_iff_perfectCore_eq_bot Y).2 h)
  obtain ⟨K, hKY⟩ : ∃ K, K ∈ cComp Y := by
    by_contra hnone
    push Not at hnone
    apply hpc
    rw [← hspan, cCompSpan, eq_bot_iff]
    exact sSup_le fun K hK => absurd hK (hnone K)

  have hYsub : CFSG.Open.IsSubnormal Y (normalizer (V₂ : Set G)) := by
    refine CFSG.Open.IsSubnormal.step S.Y_CV2 ?_
      (CFSG.Open.IsSubnormal.step (centralizer_le_normalizer _) ?_ (CFSG.Open.IsSubnormal.refl _))
    · exact normal_subgroupOf_of_le_normalizer (fun c hc => G1_NY (S.CV2_G1 hc))
    · exact normal_subgroupOf_of_le_normalizer (fun n hn => mem_normalizer_centralizer hn)
  have hKG2 := cComp_mem_of_subnormal hYsub hKY
  have hV2ne : V₂ ≠ ⊥ := fun h => S.V1_ne (le_bot_iff.1 (h ▸ S.le12))
  have hO2G2 : pCoreOf 2 (normalizer (V₂ : Set G)) ≠ ⊥ := by
    intro hb
    apply hV2ne
    have hV2p : IsPGroup 2 V₂ := S.isP_T.to_le (S.le2V.trans S.V_T)
    have := CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer le_normalizer le_rfl hV2p
    rw [hb] at this
    exact le_bot_iff.1 this
  have hgo : Odd (orderOf g) := by
    have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h <;> rw [h] <;> decide
  have hgK := odd_mem_normalizer_of_mem_cComp hK hs hnab h37 h38 hO2G2 hKG2 hg2 hgo

  have hKle : K ≤ Y ⊓ Y.map (MulAut.conj g).toMonoidHom := by
    intro k hk
    refine Subgroup.mem_inf.2 ⟨le_of_mem_cComp hKY hk, mem_map_conj_iff.2 ?_⟩
    have h1 := (mem_normalizer_iff.1 (inv_mem hgK) k).1 hk
    have h2 : g⁻¹ * k * g ∈ K := by simpa using h1
    exact le_of_mem_cComp hKY h2
  exact not_isPGroup_of_perfect (perfect_of_mem_cComp hKY) (ne_bot_of_mem_cComp hKY)
    (h2.to_le hKle)

end Set14

end CFSG.Quasithin.H13.U3
