module

public import CFSG.GH74.GLS.Prop27.Elim
public import CFSG.GH74.GLS.C3.Layer1.St1Thm5C
public import CFSG.GH74.GLS.Prop27.EndGame

public section

namespace CFSG.GH74.GLS.C3.Layer1.Iv85

open Subgroup CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Prop27

variable {G : Type} [Group G] [Finite G]

theorem isSporadic_J1_or_isBenderGroup_of_thm182 [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KGH G) (hrank : 3 ≤ CFSG.Open.twoRank G)
    (hThm : Uniqueness.S_Thm182)
    (hbal : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → a * b = b * a →
      Assembly.Dichotomy.involutionOddCore a ⊓ centralizer ({b} : Set G) ≤
        Assembly.Dichotomy.involutionOddCore b)
    {t : G} (ht : orderOf t = 2) (hne : Assembly.Dichotomy.involutionOddCore t ≠ ⊥) :
    NativeSporadic.IsSporadic G .J1 ∨ CFSG.BenderSuzuki.IsBenderGroup G := by
  classical
  have hperf : commutator G = ⊤ :=
    Assembly.Dichotomy.commutator_eq_top_of_isSimpleGroup hnonab
  have hO := Assembly.Dichotomy.oddCore_eq_bot_of_isSimpleGroup hnonab
  have hrank' : 3 ≤ Assembly.twoRank G := hrank
  obtain ⟨E, hE, hE8, htE⟩ :=
    Assembly.Dichotomy.perfectInvolutionCoverage G hperf hrank' t ht
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  have hΩE := Assembly.Dichotomy.oddCoreSpan_ne_bot_of_mem htE ht (fun h => hne (by
    unfold Assembly.Dichotomy.involutionOddCore
    rw [h, Subgroup.map_bot]))
  have hS3 : 3 ≤ Assembly.pRank 2 (S : Subgroup G) :=
    (Assembly.Dichotomy.pRank_sylow_eq_twoRank S).symm ▸ hrank'
  obtain ⟨U, hUS, hUn, hU, hU4⟩ :=
    Assembly.Dichotomy.exists_normal_four_of_three_le_pRank S.isPGroup' hS3
  have hcompl : ∀ D : Subgroup G, Assembly.IsElemAbelian 2 D → Nat.card D = 8 →
      Assembly.Dichotomy.OddCoreSpanCompleted D := by
    intro D hD hD8
    refine (Assembly.Dichotomy.balanced_oddCoreSpan_completed D hD hD8.ge ?_).1
    intro a ha ha1 b hb hb1
    have hab : a * b = b * a := congrArg Subtype.val (hD.1.is_comm.comm (⟨a, ha⟩ : D) ⟨b, hb⟩)
    exact hbal a b (Assembly.Dichotomy.orderOf_eq_two_of_isElemAbelian hD ha ha1)
      (Assembly.Dichotomy.orderOf_eq_two_of_isElemAbelian hD hb hb1) hab
  obtain ⟨hWodd, hSW, hCW, hEW, hVW, hDW, hW1⟩ :=
    Assembly.Dichotomy.completedSpanPreparation G hrank' S U hUS hUn hU hU4 hcompl
  obtain ⟨-, hMG⟩ := hW1 ⟨E, hES, hE, hE8, hΩE⟩
  have hMne := hMG hO
  have hge : Uniqueness.gammaElem (S : Subgroup G) ≤
      normalizer (Assembly.Dichotomy.oddCoreSpan U : Set G) := by
    refine iSup_le fun E' => iSup_le fun hE'S => iSup_le fun hE'ab => iSup_le fun h2 =>
      iSup_le fun h3 => ?_
    by_cases h3' : 3 ≤ CFSG.Open.pRank 2 E'
    · exact hDW E' hE'S h3'
    · have h4 := card_eq_four_of_pRank_eq_two hE'ab h2 h3'
      exact (hVW E' hE'S hE'ab h4 (by rwa [inf_comm] at h3)).2
  exact hThm G inferInstance hnonab hK S hS3 (fun htop => hMne (top_unique (htop ▸ hge)))

omit [Finite G] in
theorem involutionOddCore_eq_pPrimeCoreOf (a : G) :
    Assembly.Dichotomy.involutionOddCore a = pPrimeCoreOf 2 (centralizer ({a} : Set G)) := by
  unfold Assembly.Dichotomy.involutionOddCore pPrimeCoreOf
  rw [CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore]

omit [Finite G] in
theorem involutionOddCore_eq_bot_iff (a : G) :
    Assembly.Dichotomy.involutionOddCore a = ⊥ ↔ pPrimeCore 2 ↥(centralizer ({a} : Set G)) = ⊥ := by
  rw [involutionOddCore_eq_pPrimeCoreOf, pPrimeCoreOf,
    Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)]

theorem b_iv2_8_5_of_thm182
    (hThm : Uniqueness.S_Thm182) : B_iv2_8_5 := by
  intro G _ _ hG ⟨t, ht, hne⟩
  by_contra hcon
  have : IsSimpleGroup G := hG.kproper.1
  have hbal : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → a * b = b * a →
      Assembly.Dichotomy.involutionOddCore a ⊓ centralizer ({b} : Set G) ≤
        Assembly.Dichotomy.involutionOddCore b := by
    intro a b ha hb hab
    by_contra hle
    refine hcon ⟨b, a, hb, ha, hab.symm, ?_⟩
    rwa [involutionOddCore_eq_pPrimeCoreOf, involutionOddCore_eq_pPrimeCoreOf] at hle
  have hrank : 3 ≤ CFSG.Open.twoRank G := by
    rw [← pRank_two_eq_twoRank, hG.pRank_eq_four]
    norm_num
  have hne' : Assembly.Dichotomy.involutionOddCore t ≠ ⊥ := fun h =>
    hne ((involutionOddCore_eq_bot_iff t).1 h)
  rcases isSporadic_J1_or_isBenderGroup_of_thm182 hG.kproper.2.1 hG.kgh hrank hThm hbal ht hne' with
    hJ | hB
  · exact hne (pPrimeCore_centralizer_eq_bot_of_J1 hJ t ht)
  · exact hne (pPrimeCore_centralizer_eq_bot_of_isBenderGroup hB t ht)

end CFSG.GH74.GLS.C3.Layer1.Iv85
