module

public import CFSG.GH74.GLS.Prop27.Defs
public import CFSG.Assembly.ComponentFreeOddCores
public import CFSG.Assembly.OddCoreElimination.Coverage
public import CFSG.Assembly.OddCoreElimination.Preparation
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS.Prop27

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem card_eq_four_of_pRank_eq_two {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E)
    (h2 : 2 ≤ CFSG.Open.pRank 2 E) (h3 : ¬ 3 ≤ CFSG.Open.pRank 2 E) : Nat.card E = 4 := by
  have hP : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  obtain ⟨A, hAE, hA, hAcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two E
  have hpr : CFSG.Open.pRank 2 E = 2 := by omega
  rw [hpr] at hAcard
  have hle : n ≤ CFSG.Open.pRank 2 E := CFSG.SectionRank.le_pRank one_lt_two le_rfl hE hn
  have hAle : Nat.card A ≤ Nat.card E := Subgroup.card_le_of_le hAE
  rw [hAcard, hn] at hAle
  have hn2 : 2 ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).mp hAle
  have hn2' : n = 2 := by omega
  rw [hn, hn2']
  norm_num

theorem exists_weakCore_of_balanced [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank : 3 ≤ CFSG.Open.twoRank G)
    (hbal : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → a * b = b * a →
      Assembly.Dichotomy.involutionOddCore a ⊓ centralizer ({b} : Set G) ≤
        Assembly.Dichotomy.involutionOddCore b)
    {z : G} (hz : orderOf z = 2)
    (hzne : Assembly.Dichotomy.involutionOddCore z ≠ ⊥) :
    ∃ (S : Sylow 2 G) (E U W : Subgroup G),
      z ∈ E ∧ E ≤ (S : Subgroup G) ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
      U ≤ (S : Subgroup G) ∧ CFSG.Open.IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
      (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G) ∧
      W = Assembly.Dichotomy.oddCoreSpan U ∧ W ≠ ⊥ ∧ Odd (Nat.card W) ∧
      (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) ∧
      Uniqueness.gammaElem (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) ∧
      Subgroup.normalizer (W : Set G) ≠ ⊤ ∧
      (∀ u ∈ U, u ≠ 1 → W ⊓ Subgroup.centralizer ({u} : Set G) =
        Assembly.Dichotomy.involutionOddCore u) ∧
      (∀ E' : Subgroup G, E' ≤ (S : Subgroup G) → CFSG.Open.IsElemAbelian 2 E' →
        Nat.card E' = 8 → Assembly.Dichotomy.oddCoreSpan E' = W) ∧
      (∀ V : Subgroup G, V ≤ (S : Subgroup G) → CFSG.Open.IsElemAbelian 2 V →
        Nat.card V = 4 →
        3 ≤ CFSG.Open.pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)) →
        Assembly.Dichotomy.oddCoreSpan V = W ∧
          Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (W : Set G)) ∧
      (∀ D : Subgroup G, D ≤ (S : Subgroup G) → 3 ≤ CFSG.Open.pRank 2 D →
        Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (W : Set G)) := by
  classical
  have hperf : commutator G = ⊤ :=
    Assembly.Dichotomy.commutator_eq_top_of_isSimpleGroup hnonab
  have hO := Assembly.Dichotomy.oddCore_eq_bot_of_isSimpleGroup hnonab
  have hrank' : 3 ≤ Assembly.twoRank G := hrank
  obtain ⟨E, hE, hE8, hzE⟩ :=
    Assembly.Dichotomy.perfectInvolutionCoverage G hperf hrank' z hz
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  have hΩE : Assembly.Dichotomy.oddCoreSpan E ≠ ⊥ :=
    Assembly.Dichotomy.oddCoreSpan_ne_bot_of_mem hzE hz (fun h => hzne (by
      unfold Assembly.Dichotomy.involutionOddCore
      rw [h, Subgroup.map_bot]))
  have hS3 : 3 ≤ Assembly.pRank 2 (S : Subgroup G) :=
    (Assembly.Dichotomy.pRank_sylow_eq_twoRank S).symm ▸ hrank
  obtain ⟨U, hUS, hSU, hU, hU4⟩ :=
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
    Assembly.Dichotomy.completedSpanPreparation G hrank' S U hUS hSU hU hU4 hcompl
  obtain ⟨hWne, hMneAll⟩ := hW1 ⟨E, hES, hE, hE8, hΩE⟩
  have hMne : Subgroup.normalizer (Assembly.Dichotomy.oddCoreSpan U : Set G) ≠ ⊤ :=
    hMneAll hO
  have hge : Uniqueness.gammaElem (S : Subgroup G) ≤
      normalizer (Assembly.Dichotomy.oddCoreSpan U : Set G) := by
    refine iSup_le fun E' => iSup_le fun hE'S => iSup_le fun hE'ab => iSup_le fun h2 =>
      iSup_le fun h3 => ?_
    by_cases h3' : 3 ≤ CFSG.Open.pRank 2 E'
    · exact hDW E' hE'S h3'
    · have h4 := card_eq_four_of_pRank_eq_two hE'ab h2 h3'
      exact (hVW E' hE'S hE'ab h4 (by rwa [inf_comm] at h3)).2
  exact ⟨S, E, U, Assembly.Dichotomy.oddCoreSpan U, hzE, hES, hE, hE8, hUS, hU, hU4, hSU,
    rfl, hWne, hWodd, hSW, hge, hMne, hCW, hEW, hVW, hDW⟩

theorem isSporadic_J1_or_isBenderGroup [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : KGH G) (hgen : Gen4 G) (hrank : CFSG.Open.twoRank G = 3) (hThm : S_Thm182_P27)
    (hbal : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → a * b = b * a →
      Assembly.Dichotomy.involutionOddCore a ⊓ centralizer ({b} : Set G) ≤
        Assembly.Dichotomy.involutionOddCore b)
    {t : G} (ht : orderOf t = 2) (hne : Assembly.Dichotomy.involutionOddCore t ≠ ⊥) :
    NativeSporadic.IsSporadic G .J1 ∨ CFSG.BenderSuzuki.IsBenderGroup G := by
  classical
  obtain ⟨S, _E, _U, _W, _hzE, _hES, _hE, _hE8, _hUS, _hU, _hU4, _hSU, _hWdef, _hWne,
    _hWodd, _hSW, hge, hMne, _hCW, _hEW, _hVW, _hDW⟩ :=
    exists_weakCore_of_balanced hnonab hrank.ge hbal ht hne
  have hS3eq : CFSG.Open.pRank 2 (S : Subgroup G) = 3 :=
    (Assembly.Dichotomy.pRank_sylow_eq_twoRank S).trans hrank
  exact hThm G inferInstance hnonab hK hgen S hS3eq (fun htop => hMne (top_unique (htop ▸ hge)))

end CFSG.GH74.GLS.Prop27
