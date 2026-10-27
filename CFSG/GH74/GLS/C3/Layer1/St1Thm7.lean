module

public import CFSG.GH74.GLS.C3.Layer1.St1Thm4
public import CFSG.GH74.E2.ComponentsBasic

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_ig_6_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 3 ≤ pRank 2 G →
    ∀ (x : G) (K : Subgroup G), IsILo 2 x K →
      ∃ (x' : G) (K' : Subgroup G), LongPumpUp 2 x K x' K' ∧ IsTwoTerminal x' K'

@[expose] def B_ivk_7_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K : Subgroup G) (x' : G) (K' : Subgroup G),
    IsIL2Pair x K → InU2 (kBar K) → ¬ InC2 (kBar K) → LongPumpUp 2 x K x' K' →
      InU2 (kBar K') ∧ ¬ InC2 (kBar K')

@[expose] def B_prop14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K : Subgroup G), IsIL2Pair x K →
    InU2 (kBar K) → 4 ≤ pRank 2 ↥(centralizer ({x} : Set G))

@[expose] def B_ivk_10_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K : Subgroup G), IsIL2Pair x K →
    InU2 (kBar K) → ¬ InC2 (kBar K) → ∃ y : G, IsLocallyUnbalancing x y K

@[expose] def B_inC2_L29 : Prop :=
  ∀ (K : Type) [Group K], InU2 K → HasL2Model K (fun q => q = 9) → InC2 K

section Bookkeeping

variable {K K' : Type} [Group K] [Group K']

theorem isElementaryAbelian_two_of_mulEquiv (e : K ≃* K') (h : CFSG.IsElementaryAbelian 2 K) :
    CFSG.IsElementaryAbelian 2 K' :=
  { toIsMulCommutative := ⟨⟨fun a b => by
      have := h.toIsMulCommutative
      have h1 := mul_comm' (e.symm a) (e.symm b)
      have h2 := congrArg e h1
      simpa using h2⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      have hx := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.exponent_dvd_p (e.symm x)
      have h2 := congrArg e hx
      simpa using h2 }

theorem inU2_of_mulEquiv (e : K ≃* K') (h : InU2 K) : InU2 K' := by
  obtain ⟨hq, h⟩ := h
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_⟩
  rcases h with h | h | ⟨hl, hel, hcard⟩
  · exact Or.inl (TwoThin.hasL2Model_of_mulEquiv e h)
  · exact Or.inr (Or.inl (CFSG.GH74.nonempty_alternating_of_mulEquiv e h))
  · refine Or.inr (Or.inr ⟨TwoThin.isL34Quotient_of_mulEquiv e hl, ?_, ?_⟩)
    · exact isElementaryAbelian_two_of_mulEquiv (Subgroup.centerCongr e) hel
    · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact hcard

theorem inU2_center
    (h : InU2 K) :
    CFSG.IsElementaryAbelian 2 ↥(center K) ∧ Nat.card ↥(center K) ≤ 4 := by
  obtain ⟨hq, h⟩ := h
  rcases h with h | h | ⟨-, hel, hcard⟩
  · have hs : IsSimpleGroup K := by
      obtain ⟨p, f, hp, hf, hP, hL⟩ := h
      exact (CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _ hL).2.2
    rw [center_eq_bot_of_simple_quasisimple hs hq]
    exact ⟨isElementaryAbelian_bot, by rw [Subgroup.card_bot]; norm_num⟩
  · have hs : IsSimpleGroup K := by
      obtain ⟨e⟩ := h
      have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
    rw [center_eq_bot_of_simple_quasisimple hs hq]
    exact ⟨isElementaryAbelian_bot, by rw [Subgroup.card_bot]; norm_num⟩
  · exact ⟨hel, hcard⟩

end Bookkeeping

section Glue

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem reflTransGen_isILo {p : ℕ} {a c : G × Subgroup G} (h0 : IsILo p a.1 a.2)
    (hrt : Relation.ReflTransGen (fun a b : G × Subgroup G => PumpUpLT p a.1 a.2 b.1 b.2) a c) :
    IsILo p c.1 c.2 := by
  induction hrt with
  | refl => exact h0
  | tail _ hstep _ => exact hstep.2.1

omit [Finite G] in
theorem LongPumpUp.isILo_right {p : ℕ} {x x' : G} {K K' : Subgroup G}
    (h : LongPumpUp p x K x' K') : IsILo p x' K' :=
  reflTransGen_isILo h.1 h.2

theorem thm7_of_leaves
    (h610 : B_ig_6_10) (h720 : B_ivk_7_20) (h14 : B_prop14) (h103 : B_ivk_10_3)
    (hL34 : B_gen4_noL34_elem) (hL29 : B_inC2_L29) (hG : C3Hyp G) (hN : NoU2Triple G) :
    St1Thm7 G := by
  by_contra hnot
  simp only [St1Thm7, L2Sub, not_forall] at hnot
  obtain ⟨x, hx, Kh, hKh, hbad⟩ := hnot
  obtain ⟨K, hKpc, ⟨e⟩⟩ := exists_pComponent_of_component hKh
  have hpair : IsIL2Pair x K := ⟨hx, hKpc⟩
  have hbadK : ¬ InC2 (kBar K) := fun h => hbad (CFSG.GH74.E2.inC2_of_mulEquiv e h)
  have hU2 : InU2 (kBar K) := by
    rcases hG.lt2o.2 x hx Kh hKh with h | h
    · exact absurd h hbad
    · exact inU2_of_mulEquiv e.symm h
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  have h4 := h14 G hG x K hpair hU2
  have hILo : IsILo 2 x K := ⟨hx, by simp only [oBound, ite_true]; omega, hKpc⟩
  obtain ⟨x', K', hlong, hterm⟩ := h610 G hG.kproper (by rw [hr4]; norm_num) x K hILo
  obtain ⟨hU2', hbad'⟩ := h720 G hG x K x' K' hpair hU2 hbadK hlong
  have hILo' : IsILo 2 x' K' := hlong.isILo_right
  have hpair' : IsIL2Pair x' K' := ⟨hILo'.1, hILo'.2.2⟩
  have hstar : IsStar2 x' :=
    ⟨hILo'.1, le_antisymm (Bg.pRank_subgroup_le one_lt_two _)
      (by rw [hr4]; exact h14 G hG x' K' hpair' hU2')⟩
  obtain ⟨y, hy⟩ := h103 G hG x' K' hpair' hU2' hbad'
  apply hN
  refine ⟨x', y, K', hy, hterm, hstar, ?_, ?_⟩
  · intro hl34
    exfalso
    have hc := inU2_center hU2'
    exact hL34 G hG.gen4 x' K' hpair'.1 hpair'.2 ⟨hl34, hc.1, hc.2⟩
  · intro hl29
    exact absurd (hL29 _ hU2' hl29) hbad'

theorem b_st1_thm7_of_leaves
    (h610 : B_ig_6_10) (h720 : B_ivk_7_20) (h14 : B_prop14)
    (h103 : B_ivk_10_3) (hL34 : B_gen4_noL34_elem) (hL29 : B_inC2_L29) : B_st1_thm7 :=
  fun _ _ _ hG hN => thm7_of_leaves h610 h720 h14 h103 hL34 hL29 hG hN

end Glue

end CFSG.GH74.GLS
