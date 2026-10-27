module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Layer
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.LemmaQ
public import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting
import CFSG.GroupTheory.HyperplaneGeneration

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem fr_P_le_M (hl : FrobLocal p P M x) : (P : Subgroup G) ≤ M :=
  CFSG.LocalAnalysis.RankFourTheoremC.sylow_le_of_core hl.loc

theorem fr_layer_normal_in_centralizer (x : G) :
    centralizer ({x} : Set G) ≤ normalizer ((layerOf x : Subgroup G) : Set G) := by
  rw [layerOf_eq]
  have hmap : ∀ (e : G ≃* G) (H : Subgroup G),
      (CFSG.Open.GLBLayer H).map e.toMonoidHom ≤ CFSG.Open.GLBLayer (H.map e.toMonoidHom) := by
    intro e H
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hL)
  set C : Subgroup G := centralizer ({x} : Set G)
  have key : ∀ g ∈ normalizer (C : Set G), ∀ y ∈ CFSG.Open.GLBLayer C,
      g * y * g⁻¹ ∈ CFSG.Open.GLBLayer C := by
    intro g hg y hy
    have hH : C.map (MulAut.conj g).toMonoidHom = C :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have h := hmap (MulAut.conj g) C ⟨y, hy, rfl⟩
    rwa [hH] at h
  intro g hg
  have hg' : g ∈ normalizer (C : Set G) := le_normalizer hg
  rw [Subgroup.mem_normalizer_iff]
  exact fun y => ⟨key g hg' y, fun hy => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg') _ hy⟩

theorem ms_isElemAbelian_mono {E F : Subgroup G} (hFE : F ≤ E)
    (hE : CFSG.Open.IsElemAbelian p E) : CFSG.Open.IsElemAbelian p F := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x (hFE hx)⟩
  have h := hE.1.is_comm.comm (⟨(a : G), hFE a.2⟩ : E) ⟨(b : G), hFE b.2⟩
  have h2 := congrArg Subtype.val h
  exact h2

theorem ms_elemAbelian_class {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.IsElementaryAbelian p E :=
  { toIsMulCommutative := hE.1
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun g => by
      apply Subtype.ext
      simpa using hE.2 g.1 g.2 }

theorem ms_le_pRank [Fact p.Prime] {E H : Subgroup G} (hEH : E ≤ H)
    (hE : CFSG.Open.IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.Open.pRank p H :=
  le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p (Fact.out : p.Prime) H)
    ⟨E, hEH, hE, hk⟩

theorem ms_exists_orderTwo_mem (C : Subgroup G) (h2 : 2 ∣ Nat.card C) :
    ∃ s : G, s ∈ C ∧ orderOf s = 2 := by
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact ⟨(g : G), g.2, (Subgroup.orderOf_coe g).trans hg⟩

theorem fr_normalizer_le [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {A : Subgroup G} (hAU : A ≤ frU P x) (hA : A ≠ ⊥) : normalizer (A : Set G) ≤ M := by
  obtain ⟨n, -, -, -, hUel, hUcard⟩ := fr_layer_rank hG hl
  have hAP : A ≤ (P : Subgroup G) := hAU.trans inf_le_left
  have hAM : A ≤ M := hAP.trans (fr_P_le_M hl)
  have hAel : CFSG.Open.IsElemAbelian p A := ms_isElemAbelian_mono hAU hUel
  have hdvd : Nat.card A ∣ p ^ n := by
    rw [← hUcard]
    exact Subgroup.card_dvd_of_le hAU
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hA (Subgroup.card_eq_one.mp (by simpa using hk))
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1 : k = 1 := by omega
    subst hk1
    have hne : A ≠ zpowers x := by
      intro hAx
      have hAZ : A ≤ (P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G) := by
        rw [hAx]
        exact zpowers_le.mpr (fr_x_mem_Z0 hl)
      have hAbot : A ≤ frU P x ⊓ ((P : Subgroup G) ⊓ centralizer ((layerOf x : Subgroup G) : Set G)) :=
        le_inf hAU hAZ
      exact hA (le_bot_iff.mp (hAbot.trans_eq (fr_P_eq_sup hG hl).2))
    exact hl.norm A hAP (hk.trans (pow_one p)) hne
  · exact CFSG.LocalAnalysis.RankFourTheoremC.normalizer_le_of_two_le_pRank hG.fullCore hl.loc
      (IsPGroup.of_card hk) hAM (le_trans hk2 (ms_le_pRank le_rfl hAel hk))

theorem fr_coprime_le [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {X : Subgroup G} (hX : Nat.Coprime p (Nat.card X))
    (hUX : frU P x ≤ normalizer (X : Set G)) : X ≤ M := by
  obtain ⟨n, hn3, -, -, hUel, hUcard⟩ := fr_layer_rank hG hl
  letI : CFSG.IsElementaryAbelian p (frU P x) := ms_elemAbelian_class hUel
  letI inst : MulDistribMulAction (frU P x) X :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (frU P x) X hUX
  have hA2 : p ^ 2 ≤ Nat.card (frU P x) := by
    rw [hUcard]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  have hpX : ¬ p ∣ Nat.card X := (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hX
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation hA2 hpX
  have hle : (⊤ : Subgroup ↥X) ≤ Subgroup.comap X.subtype M := by
    rw [← hgen]
    refine iSup_le fun a => iSup_le fun ha => ?_
    intro g hg
    have hag : a • g = g := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a g).mp hg
    have hcon0 := congrArg Subtype.val hag
    have hcon : (a : G) * (g : G) * (a : G)⁻¹ = (g : G) := hcon0
    have hcomm : (a : G) * (g : G) = (g : G) * (a : G) := mul_inv_eq_iff_eq_mul.mp hcon
    have hane : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hzle : zpowers (a : G) ≤ frU P x := zpowers_le.mpr a.2
    have hzne : zpowers (a : G) ≠ ⊥ := fun h => hane (zpowers_eq_bot.mp h)
    have hNM : normalizer ((zpowers (a : G) : Subgroup G) : Set G) ≤ M :=
      fr_normalizer_le hG hl hzle hzne
    have hgC : (g : G) ∈ centralizer ((zpowers (a : G) : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_eq, mem_centralizer_singleton_iff]
      exact hcomm.symm
    have hgN : (g : G) ∈ normalizer ((zpowers (a : G) : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ hgC
    exact hNM hgN
  intro g hgX
  have h1 : (⟨g, hgX⟩ : ↥X) ∈ Subgroup.comap X.subtype M := hle (Subgroup.mem_top _)
  exact h1

theorem fr_normalizer_two_le [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hUT : frU P x ≤ normalizer (T : Set G)) :
    normalizer (T : Set G) ≤ M := by
  obtain ⟨n, hn3, -, -, hUel, hUcard⟩ := fr_layer_rank hG hl
  have hUM : frU P x ≤ M := inf_le_left.trans (fr_P_le_M hl)
  have hpR : n ≤ CFSG.Open.pRank p (normalizer (T : Set G) ⊓ M) :=
    ms_le_pRank (le_inf hUT hUM) hUel hUcard
  exact hl.conf (normalizer (T : Set G)) ⟨T, hT1, hT2, rfl⟩ (le_trans (by omega) hpR)

theorem fr_centralizer_layer_le [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    centralizer ((layerOf x : Subgroup G) : Set G) ≤ M := by
  obtain ⟨n, hn3, -, -, hUel, hUcard⟩ := fr_layer_rank hG hl
  have hUbot : frU P x ≠ ⊥ := by
    intro h
    have h1 : Nat.card (frU P x) = 1 := Subgroup.card_eq_one.mpr h
    rw [hUcard] at h1
    have hp5 := hl.p5
    have h3 : p ^ 1 ≤ p ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_one] at h3
    omega
  have hUL : ((frU P x : Subgroup G) : Set G) ⊆ ((layerOf x : Subgroup G) : Set G) :=
    SetLike.coe_subset_coe.mpr inf_le_right
  exact (Subgroup.centralizer_le hUL).trans
    ((Subgroup.centralizer_le_normalizer _).trans (fr_normalizer_le hG hl le_rfl hUbot))

theorem fr_centralizer_layer_odd [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    Odd (Nat.card (centralizer ((layerOf x : Subgroup G) : Set G))) := by
  obtain ⟨n, hn3, -, -, hUel, hUcard⟩ := fr_layer_rank hG hl
  have hUM : frU P x ≤ M := inf_le_left.trans (fr_P_le_M hl)
  rw [Nat.odd_iff]
  by_contra hne
  have h2 : 2 ∣ Nat.card (centralizer ((layerOf x : Subgroup G) : Set G)) :=
    Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨s, hs1, hs2⟩ := ms_exists_orderTwo_mem _ h2
  have hS1 : zpowers s ≠ ⊥ := by
    intro h
    have h1 := zpowers_eq_bot.mp h
    rw [h1, orderOf_one] at hs2
    omega
  have hS2 : IsPGroup 2 (zpowers s) :=
    IsPGroup.of_card (show Nat.card (zpowers s) = 2 ^ 1 by rw [Nat.card_zpowers, hs2, pow_one])
  have hLS : layerOf x ≤ centralizer ((zpowers s : Subgroup G) : Set G) := by
    intro y hy
    rw [centralizer_zpowers_eq, mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hs1 y hy
  have hUN : frU P x ≤ normalizer ((zpowers s : Subgroup G) : Set G) :=
    inf_le_right.trans (hLS.trans (Subgroup.centralizer_le_normalizer _))
  have hpR : n ≤ CFSG.Open.pRank p (normalizer ((zpowers s : Subgroup G) : Set G) ⊓ M) :=
    ms_le_pRank (le_inf hUN hUM) hUel hUcard
  have hNM : normalizer ((zpowers s : Subgroup G) : Set G) ≤ M :=
    hl.conf (normalizer ((zpowers s : Subgroup G) : Set G)) ⟨zpowers s, hS1, hS2, rfl⟩
      (le_trans (by omega) hpR)
  exact hl.not_le ((hLS.trans (Subgroup.centralizer_le_normalizer _)).trans hNM)

theorem fr_lemmaQ [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {Y : Subgroup G} (hYp : Nat.Coprime p (Nat.card Y))
    (hYL : Y ≤ normalizer ((layerOf x : Subgroup G) : Set G))
    (hUY : frU P x ≤ normalizer (Y : Set G)) :
    Y ≤ centralizer ((layerOf x : Subgroup G) : Set G) := by
  obtain ⟨n, hn, ⟨e⟩, -, -, hcard⟩ := fr_layer_sylow hG hl
  exact le_centralizer_of_coprime_of_psl2GF (by have := hl.p5; omega) hn e inf_le_right
    (P.isPGroup'.to_inf_left) hcard hYL hUY hYp

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
