module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeUnitary2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeDelta
public import CFSG.LocalAnalysis.GLTheoremA.Lemma44
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SeitzGeneration
open Polynomial Module
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {ℓ : ℕ}

local notation "V" => (Fin ℓ ⊕ Fin ℓ → F)

private theorem commute_spEnd_of_mul_commute {g d : ↥(StatedSp ℓ F)} (h : g * d = d * g) :
    Commute (spEnd g) (spEnd d) :=
  show spEnd g * spEnd d = spEnd d * spEnd g by rw [← spEnd_mul, ← spEnd_mul, h]

private theorem eq_zero_of_mem_quad_of_fixed [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {v : V} (hv : v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hdv : spEnd d v = v) : v = 0 := by
  have hss : v + v = 0 := by
    have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
    calc v + v = (2 : F) • v := (two_smul F v).symm
      _ = 0 := by rw [h2F, zero_smul]
  have h2 : spEnd d (spEnd d v) = 0 := by
    rw [spEnd_sq_apply_of_mem_primary hv, hdv, hss]
  have h3 := spEnd_cube_apply hd3 v
  rw [h2, map_zero] at h3
  exact h3.symm

private theorem not_mem_fixed_of_ne_one [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hne : primaryComponent (spEnd d) (X ^ 2 + X + 1) ≠ ⊥) :
    d ∉ spSupported d {X - 1} := by
  intro hdF
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hfix := spEnd_eq_self_on_quad_of_mem_fixed hF hd3 hd1 hdF v hv
  exact hv0 (eq_zero_of_mem_quad_of_fixed hd3 hv hfix)

private theorem pow_two_not_mem_fixed [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hne : primaryComponent (spEnd d) (X ^ 2 + X + 1) ≠ ⊥) :
    d ^ 2 ∉ spSupported d {X - 1} := by
  intro hd2F
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hfix := spEnd_eq_self_on_quad_of_mem_fixed hF hd3 hd1 hd2F v hv
  have hdd : spEnd d (spEnd d v) = v := by
    rwa [pow_two, spEnd_mul, Module.End.mul_apply] at hfix
  have hdv : spEnd d v = v := by
    have h3 := spEnd_cube_apply hd3 v
    rw [hdd] at h3
    exact h3
  exact hv0 (eq_zero_of_mem_quad_of_fixed hd3 hv hdv)

private theorem inf_zpowers_fixed_eq_bot [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hne : primaryComponent (spEnd d) (X ^ 2 + X + 1) ≠ ⊥) :
    Subgroup.zpowers d ⊓ spSupported d {X - 1} = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgz, hgF⟩ := hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgz
  have hkm : g = d ^ (k % (3 : ℤ)) := by
    calc g = d ^ k := hk.symm
      _ = d ^ (k % (3 : ℤ)) := zpow_eq_zpow_emod' k hd3
  have hlo : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
  have hhi : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hcases : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by omega
  rcases hcases with h | h | h
  · rw [h, zpow_zero] at hkm
    exact hkm
  · rw [h] at hkm
    have hdF : d ∈ spSupported d {X - 1} := by
      rw [hkm] at hgF
      simpa using hgF
    exact absurd hdF (not_mem_fixed_of_ne_one hF hd3 hd1 hne)
  · rw [h] at hkm
    have hd2F : d ^ 2 ∈ spSupported d {X - 1} := by
      rw [hkm] at hgF
      simpa using hgF
    exact absurd hd2F (pow_two_not_mem_fixed hF hd3 hd1 hne)

private theorem inf_A_fixed_eq_bot [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d) (hK : stdLayer d = ⁅spSupported d {X ^ 2 + X + 1},
      spSupported d {X ^ 2 + X + 1}⁆)
    (hne : primaryComponent (spEnd d) (X ^ 2 + X + 1) ≠ ⊥) :
    A ⊓ spSupported d {X - 1} = ⊥ := by
  have hd3 : d ^ 3 = 1 := hd.2.2.1
  have hd1 : d ≠ 1 := hd.2.1
  have hF1K : spSupported d {X - 1} ≤
      Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F)) := by
    rw [hK]
    exact spSupported_fixed_le_centralizer_layer hd3
  have hle : A ⊓ spSupported d {X - 1} ≤ Subgroup.zpowers d :=
    (inf_le_inf_left A hF1K).trans (le_of_eq hd.2.2.2.2)
  have hle' : A ⊓ spSupported d {X - 1} ≤
      Subgroup.zpowers d ⊓ spSupported d {X - 1} :=
    le_inf hle inf_le_right
  rw [inf_zpowers_fixed_eq_bot hF hd3 hd1 hne] at hle'
  exact le_bot_iff.mp hle'

private theorem spEnd_mem_quad_of_mem_A [CharP F 2]
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d) {a : ↥(StatedSp ℓ F)} (ha : a ∈ A)
    {v : V} (hv : v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1)) :
    spEnd a v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1) :=
  apply_mem_primaryComponent (commute_spEnd_of_mul_commute
    (isElemAbelian_commute hA.1 ha hd.1)) hv

private theorem mem_fixed_of_fixes_quad [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) {g : ↥(StatedSp ℓ F)} (hgd : g * d = d * g)
    (hfix : ∀ v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1), spEnd g v = v) :
    g ∈ spSupported d {X - 1} := by
  rw [mem_spSupported]
  refine ⟨hgd, ?_⟩
  intro k hk hkO v hv
  have hkq : k = X ^ 2 + X + 1 := by
    refine eq_quad_of_mem_primaryFactors hF hd3 hk ?_
    intro hX
    exact hkO (by rw [hX]; exact Set.mem_singleton _)
  rw [hkq] at hv
  exact hfix v hv

private theorem finrank_fixed_le_two [CharP F 2] (hF : Nat.card F = 2) (hℓ : 3 ≤ ℓ)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d) (hK : stdLayer d = ⁅spSupported d {X ^ 2 + X + 1},
      spSupported d {X ^ 2 + X + 1}⁆)
    (hne : primaryComponent (spEnd d) (X ^ 2 + X + 1) ≠ ⊥) :
    Module.finrank F (primaryComponent (spEnd d) (X - 1)) ≤ 2 := by
  have hcard : Nat.card A = 3 ^ (ℓ - 1) := by
    rw [hA.2.1, twoLocalRank_three_statedSp hF (by omega)]
  have hbound := card_le_card_mul_pow_restrict (ℓ := ℓ) hF
    (fun g hg h hh => isElemAbelian_commute hA.1 hg hh)
    (fun g hg => hA.1.2 g hg)
    (fun g hg v hv => spEnd_mem_quad_of_mem_A hA hd hg hv)
    (fun g hg hfix => by
      have hgd : g * d = d * g := isElemAbelian_commute hA.1 hg hd.1
      have hgF : g ∈ spSupported d {X - 1} := mem_fixed_of_fixes_quad hF hd.2.2.1 hgd hfix
      have hbot : g ∈ (⊥ : Subgroup ↥(StatedSp ℓ F)) := by
        rw [← inf_A_fixed_eq_bot hF hA hd hK hne]
        exact ⟨hg, hgF⟩
      exact hbot)
  have hbound' : Nat.card A ≤ 3 ^ (Module.finrank F
      (primaryComponent (spEnd d) (X ^ 2 + X + 1)) / 2) := by
    simpa using hbound
  rw [hcard] at hbound'
  have hle : ℓ - 1 ≤ Module.finrank F
      (primaryComponent (spEnd d) (X ^ 2 + X + 1)) / 2 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hbound'
  obtain ⟨m, hm⟩ := finrank_quad_eq_two_mul hF (d := d)
  rw [hm] at hle
  rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] at hle
  have hsum := finrank_primaryComponent_fixed_add_quad (ℓ := ℓ) hd.2.2.1
  rw [hm] at hsum
  omega

private theorem exists_W_of_not_vanishes [CharP F 2]
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d) (hv : ¬ StdVanishes A d) :
    ∃ W : Submodule F V, W ≠ ⊥ ∧
      (∀ u ∈ W, ∀ v ∈ W, spForm ℓ F u v = 0) ∧
      (∀ w ∈ W, spEnd d w ∈ W) ∧
      (∀ g ∈ stdLayer d, ∀ w ∈ W, spEnd g w ∈ W) ∧
      (∀ g ∈ A, ∀ w ∈ W, spEnd g w ∈ W) := by
  change ¬ ¬ (∃ T : Subgroup ↥(StatedSp ℓ F), T ≠ ⊥ ∧ IsPGroup 2 T ∧
      innerClosure A d ⊔ A ≤ Subgroup.normalizer (T : Set ↥(StatedSp ℓ F))) at hv
  obtain ⟨T, hT1, hT2, hT⟩ := not_not.mp hv
  obtain ⟨W, hW0, hWiso, hWE⟩ := exists_isotropic_of_le_normalizer hT2 hT1 hT
  refine ⟨W, hW0, hWiso, ?_, ?_, ?_⟩
  · intro w hw
    exact hWE d (Subgroup.mem_sup_right hd.1) w hw
  · intro g hg w hw
    exact hWE g (Subgroup.mem_sup_left (le_closureIn_self (stdLayer d) _ hg)) w hw
  · intro g hg w hw
    exact hWE g (Subgroup.mem_sup_right hg) w hw

private theorem inf_quad_eq_bot_of_isotropic [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d {X ^ 2 + X + 1}, spSupported d {X ^ 2 + X + 1}⁆)
    {W : Submodule F V} (hWiso : ∀ u ∈ W, ∀ v ∈ W, spForm ℓ F u v = 0)
    (hWd : ∀ w ∈ W, spEnd d w ∈ W)
    (hWK : ∀ g ∈ stdLayer d, ∀ w ∈ W, spEnd g w ∈ W) :
    W ⊓ primaryComponent (spEnd d) (X ^ 2 + X + 1) = ⊥ := by
  have hQ := isQuasisimple_layer_of_stdElt hd hK
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨hrW, hr3⟩ := hr
  by_contra hr0
  have hQr : spForm ℓ F r (spEnd d r) = 0 := hWiso r hrW (spEnd d r) (hWd r hrW)
  obtain ⟨r', hr'3, hrr', hQ'⟩ := exists_isotropic_partner hd.2.2.1 hr3 hr0 hQr
  have hr'0 : r' ≠ 0 := by
    intro h
    rw [h] at hrr'
    have hzero : (0 : F) = 1 := by simpa using hrr'
    exact one_ne_zero hzero.symm
  have ht := unitTransv_mem hF hd.2.2.1 hr'3 hQ'
  have htK : unitTransv d r' ∈ stdLayer d := by
    rw [hK]
    exact mem_commutator_of_sq_eq_one hF hd.2.2.1 hd.2.1 hQ ht.1 ht.2.1
  have hr'W : r' ∈ W :=
    mem_of_unitTransv_stable hF hd.2.2.1 hWd hr'3 hQ' hrW hrr' (hWK _ htK)
  have hzero := hWiso r hrW r' hr'W
  rw [hrr'] at hzero
  exact one_ne_zero hzero

private theorem le_fixed_of_inf_quad_bot [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {W : Submodule F V} (hWd : ∀ w ∈ W, spEnd d w ∈ W)
    (hbot : W ⊓ primaryComponent (spEnd d) (X ^ 2 + X + 1) = ⊥) :
    W ≤ primaryComponent (spEnd d) (X - 1) := by
  intro w hw
  have h := split_primary hd3 w
  have h1W : ((spEnd d) ^ 2 + spEnd d + 1 : Module.End F V) w ∈ W :=
    W.add_mem (W.add_mem (hWd _ (hWd w hw)) (hWd w hw)) hw
  have h3 : ((spEnd d) ^ 2 + spEnd d : Module.End F V) w ∈ W :=
    W.add_mem (hWd _ (hWd w hw)) (hWd w hw)
  have h3zero : ((spEnd d) ^ 2 + spEnd d : Module.End F V) w = 0 := by
    have hmem : ((spEnd d) ^ 2 + spEnd d : Module.End F V) w ∈ W ⊓
        primaryComponent (spEnd d) (X ^ 2 + X + 1) := ⟨h3, h.2.1⟩
    rw [hbot] at hmem
    exact hmem
  rw [h.2.2, h3zero, add_zero]
  exact h.1

private theorem finrank_fixed_eq_two [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {W : Submodule F V} (hW0 : W ≠ ⊥) (hWiso : ∀ u ∈ W, ∀ v ∈ W, spForm ℓ F u v = 0)
    (hle : W ≤ primaryComponent (spEnd d) (X - 1))
    (hle2 : Module.finrank F (primaryComponent (spEnd d) (X - 1)) ≤ 2) :
    Module.finrank F (primaryComponent (spEnd d) (X - 1)) = 2 := by
  have hW1ne : primaryComponent (spEnd d) (X - 1) ≠ ⊥ := by
    intro h
    rw [h] at hle
    exact hW0 (le_bot_iff.mp hle)
  have hpos : 1 ≤ Module.finrank F (primaryComponent (spEnd d) (X - 1)) :=
    Submodule.one_le_finrank_iff.mpr hW1ne
  have hnd := nondegenerate_primaryComponent_fixed (ℓ := ℓ) hd3
  have halt : ((spForm ℓ F).restrict (primaryComponent (spEnd d) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : V)
  obtain ⟨m, hm⟩ := LinearMap.BilinForm.IsAlt.even_finrank halt hnd
  omega

private theorem exists_r_fixes_of_not_vanishes [CharP F 2] (hF : Nat.card F = 2) (hℓ : 3 ≤ ℓ)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d {X ^ 2 + X + 1}, spSupported d {X ^ 2 + X + 1}⁆)
    (hne : primaryComponent (spEnd d) (X ^ 2 + X + 1) ≠ ⊥)
    (hWno : ¬ StdVanishes A d) :
    ∃ r : V, r ∈ primaryComponent (spEnd d) (X - 1) ∧ r ≠ 0 ∧
      ∀ a ∈ A, ∀ v ∈ primaryComponent (spEnd d) (X - 1), spEnd a v = v := by
  obtain ⟨W, hW0, hWiso, hWd, hWK, hWA⟩ := exists_W_of_not_vanishes hA hd hWno
  have hbot : W ⊓ primaryComponent (spEnd d) (X ^ 2 + X + 1) = ⊥ :=
    inf_quad_eq_bot_of_isotropic hF hA hd hK hWiso hWd hWK
  have hle : W ≤ primaryComponent (spEnd d) (X - 1) :=
    le_fixed_of_inf_quad_bot hd.2.2.1 hWd hbot
  have hle2 : Module.finrank F (primaryComponent (spEnd d) (X - 1)) ≤ 2 :=
    finrank_fixed_le_two hF hℓ hA hd hK hne
  have hdim2 : Module.finrank F (primaryComponent (spEnd d) (X - 1)) = 2 :=
    finrank_fixed_eq_two hd.2.2.1 hW0 hWiso hle hle2
  obtain ⟨r, hrW, hr0, hWspan, -⟩ :=
    eq_span_of_le_fixed_isotropic hd.2.2.1 hW0 hWiso hle hdim2
  have hr1 : r ∈ primaryComponent (spEnd d) (X - 1) := hle hrW
  have hperp := mem_span_of_perp_of_mem_fixed hd.2.2.1 hr1 hr0 hdim2
  have hfix : ∀ a ∈ A, ∀ v ∈ primaryComponent (spEnd d) (X - 1), spEnd a v = v := by
    intro a ha
    have har : spEnd a r = r := by
      have hmem : spEnd a r ∈ W := hWA a ha r hrW
      rw [hWspan] at hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have hc0 : c = 1 := by
        rcases CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_eq_one_of_card_eq_two hF c with
          h | h
        · exfalso
          have hz : spEnd a r = 0 := by rw [← hc, h, zero_smul]
          exact hr0 (by
            have := congrArg (spEnd a⁻¹) hz
            rwa [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one,
              Module.End.one_apply, map_zero] at this)
        · exact h
      rw [hc0, one_smul] at hc
      exact hc.symm
    have hb3 : a ^ 3 = 1 := hA.1.2 a ha
    have hbY : ∀ v ∈ primaryComponent (spEnd d) (X - 1),
        spEnd a v ∈ primaryComponent (spEnd d) (X - 1) := fun v hv =>
      apply_mem_primaryComponent (commute_spEnd_of_mul_commute
        (isElemAbelian_commute hA.1 ha hd.1)) hv
    have hbR : ∀ v ∈ Submodule.span F {r}, spEnd a v = v := by
      intro v hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul, har]
    exact eqOn_of_fixes_flag hb3 hbY hbR hperp
  exact ⟨r, hr1, hr0, hfix⟩

private theorem le_quad_of_eqOn_fixed [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d)
    (hfix : ∀ a ∈ A, ∀ v ∈ primaryComponent (spEnd d) (X - 1), spEnd a v = v) :
    A ≤ spSupported d {X ^ 2 + X + 1} := by
  intro a ha
  rw [mem_spSupported]
  refine ⟨isElemAbelian_commute hA.1 ha hd.1, ?_⟩
  intro k hk hkO v hv
  have hk1 : k = X - 1 := by
    refine eq_X_sub_one_of_mem_primaryFactors hF hd.2.2.1 hk ?_
    intro h
    exact hkO (by rw [h]; exact Set.mem_singleton _)
  rw [hk1] at hv
  exact hfix a ha v hv

private theorem exists_y_hyperbolic [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d {X ^ 2 + X + 1}, spSupported d {X ^ 2 + X + 1}⁆)
    (hne : primaryComponent (spEnd d) (X ^ 2 + X + 1) ≠ ⊥)
    {r : V} (hr1 : r ∈ primaryComponent (spEnd d) (X - 1)) (hr0 : r ≠ 0)
    (hAq : A ≤ spSupported d {X ^ 2 + X + 1}) :
    ∃ y : ↥(StatedSp ℓ F), y ∈ Subgroup.centralizer (A : Set ↥(StatedSp ℓ F)) ∧
      y ∈ Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F)) ∧ y ^ 3 = 1 ∧ y ∉ A := by
  obtain ⟨v, hv1, hrv⟩ := exists_spForm_eq_one_of_mem_primary hF hd.2.2.1
    (f := X - 1) (Or.inl rfl) hr1 hr0
  have hvr : spForm ℓ F r v = 1 := hrv
  have hu : spEnd d r = r := spEnd_eq_self_of_mem_fixed hr1
  have hv : spEnd d v = v := spEnd_eq_self_of_mem_fixed hv1
  have htu : spTransvection r (1 : F) ∈ spSupported d {X - 1} :=
    spTransvection_mem_spFixedFactor hu 1
  have htv : spTransvection v (1 : F) ∈ spSupported d {X - 1} :=
    spTransvection_mem_spFixedFactor hv 1
  set y : ↥(StatedSp ℓ F) := ⁅spTransvection r (1 : F), spTransvection v (1 : F)⁆ with hydef
  have hyF : y ∈ spSupported d {X - 1} :=
    Subgroup.commutator_le_self (spSupported d {X - 1})
      (Subgroup.commutator_mem_commutator htu htv)
  have hy3 : y ^ 3 = 1 := commutator_transvection_pow_three hvr
  have hyne : y ≠ 1 := by
    intro h1
    have hyr : spEnd y r = r + spForm ℓ F r r • r +
        (spForm ℓ F r r + spForm ℓ F r v) • v :=
      spEnd_commutator_transvection hvr r
    have hself : spForm ℓ F r r = 0 := spForm_isAlt.self_eq_zero r
    rw [h1, spEnd_one, Module.End.one_apply, hself, zero_smul, add_zero, hvr,
      zero_add, one_smul] at hyr
    have hv0 : v = 0 := by
      have h' : r + v = r + 0 := by simpa using hyr.symm
      exact add_left_cancel h'
    have hzero : (0 : F) = 1 := by simpa [hv0] using hrv
    exact one_ne_zero hzero.symm
  refine ⟨y, ?_, ?_, hy3, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hO : Disjoint ({X - 1} : Set F[X]) {X ^ 2 + X + 1} := by
      rw [Set.disjoint_singleton_left, Set.mem_singleton_iff]
      exact fun h => CFSG.HardMathSupport.Dickson.Bal207.X_sq_add_X_add_one_ne h.symm
    exact (commute_spSupported_of_disjoint hd.2.2.1 hO hyF (hAq ha)).symm
  · rw [hK]
    exact spSupported_fixed_le_centralizer_layer hd.2.2.1 hyF
  · intro hyA
    have hbot : A ⊓ spSupported d {X - 1} = ⊥ := inf_A_fixed_eq_bot hF hA hd hK hne
    have hybot : y ∈ A ⊓ spSupported d {X - 1} := ⟨hyA, hyF⟩
    rw [hbot] at hybot
    exact hyne hybot

private theorem exists_two_subgroup_le_layer [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hQ : CFSG.Open.IsQuasisimple ↥⁅spSupported d {X ^ 2 + X + 1},
      spSupported d {X ^ 2 + X + 1}⁆)
    (h3 : 3 ≤ Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1))) :
    ∃ T : Subgroup ↥(StatedSp ℓ F), T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤
      ⁅spSupported d {X ^ 2 + X + 1}, spSupported d {X ^ 2 + X + 1}⁆ := by
  obtain ⟨w, hw, hw0, hQw⟩ := exists_isotropic_of_three_le hF hd3
    (Y := primaryComponent (spEnd d) (X ^ 2 + X + 1)) le_rfl h3
  have ht := unitTransv_mem hF hd3 hw hQw
  have htK : unitTransv d w ∈ ⁅spSupported d {X ^ 2 + X + 1},
      spSupported d {X ^ 2 + X + 1}⁆ :=
    mem_commutator_of_sq_eq_one hF hd3 hd1 hQ ht.1 ht.2.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htne : unitTransv d w ≠ 1 := ht.2.2 hw0
  have hord : orderOf (unitTransv d w) = 2 := orderOf_eq_prime ht.2.1 htne
  refine ⟨Subgroup.zpowers (unitTransv d w), ?_, ?_, Subgroup.zpowers_le.mpr htK⟩
  · exact Subgroup.zpowers_ne_bot.mpr htne
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]

private theorem exists_T_of_le_layer [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d {X ^ 2 + X + 1}, spSupported d {X ^ 2 + X + 1}⁆)
    (h3 : 3 ≤ Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)))
    (hAle : A ≤ stdLayer d) :
    ∃ T : Subgroup ↥(StatedSp ℓ F), T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ stdLayer d ∧
      A = (A ⊓ stdLayer d) ⊔ (A ⊓ Subgroup.normalizer (T : Set ↥(StatedSp ℓ F))) := by
  have hQ := isQuasisimple_layer_of_stdElt hd hK
  obtain ⟨T, hT1, hT2, hTle⟩ := exists_two_subgroup_le_layer hF hd.2.2.1 hd.2.1 hQ h3
  refine ⟨T, hT1, hT2, by rwa [hK], ?_⟩
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  calc A = A ⊓ stdLayer d := (inf_eq_left.mpr hAle).symm
    _ ≤ (A ⊓ stdLayer d) ⊔ (A ⊓ Subgroup.normalizer (T : Set ↥(StatedSp ℓ F))) := le_sup_left

private theorem exists_isotropic_eigenvector_of_not_le_layer [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d) (hnot : ¬ A ≤ stdLayer d)
    (h7 : 7 ≤ Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1))) :
    ∃ (x : ↥(StatedSp ℓ F)) (u : V) (j : ℕ),
      x ∈ A ∧ x ∉ stdLayer d ∧ j < 3 ∧
      u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1) ∧ u ≠ 0 ∧
      spForm ℓ F u (spEnd d u) = 0 ∧
      spEnd x u = spEnd (d ^ j) u ∧ x ^ 3 = 1 ∧ x * d = d * x := by
  obtain ⟨x, hxA, hxK⟩ := Set.not_subset.mp hnot
  have hx3 : x ^ 3 = 1 := hA.1.2 x hxA
  have hxd : x * d = d * x := isElemAbelian_commute hA.1 hxA hd.1
  obtain ⟨j, hj3, hjdim⟩ := exists_three_le_finrank_eigen hd.2.2.1 hx3 hxd h7
  let E : Submodule F V := primaryComponent (spEnd d) (X ^ 2 + X + 1) ⊓
    LinearMap.ker (spEnd x - spEnd (d ^ j))
  have hE3 : 3 ≤ Module.finrank F E := hjdim
  obtain ⟨u, huE, hu0, hQu⟩ :=
    exists_isotropic_of_three_le hF hd.2.2.1 (Y := E) inf_le_left hE3
  have huW : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1) := huE.1
  have hxu : spEnd x u = spEnd (d ^ j) u := by
    have h := (LinearMap.mem_ker.mp huE.2)
    rwa [LinearMap.sub_apply, sub_eq_zero] at h
  exact ⟨x, u, j, hxA, hxK, hj3, huW, hu0, hQu, hxu, hx3, hxd⟩

private theorem exists_T_normalizing_x_of_eigenvector [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)} {d x : ↥(StatedSp ℓ F)} (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d {X ^ 2 + X + 1}, spSupported d {X ^ 2 + X + 1}⁆)
    {u : V} {j : ℕ} (huW : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hu0 : u ≠ 0) (hQu : spForm ℓ F u (spEnd d u) = 0)
    (hxu : spEnd x u = spEnd (d ^ j) u) (hxd : x * d = d * x) :
    ∃ T : Subgroup ↥(StatedSp ℓ F), T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ stdLayer d ∧
      x ∈ Subgroup.normalizer (T : Set ↥(StatedSp ℓ F)) := by
  have hQ := isQuasisimple_layer_of_stdElt hd hK
  have ht := unitTransv_mem hF hd.2.2.1 huW hQu
  have htK : unitTransv d u ∈ stdLayer d := by
    rw [hK]
    exact mem_commutator_of_sq_eq_one hF hd.2.2.1 hd.2.1 hQ ht.1 ht.2.1
  have hxt : x * unitTransv d u = unitTransv d u * x :=
    commute_unitTransv hd.2.2.1 huW hQu hxd hxu
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htne : unitTransv d u ≠ 1 := ht.2.2 hu0
  have hord : orderOf (unitTransv d u) = 2 := orderOf_eq_prime ht.2.1 htne
  have hTle : Subgroup.zpowers (unitTransv d u) ≤ stdLayer d :=
    Subgroup.zpowers_le.mpr htK
  have hTne : Subgroup.zpowers (unitTransv d u) ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr htne
  have hT2 : IsPGroup 2 (Subgroup.zpowers (unitTransv d u)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  have hxN : x ∈ Subgroup.normalizer
      (Subgroup.zpowers (unitTransv d u) : Set ↥(StatedSp ℓ F)) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hn]
    exact ((Commute.zpow_right hxt n).eq).symm
  exact ⟨Subgroup.zpowers (unitTransv d u), hTne, hT2, hTle, hxN⟩

private theorem exists_T_of_not_le_layer [CharP F 2] (hF : Nat.card F = 2) (hℓ : 3 ≤ ℓ)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d {X ^ 2 + X + 1}, spSupported d {X ^ 2 + X + 1}⁆)
    (hne : primaryComponent (spEnd d) (X ^ 2 + X + 1) ≠ ⊥)
    (hAq : A ≤ spSupported d {X ^ 2 + X + 1}) (hnot : ¬ A ≤ stdLayer d) :
    ∃ T : Subgroup ↥(StatedSp ℓ F), T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ stdLayer d ∧
      A = (A ⊓ stdLayer d) ⊔ (A ⊓ Subgroup.normalizer (T : Set ↥(StatedSp ℓ F))) := by
  have hQ := isQuasisimple_layer_of_stdElt hd hK
  have h8 := eight_le_finrank_unitary hF hd.2.2.1 hd.2.1 hQ
  obtain ⟨x, u, j, hxA, hxK, _hj3, huW, hu0, hQu, hxu, _hx3, hxd⟩ :=
    exists_isotropic_eigenvector_of_not_le_layer hF hA hd hnot (by omega)
  obtain ⟨T, hT1, hT2, hTle, hxN⟩ :=
    exists_T_normalizing_x_of_eigenvector hF hd hK huW hu0 hQu hxu hxd
  refine ⟨T, hT1, hT2, hTle, ?_⟩
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro a ha
  have hxK' : x ∉ ⁅spSupported d {X ^ 2 + X + 1}, spSupported d {X ^ 2 + X + 1}⁆ := by
    rwa [hK] at hxK
  obtain ⟨i, hi3, hai⟩ := exists_mul_pow_mem_commutator hF hd.2.2.1 hd.2.1 hQ
    (hAq hxA) hxK' (hAq ha)
  have h1 : a * x ^ i ∈ A ⊓ stdLayer d :=
    ⟨A.mul_mem ha (A.pow_mem hxA i), by rwa [hK]⟩
  let N : Subgroup ↥(StatedSp ℓ F) :=
    Subgroup.normalizer (T : Set ↥(StatedSp ℓ F))
  have hxN' : x ∈ N := hxN
  have h2 : (x ^ i)⁻¹ ∈ A ⊓ N :=
    ⟨A.inv_mem (A.pow_mem hxA i), N.inv_mem (N.pow_mem hxN' i)⟩
  have heq : (a * x ^ i) * (x ^ i)⁻¹ = a := by group
  rw [← heq]
  exact Subgroup.mul_mem_sup h1 h2

theorem stdOutcome_unitary (hF : Nat.card F = 2) (hℓ : 3 ≤ ℓ)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d {X ^ 2 + X + 1}, spSupported d {X ^ 2 + X + 1}⁆) :
    StdVanishes A d ∨ StdExtendsN 3 A d := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num)
  by_cases hv : StdVanishes A d
  · exact Or.inl hv
  · right
    have hQ := isQuasisimple_layer_of_stdElt hd hK
    have h8 := eight_le_finrank_unitary hF hd.2.2.1 hd.2.1 hQ
    have hne : primaryComponent (spEnd d) (X ^ 2 + X + 1) ≠ ⊥ := by
      intro h
      rw [h] at h8
      simp at h8
    have h3 : 3 ≤ Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) := by
      omega
    obtain ⟨r, hr1, hr0, hfix⟩ := exists_r_fixes_of_not_vanishes hF hℓ hA hd hK hne hv
    have hAq : A ≤ spSupported d {X ^ 2 + X + 1} := le_quad_of_eqOn_fixed hF hA hd hfix
    obtain ⟨y, hyA, hyK, hy3, hyA'⟩ :=
      exists_y_hyperbolic hF hA hd hK hne hr1 hr0 hAq
    refine ⟨?_, y, hyA, hyK, hy3, hyA'⟩
    by_cases hAle : A ≤ stdLayer d
    · exact exists_T_of_le_layer hF hd hK h3 hAle
    · exact exists_T_of_not_le_layer hF hℓ hA hd hK hne hAq hAle

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
