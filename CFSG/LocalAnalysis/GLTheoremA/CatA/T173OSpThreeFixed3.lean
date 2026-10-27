module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeFixed2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
  CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LieType.SeitzGeneration
open Polynomial Module
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {ℓ : ℕ}

local notation "V" => (Fin ℓ ⊕ Fin ℓ → F)

private theorem isTotallyIsotropic_spForm [CharP F 2] {W : Submodule F V}
    (h : ∀ u ∈ W, ∀ v ∈ W, spForm ℓ F u v = 0) :
    (CFSG.LieType.BorelTits.spForm ℓ F).IsTotallyIsotropic W := by
  intro w hw
  rw [CFSG.LieType.BorelTits.ReflForm.mem_perp]
  intro v hv
  have h' : (CFSG.LieType.BorelTits.spForm ℓ F).β w v = 0 := by
    rw [CFSG.LieType.BorelTits.spForm_β]
    have h1 := h w hw v hv
    rwa [CFSG.RankThree.Classical.spForm_apply] at h1
  rw [CFSG.LieType.BorelTits.ReflForm.β_swap_of_alt (F := CFSG.LieType.BorelTits.spForm ℓ F)
    (CFSG.LieType.BorelTits.spForm_self ℓ F) w v, h', neg_zero]

private theorem not_isotropic_of_eq_quad [CharP F 2] {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) {W : Submodule F V} (hW0 : W ≠ ⊥)
    (hWiso : ∀ u ∈ W, ∀ v ∈ W, spForm ℓ F u v = 0)
    (hWle3 : W ≤ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hWeq : W = primaryComponent (spEnd d) (X ^ 2 + X + 1)) : False := by
  have hW3ne : primaryComponent (spEnd d) (X ^ 2 + X + 1) ≠ ⊥ := by rwa [← hWeq]
  obtain ⟨s', hs', hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW3ne
  have hnd := nondegenerate_normKer (three_ne_zero_of_charP_two (F := F)) hd3
  rw [← primaryComponent_quad_eq_normKer] at hnd
  have h1' : (⟨s', hs'⟩ : ↥(primaryComponent (spEnd d) (X ^ 2 + X + 1))) = 0 := by
    refine hnd.1 ⟨s', hs'⟩ fun y => ?_
    have hsW : s' ∈ W := by rw [hWeq]; exact hs'
    have hyW : y.1 ∈ W := by rw [hWeq]; exact y.2
    simpa [LinearMap.BilinForm.restrict_apply] using hWiso s' hsW y.1 hyW
  exact hs0 (congrArg Subtype.val h1')

private theorem commutator_le_centralizer_singleton {G : Type*} [Group G]
    {H : Subgroup G} {a : G} (h : H ≤ Subgroup.centralizer ({a} : Set G)) :
    ⁅H, H⁆ ≤ Subgroup.centralizer ({a} : Set G) := by
  refine Subgroup.commutator_le.mpr fun u hu v hv => ?_
  have huC : u ∈ Subgroup.centralizer ({a} : Set G) := h hu
  have hvC : v ∈ Subgroup.centralizer ({a} : Set G) := h hv
  rw [commutatorElement_def]
  exact (Subgroup.centralizer _).mul_mem
    ((Subgroup.centralizer _).mul_mem
      ((Subgroup.centralizer _).mul_mem huC hvC) ((Subgroup.centralizer _).inv_mem huC))
    ((Subgroup.centralizer _).inv_mem hvC)

private theorem mem_zpowers_of_fixes_fixed [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆)
    {a : ↥(StatedSp ℓ F)} (ha : a ∈ A) (had : a * d = d * a)
    (hfix : ∀ v ∈ primaryComponent (spEnd d) (X - 1), spEnd a v = v) :
    a ∈ Subgroup.zpowers d := by
  have hd3 : d ^ 3 = 1 := hd.2.2.1
  have hcommF : ∀ g ∈ spFixedFactor d, a * g = g * a := fun g hg =>
    commute_fixed_of_fixes hF hd3 hg had hfix
  have hle : spFixedFactor d ≤ Subgroup.centralizer ({a} : Set ↥(StatedSp ℓ F)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hcommF g hg
  have hleK : stdLayer d ≤ Subgroup.centralizer ({a} : Set ↥(StatedSp ℓ F)) := by
    rw [hK]
    exact commutator_le_centralizer_singleton hle
  have haC : a ∈ Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' := hleK hx
    rw [Subgroup.mem_centralizer_iff] at hx'
    exact (hx' a (Set.mem_singleton a)).symm
  have hmem : a ∈ A ⊓ Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F)) :=
    ⟨ha, haC⟩
  rwa [hd.2.2.2.2] at hmem

theorem inf_quad_le_zpowers_of_std [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)}
    {d : ↥(StatedSp ℓ F)} (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆) :
    A ⊓ spSupported d ({X ^ 2 + X + 1} : Set F[X]) ≤ Subgroup.zpowers d := by
  have hd3 : d ^ 3 = 1 := hd.2.2.1
  have hF3C : spSupported d ({X ^ 2 + X + 1} : Set F[X]) ≤
      Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F)) := by
    rw [hK]
    exact spSupported_unitary_le_centralizer_fixed_commutator hd3
  exact inf_spSupported_le_zpowers hd hF3C

private theorem length_le_half_add_two [CharP F 2] (hF : Nat.card F = 2) (hℓ : 3 ≤ ℓ)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆)
    {s : ℕ} (hs : spFixedDim d = 2 * s) : ℓ ≤ s + 2 := by
  have hd3 : d ^ 3 = 1 := hd.2.2.1
  have hd1 : d ≠ 1 := hd.2.1
  have hdA : d ∈ A := hd.1
  have hAel : CFSG.Open.IsElemAbelian 3 A := hA.1
  have hAcard : Nat.card A = 3 ^ (ℓ - 1) := by
    rw [hA.2.1, twoLocalRank_three_statedSp hF (by omega)]
  have hAcomm : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  have hAexp : ∀ g ∈ A, g ^ 3 = 1 := hAel.2
  have had : ∀ a ∈ A, a * d = d * a := fun a ha => hAcomm a ha d hdA
  have hstabW1 : ∀ a ∈ A, ∀ v ∈ primaryComponent (spEnd d) (X - 1),
      spEnd a v ∈ primaryComponent (spEnd d) (X - 1) := by
    intro a ha v hv
    have hsa : Commute (spEnd a) (spEnd d) := by
      show spEnd a * spEnd d = spEnd d * spEnd a
      rw [← spEnd_mul, ← spEnd_mul, had a ha]
    exact apply_mem_primaryComponent hsa hv
  have hle2 := card_le_card_mul_pow_restrict (N := Subgroup.zpowers d) hF hAcomm hAexp
    hstabW1 fun a ha hfix => mem_zpowers_of_fixes_fixed hF hd hK ha (had a ha) hfix
  have hdorder : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hfinW1 : Module.finrank F (primaryComponent (spEnd d) (X - 1)) = 2 * s := hs
  have hle2' : 3 ^ (ℓ - 1) ≤ 3 * 3 ^ s := by
    rw [hAcard, hdorder] at hle2
    rwa [hfinW1, Nat.mul_div_cancel_left s (by norm_num)] at hle2
  have h3 : 3 ^ (ℓ - 1) ≤ 3 ^ (s + 1) := by
    calc 3 ^ (ℓ - 1) ≤ 3 * 3 ^ s := hle2'
      _ = 3 ^ (s + 1) := by rw [pow_succ']
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h3
  omega

private theorem exists_invariant_isotropic [CharP F 2] {A : Subgroup ↥(StatedSp ℓ F)}
    {d : ↥(StatedSp ℓ F)} (hv : ¬ StdVanishes A d) :
    ∃ W : Submodule F V, W ≠ ⊥ ∧ (∀ u ∈ W, ∀ v ∈ W, spForm ℓ F u v = 0) ∧
      ∀ g ∈ innerClosure A d ⊔ A, ∀ w ∈ W, spEnd g w ∈ W := by
  have hv' : ∃ T : Subgroup ↥(StatedSp ℓ F), T ≠ ⊥ ∧ IsPGroup 2 ↥T ∧
      innerClosure A d ⊔ A ≤ Subgroup.normalizer (T : Set ↥(StatedSp ℓ F)) := by
    by_contra h
    exact hv h
  obtain ⟨T, hTne, hT2, hTE⟩ := hv'
  exact exists_isotropic_of_le_normalizer hT2 hTne hTE

private theorem inf_fixed_eq_bot [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆)
    {W : Submodule F V} (hWiso : ∀ u ∈ W, ∀ v ∈ W, spForm ℓ F u v = 0)
    (hWE : ∀ g ∈ innerClosure A d ⊔ A, ∀ w ∈ W, spEnd g w ∈ W) :
    W ⊓ primaryComponent (spEnd d) (X - 1) = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Submodule.mem_bot]
  by_contra hu0
  have hd3 : d ^ 3 = 1 := hd.2.2.1
  have hufix : spEnd d u = u := by
    have hu' : u ∈ CFSG.LieType.SeitzGeneration.fixSub d := by
      rw [← primaryComponent_sub_one_eq_fixSub]
      exact hu.2
    exact CFSG.LieType.SeitzGeneration.mem_fixSub.mp hu'
  obtain ⟨v, hv1, huv⟩ := exists_spForm_eq_one_of_mem_primary hF hd3 (Or.inl rfl) hu.2 hu0
  have hvfix : spEnd d v = v := by
    have hv1' : v ∈ CFSG.LieType.SeitzGeneration.fixSub d := by
      rw [← primaryComponent_sub_one_eq_fixSub]
      exact hv1
    exact CFSG.LieType.SeitzGeneration.mem_fixSub.mp hv1'
  have htu : spTransvection u (1 : F) ∈ spFixedFactor d :=
    spTransvection_mem_spFixedFactor hufix 1
  have htv : spTransvection v (1 : F) ∈ spFixedFactor d :=
    spTransvection_mem_spFixedFactor hvfix 1
  set κ : ↥(StatedSp ℓ F) :=
    ⁅spTransvection u (1 : F), spTransvection v (1 : F)⁆ with hκdef
  have hκK : κ ∈ stdLayer d := by
    rw [hK]
    exact Subgroup.commutator_mem_commutator htu htv
  have hκE : κ ∈ innerClosure A d ⊔ A :=
    Subgroup.mem_sup_left (le_closureIn_self _ _ hκK)
  have hκW : ∀ w ∈ W, spEnd κ w ∈ W := fun w hw => hWE κ hκE w hw
  have hmove : spEnd κ u - u = v := by
    have h := spEnd_commutator_transvection huv u
    rw [spForm_isAlt u, zero_smul, zero_add, huv, one_smul, add_zero] at h
    change spEnd ⁅spTransvection u (1 : F), spTransvection v (1 : F)⁆ u - u = v
    rw [h]
    abel
  exact false_of_isotropic_of_move hWiso hκW hu.1 hmove huv

private theorem le_quad_of_invariant [CharP F 2] {A : Subgroup ↥(StatedSp ℓ F)}
    {d : ↥(StatedSp ℓ F)} (hd : IsStdElt 3 A d) {W : Submodule F V}
    (hdisj1 : W ⊓ primaryComponent (spEnd d) (X - 1) = ⊥)
    (hWA : ∀ a ∈ A, ∀ w ∈ W, spEnd a w ∈ W) :
    W ≤ primaryComponent (spEnd d) (X ^ 2 + X + 1) := by
  have hd3 : d ^ 3 = 1 := hd.2.2.1
  have hdA : d ∈ A := hd.1
  have hWd : ∀ w ∈ W, spEnd d w ∈ W := hWA d hdA
  intro w hw
  have hdw : spEnd d w ∈ W := hWd w hw
  have hddw : spEnd d (spEnd d w) ∈ W := hWd _ hdw
  have h1 : ((spEnd d ^ 2 + spEnd d + 1 : Module.End F V)) w ∈ W := by
    have h := W.add_mem (W.add_mem hddw hdw) hw
    simpa [pow_two, Module.End.mul_apply, LinearMap.add_apply] using h
  have h2 : ((spEnd d ^ 2 + spEnd d + 1 : Module.End F V)) w ∈
      primaryComponent (spEnd d) (X - 1) := (split_primary hd3 w).1
  have h0 : ((spEnd d ^ 2 + spEnd d + 1 : Module.End F V)) w = 0 := by
    have hin : ((spEnd d ^ 2 + spEnd d + 1 : Module.End F V)) w ∈
        W ⊓ primaryComponent (spEnd d) (X - 1) := ⟨h1, h2⟩
    rw [hdisj1] at hin
    simpa using hin
  have h3 := (split_primary hd3 w).2.2
  rw [h0, zero_add] at h3
  rw [h3]
  exact (split_primary hd3 w).2.1

private theorem finrank_quad_eq_two_mul_sub [CharP F 2] {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) {s : ℕ} (hs : spFixedDim d = 2 * s) :
    Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) = 2 * (ℓ - s) := by
  have hsum := finrank_primaryComponent_fixed_add_quad (ℓ := ℓ) hd3
  have hfin : Module.finrank F (primaryComponent (spEnd d) (X - 1)) = 2 * s := hs
  omega

private theorem exists_moved_vector {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {W : Submodule F V} (hW0 : W ≠ ⊥)
    (hdisj1 : W ⊓ primaryComponent (spEnd d) (X - 1) = ⊥) :
    ∃ r ∈ W, r ≠ 0 ∧ spEnd d r ≠ r := by
  obtain ⟨r, hrW, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  refine ⟨r, hrW, hr0, ?_⟩
  intro h
  have hrW1 : r ∈ primaryComponent (spEnd d) (X - 1) := by
    rw [primaryComponent_sub_one_eq_fixSub, CFSG.LieType.SeitzGeneration.mem_fixSub]
    exact h
  have hin : r ∈ W ⊓ primaryComponent (spEnd d) (X - 1) := ⟨hrW, hrW1⟩
  rw [hdisj1] at hin
  exact hr0 (by simpa using hin)

private theorem linearIndependent_pair_of_moved [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) {r : V} (hr0 : r ≠ 0) (hrd : spEnd d r ≠ r) :
    LinearIndependent F ![r, spEnd d r] := by
  rw [LinearIndependent.pair_iff]
  intro c c' hcc
  rcases CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_eq_one_of_card_eq_two hF c with
    rfl | rfl <;>
    rcases CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_eq_one_of_card_eq_two hF c'
      with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · rw [zero_smul, zero_add, one_smul] at hcc
    have h1 : r = 0 := by
      have h2 := congrArg (spEnd (d ^ 2)) hcc
      rwa [← Module.End.mul_apply, ← spEnd_mul, show d ^ 2 * d = d ^ 3 by group,
        hd3, spEnd_one, Module.End.one_apply, map_zero] at h2
    exact absurd h1 hr0
  · rw [zero_smul, add_zero, one_smul] at hcc
    exact absurd hcc hr0
  · rw [one_smul, one_smul] at hcc
    have hdr : spEnd d r = r := by
      have h1 : -(spEnd d r) = r := neg_eq_of_add_eq_zero_left hcc
      have hneg : -(spEnd d r) = spEnd d r := by
        rw [← neg_one_smul F (spEnd d r), CharTwo.neg_eq (1 : F), one_smul]
      rwa [hneg] at h1
    exact absurd hdr hrd

private theorem card_bound_of_invariant_isotropic [CharP F 2] (hF : Nat.card F = 2)
    (hℓ : 3 ≤ ℓ) {A : Subgroup ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    {W : Submodule F V} (hWiso : ∀ u ∈ W, ∀ v ∈ W, spForm ℓ F u v = 0)
    (hWA : ∀ a ∈ A, ∀ w ∈ W, spEnd a w ∈ W) :
    Nat.card A ≤ 3 ^ (finrank F W / 2) * 3 ^ ((finrank F V - 2 * finrank F W) / 2) := by
  have hAel : CFSG.Open.IsElemAbelian 3 A := hA.1
  have hAcomm : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)
  have hAexp : ∀ g ∈ A, g ^ 3 = 1 := hAel.2
  have hWiso' : (CFSG.LieType.BorelTits.spForm ℓ F).IsTotallyIsotropic W :=
    isTotallyIsotropic_spForm hWiso
  have hWE' : ∀ g ∈ A, ∀ w ∈ W,
      CFSG.LieType.BorelTits.natRep (StatedSp ℓ F) g w ∈ W := fun g hg w hw =>
    hWA g hg w hw
  have hpK : (3 : F) ≠ 0 := three_ne_zero_of_charP_two (F := F)
  have hdiv2 : ∀ i : ℕ, 0 < i → i < 2 → ¬ 3 ∣ Nat.card F ^ i - 1 := by
    intro i _ hi
    obtain rfl : i = 1 := by omega
    rw [pow_one, hF]
    norm_num
  exact CFSG.RankThree.PartOne.KFU.card_le_of_invariant_isotropic
    (CFSG.LieType.BorelTits.spForm ℓ F) (CFSG.LieType.BorelTits.natRep (StatedSp ℓ F))
    (CFSG.LieType.BorelTits.isIsometric_natRep_statedSp (n := ℓ) (K := F))
    (CFSG.LieType.BorelTits.natRep_injective (StatedSp ℓ F))
    Nat.prime_three (by norm_num) hpK (d := 2) (by norm_num) hdiv2 A hAcomm hAexp W
    hWiso' hWE'

private theorem dim_le_two_of_card_bound [CharP F 2] (hF : Nat.card F = 2)
    (hℓ : 3 ≤ ℓ) {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd3 : d ^ 3 = 1) {s : ℕ} (hs : spFixedDim d = 2 * s) (hℓs : ℓ ≤ s + 2)
    {W : Submodule F V} (ha2 : 2 ≤ Module.finrank F W) (hW0 : W ≠ ⊥)
    (hWiso : ∀ u ∈ W, ∀ v ∈ W, spForm ℓ F u v = 0)
    (hWle3 : W ≤ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hdimW3 : Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) = 2 * (ℓ - s))
    (hcardW : Nat.card A ≤
      3 ^ (finrank F W / 2) * 3 ^ ((finrank F V - 2 * finrank F W) / 2)) :
    Module.finrank F W ≤ 2 := by
  have hAcard : Nat.card A = 3 ^ (ℓ - 1) := by
    rw [hA.2.1, twoLocalRank_three_statedSp hF (by omega)]
  have hdimV : Module.finrank F V = 2 * ℓ := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  set a : ℕ := Module.finrank F W with ha
  have ha2' : 2 ≤ a := ha2
  have hdiv : (2 * ℓ - 2 * a) / 2 = ℓ - a := by omega
  have hineq : 3 ^ (ℓ - 1) ≤ 3 ^ (a / 2 + (ℓ - a)) := by
    have h := hcardW
    rw [hAcard, hdimV, hdiv, ← pow_add] at h
    exact h
  have hle := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hineq
  have ha4 : a ≤ 4 := by
    have h1 : a ≤ Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) :=
      Submodule.finrank_mono hWle3
    rw [hdimW3] at h1
    omega
  interval_cases a
  · omega
  · simp at hle
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 3) (by omega : ℓ - 2 < ℓ - 1)
    omega
  · have h4 : Module.finrank F W = 4 := ha.symm
    have hdimW3le : Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) ≤ 4 := by
      rw [hdimW3]; omega
    have hdimW34 : Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) = 4 :=
      le_antisymm hdimW3le (by rw [← h4]; exact Submodule.finrank_mono hWle3)
    exact (not_isotropic_of_eq_quad hd3 hW0 hWiso hWle3
      (Submodule.eq_of_le_of_finrank_eq hWle3 (by rw [h4, hdimW34]))).elim

private theorem finrank_quad_eq_four_of_lagrangian [CharP F 2] {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) {W : Submodule F V} (hW0 : W ≠ ⊥)
    (hWiso : ∀ u ∈ W, ∀ v ∈ W, spForm ℓ F u v = 0)
    (hWle3 : W ≤ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hdimW : Module.finrank F W = 2) {s : ℕ} (hℓs : ℓ ≤ s + 2)
    (hdimW3 : Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) = 2 * (ℓ - s)) :
    Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) = 4 := by
  have hle : 2 ≤ 2 * (ℓ - s) := by
    have h := Submodule.finrank_mono hWle3
    rw [hdimW, hdimW3] at h
    exact h
  have hle4 : 2 * (ℓ - s) ≤ 4 := by omega
  have hne1 : ℓ - s ≠ 1 := by
    intro h1
    have hdim2 : Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) = 2 := by
      rw [hdimW3, h1]
    exact (not_isotropic_of_eq_quad hd3 hW0 hWiso hWle3
      (Submodule.eq_of_le_of_finrank_eq hWle3 (by rw [hdimW, hdim2]))).elim
  rw [hdimW3]
  omega

private theorem quad_perp_eq_of_lagrangian [CharP F 2] {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) {W : Submodule F V}
    (hWle3 : W ≤ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hWiso : ∀ u ∈ W, ∀ v ∈ W, spForm ℓ F u v = 0)
    (hdimW3' : Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) = 4)
    (hdimW : Module.finrank F W = 2) :
    ∀ v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1),
      (∀ r ∈ W, spForm ℓ F v r = 0) → v ∈ W := by
  refine mem_of_perp_of_lagrangian hWle3 ?_ hWiso ?_
  · intro y hy h
    have hnd := nondegenerate_normKer (three_ne_zero_of_charP_two (F := F)) hd3
    rw [← primaryComponent_quad_eq_normKer] at hnd
    have h1 := hnd.1 ⟨y, hy⟩ fun x => by
      have := h x.1 x.2
      simpa [LinearMap.BilinForm.restrict_apply] using this
    exact congrArg Subtype.val h1
  · rw [hdimW3', hdimW]

private theorem span_le_eqLocus_of_eq_on_pair {f g : Module.End F V} {x y : V}
    (hx : f x = g x) (hy : f y = g y) :
    Submodule.span F {x, y} ≤ LinearMap.eqLocus f g := by
  refine Submodule.span_le.mpr ?_
  rintro z (rfl | rfl)
  · exact hx
  · exact hy

private theorem exists_pow_of_action_on_pair [CharP F 2] (hF : Nat.card F = 2)
    {A : Subgroup ↥(StatedSp ℓ F)} {d x : ↥(StatedSp ℓ F)} (hx : x ∈ A)
    {W : Submodule F V} {r : V} (hr0 : r ≠ 0)
    (hspanW : Submodule.span F {r, spEnd d r} = W) (hxrW : spEnd x r ∈ W)
    (hrW3 : r ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hdrW3 : spEnd d r ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hdx : spEnd x (spEnd d r) = spEnd d (spEnd x r)) :
    ∃ j : ℕ, j < 3 ∧ ∀ w ∈ W, spEnd x w = spEnd (d ^ j) w := by
  have hxrW' : spEnd x r ∈ Submodule.span F {r, spEnd d r} := by
    rw [hspanW]
    exact hxrW
  obtain ⟨c, c', hcc'⟩ := Submodule.mem_span_pair.mp hxrW'
  have hgen : ∀ j : ℕ, spEnd x r = spEnd (d ^ j) r →
      ∀ w ∈ W, spEnd x w = spEnd (d ^ j) w := by
    intro j hj
    have hcomm : spEnd (d ^ j) * spEnd d = spEnd d * spEnd (d ^ j) := by
      rw [← spEnd_mul, ← spEnd_mul]
      congr 1
      group
    have hsecond : spEnd x (spEnd d r) = spEnd (d ^ j) (spEnd d r) := by
      calc spEnd x (spEnd d r) = spEnd d (spEnd x r) := hdx
        _ = spEnd d (spEnd (d ^ j) r) := by rw [hj]
        _ = spEnd (d ^ j) (spEnd d r) := by
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, hcomm]
    have hspanle := span_le_eqLocus_of_eq_on_pair (f := spEnd x) (g := spEnd (d ^ j)) hj hsecond
    rw [← hspanW]
    intro w hw
    exact hspanle hw
  rcases CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_eq_one_of_card_eq_two hF c with
    rfl | rfl <;>
    rcases CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_eq_one_of_card_eq_two hF c'
      with rfl | rfl
  · exfalso
    have h0 : spEnd x r = 0 := by simpa using hcc'.symm
    have h1 : r = 0 := by
      have h2 := congrArg (spEnd x⁻¹) h0
      rwa [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one,
        Module.End.one_apply, map_zero] at h2
    exact absurd h1 hr0
  · exact ⟨1, by norm_num, hgen 1 (by simpa using hcc'.symm)⟩
  · refine ⟨0, by norm_num, hgen 0 ?_⟩
    rw [pow_zero, spEnd_one, Module.End.one_apply]
    simpa using hcc'.symm
  · refine ⟨2, by norm_num, hgen 2 ?_⟩
    rw [CFSG.LieType.SeitzGeneration.spEnd_pow d 2, pow_two, Module.End.mul_apply,
      spEnd_sq_apply_of_mem_primary hrW3]
    simpa using hcc'.symm

private theorem exists_lagrangian_data [CharP F 2] (hF : Nat.card F = 2)
    (hℓ : 3 ≤ ℓ) {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)} (hA : GLAIsBmax 3 A)
    (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆)
    {s : ℕ} (hs : spFixedDim d = 2 * s) (hv : ¬ StdVanishes A d) :
    ∃ (W : Submodule F V) (r : V), W ≠ ⊥ ∧
      (∀ a ∈ A, ∀ w ∈ W, spEnd a w ∈ W) ∧
      (∀ v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1),
        (∀ r ∈ W, spForm ℓ F v r = 0) → v ∈ W) ∧
      Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) = 4 ∧
      Submodule.span F {r, spEnd d r} = W ∧ r ∈ W ∧ r ≠ 0 ∧
      r ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1) := by
  have hd3 : d ^ 3 = 1 := hd.2.2.1
  have hdA : d ∈ A := hd.1
  obtain ⟨W, hW0, hWiso, hWE⟩ := exists_invariant_isotropic hv
  have hWA : ∀ a ∈ A, ∀ w ∈ W, spEnd a w ∈ W := fun a ha w hw =>
    hWE a (Subgroup.mem_sup_right ha) w hw
  have hdisj1 := inf_fixed_eq_bot hF hd hK hWiso hWE
  have hWle3 := le_quad_of_invariant hd hdisj1 hWA
  have hℓs := length_le_half_add_two hF hℓ hA hd hK hs
  have hdimW3 := finrank_quad_eq_two_mul_sub hd3 hs
  obtain ⟨r, hrW, hr0, hrd⟩ := exists_moved_vector hd3 hW0 hdisj1
  have hli := linearIndependent_pair_of_moved hF hd3 hr0 hrd
  have hdrW : spEnd d r ∈ W := hWA d hdA r hrW
  have hrW3 : r ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1) := hWle3 hrW
  have hdimspan : Module.finrank F (Submodule.span F {r, spEnd d r}) = 2 := by
    have h := finrank_span_eq_card hli
    rw [show Set.range ![r, spEnd d r] = ({r, spEnd d r} : Set V) from by
      ext x; simp [or_comm]] at h
    simpa using h
  have hspanle : Submodule.span F {r, spEnd d r} ≤ W :=
    Submodule.span_le.mpr (by rintro y (rfl | rfl) <;> assumption)
  have ha2 : 2 ≤ Module.finrank F W := by
    have h := Submodule.finrank_mono hspanle
    rw [hdimspan] at h
    omega
  have hcardW := card_bound_of_invariant_isotropic hF hℓ hA hWiso hWA
  have hdimW_le := dim_le_two_of_card_bound hF hℓ hA hd3 hs hℓs ha2 hW0 hWiso hWle3
    hdimW3 hcardW
  have hdimW : Module.finrank F W = 2 := by omega
  have hspanW : Submodule.span F {r, spEnd d r} = W :=
    Submodule.eq_of_le_of_finrank_eq hspanle (by rw [hdimspan, hdimW])
  have hdimW3' := finrank_quad_eq_four_of_lagrangian hd3 hW0 hWiso hWle3 hdimW hℓs hdimW3
  have hperp := quad_perp_eq_of_lagrangian hd3 hWle3 hWiso hdimW3' hdimW
  exact ⟨W, r, hW0, hWA, hperp, hdimW3', hspanW, hrW, hr0, hrW3⟩

theorem exists_lagrangian_block_of_not_stdVanishes [CharP F 2] (hF : Nat.card F = 2)
    (hℓ : 3 ≤ ℓ) {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)}
    (hA : GLAIsBmax 3 A) (hd : IsStdElt 3 A d)
    (hK : stdLayer d = ⁅spSupported d ({X - 1} : Set F[X]),
      spSupported d ({X - 1} : Set F[X])⁆)
    {s : ℕ} (hs : spFixedDim d = 2 * s) (hv : ¬ StdVanishes A d) :
    ∃ W : Submodule F V,
      (∀ a ∈ A, ∀ w ∈ W, spEnd a w ∈ W) ∧
      (∀ v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1),
        (∀ r ∈ W, spForm ℓ F v r = 0) → v ∈ W) ∧
      Module.finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1)) = 4 ∧
      (∀ x ∈ A, ∃ j : ℕ, j < 3 ∧ ∀ w ∈ W, spEnd x w = spEnd (d ^ j) w) := by
  obtain ⟨W, r, -, hWA, hperp, hdimW3', hspanW, hrW, hr0, hrW3⟩ :=
    exists_lagrangian_data hF hℓ hA hd hK hs hv
  have hd3 : d ^ 3 = 1 := hd.2.2.1
  have hdA : d ∈ A := hd.1
  have had : ∀ a ∈ A, a * d = d * a := by
    intro a ha
    have hAel : CFSG.Open.IsElemAbelian 3 A := hA.1
    exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨d, hdA⟩)
  have hdrW3 : spEnd d r ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1) :=
    apply_mem_primaryComponent (Commute.refl (spEnd d)) hrW3
  refine ⟨W, hWA, hperp, hdimW3', ?_⟩
  intro x hx
  have hdx : spEnd x (spEnd d r) = spEnd d (spEnd x r) := by
    have hsa : Commute (spEnd x) (spEnd d) := by
      show spEnd x * spEnd d = spEnd d * spEnd x
      rw [← spEnd_mul, ← spEnd_mul, had x hx]
    have h := congrArg (fun f : Module.End F V => f r) hsa.eq
    simpa [Module.End.mul_apply] using h
  exact exists_pow_of_action_on_pair hF hx hr0 hspanW (hWA x hx r hrW) hrW3 hdrW3 hdx

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
