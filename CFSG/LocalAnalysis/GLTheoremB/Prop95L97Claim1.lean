module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Quot
public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97QGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.L97

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Claim1

variable {G : Type} [Group G] [Finite G]

theorem chief_le_M {p : ℕ} {M D X W : Subgroup G} (h : Lemma97Chief p M D X W) :
    W ≤ M := h.le_core.trans (GLAPPrimeCoreOf_le p M)

theorem piM_comm_of_commutator_mem {M : Subgroup G} {a b : ↥M}
    (h : ⁅(a : G), (b : G)⁆ ∈ pCoreOf 2 M) : piM M a * piM M b = piM M b * piM M a := by
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, piM_eq_one_iff]
  simpa [commutatorElement_def] using h

theorem lemma97_Qdata {p : ℕ} {M D X W : Subgroup G} (hD : Prop95Hyp p M D)
    (h : Lemma97Chief p M D X W) :
    IsPGroup 2 (tl M (gammaD D)) ∧ (tl M W).Normal ∧ (tl M X).Normal ∧ tl M X ≤ tl M W ∧
      ∀ t ∈ tl M (gammaD D), ∀ x ∈ tl M X, t * x = x * t := by
  refine ⟨isPGroup_tl (isPGroup_gammaD D), tl_normal h.normalW, tl_normal h.normalX,
    tl_mono h.lt.le, ?_⟩
  intro t ht x hx
  obtain ⟨a, ha, rfl⟩ := mem_tl.1 ht
  obtain ⟨b, hb, rfl⟩ := mem_tl.1 hx
  refine piM_comm_of_commutator_mem ?_
  exact h.commX (Subgroup.commutator_mem_commutator ha hb)

theorem claim1 {p : ℕ} {M D X W : Subgroup G} (hD : Prop95Hyp p M D)
    (h : Lemma97Chief p M D X W) :
    ¬ ⁅gammaD D, W⁆ ≤ X ∧ ¬ (∀ w ∈ W, ∃ k : ℕ, w ^ (2 ^ k) ∈ X) := by
  have hΓM := gammaD_le_of_hyp hD
  have hWM : W ≤ M := (chief_le_M h)
  obtain ⟨hT, hWn, hXn, hXWt, hTX⟩ := lemma97_Qdata hD h
  have key : ⁅tl M (gammaD D), tl M W⁆ = ⊥ → ⁅gammaD D, W⁆ ≤ pCoreOf 2 M := by
    intro hbot g hg
    have hgM : g ∈ M := commutator_le_of_le hΓM hWM hg
    have h1 : piM M ⟨g, hgM⟩ ∈ tl M ⁅gammaD D, W⁆ := piM_mem_tl hg
    rw [tl_commutator hΓM hWM, hbot, Subgroup.mem_bot, piM_eq_one_iff] at h1
    exact h1
  refine ⟨fun hc => h.comm_ne (key ?_), fun hc => h.comm_ne (key ?_)⟩
  · refine QGroup.commutator_eq_bot_of_commutator_le (hO_Mt M) hT hWn hXn hXWt hTX ?_
    rw [← tl_commutator hΓM hWM]
    exact tl_mono hc
  · refine QGroup.commutator_eq_bot_of_pGroup_quotient (hO_Mt M) hT hWn hXn hXWt hTX ?_
    intro w hw
    obtain ⟨a, ha, rfl⟩ := mem_tl.1 hw
    obtain ⟨k, hk⟩ := hc a ha
    refine ⟨k, ?_⟩
    have : piM M a ^ (2 ^ k) = piM M (a ^ (2 ^ k)) := (map_pow _ _ _).symm
    rw [this]
    exact piM_mem_tl (by simpa using hk)

theorem mul_pow_two_pow_mem_of_commutator_le {W X : Subgroup G} (hXW : X ≤ W)
    (hWN : W ≤ Subgroup.normalizer (X : Set G)) (hab : ⁅W, W⁆ ≤ X) {w w' : G} (hw : w ∈ W)
    (hw' : w' ∈ W) {a b : ℕ} (ha : w ^ (2 ^ a) ∈ X) (hb : w' ^ (2 ^ b) ∈ X) :
    (w * w') ^ (2 ^ (a + b)) ∈ X := by
  haveI : (X.subgroupOf W).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXW).2 hWN
  let f := QuotientGroup.mk' (X.subgroupOf W)
  have hker : ∀ x : ↥W, f x = 1 ↔ (x : G) ∈ X := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcomm : f ⟨w, hw⟩ * f ⟨w', hw'⟩ = f ⟨w', hw'⟩ * f ⟨w, hw⟩ := by
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, hker]
    simpa [commutatorElement_def] using hab (Subgroup.commutator_mem_commutator hw hw')
  have h1 : f ⟨w, hw⟩ ^ (2 ^ a) = 1 := by
    rw [← map_pow, hker]
    simpa using ha
  have h2 : f ⟨w', hw'⟩ ^ (2 ^ b) = 1 := by
    rw [← map_pow, hker]
    simpa using hb
  have h3 : f (⟨w, hw⟩ * ⟨w', hw'⟩) ^ (2 ^ (a + b)) = 1 := by
    rw [map_mul, Commute.mul_pow hcomm, pow_add, pow_mul, pow_mul', h1, h2]
    simp
  have h4 : f ((⟨w, hw⟩ * ⟨w', hw'⟩) ^ (2 ^ (a + b))) = 1 := by rw [map_pow]; exact h3
  have := (hker _).1 h4
  simpa using this

theorem lemma97_two_power_mem {p : ℕ} {M D X W : Subgroup G} (hD : Prop95Hyp p M D)
    (h : Lemma97Chief p M D X W) (hab : ⁅W, W⁆ ≤ X) :
    ∀ w ∈ W, (∃ k : ℕ, w ^ (2 ^ k) ∈ X) → w ∈ X := by
  have hWM : W ≤ M := (chief_le_M h)
  have hXW : X ≤ W := h.lt.le
  have hXM : X ≤ M := hXW.trans hWM
  have hXN : M ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).1 h.normalX
  have hWN : M ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWM).1 h.normalW
  have hWXN : W ≤ Subgroup.normalizer (X : Set G) := hWM.trans hXN
  let V2 : Subgroup G :=
    { carrier := {w | w ∈ W ∧ ∃ k : ℕ, w ^ (2 ^ k) ∈ X}
      one_mem' := ⟨W.one_mem, 0, by simpa using X.one_mem⟩
      mul_mem' := by
        rintro w w' ⟨hw, a, ha⟩ ⟨hw', b, hb⟩
        exact ⟨W.mul_mem hw hw', a + b,
          mul_pow_two_pow_mem_of_commutator_le hXW hWXN hab hw hw' ha hb⟩
      inv_mem' := by
        rintro w ⟨hw, a, ha⟩
        refine ⟨W.inv_mem hw, a, ?_⟩
        rw [inv_pow]
        exact X.inv_mem ha }
  have hV2M : V2 ≤ M := fun w hw => hWM hw.1
  have hconj : ∀ m ∈ M, ∀ w ∈ V2, m * w * m⁻¹ ∈ V2 := by
    rintro m hm w ⟨hw, k, hk⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hWN hm) w).1 hw, k, ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 (hXN hm) _).1 hk
    simpa [conj_pow] using this
  have hV2n : (V2.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hV2M]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hconj m hm w hw, fun hw => ?_⟩
    have := hconj m⁻¹ (M.inv_mem hm) _ hw
    simpa [mul_assoc] using this
  have hXV2 : X ≤ V2 := fun x hx => ⟨hXW hx, 0, by simpa using hx⟩
  have hV2W : V2 ≤ W := fun w hw => hw.1
  rcases h.chief V2 hV2M hV2n hXV2 hV2W with h2 | h2
  · intro w hw hk
    have : w ∈ V2 := ⟨hw, hk⟩
    rwa [h2] at this
  · exfalso
    refine (claim1 hD h).2 fun w hw => ?_
    have : w ∈ V2 := by rwa [h2]
    exact this.2

theorem commutator_pow_of_commute {R : Type*} [Group R] {a w : R}
    (hc : Commute a ⁅a, w⁆) (n : ℕ) : ⁅a ^ n, w⁆ = ⁅a, w⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ⁅a ^ (n + 1), w⁆ = a * ⁅a ^ n, w⁆ * (a⁻¹ * ⁅a, w⁆) := by
      simp only [commutatorElement_def, pow_succ', mul_inv_rev]
      group
    rw [e, ih, pow_succ]
    have h2 : a * ⁅a, w⁆ ^ n = ⁅a, w⁆ ^ n * a := (hc.pow_right n).eq
    calc a * ⁅a, w⁆ ^ n * (a⁻¹ * ⁅a, w⁆) = (a * ⁅a, w⁆ ^ n) * a⁻¹ * ⁅a, w⁆ := by group
      _ = (⁅a, w⁆ ^ n * a) * a⁻¹ * ⁅a, w⁆ := by rw [h2]
      _ = ⁅a, w⁆ ^ n * ⁅a, w⁆ := by group

theorem lemma97_false_of_commutator_le_normalizer {p : ℕ} {M D X W : Subgroup G}
    (hD : Prop95Hyp p M D) (h : Lemma97Chief p M D X W) (hab : ⁅W, W⁆ ≤ X)
    (hN : ⁅gammaD D, W⁆ ≤ Subgroup.normalizer (gammaD D : Set G)) : False := by
  have hΓM := gammaD_le_of_hyp hD
  have hWM : W ≤ M := (chief_le_M h)
  have hXM : X ≤ M := h.lt.le.trans hWM
  have hWN : M ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWM).1 h.normalW
  have hstar := lemma97_two_power_mem hD h hab
  haveI : (X.subgroupOf M).Normal := h.normalX
  let πx := QuotientGroup.mk' (X.subgroupOf M)
  have hker : ∀ x : ↥M, πx x = 1 ↔ (x : G) ∈ X := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  refine (claim1 hD h).1 ?_
  rw [Subgroup.commutator_le]
  intro γ hγ w hw
  have hγM : γ ∈ M := hΓM hγ
  have hwM : w ∈ M := hWM hw
  have hcW : ⁅γ, w⁆ ∈ W := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (hWN hγM) w).1 hw
    simpa [commutatorElement_def, mul_assoc] using W.mul_mem h1 (W.inv_mem hw)
  have hcN : ⁅γ, w⁆ ∈ Subgroup.normalizer (gammaD D : Set G) :=
    hN (Subgroup.commutator_mem_commutator hγ hw)
  have h1 : ⁅γ, ⁅γ, w⁆⁆ ∈ gammaD D := by
    have h3 := (Subgroup.mem_normalizer_iff.1 hcN γ⁻¹).1 ((gammaD D).inv_mem hγ)
    have := (gammaD D).mul_mem hγ h3
    simpa [commutatorElement_def, mul_assoc] using this
  have h2 : ⁅γ, ⁅γ, w⁆⁆ ∈ W := by
    have h4 := (Subgroup.mem_normalizer_iff.1 (hWN hγM) _).1 hcW
    simpa [commutatorElement_def, mul_assoc] using W.mul_mem h4 (W.inv_mem hcW)
  have hX2 : ⁅γ, ⁅γ, w⁆⁆ ∈ X := by
    refine hstar _ h2 ?_
    obtain ⟨k, hk⟩ := isPGroup_gammaD D ⟨_, h1⟩
    refine ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [this]
    exact X.one_mem
  obtain ⟨k, hk⟩ := isPGroup_gammaD D ⟨γ, hγ⟩
  have hγk : γ ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  set γ' : ↥M := ⟨γ, hγM⟩
  set w' : ↥M := ⟨w, hwM⟩
  have hcomm : Commute (πx γ') ⁅πx γ', πx w'⁆ := by
    show πx γ' * ⁅πx γ', πx w'⁆ = ⁅πx γ', πx w'⁆ * πx γ'
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, ← map_commutatorElement,
      hker]
    exact hX2
  have h5 := commutator_pow_of_commute hcomm (2 ^ k)
  have h6 : πx γ' ^ (2 ^ k) = 1 := by
    rw [← map_pow]
    have : γ' ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hγk)
    rw [this, map_one]
  rw [h6, ← map_commutatorElement, ← map_pow, commutatorElement_one_left] at h5
  have h7 := (hker _).1 h5.symm
  have h8 : ⁅γ, w⁆ ^ (2 ^ k) ∈ X := h7
  exact hstar _ hcW ⟨k, h8⟩

end Claim1

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.L97
