module

public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.L2Order

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.RankThree.PartTwo.KFacts

theorem cube_ne_four_five (n : ℕ) : n ^ 3 ≠ 4 ∧ n ^ 3 ≠ 5 := by
  have hn : n < 2 ∨ 2 ≤ n := by omega
  rcases hn with hn | hn
  · interval_cases n <;> simp
  · have : 2 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
    omega

theorem fieldAut_cube_facts (hU : L2OrderUnique) (hF : L2FieldFixed) {Q : Type} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) {α : MulAut Q} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hfld : IsFieldAutPSLn 2 α) {q : ℕ} (hq : IsTypeL2 q Q) (hq3 : ¬ 3 ∣ q) (hq8 : q ≠ 8) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (θ : (Q ⧸ Subgroup.center Q) ≃* StatedProj (StatedSL 2 F))
      (F₀ : Type) (_ : Field F₀) (_ : Finite F₀),
      4 ≤ Nat.card F₀ ∧ q = Nat.card F₀ ^ 3 ∧
      Nonempty (↥(fixSub (MulAut.congr θ (centerDescend Q α))) ≃* StatedProj (StatedSL 2 F₀)) ∧
      MulAut.congr θ (centerDescend Q α) ≠ 1 := by
  obtain ⟨F, hFf, hFfin, θ, σ, φ, γ, hφ, hθ⟩ := id hfld
  set β : MulAut (StatedProj (StatedSL 2 F)) := MulAut.congr θ (centerDescend Q α) with hβdef
  have hβ3 : β ^ 3 = 1 := by
    rw [hβdef, ← map_pow, ← map_pow, hα3, map_one, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα1
    apply eq_one_of_centerDescend_eq_one hQ
    apply (MulAut.congr θ).injective
    rw [← hβdef, h, map_one]
  have hβeq : β = γ * φ * γ⁻¹ := by
    apply MulEquiv.ext
    intro z
    obtain ⟨z', rfl⟩ := θ.surjective z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z'
    rw [hβdef, descend_apply_mk]
    exact hθ y
  obtain ⟨F₀, hF₀f, hF₀fin, hcard, hiso⟩ := hF F β hβ3 hβ1 σ φ γ hφ hβeq
  have hF' : IsTypeL2 (Nat.card F) Q := ⟨F, hFf, hFfin, rfl, ⟨θ⟩⟩
  have hqF : q = Nat.card F := by
    rcases hU Q (Nat.card F) q hF' hq with h | ⟨h4, h5⟩ | ⟨h5, h4⟩
    · exact h.symm
    · exact absurd (hcard ▸ h4) (cube_ne_four_five _).1
    · exact absurd (hcard ▸ h5) (cube_ne_four_five _).2
  have hq0 : 4 ≤ Nat.card F₀ := by
    have h2 : 2 ≤ Nat.card F₀ := by
      have := Finite.one_lt_card (α := F₀)
      omega
    by_contra hlt
    push Not at hlt
    interval_cases hq0 : Nat.card F₀
    · exact hq8 (by rw [hqF, hcard]; norm_num)
    · exact hq3 (by rw [hqF, hcard]; norm_num)
  exact ⟨F, hFf, hFfin, θ, F₀, hF₀f, hF₀fin, hq0, hqF.trans hcard, hiso, hβ1⟩

theorem cube_of_fieldAut (hU : L2OrderUnique) (hF : L2FieldFixed) {Q : Type} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) {α : MulAut Q} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hfld : IsFieldAutPSLn 2 α) {q : ℕ} (hq : IsTypeL2 q Q) (hq3 : ¬ 3 ∣ q) (hq8 : q ≠ 8) :
    ∃ q0 : ℕ, 4 ≤ q0 ∧ q = q0 ^ 3 := by
  obtain ⟨-, -, -, -, F₀, -, -, h4, hq0, -⟩ := fieldAut_cube_facts hU hF hQ hα3 hα1 hfld hq hq3 hq8
  exact ⟨_, h4, hq0⟩

theorem not_isInnerAut_descend_of_fieldAut (hU : L2OrderUnique) (hF : L2FieldFixed) {Q : Type}
    [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) {α : MulAut Q} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hfld : IsFieldAutPSLn 2 α) {q : ℕ} (hq : IsTypeL2 q Q) (hq3 : ¬ 3 ∣ q) (hq8 : q ≠ 8) :
    ¬ IsInnerAut (centerDescend Q α) := by
  obtain ⟨F, hFf, hFfin, θ, F₀, hF₀f, hF₀fin, h4, -, ⟨e⟩, hβ1⟩ :=
    fieldAut_cube_facts hU hF hQ hα3 hα1 hfld hq hq3 hq8
  intro hinn
  obtain ⟨g, hg⟩ := (isInnerAut_congr θ _).2 hinn
  apply hβ1
  rw [← hg]
  have hgfix : g ∈ fixSub (MulAut.congr θ (centerDescend Q α)) := by
    rw [mem_fixSub, ← hg]
    simp [MulAut.conj_apply]
  have hcen : Subgroup.center ↥(fixSub (MulAut.congr θ (centerDescend Q α))) = ⊥ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns.center_eq_bot_of_mulEquiv' e
      (l2fld_isQuasisimple_psl2 h4).2
  have hz : (⟨g, hgfix⟩ : ↥(fixSub (MulAut.congr θ (centerDescend Q α)))) ∈
      Subgroup.center ↥(fixSub (MulAut.congr θ (centerDescend Q α))) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hy : MulAut.conj g (y : StatedProj (StatedSL 2 F)) = y := by
      rw [hg]
      exact y.2
    simp only [MulAut.conj_apply] at hy
    show (y : StatedProj (StatedSL 2 F)) * g = g * y
    calc (y : StatedProj (StatedSL 2 F)) * g = (g * y * g⁻¹) * g := by rw [hy]
      _ = g * y := by group
  rw [hcen, Subgroup.mem_bot] at hz
  have : g = 1 := congrArg Subtype.val hz
  rw [this, map_one]

end CFSG.HardMathSupport.Dickson.Sec6.I1431
