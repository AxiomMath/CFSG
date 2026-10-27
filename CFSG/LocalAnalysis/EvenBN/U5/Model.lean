module

public import CFSG.LocalAnalysis.EvenBN.U5.Setting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankTwoLevi
public import CFSG.RankThree.CentralLiftU.HypRankOneConj
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.CentralLift.LinearTorusMonomial
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.U5K.Hyp.Parabolic
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

abbrev ιe₁ : HypIndex 2 1 := .inl 0
abbrev ιe₂ : HypIndex 2 1 := .inl 1
abbrev ιz : HypIndex 2 1 := .inr (.inl 0)
abbrev ιf₁ : HypIndex 2 1 := .inr (.inr 0)
abbrev ιf₂ : HypIndex 2 1 := .inr (.inr 1)

theorem mat_inv_apply (g : hypSU h 2 1) (a b : HypIndex 2 1) :
    mat g⁻¹ a b = h.bar (mat g (hypPartner b) (hypPartner a)) := by
  have hgram : ((mat g).map h.bar)ᵀ * hypGram 2 1 K * mat g = hypGram 2 1 K :=
    (mem_hypSU.1 g.2).1
  have hinv : mat g⁻¹ = hypGram 2 1 K * ((mat g).map h.bar)ᵀ * hypGram 2 1 K := by
    apply mat_inv_eq
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (mat g), hgram,
      hypGram_mul_self]
  rw [hinv, mul_hypGram_apply, hypGram_mul_apply]
  simp

theorem U_entries {g : hypSU h 2 1} (hg : g ∈ hypUnitriangular h 2 1) :
    (mat g ιe₁ ιe₁ = 1 ∧ mat g ιe₂ ιe₂ = 1 ∧ mat g ιz ιz = 1 ∧ mat g ιf₁ ιf₁ = 1 ∧
      mat g ιf₂ ιf₂ = 1) ∧
    (mat g ιe₂ ιe₁ = 0 ∧ mat g ιz ιe₁ = 0 ∧ mat g ιf₂ ιe₁ = 0 ∧ mat g ιf₁ ιe₁ = 0 ∧
      mat g ιz ιe₂ = 0 ∧ mat g ιf₂ ιe₂ = 0 ∧ mat g ιf₁ ιe₂ = 0 ∧ mat g ιf₂ ιz = 0 ∧
      mat g ιf₁ ιz = 0 ∧ mat g ιf₁ ιf₂ = 0) := by
  refine ⟨⟨U_diag hg _, U_diag hg _, U_diag hg _, U_diag hg _, U_diag hg _⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> exact U_lower hg (by simp)

macro "u5_mul_entry" hg:term:max hg':term:max : tactic => `(tactic| (
  obtain ⟨⟨_, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩⟩ := U_entries $hg
  obtain ⟨⟨_, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩⟩ := U_entries $hg'
  rw [mat_mul, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [Fin.sum_univ_two, *]
  try ring))

section Mul

variable {g g' : hypSU h 2 1} (hg : g ∈ hypUnitriangular h 2 1)
  (hg' : g' ∈ hypUnitriangular h 2 1)
include hg hg'

theorem mul_e₁e₂ : mat (g * g') ιe₁ ιe₂ = mat g ιe₁ ιe₂ + mat g' ιe₁ ιe₂ := by u5_mul_entry hg hg'

theorem mul_e₁z : mat (g * g') ιe₁ ιz = mat g ιe₁ ιz + mat g' ιe₁ ιz +
    mat g ιe₁ ιe₂ * mat g' ιe₂ ιz := by u5_mul_entry hg hg'

theorem mul_e₂z : mat (g * g') ιe₂ ιz = mat g ιe₂ ιz + mat g' ιe₂ ιz := by u5_mul_entry hg hg'

theorem mul_e₁f₂ : mat (g * g') ιe₁ ιf₂ = mat g ιe₁ ιf₂ + mat g' ιe₁ ιf₂ +
    mat g ιe₁ ιe₂ * mat g' ιe₂ ιf₂ + mat g ιe₁ ιz * mat g' ιz ιf₂ := by u5_mul_entry hg hg'

theorem mul_e₂f₂ : mat (g * g') ιe₂ ιf₂ = mat g ιe₂ ιf₂ + mat g' ιe₂ ιf₂ +
    mat g ιe₂ ιz * mat g' ιz ιf₂ := by u5_mul_entry hg hg'

theorem mul_zf₂ : mat (g * g') ιz ιf₂ = mat g ιz ιf₂ + mat g' ιz ιf₂ := by u5_mul_entry hg hg'

theorem mul_e₁f₁ : mat (g * g') ιe₁ ιf₁ = mat g ιe₁ ιf₁ + mat g' ιe₁ ιf₁ +
    mat g ιe₁ ιe₂ * mat g' ιe₂ ιf₁ + mat g ιe₁ ιz * mat g' ιz ιf₁ +
      mat g ιe₁ ιf₂ * mat g' ιf₂ ιf₁ := by u5_mul_entry hg hg'

theorem mul_e₂f₁ : mat (g * g') ιe₂ ιf₁ = mat g ιe₂ ιf₁ + mat g' ιe₂ ιf₁ +
    mat g ιe₂ ιz * mat g' ιz ιf₁ + mat g ιe₂ ιf₂ * mat g' ιf₂ ιf₁ := by u5_mul_entry hg hg'

theorem mul_zf₁ : mat (g * g') ιz ιf₁ = mat g ιz ιf₁ + mat g' ιz ιf₁ +
    mat g ιz ιf₂ * mat g' ιf₂ ιf₁ := by u5_mul_entry hg hg'

theorem mul_f₂f₁ : mat (g * g') ιf₂ ιf₁ = mat g ιf₂ ιf₁ + mat g' ιf₂ ιf₁ := by u5_mul_entry hg hg'

end Mul

section Relations

variable {g : hypSU h 2 1} (hg : g ∈ hypUnitriangular h 2 1)
include hg

theorem U_inv_rel : mat g ιe₁ ιe₂ + h.bar (mat g ιf₂ ιf₁) = 0 ∧
    mat g ιe₂ ιz + h.bar (mat g ιz ιf₂) = 0 ∧
    mat g ιe₁ ιz + h.bar (mat g ιz ιf₁) + mat g ιe₁ ιe₂ * h.bar (mat g ιz ιf₂) = 0 ∧
    mat g ιe₂ ιf₂ + h.bar (mat g ιe₂ ιf₂) + mat g ιe₂ ιz * h.bar (mat g ιe₂ ιz) = 0 ∧
    mat g ιe₁ ιf₂ + h.bar (mat g ιe₂ ιf₁) + mat g ιe₁ ιe₂ * h.bar (mat g ιe₂ ιf₂) +
      mat g ιe₁ ιz * h.bar (mat g ιe₂ ιz) = 0 ∧
    mat g ιe₁ ιf₁ + h.bar (mat g ιe₁ ιf₁) + mat g ιe₁ ιe₂ * h.bar (mat g ιe₁ ιf₂) +
      mat g ιe₁ ιz * h.bar (mat g ιe₁ ιz) + mat g ιe₁ ιf₂ * h.bar (mat g ιe₁ ιe₂) = 0 := by
  have hi := inv_mem hg
  have e : ∀ a b : HypIndex 2 1, a ≠ b → mat (g * g⁻¹) a b = 0 := fun a b hab => by
    rw [mul_inv_cancel, mat_one, one_apply_ne hab]
  have e1 := e ιe₁ ιe₂ (by decide)
  have e2 := e ιe₂ ιz (by decide)
  have e3 := e ιe₁ ιz (by decide)
  have e4 := e ιe₂ ιf₂ (by decide)
  have e5 := e ιe₁ ιf₂ (by decide)
  have e6 := e ιe₁ ιf₁ (by decide)
  rw [mul_e₁e₂ hg hi, mat_inv_apply] at e1
  rw [mul_e₂z hg hi, mat_inv_apply] at e2
  rw [mul_e₁z hg hi, mat_inv_apply, mat_inv_apply] at e3
  rw [mul_e₂f₂ hg hi, mat_inv_apply, mat_inv_apply] at e4
  rw [mul_e₁f₂ hg hi, mat_inv_apply, mat_inv_apply, mat_inv_apply] at e5
  rw [mul_e₁f₁ hg hi, mat_inv_apply, mat_inv_apply, mat_inv_apply, mat_inv_apply] at e6
  simp only [hypPartner_inl, hypPartner_inr_inl, hypPartner_inr_inr] at e1 e2 e3 e4 e5 e6
  exact ⟨e1, e2, e3, e4, e5, e6⟩

theorem U_rel : mat g ιf₂ ιf₁ = h.bar (mat g ιe₁ ιe₂) ∧ mat g ιz ιf₂ = h.bar (mat g ιe₂ ιz) ∧
    mat g ιz ιf₁ = h.bar (mat g ιe₁ ιz) + h.bar (mat g ιe₁ ιe₂) * h.bar (mat g ιe₂ ιz) ∧
    mat g ιe₂ ιf₁ = h.bar (mat g ιe₁ ιf₂) + h.bar (mat g ιe₁ ιe₂) * mat g ιe₂ ιf₂ +
      h.bar (mat g ιe₁ ιz) * mat g ιe₂ ιz ∧
    mat g ιe₂ ιf₂ + h.bar (mat g ιe₂ ιf₂) = mat g ιe₂ ιz * h.bar (mat g ιe₂ ιz) ∧
    mat g ιe₁ ιf₁ + h.bar (mat g ιe₁ ιf₁) = mat g ιe₁ ιz * h.bar (mat g ιe₁ ιz) +
      (mat g ιe₁ ιe₂ * h.bar (mat g ιe₁ ιf₂) + mat g ιe₁ ιf₂ * h.bar (mat g ιe₁ ιe₂)) := by
  have := h.charP
  have h2 : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  have hbb := h.bar_bar
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := U_inv_rel hg
  have r1 : mat g ιf₂ ιf₁ = h.bar (mat g ιe₁ ιe₂) := by
    have := congrArg h.bar e1
    rw [map_add, hbb, map_zero] at this
    linear_combination this - h2 (h.bar (mat g ιe₁ ιe₂))
  have r2 : mat g ιz ιf₂ = h.bar (mat g ιe₂ ιz) := by
    have := congrArg h.bar e2
    rw [map_add, hbb, map_zero] at this
    linear_combination this - h2 (h.bar (mat g ιe₂ ιz))
  refine ⟨r1, r2, ?_, ?_, ?_, ?_⟩
  · rw [r2, hbb] at e3
    have := congrArg h.bar e3
    simp only [map_add, map_mul, hbb, map_zero] at this
    linear_combination this -
      h2 (h.bar (mat g ιe₁ ιz) + h.bar (mat g ιe₁ ιe₂) * h.bar (mat g ιe₂ ιz))
  · have := congrArg h.bar e5
    simp only [map_add, map_mul, hbb, map_zero] at this
    linear_combination this - h2 (h.bar (mat g ιe₁ ιf₂) + h.bar (mat g ιe₁ ιe₂) * mat g ιe₂ ιf₂ +
      h.bar (mat g ιe₁ ιz) * mat g ιe₂ ιz)
  · linear_combination e4 - h2 (mat g ιe₂ ιz * h.bar (mat g ιe₂ ιz))
  · linear_combination e6 - h2 (mat g ιe₁ ιz * h.bar (mat g ιe₁ ιz) +
      (mat g ιe₁ ιe₂ * h.bar (mat g ιe₁ ιf₂) + mat g ιe₁ ιf₂ * h.bar (mat g ιe₁ ιe₂)))

end Relations

structure IsPattern (S : Finset (HypIndex 2 1 × HypIndex 2 1)) : Prop where
  upper : ∀ p ∈ S, fullPos p.1 < fullPos p.2
  closed : ∀ p ∈ S, ∀ c : HypIndex 2 1, fullPos p.1 < fullPos c → fullPos c < fullPos p.2 →
    (p.1, c) ∈ S ∨ (c, p.2) ∈ S
  partner : ∀ p ∈ S, (hypPartner p.2, hypPartner p.1) ∈ S

@[expose] def patSub (h : UnitaryFieldData 2 f K) (S : Finset (HypIndex 2 1 × HypIndex 2 1))
    (hS : IsPattern S) : Subgroup (hypSU h 2 1) where
  carrier := {g | g ∈ hypUnitriangular h 2 1 ∧ ∀ p ∈ S, mat g p.1 p.2 = 0}
  one_mem' := ⟨one_mem _, fun p hp => by
    rw [mat_one, one_apply_ne]
    intro e
    exact (hS.upper p hp).ne (congrArg fullPos e)⟩
  mul_mem' := by
    rintro g g' ⟨hg, hgS⟩ ⟨hg', hg'S⟩
    refine ⟨mul_mem hg hg', fun p hp => ?_⟩
    rw [mat_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_trichotomy (fullPos c) (fullPos p.1) with hc | hc | hc
    · rw [U_lower hg hc, zero_mul]
    · rw [fullPos_injective hc, hg'S p hp, mul_zero]
    · rcases lt_trichotomy (fullPos c) (fullPos p.2) with hc' | hc' | hc'
      · rcases hS.closed p hp c hc hc' with h1 | h1
        · rw [hgS _ h1, zero_mul]
        · rw [hg'S _ h1, mul_zero]
      · rw [fullPos_injective hc', hgS p hp, zero_mul]
      · rw [U_lower hg' hc', mul_zero]
  inv_mem' := by
    rintro g ⟨hg, hgS⟩
    exact ⟨inv_mem hg, fun p hp => by rw [mat_inv_apply, hgS _ (hS.partner p hp), map_zero]⟩

theorem mem_patSub {S : Finset (HypIndex 2 1 × HypIndex 2 1)} {hS : IsPattern S}
    {g : hypSU h 2 1} :
    g ∈ patSub h S hS ↔ g ∈ hypUnitriangular h 2 1 ∧ ∀ p ∈ S, mat g p.1 p.2 = 0 :=
  Iff.rfl

theorem patSub_le_U (S : Finset (HypIndex 2 1 × HypIndex 2 1)) (hS : IsPattern S) :
    patSub h S hS ≤ hypUnitriangular h 2 1 := fun _ hg => hg.1

theorem patSub_mono {S S' : Finset (HypIndex 2 1 × HypIndex 2 1)} (hS : IsPattern S)
    (hS' : IsPattern S') (hSS : S' ⊆ S) : patSub h S hS ≤ patSub h S' hS' :=
  fun _ ⟨hg, hgS⟩ => ⟨hg, fun p hp => hgS p (hSS hp)⟩

theorem patSub_inf {S S' : Finset (HypIndex 2 1 × HypIndex 2 1)} (hS : IsPattern S)
    (hS' : IsPattern S') (hSS : IsPattern (S ∪ S')) :
    patSub h S hS ⊓ patSub h S' hS' = patSub h (S ∪ S') hSS := by
  ext g
  simp only [mem_inf, mem_patSub, Finset.mem_union]
  constructor
  · rintro ⟨⟨hg, h1⟩, -, h2⟩
    exact ⟨hg, fun p hp => hp.elim (h1 p) (h2 p)⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨hg, fun p hp => h1 p (Or.inl hp)⟩, hg, fun p hp => h1 p (Or.inr hp)⟩

theorem eq_of_U_entries {g g' : hypSU h 2 1} (hg : g ∈ hypUnitriangular h 2 1)
    (hg' : g' ∈ hypUnitriangular h 2 1)
    (he : ∀ a b : HypIndex 2 1, fullPos a < fullPos b → mat g a b = mat g' a b) : g = g' := by
  apply mat_injective
  ext a b
  rcases lt_trichotomy (fullPos a) (fullPos b) with hab | hab | hab
  · exact he a b hab
  · rw [fullPos_injective hab, U_diag hg, U_diag hg']
  · rw [U_lower hg hab, U_lower hg' hab]

theorem patSub_eq_bot {S : Finset (HypIndex 2 1 × HypIndex 2 1)} (hS : IsPattern S)
    (hall : ∀ a b : HypIndex 2 1, fullPos a < fullPos b → (a, b) ∈ S) : patSub h S hS = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g ⟨hg, hgS⟩ => eq_of_U_entries hg (one_mem _)
    fun a b hab => ?_
  rw [hgS (a, b) (hall a b hab), mat_one, one_apply_ne]
  intro e
  exact hab.ne (congrArg fullPos e)

section Torus

variable {t t' : hypSU h 2 1}

theorem torus_mat (ht : t ∈ hypTorus h 2 1) : mat t = diagonal fun a => mat t a a := by
  obtain ⟨a, d, -, -, hm⟩ := ht
  change mat t = _ at hm
  rw [hm]
  congr 1
  funext x
  rw [diagonal_apply_eq]

theorem torus_offdiag (ht : t ∈ hypTorus h 2 1) {a b : HypIndex 2 1} (hab : a ≠ b) :
    mat t a b = 0 := by
  rw [torus_mat ht, diagonal_apply_ne _ hab]

theorem torus_ne_zero (ht : t ∈ hypTorus h 2 1) (a : HypIndex 2 1) : mat t a a ≠ 0 :=
  CFSG.RankThree.CentralLiftU.diag_entry_ne_zero h (torus_mat ht) a

theorem torus_bar_mul (ht : t ∈ hypTorus h 2 1) (a : HypIndex 2 1) :
    h.bar (mat t a a) * mat t (hypPartner a) (hypPartner a) = 1 :=
  CFSG.RankThree.CentralLiftU.diag_entries h (torus_mat ht) a

theorem torus_mul_apply (ht : t ∈ hypTorus h 2 1) (ht' : t' ∈ hypTorus h 2 1)
    (a : HypIndex 2 1) : mat (t * t') a a = mat t a a * mat t' a a := by
  conv_lhs => rw [mat_mul, torus_mat ht, torus_mat ht', diagonal_mul_diagonal, diagonal_apply_eq]

theorem torus_inv_apply (ht : t ∈ hypTorus h 2 1) (a : HypIndex 2 1) :
    mat t⁻¹ a a = (mat t a a)⁻¹ := by
  have h1 := torus_mul_apply ht (inv_mem ht) a
  rw [mul_inv_cancel, mat_one, one_apply_eq] at h1
  exact (eq_inv_of_mul_eq_one_right h1.symm)

theorem torus_conj_apply (ht : t ∈ hypTorus h 2 1) (g : hypSU h 2 1) (a b : HypIndex 2 1) :
    mat (t * g * t⁻¹) a b = mat t a a * mat g a b * (mat t b b)⁻¹ := by
  conv_lhs => rw [mat_mul, mat_mul, torus_mat ht, torus_mat (inv_mem ht)]
  rw [mul_diagonal, diagonal_mul, torus_inv_apply ht]

theorem torus_commute_iff (ht : t ∈ hypTorus h 2 1) (g : hypSU h 2 1) :
    t * g = g * t ↔ ∀ a b : HypIndex 2 1, mat t a a * mat g a b = mat g a b * mat t b b := by
  constructor
  · intro e a b
    have := congrFun (congrFun (congrArg mat e) a) b
    rw [mat_mul, mat_mul] at this
    conv at this => rw [torus_mat ht]
    rwa [diagonal_mul, mul_diagonal] at this
  · intro e
    apply mat_injective
    ext a b
    rw [mat_mul, mat_mul]
    conv => rw [torus_mat ht]
    rw [diagonal_mul, mul_diagonal]
    exact e a b

end Torus

theorem exists_torus (h : UnitaryFieldData 2 f K) {a₁ a₂ : K} (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) :
    ∃ t ∈ hypTorus h 2 1, mat t ιe₁ ιe₁ = a₁ ∧ mat t ιe₂ ιe₂ = a₂ ∧
      mat t ιz ιz = h.bar a₁ * h.bar a₂ / (a₁ * a₂) ∧ mat t ιf₁ ιf₁ = (h.bar a₁)⁻¹ ∧
      mat t ιf₂ ιf₂ = (h.bar a₂)⁻¹ := by
  have hb₁ : h.bar a₁ ≠ 0 := (map_ne_zero h.bar).2 h₁
  have hb₂ : h.bar a₂ ≠ 0 := (map_ne_zero h.bar).2 h₂
  have hd0 : h.bar a₁ * h.bar a₂ / (a₁ * a₂) ≠ 0 := by positivity
  set a : Fin 2 → Kˣ := ![Units.mk0 a₁ h₁, Units.mk0 a₂ h₂]
  set d : Fin 1 → Kˣ := fun _ => Units.mk0 _ hd0
  have hd : ∀ k, h.norm (d k : K) = 1 := fun k => by
    simp only [UnitaryFieldData.norm, d, Units.val_mk0, map_div₀, map_mul, h.bar_bar]
    field_simp
  have hp : torusRatio h a d = 1 := by
    simp only [torusRatio, Fin.prod_univ_two, Fin.prod_univ_one, a, d, Units.val_mk0,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
  obtain ⟨t, ht, htm⟩ := torusMat_mem_hypSU h a hd hp
  refine ⟨t, ht, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [mat, htm, torusEntries, a, d]

@[expose] def torusEq (h : UnitaryFieldData 2 f K) (S : Finset (HypIndex 2 1 × HypIndex 2 1)) :
    Subgroup (hypSU h 2 1) where
  carrier := {t | t ∈ hypTorus h 2 1 ∧ ∀ p ∈ S, mat t p.1 p.1 = mat t p.2 p.2}
  one_mem' := ⟨one_mem _, fun p _ => by rw [mat_one, one_apply_eq, one_apply_eq]⟩
  mul_mem' := by
    rintro t t' ⟨ht, htS⟩ ⟨ht', ht'S⟩
    exact ⟨mul_mem ht ht', fun p hp => by
      rw [torus_mul_apply ht ht', torus_mul_apply ht ht', htS p hp, ht'S p hp]⟩
  inv_mem' := by
    rintro t ⟨ht, htS⟩
    exact ⟨inv_mem ht, fun p hp => by
      rw [torus_inv_apply ht, torus_inv_apply ht, htS p hp]⟩

theorem mem_torusEq {S : Finset (HypIndex 2 1 × HypIndex 2 1)} {t : hypSU h 2 1} :
    t ∈ torusEq h S ↔ t ∈ hypTorus h 2 1 ∧ ∀ p ∈ S, mat t p.1 p.1 = mat t p.2 p.2 :=
  Iff.rfl

theorem torusEq_le (S : Finset (HypIndex 2 1 × HypIndex 2 1)) : torusEq h S ≤ hypTorus h 2 1 :=
  fun _ ht => ht.1

theorem U_inf_centralizer_eq {X : Subgroup (hypSU h 2 1)} (hX : X ≤ hypTorus h 2 1)
    {S : Finset (HypIndex 2 1 × HypIndex 2 1)} (hS : IsPattern S)
    (hsep : ∀ p ∈ S, ∃ t ∈ X, mat t p.1 p.1 ≠ mat t p.2 p.2)
    (hfix : ∀ t ∈ X, ∀ a b : HypIndex 2 1, fullPos a < fullPos b → (a, b) ∉ S →
      mat t a a = mat t b b) :
    hypUnitriangular h 2 1 ⊓ centralizer (X : Set (hypSU h 2 1)) = patSub h S hS := by
  ext g
  rw [mem_inf, mem_patSub, mem_centralizer_iff]
  constructor
  · rintro ⟨hg, hgc⟩
    refine ⟨hg, fun p hp => ?_⟩
    obtain ⟨t, htX, htp⟩ := hsep p hp
    have e := (torus_commute_iff (hX htX) g).1 (hgc t htX) p.1 p.2
    have : mat g p.1 p.2 * (mat t p.1 p.1 - mat t p.2 p.2) = 0 := by linear_combination e
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 htp)
  · rintro ⟨hg, hgS⟩
    refine ⟨hg, fun t htX => ((torus_commute_iff (hX htX) g).2 fun a b => ?_)⟩
    rcases lt_trichotomy (fullPos a) (fullPos b) with hab | hab | hab
    · by_cases hp : (a, b) ∈ S
      · rw [hgS _ hp, mul_zero, zero_mul]
      · rw [hfix t htX a b hab hp, mul_comm]
    · rw [fullPos_injective hab, mul_comm]
    · rw [U_lower hg hab, mul_zero, zero_mul]

@[expose] def sA₂ : Finset (HypIndex 2 1 × HypIndex 2 1) := {(ιe₂, ιz), (ιz, ιf₂), (ιe₂, ιf₂)}

theorem isPattern_sA₂ : IsPattern sA₂ := ⟨by decide, by decide, by decide⟩

@[expose] def sZP : Finset (HypIndex 2 1 × HypIndex 2 1) :=
  {(ιe₁, ιe₂), (ιf₂, ιf₁), (ιe₁, ιz), (ιz, ιf₁), (ιe₂, ιz), (ιz, ιf₂), (ιe₁, ιf₂), (ιe₂, ιf₁),
    (ιe₂, ιf₂)}

theorem isPattern_sZP : IsPattern sZP := ⟨by decide, by decide, by decide⟩

example (g : hypSU h 2 1) : g ∈ patSub h sZP isPattern_sZP ↔ g ∈ hypUnitriangular h 2 1 ∧
    mat g ιe₁ ιe₂ = 0 ∧ mat g ιf₂ ιf₁ = 0 ∧ mat g ιe₁ ιz = 0 ∧ mat g ιz ιf₁ = 0 ∧ mat g ιe₂ ιz = 0 ∧
    mat g ιz ιf₂ = 0 ∧ mat g ιe₁ ιf₂ = 0 ∧ mat g ιe₂ ιf₁ = 0 ∧ mat g ιe₂ ιf₂ = 0 := by
  simp [mem_patSub, sZP]

theorem isUnitriangular_unip (a : K) :
    IsUnitriangular (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) K) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i <;> simp

theorem exists_U_of_coord (h : UnitaryFieldData 2 f K) (a : K) (x : Fin 2 → K)
    (C : Matrix (Fin 2) (Fin 2) K) (hC : C + (C.map h.bar)ᵀ = -vecMulVec x fun j => h.bar (x j)) :
    ∃ g ∈ hypUnitriangular h 2 1, mat g ιe₁ ιe₂ = a ∧ mat g ιe₁ ιz = x 0 + a * x 1 ∧
      mat g ιe₂ ιz = x 1 ∧ mat g ιe₁ ιf₁ = C 0 0 + a * C 1 0 ∧
      mat g ιe₁ ιf₂ = C 0 1 + a * C 1 1 ∧ mat g ιe₂ ιf₁ = C 1 0 ∧ mat g ιe₂ ιf₂ = C 1 1 := by
  obtain ⟨g, hg, hgm⟩ := (exists_mem_hypUnitriangular_odd_iff (h := h) (r := 2)
    (oddDiag h !![1, a; 0, 1] 1 * oddUni h x C)).2 ⟨_, C, x, isUnitriangular_unip a, hC, rfl⟩
  refine ⟨g, hg, ?_⟩
  simp [mat, hgm, oddDiag, oddUni, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def sA₃ : Finset (HypIndex 2 1 × HypIndex 2 1) := {(ιe₁, ιe₂), (ιf₂, ιf₁)}

theorem isPattern_sA₃ : IsPattern sA₃ := ⟨by decide, by decide, by decide⟩

@[expose] def sA₁ : Finset (HypIndex 2 1 × HypIndex 2 1) :=
  {(ιe₁, ιe₂), (ιf₂, ιf₁), (ιe₁, ιz), (ιz, ιf₁), (ιe₂, ιz), (ιz, ιf₂)}

theorem isPattern_sA₁ : IsPattern sA₁ := ⟨by decide, by decide, by decide⟩

@[expose] def sZ₂P : Finset (HypIndex 2 1 × HypIndex 2 1) :=
  {(ιe₁, ιe₂), (ιf₂, ιf₁), (ιe₁, ιz), (ιz, ιf₁), (ιe₂, ιz), (ιz, ιf₂), (ιe₂, ιf₂)}

theorem isPattern_sZ₂P : IsPattern sZ₂P := ⟨by decide, by decide, by decide⟩

theorem U_eq_patSub : hypUnitriangular h 2 1 = patSub h ∅ ⟨by decide, by decide, by decide⟩ := by
  ext g
  simp [mem_patSub]

theorem Ssub_eq_patSub : Ssub h = patSub h sA₃ isPattern_sA₃ := by
  ext g
  simp only [mem_patSub, sA₃, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq]
  constructor
  · intro hg
    have hgU := Ssub_le_Usub hg
    have ha : mat g ιe₁ ιe₂ = 0 := (mem_Ssub_iff hgU).1 hg
    exact ⟨hgU, ha, by rw [(U_rel hgU).1, ha, map_zero]⟩
  · rintro ⟨hgU, ha, -⟩
    exact (mem_Ssub_iff hgU).2 ha

theorem Vsub_eq_patSub : Vsub h = patSub h sA₁ isPattern_sA₁ := by
  ext g
  simp only [mem_patSub, sA₁, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq]
  constructor
  · intro hg
    have hgS := Vsub_le_Ssub hg
    have hgU := Ssub_le_Usub hgS
    have ha : mat g ιe₁ ιe₂ = 0 := (mem_Ssub_iff hgU).1 hgS
    have hx := (mem_Vsub_iff hgS).1 hg
    obtain ⟨r1, r2, r3, -⟩ := U_rel hgU
    have hx0 : mat g ιe₁ ιz = 0 := hx 0
    have hx1 : mat g ιe₂ ιz = 0 := hx 1
    refine ⟨hgU, ha, by rw [r1, ha, map_zero], hx0, by rw [r3, hx0, ha]; simp, hx1,
      by rw [r2, hx1, map_zero]⟩
  · rintro ⟨hgU, ha, -, hx0, -, hx1, -⟩
    have hgS : g ∈ Ssub h := (mem_Ssub_iff hgU).2 ha
    refine (mem_Vsub_iff hgS).2 fun i => ?_
    fin_cases i
    · exact hx0
    · exact hx1

@[expose] def A₂sub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  patSub h sA₂ isPattern_sA₂

@[expose] def ZPsub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  patSub h sZP isPattern_sZP

@[expose] def Z₂Psub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) := Vsub h ⊓ A₂sub h

theorem mem_A₂sub {g : hypSU h 2 1} : g ∈ A₂sub h ↔ g ∈ hypUnitriangular h 2 1 ∧
    mat g ιe₂ ιz = 0 ∧ mat g ιz ιf₂ = 0 ∧ mat g ιe₂ ιf₂ = 0 := by
  simp [A₂sub, mem_patSub, sA₂]

theorem mem_ZPsub {g : hypSU h 2 1} : g ∈ ZPsub h ↔ g ∈ hypUnitriangular h 2 1 ∧
    mat g ιe₁ ιe₂ = 0 ∧ mat g ιf₂ ιf₁ = 0 ∧ mat g ιe₁ ιz = 0 ∧ mat g ιz ιf₁ = 0 ∧
    mat g ιe₂ ιz = 0 ∧ mat g ιz ιf₂ = 0 ∧ mat g ιe₁ ιf₂ = 0 ∧ mat g ιe₂ ιf₁ = 0 ∧
    mat g ιe₂ ιf₂ = 0 := by
  simp [ZPsub, mem_patSub, sZP]

theorem Z₂Psub_eq_patSub : Z₂Psub h = patSub h sZ₂P isPattern_sZ₂P := by
  ext g
  simp only [Z₂Psub, A₂sub, Vsub_eq_patSub, mem_inf, mem_patSub, sA₁, sA₂, sZ₂P,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  tauto

theorem mem_Z₂Psub {g : hypSU h 2 1} : g ∈ Z₂Psub h ↔ g ∈ hypUnitriangular h 2 1 ∧
    mat g ιe₁ ιe₂ = 0 ∧ mat g ιf₂ ιf₁ = 0 ∧ mat g ιe₁ ιz = 0 ∧ mat g ιz ιf₁ = 0 ∧
    mat g ιe₂ ιz = 0 ∧ mat g ιz ιf₂ = 0 ∧ mat g ιe₂ ιf₂ = 0 := by
  rw [Z₂Psub_eq_patSub]
  simp [mem_patSub, sZ₂P]

theorem A₂sub_le_U : A₂sub h ≤ hypUnitriangular h 2 1 := patSub_le_U _ _

theorem ZPsub_le_Z₂Psub : ZPsub h ≤ Z₂Psub h := by
  rw [Z₂Psub_eq_patSub]
  exact patSub_mono _ _ (by decide)

theorem Z₂Psub_le_Vsub : Z₂Psub h ≤ Vsub h := inf_le_left

theorem Z₂Psub_le_A₂sub : Z₂Psub h ≤ A₂sub h := inf_le_right

theorem ZPsub_le_Vsub : ZPsub h ≤ Vsub h := ZPsub_le_Z₂Psub.trans Z₂Psub_le_Vsub

theorem ZPsub_le_U : ZPsub h ≤ hypUnitriangular h 2 1 := patSub_le_U _ _

theorem forall_upper {P : HypIndex 2 1 → HypIndex 2 1 → Prop} :
    (∀ a b : HypIndex 2 1, fullPos a < fullPos b → P a b) ↔
      P ιe₁ ιe₂ ∧ P ιe₁ ιz ∧ P ιe₁ ιf₂ ∧ P ιe₁ ιf₁ ∧ P ιe₂ ιz ∧ P ιe₂ ιf₂ ∧ P ιe₂ ιf₁ ∧
        P ιz ιf₂ ∧ P ιz ιf₁ ∧ P ιf₂ ιf₁ := by
  constructor
  · intro hP
    exact ⟨hP _ _ (by decide), hP _ _ (by decide), hP _ _ (by decide), hP _ _ (by decide),
      hP _ _ (by decide), hP _ _ (by decide), hP _ _ (by decide), hP _ _ (by decide),
      hP _ _ (by decide), hP _ _ (by decide)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ a b hab
    rcases a with i | k | i <;> rcases b with j | l | j <;> (try fin_cases i) <;>
      (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
      first | assumption | exact absurd hab (by decide)

@[expose] def sI₁ : Finset (HypIndex 2 1 × HypIndex 2 1) :=
  {(ιe₁, ιz), (ιz, ιf₁), (ιe₂, ιz), (ιz, ιf₂), (ιe₁, ιf₂), (ιe₂, ιf₁), (ιe₂, ιf₂), (ιe₁, ιf₁)}

theorem isPattern_sI₁ : IsPattern sI₁ := ⟨by decide, by decide, by decide⟩

@[expose] def sI₂ : Finset (HypIndex 2 1 × HypIndex 2 1) :=
  {(ιe₁, ιe₂), (ιf₂, ιf₁), (ιe₁, ιz), (ιz, ιf₁), (ιe₁, ιf₂), (ιe₂, ιf₁), (ιe₁, ιf₁)}

theorem isPattern_sI₂ : IsPattern sI₂ := ⟨by decide, by decide, by decide⟩

@[expose] def sI₄ : Finset (HypIndex 2 1 × HypIndex 2 1) :=
  {(ιe₁, ιe₂), (ιf₂, ιf₁), (ιe₁, ιz), (ιz, ιf₁), (ιe₂, ιz), (ιz, ιf₂), (ιe₂, ιf₂), (ιe₁, ιf₁)}

theorem isPattern_sI₄ : IsPattern sI₄ := ⟨by decide, by decide, by decide⟩

@[expose] def sI₅ : Finset (HypIndex 2 1 × HypIndex 2 1) :=
  {(ιe₁, ιe₂), (ιf₂, ιf₁), (ιe₂, ιz), (ιz, ιf₂), (ιe₁, ιf₂), (ιe₂, ιf₁), (ιe₂, ιf₂)}

theorem isPattern_sI₅ : IsPattern sI₅ := ⟨by decide, by decide, by decide⟩

@[expose] def sI₆ : Finset (HypIndex 2 1 × HypIndex 2 1) :=
  {(ιe₁, ιe₂), (ιf₂, ιf₁), (ιe₁, ιz), (ιz, ιf₁), (ιe₂, ιz), (ιz, ιf₂), (ιe₁, ιf₂), (ιe₂, ιf₁),
    (ιe₁, ιf₁)}

theorem isPattern_sI₆ : IsPattern sI₆ := ⟨by decide, by decide, by decide⟩

@[expose] def sI₃₆ : Finset (HypIndex 2 1 × HypIndex 2 1) :=
  {(ιe₁, ιe₂), (ιf₂, ιf₁), (ιe₁, ιz), (ιz, ιf₁), (ιe₂, ιz), (ιz, ιf₂), (ιe₁, ιf₂), (ιe₂, ιf₁)}

theorem isPattern_sI₃₆ : IsPattern sI₃₆ := ⟨by decide, by decide, by decide⟩

section Roots

theorem exists_rootI₁ (h : UnitaryFieldData 2 f K) (a : K) :
    ∃ g ∈ patSub h sI₁ isPattern_sI₁, mat g ιe₁ ιe₂ = a := by
  obtain ⟨g, hg, e1, e2, e3, e4, e5, e6, e7⟩ := exists_U_of_coord h a 0 0 (by
    ext i j; simp [vecMulVec])
  obtain ⟨r1, r2, r3, r4, -, -⟩ := U_rel hg
  refine ⟨g, ?_, e1⟩
  simp only [mem_patSub, sI₁, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq]
  simp_all

theorem exists_rootI₄ (h : UnitaryFieldData 2 f K) (b : K) :
    ∃ g ∈ patSub h sI₄ isPattern_sI₄, mat g ιe₁ ιf₂ = b := by
  have := h.charP
  obtain ⟨g, hg, e1, e2, e3, e4, e5, e6, e7⟩ := exists_U_of_coord h 0 0 !![0, b; h.bar b, 0] (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [vecMulVec, h.bar_bar, CharTwo.add_self_eq_zero])
  obtain ⟨r1, r2, r3, r4, -, -⟩ := U_rel hg
  refine ⟨g, ?_, by simpa using e5⟩
  simp only [mem_patSub, sI₄, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq]
  simp_all

theorem exists_rootZP (h : UnitaryFieldData 2 f K) {c : K} (hc : h.bar c = c) :
    ∃ g ∈ ZPsub h, mat g ιe₁ ιf₁ = c := by
  have := h.charP
  obtain ⟨g, hg, e1, e2, e3, e4, e5, e6, e7⟩ := exists_U_of_coord h 0 0 !![c, 0; 0, 0] (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [vecMulVec, hc, CharTwo.add_self_eq_zero])
  obtain ⟨r1, r2, r3, r4, -, -⟩ := U_rel hg
  refine ⟨g, ?_, by simpa using e4⟩
  rw [mem_ZPsub]
  simp_all

theorem exists_rootI₆ (h : UnitaryFieldData 2 f K) {c : K} (hc : h.bar c = c) :
    ∃ g ∈ patSub h sI₆ isPattern_sI₆, mat g ιe₂ ιf₂ = c := by
  have := h.charP
  obtain ⟨g, hg, e1, e2, e3, e4, e5, e6, e7⟩ := exists_U_of_coord h 0 0 !![0, 0; 0, c] (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [vecMulVec, hc, CharTwo.add_self_eq_zero])
  obtain ⟨r1, r2, r3, r4, -, -⟩ := U_rel hg
  refine ⟨g, ?_, by simpa using e7⟩
  simp only [mem_patSub, sI₆, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq]
  simp_all

theorem exists_rootI₅ (h : UnitaryFieldData 2 f K) {u c : K} (huc : c + h.bar c = u * h.bar u) :
    ∃ g ∈ patSub h sI₅ isPattern_sI₅, mat g ιe₁ ιz = u ∧ mat g ιe₁ ιf₁ = c := by
  have := h.charP
  obtain ⟨g, hg, e1, e2, e3, e4, e5, e6, e7⟩ := exists_U_of_coord h 0 ![u, 0] !![c, 0; 0, 0] (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [vecMulVec, huc, CharTwo.neg_eq])
  obtain ⟨r1, r2, r3, r4, -, -⟩ := U_rel hg
  refine ⟨g, ?_, by simpa using e2, by simpa using e4⟩
  simp only [mem_patSub, sI₅, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq]
  simp_all

theorem exists_rootI₂ (h : UnitaryFieldData 2 f K) {u c : K} (huc : c + h.bar c = u * h.bar u) :
    ∃ g ∈ patSub h sI₂ isPattern_sI₂, mat g ιe₂ ιz = u ∧ mat g ιe₂ ιf₂ = c := by
  have := h.charP
  obtain ⟨g, hg, e1, e2, e3, e4, e5, e6, e7⟩ := exists_U_of_coord h 0 ![0, u] !![0, 0; 0, c] (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [vecMulVec, huc, CharTwo.neg_eq])
  obtain ⟨r1, r2, r3, r4, -, -⟩ := U_rel hg
  refine ⟨g, ?_, by simpa using e3, by simpa using e7⟩
  simp only [mem_patSub, sI₂, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq]
  simp_all

end Roots

section Orders

theorem bar_eq_of_add_eq_zero (h : UnitaryFieldData 2 f K) {a : K} (ha : a + h.bar a = 0) :
    h.bar a = a := by
  have := h.charP
  linear_combination ha - CharTwo.add_self_eq_zero a

theorem card_eq_mul_of_coord {H N : Subgroup (hypSU h 2 1)} (hNH : N ≤ H)
    (φ : hypSU h 2 1 → K) (hφ : ∀ x ∈ H, ∀ y ∈ H, φ (x * y) = φ x + φ y)
    (hker : ∀ x ∈ H, φ x = 0 ↔ x ∈ N) (hsurj : ∀ c : K, ∃ x ∈ H, φ x = c) :
    Nat.card H = Nat.card N * (2 ^ f) ^ 2 := by
  have h1 : φ 1 = 0 := by
    have := hφ 1 (one_mem _) 1 (one_mem _)
    rw [one_mul] at this
    linear_combination -this
  let ψ : H →* Multiplicative K :=
    { toFun := fun x => Multiplicative.ofAdd (φ x)
      map_one' := by simp [h1]
      map_mul' := fun x y => by simp [hφ x x.2 y y.2, ofAdd_add] }
  have hrange : ψ.range = ⊤ := by
    refine eq_top_iff.2 fun c _ => ?_
    obtain ⟨x, hx, hxc⟩ := hsurj (Multiplicative.toAdd c)
    exact ⟨⟨x, hx⟩, by simp [ψ, hxc]⟩
  have hkerN : ψ.ker = N.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change Multiplicative.ofAdd (φ x) = 1 ↔ _
    rw [ofAdd_eq_one]
    exact hker x x.2
  have hc := Subgroup.card_ker_mul_card_range ψ
  rw [hrange, Subgroup.card_top, hkerN,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv,
    Nat.card_congr Multiplicative.toAdd, h.card_eq_sq] at hc
  exact hc.symm

theorem card_ZPsub : Nat.card (ZPsub h) = 2 ^ f := by
  have := h.charP
  rw [← h.card_fixedField]
  have hfix : ∀ g ∈ ZPsub h, h.bar (mat g ιe₁ ιf₁) = mat g ιe₁ ιf₁ := by
    intro g hg
    obtain ⟨hgU, e1, -, e3, -, -, -, e7, -, -⟩ := mem_ZPsub.1 hg
    obtain ⟨-, -, -, -, -, r6⟩ := U_rel hgU
    rw [e1, e3, e7] at r6
    exact bar_eq_of_add_eq_zero h (by simpa using r6)
  refine Nat.card_congr (Equiv.ofBijective (fun g : ZPsub h =>
    (⟨mat g.1 ιe₁ ιf₁, h.mem_fixedField.2 (hfix g g.2)⟩ : h.fixedField)) ⟨?_, ?_⟩)
  · rintro ⟨g, hg⟩ ⟨g', hg'⟩ e
    have e' : mat g ιe₁ ιf₁ = mat g' ιe₁ ιf₁ := congrArg Subtype.val e
    obtain ⟨hgU, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := mem_ZPsub.1 hg
    obtain ⟨hgU', b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := mem_ZPsub.1 hg'
    exact Subtype.ext (eq_of_U_entries hgU hgU' (forall_upper.2 (by simp_all)))
  · rintro ⟨c, hc⟩
    obtain ⟨g, hg, hgc⟩ := exists_rootZP h (h.mem_fixedField.1 hc)
    exact ⟨⟨g, hg⟩, Subtype.ext hgc⟩

theorem card_Z₂Psub : Nat.card (Z₂Psub h) = (2 ^ f) ^ 3 := by
  have := h.charP
  have hfix : ∀ g ∈ Z₂Psub h, h.bar (mat g ιe₁ ιf₁) = mat g ιe₁ ιf₁ := by
    intro g hg
    obtain ⟨hgU, e1, -, e3, -, -, -, -⟩ := mem_Z₂Psub.1 hg
    obtain ⟨-, -, -, -, -, r6⟩ := U_rel hgU
    rw [e1, e3] at r6
    exact bar_eq_of_add_eq_zero h (by simpa using r6)
  have hcard : Nat.card (h.fixedField × K) = (2 ^ f) ^ 3 := by
    rw [Nat.card_prod, h.card_fixedField, h.card_eq_sq]
    ring
  rw [← hcard]
  refine Nat.card_congr (Equiv.ofBijective (fun g : Z₂Psub h =>
    ((⟨mat g.1 ιe₁ ιf₁, h.mem_fixedField.2 (hfix g g.2)⟩ : h.fixedField), mat g.1 ιe₁ ιf₂))
    ⟨?_, ?_⟩)
  · rintro ⟨g, hg⟩ ⟨g', hg'⟩ e
    have e1 : mat g ιe₁ ιf₁ = mat g' ιe₁ ιf₁ := congrArg (fun p => (p.1 : K)) e
    have e2 : mat g ιe₁ ιf₂ = mat g' ιe₁ ιf₂ := congrArg Prod.snd e
    obtain ⟨hgU, a1, a2, a3, a4, a5, a6, a7⟩ := mem_Z₂Psub.1 hg
    obtain ⟨hgU', b1, b2, b3, b4, b5, b6, b7⟩ := mem_Z₂Psub.1 hg'
    have r := (U_rel hgU).2.2.2.1
    have r' := (U_rel hgU').2.2.2.1
    exact Subtype.ext (eq_of_U_entries hgU hgU' (forall_upper.2 (by simp_all)))
  · rintro ⟨⟨c, hc⟩, b⟩
    have hc' : h.bar c = c := h.mem_fixedField.1 hc
    obtain ⟨g, hg, e1, e2, e3, e4, e5, e6, e7⟩ := exists_U_of_coord h 0 0 !![c, b; h.bar b, 0]
      (by ext i j; fin_cases i <;> fin_cases j <;>
        simp [vecMulVec, hc', h.bar_bar, CharTwo.add_self_eq_zero])
    obtain ⟨r1, r2, r3, -, -, -⟩ := U_rel hg
    refine ⟨⟨g, mem_Z₂Psub.2 ?_⟩, ?_⟩
    · simp_all
    · simp only [Prod.mk.injEq, Subtype.mk.injEq]
      simp_all

theorem mul_e₁z_of_Ssub {x y : hypSU h 2 1} (hx : x ∈ Ssub h) (hy : y ∈ Ssub h) :
    mat (x * y) ιe₁ ιz = mat x ιe₁ ιz + mat y ιe₁ ιz := by
  have ha : mat x ιe₁ ιe₂ = 0 := (mem_Ssub_iff (Ssub_le_Usub hx)).1 hx
  rw [mul_e₁z (Ssub_le_Usub hx) (Ssub_le_Usub hy), ha]
  ring

theorem card_A₂sub_inf_Ssub : Nat.card (A₂sub h ⊓ Ssub h : Subgroup (hypSU h 2 1)) =
    (2 ^ f) ^ 5 := by
  rw [card_eq_mul_of_coord (H := A₂sub h ⊓ Ssub h) (N := Z₂Psub h)
    (fun x hx => ⟨Z₂Psub_le_A₂sub hx, Vsub_le_Ssub (Z₂Psub_le_Vsub hx)⟩)
    (fun x => mat x ιe₁ ιz) (fun x hx y hy => mul_e₁z_of_Ssub hx.2 hy.2) ?_ ?_, card_Z₂Psub]
  · ring
  · rintro x ⟨hxA, hxS⟩
    constructor
    · intro hx0
      refine ⟨(mem_Vsub_iff hxS).2 fun i => ?_, hxA⟩
      fin_cases i
      · exact hx0
      · exact (mem_A₂sub.1 hxA).2.1
    · intro hx
      exact (mem_Vsub_iff hxS).1 (Z₂Psub_le_Vsub hx) 0
  · intro u
    obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := u * h.bar u) (by rw [map_mul, h.bar_bar, mul_comm])
    obtain ⟨g, hg, hgu, -⟩ := exists_rootI₅ h hc
    refine ⟨g, ⟨?_, ?_⟩, hgu⟩
    · exact patSub_mono isPattern_sI₅ isPattern_sA₂ (by decide) hg
    · rw [Ssub_eq_patSub]
      exact patSub_mono isPattern_sI₅ isPattern_sA₃ (by decide) hg

theorem card_A₂sub : Nat.card (A₂sub h) = (2 ^ f) ^ 7 := by
  rw [card_eq_mul_of_coord (H := A₂sub h) (N := A₂sub h ⊓ Ssub h) inf_le_left
    (fun x => mat x ιe₁ ιe₂) (fun x hx y hy => mul_e₁e₂ (A₂sub_le_U hx) (A₂sub_le_U hy)) ?_ ?_,
    card_A₂sub_inf_Ssub]
  · ring
  · intro x hx
    rw [mem_inf, mem_Ssub_iff (A₂sub_le_U hx)]
    exact ⟨fun e => ⟨hx, e⟩, fun e => e.2⟩
  · intro a
    obtain ⟨g, hg, hga⟩ := exists_rootI₁ h a
    exact ⟨g, patSub_mono isPattern_sI₁ isPattern_sA₂ (by decide) hg, hga⟩

end Orders

section Perm

theorem permMatrix_hypGram (h : UnitaryFieldData 2 f K) (σ : Equiv.Perm (HypIndex 2 1))
    (hσ : ∀ a, σ (hypPartner a) = hypPartner (σ a)) :
    ((σ.permMatrix K).map h.bar)ᵀ * hypGram 2 1 K * σ.permMatrix K = hypGram 2 1 K := by
  ext a b
  rw [conjTranspose_hypGram_mul_apply, hypGram_apply]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  rw [Finset.sum_eq_single (σ.symm a)]
  · simp only [Equiv.apply_symm_apply, ite_true, map_one, one_mul, hσ]
    by_cases hb : b = hypPartner a
    · simp [hb]
    · rw [ite_eq_right, ite_eq_right hb]
      intro e
      exact hb (by rw [← e])
  · intro x _ hx
    rw [ite_eq_right (fun e => hx (by rw [← e, Equiv.symm_apply_apply])), map_zero, zero_mul]
  · simp

theorem det_permMatrix_hyp (h : UnitaryFieldData 2 f K) (σ : Equiv.Perm (HypIndex 2 1)) :
    (σ.permMatrix K).det = 1 := by
  have := h.charP
  rw [det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> rw [e]
  · simp
  · simp [CharTwo.neg_eq]

@[expose] noncomputable def hypPermElt (h : UnitaryFieldData 2 f K) (σ : Equiv.Perm (HypIndex 2 1))
    (hσ : ∀ a, σ (hypPartner a) = hypPartner (σ a)) : hypSU h 2 1 :=
  mkHypSU h (σ.permMatrix K) (permMatrix_hypGram h σ hσ) (det_permMatrix_hyp h σ)

theorem mat_hypPermElt (σ : Equiv.Perm (HypIndex 2 1))
    (hσ : ∀ a, σ (hypPartner a) = hypPartner (σ a))
    (a b : HypIndex 2 1) : mat (hypPermElt h σ hσ) a b = if σ a = b then 1 else 0 := by
  simp [mat, hypPermElt, coe_mkHypSU, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem conj_perm_apply {w : hypSU h 2 1} {σ : Equiv.Perm (HypIndex 2 1)}
    (hσσ : ∀ a, σ (σ a) = a) (hσ : ∀ a, σ (hypPartner a) = hypPartner (σ a))
    (hw : ∀ a b, mat w a b = if σ a = b then 1 else 0) (g : hypSU h 2 1) (a b : HypIndex 2 1) :
    mat (w * g * w⁻¹) a b = mat g (σ a) (σ b) := by
  have hwi : ∀ a b, mat w⁻¹ a b = if σ a = b then 1 else 0 := by
    intro a b
    rw [mat_inv_apply, hw, hσ]
    have hiff : hypPartner (σ b) = hypPartner a ↔ σ a = b := by
      rw [hypPartner_injective.eq_iff]
      constructor <;> intro e <;> rw [← e, hσσ]
    by_cases e : σ a = b
    · rw [ite_eq_left (hiff.2 e), ite_eq_left e, map_one]
    · rw [ite_eq_right (fun e' => e (hiff.1 e')), ite_eq_right e, map_zero]
  rw [mat_mul, mat_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single (σ b)]
  · rw [hwi, ite_eq_left (hσσ b), mul_one, Matrix.mul_apply, Finset.sum_eq_single (σ a)]
    · rw [hw, ite_eq_left rfl, one_mul]
    · intro c _ hc
      rw [hw, ite_eq_right (Ne.symm hc), zero_mul]
    · simp
  · intro c _ hc
    rw [hwi, ite_eq_right (fun e => hc (by rw [← e, hσσ])), mul_zero]
  · simp

theorem hypPerm_mul_self {w : hypSU h 2 1} {σ : Equiv.Perm (HypIndex 2 1)}
    (hσσ : ∀ a, σ (σ a) = a) (hw : ∀ a b, mat w a b = if σ a = b then 1 else 0) : w * w = 1 := by
  apply mat_injective
  ext a b
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single (σ a)]
  · rw [hw, hw, ite_eq_left rfl, one_mul, mat_one, one_apply, hσσ]
  · intro c _ hc
    rw [hw, ite_eq_right (Ne.symm hc), zero_mul]
  · simp

end Perm

@[expose] def σr : Equiv.Perm (HypIndex 2 1) := Equiv.swap ιe₁ ιe₂ * Equiv.swap ιf₁ ιf₂

@[expose] def σs : Equiv.Perm (HypIndex 2 1) := Equiv.swap ιe₂ ιf₂

theorem σr_σr (a : HypIndex 2 1) : σr (σr a) = a := by revert a; decide

theorem σs_σs (a : HypIndex 2 1) : σs (σs a) = a := by revert a; decide

theorem σr_partner (a : HypIndex 2 1) : σr (hypPartner a) = hypPartner (σr a) := by
  revert a; decide

theorem σs_partner (a : HypIndex 2 1) : σs (hypPartner a) = hypPartner (σs a) := by
  revert a; decide

@[expose] noncomputable def rSU (h : UnitaryFieldData 2 f K) : hypSU h 2 1 :=
  hypPermElt h σr σr_partner

@[expose] noncomputable def sSU (h : UnitaryFieldData 2 f K) : hypSU h 2 1 :=
  hypPermElt h σs σs_partner

theorem mat_rSU (a b : HypIndex 2 1) : mat (rSU h) a b = if σr a = b then 1 else 0 :=
  mat_hypPermElt _ _ a b

theorem mat_sSU (a b : HypIndex 2 1) : mat (sSU h) a b = if σs a = b then 1 else 0 :=
  mat_hypPermElt _ _ a b

theorem conj_rSU_apply (g : hypSU h 2 1) (a b : HypIndex 2 1) :
    mat (rSU h * g * (rSU h)⁻¹) a b = mat g (σr a) (σr b) :=
  conj_perm_apply σr_σr σr_partner mat_rSU g a b

theorem conj_sSU_apply (g : hypSU h 2 1) (a b : HypIndex 2 1) :
    mat (sSU h * g * (sSU h)⁻¹) a b = mat g (σs a) (σs b) :=
  conj_perm_apply σs_σs σs_partner mat_sSU g a b

theorem rSU_mul_self : rSU h * rSU h = 1 := hypPerm_mul_self σr_σr mat_rSU

theorem sSU_mul_self : sSU h * sSU h = 1 := hypPerm_mul_self σs_σs mat_sSU

abbrev Isub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) := hypTorus h 2 1

@[expose] def I₁sub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  torusEq h {(ιe₁, ιe₂)}

@[expose] def I₂sub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  torusEq h {(ιe₂, ιz), (ιz, ιf₂)}

@[expose] def I₃sub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  torusEq h {(ιe₁, ιf₁)}

@[expose] def I₄sub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  torusEq h {(ιe₁, ιf₂)}

@[expose] def I₅sub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  torusEq h {(ιe₁, ιz), (ιz, ιf₁)}

@[expose] def I₆sub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  torusEq h {(ιe₂, ιf₂)}

theorem mem_I₁sub {t : hypSU h 2 1} : t ∈ I₁sub h ↔ t ∈ Isub h ∧ mat t ιe₁ ιe₁ = mat t ιe₂ ιe₂ := by
  simp [I₁sub, mem_torusEq]

theorem mem_I₂sub {t : hypSU h 2 1} : t ∈ I₂sub h ↔
    t ∈ Isub h ∧ mat t ιe₂ ιe₂ = mat t ιz ιz ∧ mat t ιz ιz = mat t ιf₂ ιf₂ := by
  simp [I₂sub, mem_torusEq]

theorem mem_I₃sub {t : hypSU h 2 1} : t ∈ I₃sub h ↔ t ∈ Isub h ∧ mat t ιe₁ ιe₁ = mat t ιf₁ ιf₁ := by
  simp [I₃sub, mem_torusEq]

theorem mem_I₄sub {t : hypSU h 2 1} : t ∈ I₄sub h ↔ t ∈ Isub h ∧ mat t ιe₁ ιe₁ = mat t ιf₂ ιf₂ := by
  simp [I₄sub, mem_torusEq]

theorem mem_I₅sub {t : hypSU h 2 1} : t ∈ I₅sub h ↔
    t ∈ Isub h ∧ mat t ιe₁ ιe₁ = mat t ιz ιz ∧ mat t ιz ιz = mat t ιf₁ ιf₁ := by
  simp [I₅sub, mem_torusEq]

theorem mem_I₆sub {t : hypSU h 2 1} : t ∈ I₆sub h ↔ t ∈ Isub h ∧ mat t ιe₂ ιe₂ = mat t ιf₂ ιf₂ := by
  simp [I₆sub, mem_torusEq]

theorem mat_leviSU (A : SpecialLinearGroup (Fin 2) K) :
    mat (UnitaryHigher.leviSU h 1 A) =
      blk3 (A : Matrix (Fin 2) (Fin 2) K) 0 0 1 0
        (UnitaryHigher.leviDual h (SpecialLinearGroup.toGL A)) := by
  rw [mat, UnitaryHigher.coe_leviSU, UnitaryHigher.coe_leviGL]
  rfl

theorem leviSU_injective : Function.Injective (UnitaryHigher.leviSU h 1 :
    SpecialLinearGroup (Fin 2) K →* hypSU h 2 1) := by
  intro A B e
  ext i j
  have := congrFun (congrFun (congrArg mat e) (.inl i)) (.inl j)
  rwa [mat_leviSU, mat_leviSU, blk3_inl_inl, blk3_inl_inl] at this

@[expose] def N₁sub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  (UnitaryHigher.leviSU h 1 : SpecialLinearGroup (Fin 2) K →* hypSU h 2 1).range

noncomputable def N₁equiv (h : UnitaryFieldData 2 f K) : SpecialLinearGroup (Fin 2) K ≃* N₁sub h :=
  MonoidHom.ofInjective leviSU_injective

@[expose] def N₂sub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  MulAction.stabilizer (hypSU h 2 1) (Pi.single ιe₁ (1 : K) : HypIndex 2 1 → K) ⊓
    MulAction.stabilizer (hypSU h 2 1) (Pi.single ιf₁ (1 : K) : HypIndex 2 1 → K)

theorem mem_N₂sub {g : hypSU h 2 1} : g ∈ N₂sub h ↔
    (∀ a, mat g a ιe₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a ιe₁) ∧
      ∀ a, mat g a ιf₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a ιf₁ := by
  rw [N₂sub, mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  have key : ∀ b : HypIndex 2 1, g • (Pi.single b (1 : K) : HypIndex 2 1 → K) =
      Pi.single b 1 ↔ ∀ a, mat g a b = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b := by
    intro b
    change ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ
      Pi.single b 1 = _ ↔ _
    rw [mulVec_single_one, funext_iff]
    simp only [col_apply, one_apply, Pi.single_apply, mat]
  rw [key, key]

@[expose] def N₄sub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  (N₁sub h).map (MulAut.conj (sSU h)).toMonoidHom

@[expose] def N₅sub (h : UnitaryFieldData 2 f K) : Subgroup (hypSU h 2 1) :=
  (N₂sub h).map (MulAut.conj (rSU h)).toMonoidHom

theorem sSU_mem_N₂sub : sSU h ∈ N₂sub h := by
  have e1 : ∀ a, σs a = ιe₁ ↔ a = ιe₁ := by decide
  have e2 : ∀ a, σs a = ιf₁ ↔ a = ιf₁ := by decide
  rw [mem_N₂sub]
  exact ⟨fun a => by simp only [mat_sSU, one_apply, e1],
    fun a => by simp only [mat_sSU, one_apply, e2]⟩

theorem det_swapM (h : UnitaryFieldData 2 f K) : (swapM : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  have := h.charP
  simp [swapM, Matrix.det_fin_two, CharTwo.neg_eq]

@[expose] def swapSL (h : UnitaryFieldData 2 f K) : SpecialLinearGroup (Fin 2) K :=
  ⟨swapM, det_swapM h⟩

theorem rSU_eq_leviSU : rSU h = UnitaryHigher.leviSU h 1 (swapSL h) := by
  have := h.charP
  apply mat_injective
  have hinv : (swapSL h)⁻¹ = swapSL h :=
    inv_eq_of_mul_eq_one_right (Subtype.ext swapM_mul_swapM)
  have hd : UnitaryHigher.leviDual h (SpecialLinearGroup.toGL (swapSL h)) =
      (swapM : Matrix (Fin 2) (Fin 2) K) := by
    rw [UnitaryHigher.leviDual, ← map_inv, hinv, SpecialLinearGroup.coe_GL_coe_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swapSL, swapM]
  rw [mat_leviSU, hd]
  ext a b
  rw [mat_rSU]
  rcases a with i | k | i <;> rcases b with j | l | j <;> (try fin_cases i) <;>
    (try fin_cases j) <;> (try fin_cases k) <;> (try fin_cases l) <;>
    simp [σr, swapSL, swapM, Equiv.swap_apply_def]

theorem rSU_mem_N₁sub : rSU h ∈ N₁sub h := ⟨swapSL h, rSU_eq_leviSU.symm⟩

@[expose] def vSU (h : UnitaryFieldData 2 f K) (Y : Matrix (Fin 2) (Fin 2) K) (hY : IsHerm h Y) :
    hypSU h 2 1 :=
  mkHypSU h (oddUni h 0 Y)
    (by
      have := oddProd_gram (h := h) (A := 1) (d := 1) (x := 0) (C := Y) (by simp) (by simp)
        (by rw [hY]; ext i j; simp [vecMulVec])
      rwa [oddDiag_one, Matrix.one_mul] at this)
    (by
      have := det_oddProd (h := h) (A := (1 : Matrix (Fin 2) (Fin 2) K)) (by simp) 1 0 Y
      rw [oddDiag_one, Matrix.one_mul] at this
      rw [this]
      simp)

theorem mat_vSU {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y) :
    mat (vSU h Y hY) = oddUni h 0 Y :=
  coe_mkHypSU _ _ _ _

theorem vSU_mem_Vsub {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y) : vSU h Y hY ∈ Vsub h :=
  mem_Vsub_of_mat (mat_vSU hY)

theorem isHerm_e₁₁ (h : UnitaryFieldData 2 f K) :
    IsHerm h (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) := by
  have := h.charP
  ext i j; fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

theorem isHerm_swap (h : UnitaryFieldData 2 f K) :
    IsHerm h (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) := by
  have := h.charP
  ext i j; fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

@[expose] def z₁SU (h : UnitaryFieldData 2 f K) : hypSU h 2 1 := vSU h !![1, 0; 0, 0] (isHerm_e₁₁ h)

@[expose] def z₂SU (h : UnitaryFieldData 2 f K) : hypSU h 2 1 :=
  vSU h !![0, 1; 1, 0] (isHerm_swap h)

theorem z₁SU_mem_ZPsub : z₁SU h ∈ ZPsub h := by
  rw [mem_ZPsub, z₁SU, mat_vSU]
  refine ⟨mem_U_of_oddUni (mat_vSU _), ?_⟩
  simp [oddUni]

theorem z₂SU_mem_Z₂Psub : z₂SU h ∈ Z₂Psub h := by
  rw [mem_Z₂Psub, z₂SU, mat_vSU]
  refine ⟨mem_U_of_oddUni (mat_vSU _), ?_⟩
  simp [oddUni]

theorem mat_z₁SU_e₁f₁ : mat (z₁SU h) ιe₁ ιf₁ = 1 := by
  rw [z₁SU, mat_vSU]
  simp [oddUni]

theorem mat_z₂SU_e₁f₂ : mat (z₂SU h) ιe₁ ιf₂ = 1 := by
  rw [z₂SU, mat_vSU]
  simp [oddUni]

theorem z₁SU_ne_one : z₁SU h ≠ 1 := fun e => by
  have := mat_z₁SU_e₁f₁ (h := h)
  rw [e, mat_one, one_apply_ne (by decide)] at this
  exact zero_ne_one this

theorem z₂SU_ne_one : z₂SU h ≠ 1 := fun e => by
  have := mat_z₂SU_e₁f₂ (h := h)
  rw [e, mat_one, one_apply_ne (by decide)] at this
  exact zero_ne_one this

theorem orderOf_z₁SU : orderOf (z₁SU h) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact Vsub_sq (vSU_mem_Vsub _)) z₁SU_ne_one

theorem orderOf_z₂SU : orderOf (z₂SU h) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact Vsub_sq (vSU_mem_Vsub _)) z₂SU_ne_one

theorem exists_scalar_of_mem_hypScalars {g : hypSU h 2 1} (hg : g ∈ hypScalars h 2 1) :
    ∃ c : K, c ≠ 0 ∧ ∀ a b, mat g a b = if a = b then c else 0 := by
  obtain ⟨c, -, -, hc⟩ := hg
  refine ⟨c, c.ne_zero, fun a b => ?_⟩
  change ((g : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b = _
  rw [hc]
  by_cases e : a = b
  · subst e
    simp
  · simp [e]

theorem rSU_not_mem_hypScalars : rSU h ∉ hypScalars h 2 1 := fun hr => by
  obtain ⟨c, hc, hcm⟩ := exists_scalar_of_mem_hypScalars hr
  have := hcm ιe₁ ιe₁
  rw [mat_rSU, ite_eq_right (by decide), ite_eq_left rfl] at this
  exact hc this.symm

theorem sSU_not_mem_hypScalars : sSU h ∉ hypScalars h 2 1 := fun hs => by
  obtain ⟨c, hc, hcm⟩ := exists_scalar_of_mem_hypScalars hs
  have := hcm ιe₂ ιe₂
  rw [mat_sSU, ite_eq_right (by decide), ite_eq_left rfl] at this
  exact hc this.symm

namespace Data

variable {G : Type} [Group G] (d : Data G h)

@[expose] def A₂ : Subgroup G := d.pull (A₂sub h)

@[expose] def Zp : Subgroup G := d.pull (ZPsub h)

@[expose] def Z₂p : Subgroup G := d.pull (Z₂Psub h)

@[expose] def I : Subgroup G := d.pull (Isub h)

@[expose] def I₁ : Subgroup G := d.pull (I₁sub h)

@[expose] def I₂ : Subgroup G := d.pull (I₂sub h)

@[expose] def I₃ : Subgroup G := d.pull (I₃sub h)

@[expose] def I₄ : Subgroup G := d.pull (I₄sub h)

@[expose] def I₅ : Subgroup G := d.pull (I₅sub h)

@[expose] def I₆ : Subgroup G := d.pull (I₆sub h)

@[expose] def N₁ : Subgroup G := d.pull (N₁sub h)

@[expose] def N₂ : Subgroup G := d.pull (N₂sub h)

@[expose] def N₄ : Subgroup G := d.pull (N₄sub h)

@[expose] def N₅ : Subgroup G := d.pull (N₅sub h)

@[expose] def r : G := d.η (rSU h)

@[expose] def s : G := d.η (sSU h)

@[expose] def z₁ : G := d.η (z₁SU h)

@[expose] def z₂ : G := d.η (z₂SU h)

theorem η_eq_one_iff (g : hypSU h 2 1) : d.η g = 1 ↔ g ∈ hypScalars h 2 1 := by
  rw [← MonoidHom.mem_ker, ker_η]

theorem pull_inf {M M' : Subgroup (hypSU h 2 1)} (hM : M ≤ hypUnitriangular h 2 1)
    (hM' : M' ≤ hypUnitriangular h 2 1) : d.pull (M ⊓ M') = d.pull M ⊓ d.pull M' := by
  refine le_antisymm (le_inf (d.pull_mono inf_le_left) (d.pull_mono inf_le_right)) ?_
  rintro _ ⟨⟨m, hm, rfl⟩, ⟨m', hm', e⟩⟩
  rw [d.η_injOn (hM' hm') (hM hm) e] at hm'
  exact ⟨m, ⟨hm, hm'⟩, rfl⟩

theorem η_mem_pull_iff {M : Subgroup (hypSU h 2 1)} (hM : M ≤ hypUnitriangular h 2 1)
    {g : hypSU h 2 1} (hg : g ∈ hypUnitriangular h 2 1) : d.η g ∈ d.pull M ↔ g ∈ M := by
  constructor
  · rintro ⟨m, hm, e⟩
    rwa [← d.η_injOn (hM hm) hg e]
  · intro hgM
    exact ⟨g, hgM, rfl⟩

theorem pull_conj (M : Subgroup (hypSU h 2 1)) (g : hypSU h 2 1) :
    d.pull (M.map (MulAut.conj g).toMonoidHom) =
      (d.pull M).map (MulAut.conj (d.η g)).toMonoidHom := by
  ext x
  simp only [pull, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨d.η m, ⟨m, hm, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨g * m * g⁻¹, ⟨m, hm, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩

theorem card_A₂ : Nat.card d.A₂ = (2 ^ f) ^ 7 := by
  rw [A₂, d.card_pull A₂sub_le_U, card_A₂sub]

theorem card_Zp : Nat.card d.Zp = 2 ^ f := by
  rw [Zp, d.card_pull ZPsub_le_U, card_ZPsub]

theorem card_Z₂p : Nat.card d.Z₂p = (2 ^ f) ^ 3 := by
  rw [Z₂p, d.card_pull (Z₂Psub_le_A₂sub.trans A₂sub_le_U), card_Z₂Psub]

theorem Z₂p_eq : d.Z₂p = d.A₁ ⊓ d.A₂ :=
  d.pull_inf (Vsub_le_Ssub.trans Ssub_le_Usub) A₂sub_le_U

theorem A₂_le_P : d.A₂ ≤ d.P := d.pull_mono A₂sub_le_U

theorem Zp_le_Z₂p : d.Zp ≤ d.Z₂p := d.pull_mono ZPsub_le_Z₂Psub

theorem Z₂p_le_A₁ : d.Z₂p ≤ d.A₁ := d.pull_mono Z₂Psub_le_Vsub

theorem Z₂p_le_A₂ : d.Z₂p ≤ d.A₂ := d.pull_mono Z₂Psub_le_A₂sub

theorem z₁_mem_Zp : d.z₁ ∈ d.Zp := ⟨_, z₁SU_mem_ZPsub, rfl⟩

theorem z₂_mem_Z₂p : d.z₂ ∈ d.Z₂p := ⟨_, z₂SU_mem_Z₂Psub, rfl⟩

theorem orderOf_z₁ : orderOf d.z₁ = 2 := by
  have hU : z₁SU h ∈ hypUnitriangular h 2 1 := ZPsub_le_U z₁SU_mem_ZPsub
  refine orderOf_eq_prime
    (by rw [sq, z₁, ← map_mul, Vsub_sq (ZPsub_le_Vsub z₁SU_mem_ZPsub), map_one]) ?_
  intro e
  exact z₁SU_ne_one (d.η_injOn hU (one_mem _) (by rw [← z₁, e, map_one]))

theorem orderOf_z₂ : orderOf d.z₂ = 2 := by
  have hU : z₂SU h ∈ hypUnitriangular h 2 1 :=
    (Z₂Psub_le_A₂sub.trans A₂sub_le_U) z₂SU_mem_Z₂Psub
  refine orderOf_eq_prime
    (by rw [sq, z₂, ← map_mul, Vsub_sq (Z₂Psub_le_Vsub z₂SU_mem_Z₂Psub), map_one]) ?_
  intro e
  exact z₂SU_ne_one (d.η_injOn hU (one_mem _) (by rw [← z₂, e, map_one]))

theorem r_mem_N₁ : d.r ∈ d.N₁ := ⟨_, rSU_mem_N₁sub, rfl⟩

theorem s_mem_N₂ : d.s ∈ d.N₂ := ⟨_, sSU_mem_N₂sub, rfl⟩

theorem orderOf_r : orderOf d.r = 2 :=
  orderOf_eq_prime (by rw [sq, r, ← map_mul, rSU_mul_self, map_one])
    (fun e => rSU_not_mem_hypScalars ((d.η_eq_one_iff _).1 e))

theorem orderOf_s : orderOf d.s = 2 :=
  orderOf_eq_prime (by rw [sq, s, ← map_mul, sSU_mul_self, map_one])
    (fun e => sSU_not_mem_hypScalars ((d.η_eq_one_iff _).1 e))

theorem N₄_eq : d.N₄ = d.N₁.map (MulAut.conj d.s).toMonoidHom := d.pull_conj _ _

theorem N₅_eq : d.N₅ = d.N₂.map (MulAut.conj d.r).toMonoidHom := d.pull_conj _ _

end Data

end CFSG.LocalAnalysis.EvenBN.U5
