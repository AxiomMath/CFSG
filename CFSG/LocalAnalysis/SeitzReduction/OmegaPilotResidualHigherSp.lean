module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherKernels
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherSLTwo

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

abbrev SpTarget (K : Type) [Field K] (r : {r : ℕ // 1 ≤ r}) : Type :=
  StatedProj (StatedSp r.1 K)

@[expose] def SpRel (K : Type) [Field K] [CharP K 2] (r : {r : ℕ // 1 ≤ r})
    (θ : MulAut (SpTarget K r)) (σ : K ≃+* K) : Prop :=
  SpTraceRead r.1 θ σ

omit [Finite K] in
theorem spRel_unique (r : {r : ℕ // 1 ≤ r}) (θ : MulAut (SpTarget K r)) (σ σ' : K ≃+* K)
    (h : SpRel K r θ σ) (h' : SpRel K r θ σ') : σ = σ' :=
  spTraceRead_unique r.2 h h'

theorem spTraceRead_conj_of_one_le {f : ℕ} (hK : Nat.card K = 2 ^ f) {r : ℕ} (hr : 1 ≤ r)
    (μ : MulAut (StatedProj (StatedSp r K))) {θ : MulAut (StatedProj (StatedSp r K))}
    {σ : K ≃+* K} (h : SpTraceRead r θ σ) : SpTraceRead r (μ * θ * μ⁻¹) σ := by
  rcases (show r = 1 ∨ r = 2 ∨ 3 ≤ r by omega) with rfl | rfl | hr3
  · exact spTraceRead_conj_one μ h
  · exact spTraceRead_conj_two hK μ h
  · exact spTraceRead_conj hr3 μ h

theorem simple_perfect_statedProj_of_one_le (hq : 4 ≤ Nat.card K) {r : ℕ} (hr : 1 ≤ r) :
    IsSimpleGroup (StatedProj (StatedSp r K)) ∧ Group.IsPerfect (StatedProj (StatedSp r K)) := by
  rcases (show r = 1 ∨ 2 ≤ r by omega) with rfl | hr2
  · exact ⟨isSimpleGroup_statedProj_statedSp_one hq, isPerfect_statedProj_statedSp_one hq⟩
  · exact CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := K) hr2 (by omega)

theorem spTraceRead_of_chart {C : Type*} [Group C] [Finite C] (fp : MulAut C →* (K ≃+* K))
    {f : ℕ} (hK : Nat.card K = 2 ^ f) {X : Subgroup C} (N : Subgroup ↥X) [N.Normal] {r₀ : ℕ}
    (hr₀ : 1 ≤ r₀) (ε₀ : ↥X ⧸ N ≃* StatedProj (StatedSp r₀ K))
    (h₀ : ∀ (β : MulAut C) (hβ : ∀ x ∈ X, β x ∈ X)
      (hN : ∀ m ∈ N, restrictAutOfMapsTo β X hβ m ∈ N),
      SpTraceRead r₀ ((ε₀.symm.trans (quotAutOfMapsTo N (restrictAutOfMapsTo β X hβ) hN)).trans ε₀)
        (fp β))
    {r : ℕ} (ε : ↥X ⧸ N ≃* StatedProj (StatedSp r K)) (β : MulAut C) (hβ : ∀ x ∈ X, β x ∈ X)
    (hN : ∀ m ∈ N, restrictAutOfMapsTo β X hβ m ∈ N) :
    SpTraceRead r ((ε.symm.trans (quotAutOfMapsTo N (restrictAutOfMapsTo β X hβ) hN)).trans ε)
      (fp β) := by
  obtain rfl := rank_eq_of_mulEquiv (ε₀.symm.trans ε)
  have h := spTraceRead_conj_of_one_le hK hr₀ (ε₀.symm.trans ε) (h₀ β hβ hN)
  convert h using 1
  ext y
  simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulAut.inv_def, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply]

section Core

variable {C : Type*} [Group C] [Finite C]

abbrev SpCoreRead (fp : MulAut C →* (K ≃+* K)) (X : Subgroup C) : Prop :=
  CoreRead fp X (SpTarget K) (SpRel K)

@[expose] def SpLeviSection (fp : MulAut C →* (K ≃+* K)) (X : Subgroup C) (N : Subgroup ↥X)
    [N.Normal] : Prop :=
  (∀ r : ℕ, 1 ≤ r → IsEmpty (↥X ⧸ N ≃* StatedProj (StatedSp r K))) ∨
    ∃ (r₀ : ℕ) (_ : 1 ≤ r₀) (ε₀ : ↥X ⧸ N ≃* StatedProj (StatedSp r₀ K)),
      ∀ (β : MulAut C) (hβ : ∀ x ∈ X, β x ∈ X) (hN : ∀ m ∈ N, restrictAutOfMapsTo β X hβ m ∈ N),
        SpTraceRead r₀
          ((ε₀.symm.trans (quotAutOfMapsTo N (restrictAutOfMapsTo β X hβ) hN)).trans ε₀) (fp β)

@[expose] def SpLeviData (fp : MulAut C →* (K ≃+* K)) (X : Subgroup C) : Prop :=
  ∃ (N₁ N₂ N₃ : Subgroup ↥X) (_ : N₁.Normal) (_ : N₂.Normal) (_ : N₃.Normal),
    IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃) ∧
    (∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)),
      ∀ M : Subgroup ↥X, M.Normal → N ≤ M → M = N ∨ M = ⊤) ∧
    (∀ (N : Subgroup ↥X) [N.Normal], N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)) →
      SpLeviSection fp X N) ∧
    ∃ r : ℕ, 1 ≤ r ∧ Nonempty (↥X ⧸ N₁ ≃* StatedProj (StatedSp r K)) ∧
      ∀ (β : MulAut C) (hβ : ∀ x ∈ X, β x ∈ X), ∀ m ∈ N₁, restrictAutOfMapsTo β X hβ m ∈ N₁

theorem readsThrough_section_of_spLeviSection (fp : MulAut C →* (K ≃+* K)) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) {X : Subgroup C} {N : Subgroup ↥X} [N.Normal]
    (h : SpLeviSection fp X N) (r : {r : ℕ // 1 ≤ r}) (ε : ↥X ⧸ N ≃* SpTarget K r)
    (β : MulAut C) (hβ : ∀ x ∈ X, β x ∈ X) (hN : ∀ m ∈ N, restrictAutOfMapsTo β X hβ m ∈ N) :
    SpRel K r ((ε.symm.trans (quotAutOfMapsTo N (restrictAutOfMapsTo β X hβ) hN)).trans ε)
      (fp β) := by
  rcases h with hno | ⟨r₀, hr₀, ε₀, h₀⟩
  · exact ((hno r.1 r.2).false ε).elim
  · exact spTraceRead_of_chart fp hK N hr₀ ε₀ h₀ ε β hβ hN

theorem spCoreRead_of_spLeviData (fp : MulAut C →* (K ≃+* K)) {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) {X : Subgroup C} (h : SpLeviData fp X) : SpCoreRead fp X := by
  obtain ⟨N₁, N₂, N₃, hN₁, hN₂, hN₃, h123, hq', hs, r, hr, ⟨e⟩, hinv⟩ := h
  refine ⟨⟨⟨r, hr⟩, N₁, hN₁, ⟨e⟩, hinv⟩, fun r' => ?_⟩
  obtain ⟨hsimple, hperf⟩ := simple_perfect_statedProj_of_one_le hq r'.2
  have hnc : ∃ a b : SpTarget K r', a * b ≠ b * a := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    have hbot : commutator (SpTarget K r') = ⊥ := by
      rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_def, hall a b, mul_inv_cancel_right,
        mul_inv_cancel]
    have htop : commutator (SpTarget K r') = ⊤ := hperf.commutator_eq_top
    have hnt : Nontrivial (SpTarget K r') := IsSimpleGroup.toNontrivial
    rw [hbot] at htop
    exact (bot_ne_top : (⊥ : Subgroup (SpTarget K r')) ≠ ⊤) htop
  exact readsThrough_of_three fp hnc N₁ N₂ N₃ h123 hq' fun N _ hN =>
    readsThrough_section_of_spLeviSection fp hK (hs N hN) r'

end Core

section Assembly

variable {n : ℕ}

omit [CharP K 2] in
theorem four_le_card_of_even {f : ℕ} (hK : Nat.card K = 2 ^ f) (hfe : Even f) :
    4 ≤ Nat.card K := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨g, rfl⟩ := hfe
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · rw [hK] at h1
    simp at h1
  · rw [hK, ← two_mul, pow_mul]
    calc 4 = (2 ^ 2) ^ 1 := by norm_num
      _ ≤ (2 ^ 2) ^ g := Nat.pow_le_pow_right (by norm_num) hg

end Assembly

end CFSG.SeitzReduction.OmegaPilot
