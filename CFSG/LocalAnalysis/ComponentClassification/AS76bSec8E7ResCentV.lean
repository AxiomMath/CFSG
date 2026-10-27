module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7ResCentVLevel
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVLevi

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.E7Pilot
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)
open CFSG.LieType.Universal.Symplectic.SpExtras (elt)

local instance e7ResCentVNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

theorem resCent_conj {C : Type*} [Group C] [Finite C] (n : C) {x : C} {Z : Subgroup C}
    (h : Exc.ResCent x Z) :
    Exc.ResCent (n * x * n⁻¹) (Z.map (MulAut.conj n).toMonoidHom) := by
  have hcent : Exc.cent (n * x * n⁻¹) = (Exc.cent x).map (MulAut.conj n).toMonoidHom := by
    ext y
    simp only [Exc.cent, mem_centralizer_singleton_iff, mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · intro hy
      refine ⟨n⁻¹ * y * n, ?_, by group⟩
      calc n⁻¹ * y * n * x = n⁻¹ * (y * (n * x * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * x * n⁻¹) * y) * n := by rw [hy]
        _ = x * (n⁻¹ * y * n) := by group
    · rintro ⟨z, hz, rfl⟩
      calc n * z * n⁻¹ * (n * x * n⁻¹) = n * (z * x) * n⁻¹ := by group
        _ = n * (x * z) * n⁻¹ := by rw [hz]
        _ = n * x * n⁻¹ * (n * z * n⁻¹) := by group
  intro y hy hy2 hyc
  rw [hcent] at hy hyc
  rw [← CFSG.Quasithin.map_perfectCore] at hyc
  obtain ⟨z, hz, rfl⟩ := hy
  refine ⟨z, h z hz ?_ fun d hd => ?_, rfl⟩
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy2
    have e : n * (z * z) * n⁻¹ = 1 := by
      calc n * (z * z) * n⁻¹ = n * z * n⁻¹ * (n * z * n⁻¹) := by group
        _ = 1 := hy2
    have : z * z = n⁻¹ * 1 * n := by
      calc z * z = n⁻¹ * (n * (z * z) * n⁻¹) * n := by group
        _ = n⁻¹ * 1 * n := by rw [e]
    simpa using this
  · have h1 := hyc ((MulAut.conj n).toMonoidHom d) ⟨d, hd, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have : n * (z * d) * n⁻¹ = n * (d * z) * n⁻¹ := by
      calc n * (z * d) * n⁻¹ = n * z * n⁻¹ * (n * d * n⁻¹) := by group
        _ = n * d * n⁻¹ * (n * z * n⁻¹) := h1
        _ = n * (d * z) * n⁻¹ := by group
    simpa using this

section Coeff

variable {K : Type} [Field K]


theorem vConjCoeff_eq_of_commute [CharP K 2] {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α)
    (hα0 : vLevel α = 0) {e : (Fin Tag.E7.rank → ℤ) → K}
    (h : pinnedX .E7 K α 1 * rootProd .E7 K vPsi e = rootProd .E7 K vPsi e * pinnedX .E7 K α 1) :
    ∀ ρ ∈ vPsi, conjCoeff α 1 vPsi e ρ = e ρ := by
  have h' := conj_rootProd_vPsi hα hα0.ge 1 e
  rw [h, mul_inv_cancel_right] at h'
  exact E6Pilot.rootProd_injective vPsi_nodup (fun β hβ => pos_of_mem_vPsi hβ) h'.symm

theorem vConjCoeff_pair_eq_of_commute [CharP K 2] {a b : Fin Tag.E7.rank → ℤ}
    (ha : IsRoot .E7 a) (hb : IsRoot .E7 b) (ha0 : vLevel a = 0) (hb0 : vLevel b = 0)
    {e : (Fin Tag.E7.rank → ℤ) → K}
    (h : pinnedX .E7 K a 1 * pinnedX .E7 K b 1 * rootProd .E7 K vPsi e =
      rootProd .E7 K vPsi e * (pinnedX .E7 K a 1 * pinnedX .E7 K b 1)) :
    ∀ ρ ∈ vPsi, conjCoeff a 1 vPsi (conjCoeff b 1 vPsi e) ρ = e ρ := by
  have h' : rootProd .E7 K vPsi (conjCoeff a 1 vPsi (conjCoeff b 1 vPsi e)) =
      rootProd .E7 K vPsi e := by
    rw [← conj_rootProd_vPsi ha ha0.ge, ← conj_rootProd_vPsi hb hb0.ge]
    calc pinnedX .E7 K a 1 * (pinnedX .E7 K b 1 * rootProd .E7 K vPsi e *
          (pinnedX .E7 K b 1)⁻¹) * (pinnedX .E7 K a 1)⁻¹ =
        pinnedX .E7 K a 1 * pinnedX .E7 K b 1 * rootProd .E7 K vPsi e *
          (pinnedX .E7 K a 1 * pinnedX .E7 K b 1)⁻¹ := by group
      _ = rootProd .E7 K vPsi e := by rw [h]; group
  exact E6Pilot.rootProd_injective vPsi_nodup (fun β hβ => pos_of_mem_vPsi hβ) h'

@[expose] def vPsiKillB (α ρ β : Fin Tag.E7.rank → ℤ) : Bool :=
  decide (ρ ∈ vPsi) && decide (ρ - α = β) && decide (β ∈ vPsi)

theorem vPsiKill {α : Fin Tag.E7.rank → ℤ} {e : (Fin Tag.E7.rank → ℤ) → K}
    (hc : vLevel α = 0 ∧ ∀ ρ ∈ vPsi, conjCoeff α 1 vPsi e ρ = e ρ) {ρ β : Fin Tag.E7.rank → ℤ}
    (h : vPsiKillB α ρ β = true) : e β = 0 := by
  simp only [vPsiKillB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hρ, hβ⟩, hβΨ⟩ := h
  have h' := hc.2 ρ hρ
  rw [conjCoeff_vPsi_apply (by rw [hc.1]; norm_num) 1 e hρ, hβ, ite_eq_left hβΨ, one_mul,
    add_eq_left] at h'
  exact h'

@[expose] def vPairThreeB (a b ρ β₁ β₂ β₃ : Fin Tag.E7.rank → ℤ) : Bool :=
  decide (ρ ∈ vPsi) && decide (ρ - b = β₁) && decide (β₁ ∈ vPsi) && decide (ρ - a = β₂) &&
    decide (β₂ ∈ vPsi) && decide (β₂ - b = β₃) && decide (β₃ ∈ vPsi)

theorem vPairThree {a b : Fin Tag.E7.rank → ℤ} {e : (Fin Tag.E7.rank → ℤ) → K}
    (hc : vLevel a = 0 ∧ vLevel b = 0 ∧
      ∀ ρ ∈ vPsi, conjCoeff a 1 vPsi (conjCoeff b 1 vPsi e) ρ = e ρ)
    {ρ β₁ β₂ β₃ : Fin Tag.E7.rank → ℤ} (h : vPairThreeB a b ρ β₁ β₂ β₃ = true) :
    e β₁ + (e β₂ + e β₃) = 0 := by
  obtain ⟨ha0, hb0, hc⟩ := hc
  simp only [vPairThreeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hρ, hb⟩, h1⟩, ha⟩, h2⟩, hab⟩, h3⟩ := h
  have e1 := hc ρ hρ
  have hla : vLevel a ≤ 1 := by rw [ha0]; norm_num
  have hlb : vLevel b ≤ 1 := by rw [hb0]; norm_num
  rw [conjCoeff_vPsi_apply hla 1 _ hρ, conjCoeff_vPsi_apply hlb 1 e hρ, ha,
    ite_eq_left h2, conjCoeff_vPsi_apply hlb 1 e h2, hb, ite_eq_left h1, hab, ite_eq_left h3] at e1
  linear_combination e1

@[expose] def vLinkB (β₁ β₂ ρ γ θ : Fin Tag.E7.rank → ℤ) : Bool :=
  decide (ρ ∈ vPsi) && decide (ρ - β₁ = γ) && decide (γ ∈ vPsi) && decide (ρ - β₂ = θ) &&
    decide (θ ∈ vPsi) && decide (θ - β₁ ∉ vPsi)

theorem vLink {β₁ β₂ : Fin Tag.E7.rank → ℤ} (h₁ : vLevel β₁ = 1) (h₂ : vLevel β₂ = 1)
    (e : (Fin Tag.E7.rank → ℤ) → K) {ρ γ θ : Fin Tag.E7.rank → ℤ}
    (h : vLinkB β₁ β₂ ρ γ θ = true) :
    conjCoeff β₂ 1 vPsi (conjCoeff β₁ 1 vPsi e) ρ = e ρ + e γ + e θ := by
  simp only [vLinkB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hρ, hγe⟩, hγ⟩, hθe⟩, hθ⟩, hθβ⟩ := h
  rw [conjCoeff_vPsi_apply h₂.le 1 _ hρ, conjCoeff_vPsi_apply h₁.le 1 e hρ, hθe, ite_eq_left hθ,
    conjCoeff_vPsi_apply h₁.le 1 e hθ, ite_eq_right hθβ, hγe, ite_eq_left hγ]
  ring

theorem commute_vAS_pair [CharP K 2] {β₁ β₂ : Fin Tag.E7.rank → ℤ}
    (h₁ : IsRoot .E7 β₁ ∧ vLevel β₁ = 1) (h₂ : IsRoot .E7 β₂ ∧ vLevel β₂ = 1)
    (hF : ∀ ρ ∈ vPsi, (ρ - β₁ ∈ vFrame ↔ ρ - β₂ ∈ vFrame)) :
    pinnedX .E7 K β₁ 1 * pinnedX .E7 K β₂ 1 * vAS K =
      vAS K * (pinnedX .E7 K β₁ 1 * pinnedX .E7 K β₂ 1) := by
  have hv : ∀ x, (if x ∈ vPsi then (1 : K) * vCoeff x else 0) = if x ∈ vFrame then 1 else 0 := by
    intro x
    by_cases hx : x ∈ vFrame
    · rw [ite_eq_left (mem_vPsi_of_mem_vFrame hx), one_mul, ite_eq_left hx]
      simp only [vCoeff]
      rw [ite_eq_left hx]
    · rw [ite_eq_right hx, vCoeff_eq_zero_of_not_mem hx, mul_zero]
      split_ifs <;> rfl
  have hc : ∀ ρ ∈ vPsi, conjCoeff β₁ 1 vPsi (conjCoeff β₂ 1 vPsi (vCoeff (K := K))) ρ =
      vCoeff ρ := by
    intro ρ hρ
    rw [conjCoeff_vPsi_apply h₁.2.le 1 _ hρ, conjCoeff_vPsi_apply h₂.2.le 1 vCoeff hρ, hv]
    have hlow : ∀ x ∈ vPsi, x - β₂ ∉ vPsi →
        conjCoeff β₂ 1 vPsi (vCoeff (K := K)) x = vCoeff x := by
      intro x hx hx'
      rw [conjCoeff_vPsi_apply h₂.2.le 1 vCoeff hx, ite_eq_right hx', add_zero]
    by_cases hb : ρ - β₁ ∈ vPsi
    · have hb2 : ρ - β₁ - β₂ ∉ vPsi := by
        intro h
        have h2 := level_of_mem_vPsi h
        have h3 : vLevel ρ ≤ 3 := by
          have := vPsi_level_check ρ hρ
          omega
        rw [sub_eq_add_neg, sub_eq_add_neg, vLevel_add, vLevel_add, vLevel_neg, vLevel_neg,
          h₁.2, h₂.2] at h2
        omega
      rw [ite_eq_left hb, hlow _ hb hb2]
      have e2 := hv (ρ - β₁)
      rw [ite_eq_left hb] at e2
      rw [e2]
      by_cases hf : ρ - β₁ ∈ vFrame
      · rw [ite_eq_left hf, ite_eq_left ((hF ρ hρ).1 hf), add_assoc,
          CharTwo.add_self_eq_zero, add_zero]
      · rw [ite_eq_right hf, ite_eq_right fun h => hf ((hF ρ hρ).2 h), add_zero, add_zero]
    · rw [ite_eq_right hb, add_zero]
      have hf : ρ - β₁ ∉ vFrame := fun h => hb (mem_vPsi_of_mem_vFrame h)
      rw [ite_eq_right fun h => hf ((hF ρ hρ).2 h), add_zero]
  have hconj : pinnedX .E7 K β₁ 1 * pinnedX .E7 K β₂ 1 * vAS K *
      (pinnedX .E7 K β₁ 1 * pinnedX .E7 K β₂ 1)⁻¹ = vAS K := by
    rw [← rootProd_vPsi_vCoeff]
    calc pinnedX .E7 K β₁ 1 * pinnedX .E7 K β₂ 1 * rootProd .E7 K vPsi vCoeff *
          (pinnedX .E7 K β₁ 1 * pinnedX .E7 K β₂ 1)⁻¹ =
        pinnedX .E7 K β₁ 1 * (pinnedX .E7 K β₂ 1 * rootProd .E7 K vPsi vCoeff *
          (pinnedX .E7 K β₂ 1)⁻¹) * (pinnedX .E7 K β₁ 1)⁻¹ := by group
      _ = rootProd .E7 K vPsi vCoeff := by
        rw [conj_rootProd_vPsi h₂.1 (by rw [h₂.2]; norm_num),
          conj_rootProd_vPsi h₁.1 (by rw [h₁.2]; norm_num), E6Pilot.rootProd_congr hc]
  calc pinnedX .E7 K β₁ 1 * pinnedX .E7 K β₂ 1 * vAS K =
      pinnedX .E7 K β₁ 1 * pinnedX .E7 K β₂ 1 * vAS K *
        (pinnedX .E7 K β₁ 1 * pinnedX .E7 K β₂ 1)⁻¹ *
          (pinnedX .E7 K β₁ 1 * pinnedX .E7 K β₂ 1) := by group
    _ = vAS K * (pinnedX .E7 K β₁ 1 * pinnedX .E7 K β₂ 1) := by rw [hconj]

end Coeff

@[expose] def vAuxRoot : Fin 6 → Fin Tag.E7.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 1, 1], ![1, 1, 2, 2, 1, 0, 0]]

theorem vAuxRoot_check : (∀ i : Fin 6, isRootB .E7 (vAuxRoot i) = true) ∧
    vLevel (vAuxRoot 0) = 0 ∧ vLevel (vAuxRoot 1) = 0 ∧ vLevel (vAuxRoot 2) = 0 ∧
    vLevel (vAuxRoot 3) = 0 ∧ vLevel (vAuxRoot 4) = 1 ∧ vLevel (vAuxRoot 5) = 1 ∧
    ∀ ρ ∈ vPsi, decide (ρ - vAuxRoot 4 ∈ vFrame) = decide (ρ - vAuxRoot 5 ∈ vFrame) := by
  decide +kernel

theorem e7A5Root_spIdx_check :
    e7A5Root (e7SpIdx (.inl 0)) (e7SpIdx (.inr 0)) = vLongGen 0 ∧
    e7A5Root (e7SpIdx (.inr 0)) (e7SpIdx (.inl 0)) = vLongGen 1 ∧
    e7A5Root (e7SpIdx (.inl 1)) (e7SpIdx (.inr 1)) = vLongGen 2 ∧
    e7A5Root (e7SpIdx (.inr 1)) (e7SpIdx (.inl 1)) = vLongGen 3 ∧
    e7A5Root (e7SpIdx (.inl 2)) (e7SpIdx (.inr 2)) = vLongGen 4 ∧
    e7A5Root (e7SpIdx (.inr 2)) (e7SpIdx (.inl 2)) = vLongGen 5 ∧
    e7A5Root (e7SpIdx (.inl 0)) (e7SpIdx (.inl 1)) = vAuxRoot 0 ∧
    e7A5Root (e7SpIdx (.inr 1)) (e7SpIdx (.inr 0)) = vAuxRoot 1 ∧
    e7A5Root (e7SpIdx (.inl 1)) (e7SpIdx (.inl 2)) = vAuxRoot 2 ∧
    e7A5Root (e7SpIdx (.inr 2)) (e7SpIdx (.inr 1)) = vAuxRoot 3 := by
  decide +kernel

section Finite

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem commutator_range_spToAdjointE7_eq :
    ⁅(spToAdjointE7 K).range, (spToAdjointE7 K).range⁆ = (spToAdjointE7 K).range := by
  have hperf : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSp 3 K) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 3 K (by norm_num)
      F4Pilot.sp6_field_condition).1
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    hperf.commutator_eq_top]

theorem range_spToAdjointE7_le_perfectCore :
    (spToAdjointE7 K).range ≤
      CFSG.Quasithin.perfectCore (centralizer ({e7ASRep K 4} : Set (adjointGroup .E7 K))) :=
  CFSG.Quasithin.le_perfectCore_of_perfect range_spToAdjointE7_le_centralizer
    commutator_range_spToAdjointE7_eq

theorem exists_spToAdjointE7_eq_vLongGen (i : Fin 6) :
    ∃ X, (spToAdjointE7 K X : ModGL .E7 K) = pinnedX .E7 K (vLongGen i) 1 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, -⟩ := e7A5Root_spIdx_check
  fin_cases i
  · exact ⟨elt (.positiveLong 0) 1, by rw [spToAdjointE7_positiveLong, coe_e7A5Elt, c0]; rfl⟩
  · exact ⟨elt (.negativeLong 0) 1, by rw [spToAdjointE7_negativeLong, coe_e7A5Elt, c1]; rfl⟩
  · exact ⟨elt (.positiveLong 1) 1, by rw [spToAdjointE7_positiveLong, coe_e7A5Elt, c2]; rfl⟩
  · exact ⟨elt (.negativeLong 1) 1, by rw [spToAdjointE7_negativeLong, coe_e7A5Elt, c3]; rfl⟩
  · exact ⟨elt (.positiveLong 2) 1, by rw [spToAdjointE7_positiveLong, coe_e7A5Elt, c4]; rfl⟩
  · exact ⟨elt (.negativeLong 2) 1, by rw [spToAdjointE7_negativeLong, coe_e7A5Elt, c5]; rfl⟩

theorem exists_spToAdjointE7_eq_short :
    (∃ X, (spToAdjointE7 K X : ModGL .E7 K) =
      pinnedX .E7 K (vAuxRoot 0) 1 * pinnedX .E7 K (vAuxRoot 1) 1) ∧
    ∃ X, (spToAdjointE7 K X : ModGL .E7 K) =
      pinnedX .E7 K (vAuxRoot 2) 1 * pinnedX .E7 K (vAuxRoot 3) 1 := by
  obtain ⟨-, -, -, -, -, -, d0, d1, d2, d3⟩ := e7A5Root_spIdx_check
  refine ⟨⟨elt (.difference 0 1 (by decide)) 1, ?_⟩, ⟨elt (.difference 1 2 (by decide)) 1, ?_⟩⟩
  · rw [spToAdjointE7_difference, Subgroup.coe_mul, coe_e7A5Elt, coe_e7A5Elt, d0, d1]
  · rw [spToAdjointE7_difference, Subgroup.coe_mul, coe_e7A5Elt, coe_e7A5Elt, d2, d3]

theorem mem_e7FrameLine_vFrame_of_mem_parabolicRadical {y : adjointGroup .E7 K}
    (hyQ : (y : ModGL .E7 K) ∈ parabolicRadical .E7 K vNodes)
    (hyc : ∀ d ∈ CFSG.Quasithin.perfectCore
      (centralizer ({e7ASRep K 4} : Set (adjointGroup .E7 K))), y * d = d * y) :
    y ∈ e7FrameLine K vFrame := by
  have hL0 : ∀ X, (y : ModGL .E7 K) * (spToAdjointE7 K X : ModGL .E7 K) =
      (spToAdjointE7 K X : ModGL .E7 K) * y := fun X =>
    congrArg Subtype.val (hyc _ (range_spToAdjointE7_le_perfectCore ⟨X, rfl⟩))
  have hlong : ∀ i : Fin 6, pinnedX .E7 K (vLongGen i) 1 * (y : ModGL .E7 K) =
      y * pinnedX .E7 K (vLongGen i) 1 := by
    intro i
    obtain ⟨X, hX⟩ := exists_spToAdjointE7_eq_vLongGen (K := K) i
    rw [← hX]
    exact (hL0 X).symm
  obtain ⟨e, he⟩ := exists_rootProd_vPsi_of_commute hyQ hlong
  have hL : ∀ i : Fin 6, vLevel (vLongGen i) = 0 ∧
      ∀ ρ ∈ vPsi, conjCoeff (vLongGen i) 1 vPsi e ρ = e ρ := fun i =>
    ⟨(vLongGen_check i).2, vConjCoeff_eq_of_commute (isRootB_iff.1 (vLongGen_check i).1)
      (vLongGen_check i).2 (by rw [← he]; exact hlong i)⟩
  have k0101111 : e ![0, 1, 0, 1, 1, 1, 1] = 0 := vPsiKill (hL 0) (ρ := ![1, 1, 1, 2, 2, 2, 1])
    (by decide +kernel)
  have k0111111 : e ![0, 1, 1, 1, 1, 1, 1] = 0 := vPsiKill (hL 0) (ρ := ![1, 1, 2, 2, 2, 2, 1])
    (by decide +kernel)
  have k0112111 : e ![0, 1, 1, 2, 1, 1, 1] = 0 := vPsiKill (hL 0) (ρ := ![1, 1, 2, 3, 2, 2, 1])
    (by decide +kernel)
  have k1111111 : e ![1, 1, 1, 1, 1, 1, 1] = 0 := vPsiKill (hL 2) (ρ := ![1, 1, 2, 2, 2, 1, 1])
    (by decide +kernel)
  have k0112211 : e ![0, 1, 1, 2, 2, 1, 1] = 0 := vPsiKill (hL 0) (ρ := ![1, 1, 2, 3, 3, 2, 1])
    (by decide +kernel)
  have k1112111 : e ![1, 1, 1, 2, 1, 1, 1] = 0 := vPsiKill (hL 2) (ρ := ![1, 1, 2, 3, 2, 1, 1])
    (by decide +kernel)
  have k1112221 : e ![1, 1, 1, 2, 2, 2, 1] = 0 := vPsiKill (hL 1) (ρ := ![0, 1, 0, 1, 1, 1, 1])
    (by decide +kernel)
  have k1122211 : e ![1, 1, 2, 2, 2, 1, 1] = 0 := vPsiKill (hL 3) (ρ := ![1, 1, 1, 1, 1, 1, 1])
    (by decide +kernel)
  have k1122221 : e ![1, 1, 2, 2, 2, 2, 1] = 0 := vPsiKill (hL 1) (ρ := ![0, 1, 1, 1, 1, 1, 1])
    (by decide +kernel)
  have k1123211 : e ![1, 1, 2, 3, 2, 1, 1] = 0 := vPsiKill (hL 3) (ρ := ![1, 1, 1, 2, 1, 1, 1])
    (by decide +kernel)
  have k1123221 : e ![1, 1, 2, 3, 2, 2, 1] = 0 := vPsiKill (hL 1) (ρ := ![0, 1, 1, 2, 1, 1, 1])
    (by decide +kernel)
  have k1223211 : e ![1, 2, 2, 3, 2, 1, 1] = 0 := vPsiKill (hL 0) (ρ := ![2, 2, 3, 4, 3, 2, 1])
    (by decide +kernel)
  have k1123321 : e ![1, 1, 2, 3, 3, 2, 1] = 0 := vPsiKill (hL 1) (ρ := ![0, 1, 1, 2, 2, 1, 1])
    (by decide +kernel)
  have k1223221 : e ![1, 2, 2, 3, 2, 2, 1] = 0 := vPsiKill (hL 2) (ρ := ![1, 2, 3, 4, 3, 2, 1])
    (by decide +kernel)
  have k1223321 : e ![1, 2, 2, 3, 3, 2, 1] = 0 := vPsiKill (hL 4) (ρ := ![1, 2, 2, 4, 3, 2, 1])
    (by decide +kernel)
  have k1224321 : e ![1, 2, 2, 4, 3, 2, 1] = 0 := vPsiKill (hL 5) (ρ := ![1, 2, 2, 3, 3, 2, 1])
    (by decide +kernel)
  have k1234321 : e ![1, 2, 3, 4, 3, 2, 1] = 0 := vPsiKill (hL 3) (ρ := ![1, 2, 2, 3, 2, 2, 1])
    (by decide +kernel)
  have k2234321 : e ![2, 2, 3, 4, 3, 2, 1] = 0 := vPsiKill (hL 1) (ρ := ![1, 2, 2, 3, 2, 1, 1])
    (by decide +kernel)
  obtain ⟨⟨X1, hX1⟩, ⟨X2, hX2⟩⟩ := exists_spToAdjointE7_eq_short (K := K)
  obtain ⟨hAr, hA0, hA1, hA2, hA3, hA4, hA5, hAF⟩ := vAuxRoot_check
  have hD01 : vLevel (vAuxRoot 0) = 0 ∧ vLevel (vAuxRoot 1) = 0 ∧
      ∀ ρ ∈ vPsi, conjCoeff (vAuxRoot 0) 1 vPsi (conjCoeff (vAuxRoot 1) 1 vPsi e) ρ = e ρ := by
    refine ⟨hA0, hA1, vConjCoeff_pair_eq_of_commute (isRootB_iff.1 (hAr 0))
      (isRootB_iff.1 (hAr 1)) hA0 hA1 ?_⟩
    have h := hL0 X1
    rw [hX1, he] at h
    exact h.symm
  have hD12 : vLevel (vAuxRoot 2) = 0 ∧ vLevel (vAuxRoot 3) = 0 ∧
      ∀ ρ ∈ vPsi, conjCoeff (vAuxRoot 2) 1 vPsi (conjCoeff (vAuxRoot 3) 1 vPsi e) ρ = e ρ := by
    refine ⟨hA2, hA3, vConjCoeff_pair_eq_of_commute (isRootB_iff.1 (hAr 2))
      (isRootB_iff.1 (hAr 3)) hA2 hA3 ?_⟩
    have h := hL0 X2
    rw [hX2, he] at h
    exact h.symm
  have fθ : e ![1, 1, 1, 2, 2, 1, 1] + (e ![0, 1, 1, 2, 2, 2, 1] + e ![0, 1, 1, 2, 2, 1, 1]) = 0 :=
    vPairThree hD01 (ρ := ![1, 1, 1, 2, 2, 2, 1]) (by decide +kernel)
  have fψ : e ![1, 1, 2, 2, 1, 1, 1] + (e ![1, 1, 1, 2, 2, 1, 1] + e ![1, 1, 1, 2, 1, 1, 1]) = 0 :=
    vPairThree hD12 (ρ := ![1, 1, 2, 2, 2, 1, 1]) (by decide +kernel)
  rw [k0112211, add_zero] at fθ
  rw [k1112111, add_zero] at fψ
  have hr1 : IsRoot .E7 (vAuxRoot 4) ∧ vLevel (vAuxRoot 4) = 1 := ⟨isRootB_iff.1 (hAr 4), hA4⟩
  have hr2 : IsRoot .E7 (vAuxRoot 5) ∧ vLevel (vAuxRoot 5) = 1 := ⟨isRootB_iff.1 (hAr 5), hA5⟩
  have hFr : ∀ ρ ∈ vPsi, (ρ - vAuxRoot 4 ∈ vFrame ↔ ρ - vAuxRoot 5 ∈ vFrame) := by
    intro ρ hρ
    simpa using hAF ρ hρ
  set r : adjointGroup .E7 K :=
    ⟨pinnedX .E7 K (vAuxRoot 4) 1 * pinnedX .E7 K (vAuxRoot 5) 1,
      mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩ with hrdef
  have hrC : r ∈ centralizer ({e7ASRep K 4} : Set (adjointGroup .E7 K)) := by
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_e7ASRep_four]
    exact commute_vAS_pair hr1 hr2 hFr
  obtain ⟨X3, hX3⟩ := exists_spToAdjointE7_eq_vLongGen (K := K) 3
  set C := centralizer ({e7ASRep K 4} : Set (adjointGroup .E7 K))
  have hlP : spToAdjointE7 K X3 ∈ CFSG.Quasithin.perfectCore C :=
    range_spToAdjointE7_le_perfectCore ⟨X3, rfl⟩
  have hrl : r * spToAdjointE7 K X3 * r⁻¹ ∈ CFSG.Quasithin.perfectCore C := by
    have h := (CFSG.Quasithin.perfectCore_normal C).conj_mem
      ⟨_, CFSG.Quasithin.perfectCore_le C hlP⟩ (mem_subgroupOf.2 hlP) ⟨r, hrC⟩
    rw [mem_subgroupOf] at h
    exact h
  have h1 := hyc _ hrl
  have h2 := hyc _ hlP
  have h3 : (r⁻¹ * y * r) * spToAdjointE7 K X3 = spToAdjointE7 K X3 * (r⁻¹ * y * r) := by
    calc r⁻¹ * y * r * spToAdjointE7 K X3 =
        r⁻¹ * (y * (r * spToAdjointE7 K X3 * r⁻¹)) * r := by group
      _ = r⁻¹ * ((r * spToAdjointE7 K X3 * r⁻¹) * y) * r := by rw [h1]
      _ = spToAdjointE7 K X3 * (r⁻¹ * y * r) := by group
  have hinv : ∀ β : Fin Tag.E7.rank → ℤ, (pinnedX .E7 K β 1)⁻¹ = pinnedX .E7 K β 1 := fun β => by
    rw [pinnedX_neg, CharTwo.neg_eq]
  have hrc : (r : ModGL .E7 K) = pinnedX .E7 K (vAuxRoot 4) 1 * pinnedX .E7 K (vAuxRoot 5) 1 := by
    rw [hrdef]
  have hry : ((r : ModGL .E7 K))⁻¹ * (y : ModGL .E7 K) * r = rootProd .E7 K vPsi
      (conjCoeff (vAuxRoot 5) 1 vPsi (conjCoeff (vAuxRoot 4) 1 vPsi e)) := by
    rw [hrc, he, mul_inv_rev, hinv, hinv,
      ← conj_rootProd_vPsi hr2.1 (by rw [hr2.2]; norm_num),
      ← conj_rootProd_vPsi hr1.1 (by rw [hr1.2]; norm_num), hinv, hinv]
    group
  have h4 : pinnedX .E7 K (vLongGen 3) 1 * rootProd .E7 K vPsi
      (conjCoeff (vAuxRoot 5) 1 vPsi (conjCoeff (vAuxRoot 4) 1 vPsi e)) =
      rootProd .E7 K vPsi
        (conjCoeff (vAuxRoot 5) 1 vPsi (conjCoeff (vAuxRoot 4) 1 vPsi e)) *
        pinnedX .E7 K (vLongGen 3) 1 := by
    have h := congrArg Subtype.val h3
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [hry, hX3] at h
    exact h.symm
  have hk := vPsiKill ⟨(vLongGen_check 3).2, vConjCoeff_eq_of_commute
    (isRootB_iff.1 (vLongGen_check 3).1) (vLongGen_check 3).2 h4⟩
    (ρ := ![1, 2, 2, 3, 2, 2, 1]) (β := ![1, 2, 3, 4, 3, 2, 1]) (by decide +kernel)
  rw [vLink hr1.2 hr2.2 e (ρ := ![1, 2, 3, 4, 3, 2, 1]) (γ := ![1, 2, 2, 3, 2, 1, 0])
    (θ := ![0, 1, 1, 2, 2, 2, 1]) (by decide +kernel), k1234321, zero_add] at hk
  have hd : ∀ β ∈ vPsi, e β = if β ∈ vFrame then e vφ else 0 := by
    intro β hβ
    simp only [vPsi, List.mem_append] at hβ
    rcases hβ with (hβ | hβ) | hβ
    · rw [ite_eq_left hβ]
      rw [vFrame_eq] at hβ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ
      rcases hβ with rfl | rfl | rfl | rfl
      ·
        have hθφ := (eq_neg_of_add_eq_zero_left fθ).trans (CharTwo.neg_eq _)
        have hγθ := (eq_neg_of_add_eq_zero_left hk).trans (CharTwo.neg_eq _)
        exact hγθ.trans hθφ.symm
      · exact ((eq_neg_of_add_eq_zero_left fθ).trans (CharTwo.neg_eq _)).symm
      · exact (eq_neg_of_add_eq_zero_left fψ).trans (CharTwo.neg_eq _)
      · rfl
    · rw [ite_eq_right fun h => vLowHigh_not_mem_vFrame.1 β hβ h]
      iterate 5 (rcases List.mem_cons.1 hβ with rfl | hβ <;> try assumption)
      rcases List.mem_singleton.1 hβ with rfl
      assumption
    · rw [ite_eq_right fun h => vLowHigh_not_mem_vFrame.2 β hβ h]
      iterate 11 (rcases List.mem_cons.1 hβ with rfl | hβ <;> try assumption)
      rcases List.mem_singleton.1 hβ with rfl
      assumption
  have hy : y = e7FrameElt K vFrame (e vφ) := by
    apply Subtype.ext
    rw [coe_e7FrameElt, he, E6Pilot.rootProd_congr hd,
      show (fun β => if β ∈ vFrame then e vφ else 0) =
        fun ρ => if ρ ∈ vFrame then (fun _ => e vφ) ρ else 0 from rfl,
      E6Pilot.rootProd_ite_mem, vPsi_filter_vFrame]
    rfl
  rw [hy]
  exact e7FrameElt_mem_e7FrameLine vFrame (e vφ)

theorem resCent_vAS_of
    (hLevi : ∀ y ∈ centralizer ({e7ASRep K 4} : Set (adjointGroup .E7 K)), y * y = 1 →
      (∀ l ∈ (spToAdjointE7 K).range, y * l = l * y) →
        (y : ModGL .E7 K) ∈ parabolicRadical .E7 K vNodes) :
    Exc.ResCent (e7ASRep K 4) (e7FrameLine K vFrame) := by
  intro y hy hy2 hyc
  exact mem_e7FrameLine_vFrame_of_mem_parabolicRadical
    (hLevi y hy hy2 fun l hl => hyc l (range_spToAdjointE7_le_perfectCore hl)) hyc

omit [Finite K] [CharP K 2] in
theorem e7Rep_four_eq_e7FramePt : e7Rep K 4 = e7FramePt K e7FrameV := by
  rw [← e7FrameElt_one, ← e7FrameElt_perm (F := e7RepFrames 4) (by decide +kernel)
    (e7RepFrames_isRoot 4) (e7RepFrames_pairwise 4)]
  rfl

omit [Finite K] in
theorem map_conj_e7FrameLine_vFrame :
    (e7FrameLine K vFrame).map (MulAut.conj (e7RepConj K 4)).toMonoidHom =
      e7FrameLine K e7FrameV := by
  have h4 : vFrame.map (e7RepWeyl 4 • ·) = e7RepFrames 4 := e7RepWeyl_smul_e7ASFrame 4
  rw [show e7RepConj K 4 = e7WeylRep K (e7RepWeyl 4) from rfl,
    map_conj_e7FrameLine_weyl _ fun σ hσ => isRoot_of_mem_vPsi (mem_vPsi_of_mem_vFrame hσ), h4]
  exact e7FrameLine_perm (by decide +kernel) (e7RepFrames_isRoot 4) (e7RepFrames_pairwise 4)

theorem resCent_e7FrameV_of
    (hLevi : ∀ y ∈ centralizer ({e7ASRep K 4} : Set (adjointGroup .E7 K)), y * y = 1 →
      (∀ l ∈ (spToAdjointE7 K).range, y * l = l * y) →
        (y : ModGL .E7 K) ∈ parabolicRadical .E7 K vNodes) :
    Exc.ResCent (e7FramePt K e7FrameV) (e7FrameLine K e7FrameV) := by
  have : Finite (ModGL .E7 K) := finite_modGL
  have h := resCent_conj (e7RepConj K 4) (resCent_vAS_of hLevi)
  rwa [e7RepConj_mul_e7ASRep_mul_inv, e7Rep_four_eq_e7FramePt, map_conj_e7FrameLine_vFrame] at h

end Finite

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
