module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFRel

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {fr : SFrame Γ}

private lemma sq_mul_eq_one {x y z : Γ} (hxy : Commute x y) (hx : x ^ 2 = z) (hy : y ^ 2 = z)
    (hz : z ^ 2 = 1) : (x * y) ^ 2 = 1 := by
  rw [hxy.mul_pow 2, hx, hy]
  simpa [pow_two] using hz

private lemma sq_mul_of_commutator_eq {x y z : Γ} (h : ⁅x, y⁆ = z) (hx : x ^ 2 = z)
    (hy : y ^ 2 = z) (hz : z ^ 2 = 1) : (x * y) ^ 2 = z := by
  have hxy : x * y = z * y * x := by
    have h' := h
    rw [commutatorElement_def] at h'
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = z * (y * x) := by rw [h']
      _ = z * y * x := by group
  have hx2 : x * x = z := by simpa [pow_two] using hx
  have hy2 : y * y = z := by simpa [pow_two] using hy
  have hz2 : z * z = 1 := by simpa [pow_two] using hz
  have hzy : z * y = y * z := by
    rw [← hy]
    exact ((Commute.refl y).pow_left 2).eq
  calc (x * y) ^ 2
      = (z * y * x) * (x * y) := by rw [pow_two]; nth_rewrite 1 [hxy]; rfl
    _ = (z * y * (x * x)) * y := by group
    _ = (z * y * z) * y := by rw [hx2]
    _ = (z * (y * z)) * y := by group
    _ = (z * (z * y)) * y := by rw [← hzy]
    _ = (z * z) * (y * y) := by group
    _ = z := by rw [hz2, hy2]; group

private lemma commute_of_mul_eq_one_left {x y b : Γ} (hx : Commute x b) (h : x * y = 1) :
    Commute y b := by
  rw [← inv_eq_of_mul_eq_one_right h]
  exact hx.inv_left

private lemma commute_of_mul_eq_one_right {x y b : Γ} (hb : Commute b y) (h : x * y = 1) :
    Commute b x := by
  rw [← inv_eq_of_mul_eq_one_left h]
  exact hb.inv_right

theorem srel_closure_invols_A (h : SRel fr) (hz : fr.z ≠ 1) :
    closure (invols fr.A) = fr.A := by
  have ca1a2 : Commute fr.a₁ fr.a₂ := commutatorElement_eq_one_iff_commute.mp h.a1a2
  have ca1b2 : Commute fr.a₁ fr.b₂ := commutatorElement_eq_one_iff_commute.mp h.a1b2
  have cb1a2 : Commute fr.b₁ fr.a₂ := commutatorElement_eq_one_iff_commute.mp h.b1a2
  have cb1b2 : Commute fr.b₁ fr.b₂ := commutatorElement_eq_one_iff_commute.mp h.b1b2
  have n12 : fr.a₁ * fr.b₁ ≠ fr.b₁ * fr.a₁ := by
    intro hc
    have h1 : ⁅fr.a₁, fr.b₁⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hc
    rw [h.comm1] at h1
    exact hz h1
  have n22 : fr.a₂ * fr.b₂ ≠ fr.b₂ * fr.a₂ := by
    intro hc
    have h2 : ⁅fr.a₂, fr.b₂⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hc
    rw [h.comm2] at h2
    exact hz h2
  have hi1_sq : (fr.a₁ * fr.a₂) ^ 2 = 1 := sq_mul_eq_one ca1a2 h.a1_sq h.a2_sq h.z_sq
  have hi2_sq : (fr.a₁ * fr.b₂) ^ 2 = 1 := sq_mul_eq_one ca1b2 h.a1_sq h.b2_sq h.z_sq
  have hi4_sq : (fr.b₁ * fr.b₂) ^ 2 = 1 := sq_mul_eq_one cb1b2 rfl h.b2_sq h.z_sq
  have hab_sq : (fr.a₁ * fr.b₁) ^ 2 = fr.z :=
    sq_mul_of_commutator_eq h.comm1 h.a1_sq rfl h.z_sq
  have hi5_sq : (fr.a₁ * fr.b₁ * fr.a₂) ^ 2 = 1 :=
    sq_mul_eq_one (ca1a2.mul_left cb1a2) hab_sq h.a2_sq h.z_sq
  have hi1_ne : fr.a₁ * fr.a₂ ≠ 1 := fun he =>
    n22 (commute_of_mul_eq_one_left ca1b2 he).eq
  have hi2_ne : fr.a₁ * fr.b₂ ≠ 1 := fun he =>
    n12 (commute_of_mul_eq_one_right cb1b2 he).eq.symm
  have hi4_ne : fr.b₁ * fr.b₂ ≠ 1 := fun he =>
    n22 (commute_of_mul_eq_one_left cb1a2 he).symm.eq
  have hi5_ne : fr.a₁ * fr.b₁ * fr.a₂ ≠ 1 := fun he =>
    n22 (commute_of_mul_eq_one_left (ca1b2.mul_left cb1b2) he).eq
  have hmembers : ({fr.a₁, fr.b₁, fr.a₂, fr.b₂} : Set Γ) ⊆ fr.A := by
    intro x hx
    change x ∈ closure ({fr.a₁, fr.b₁, fr.a₂, fr.b₂} : Set Γ)
    exact Subgroup.subset_closure hx
  have ha1A : fr.a₁ ∈ fr.A := hmembers (by simp)
  have hb1A : fr.b₁ ∈ fr.A := hmembers (by simp)
  have ha2A : fr.a₂ ∈ fr.A := hmembers (by simp)
  have hb2A : fr.b₂ ∈ fr.A := hmembers (by simp)
  have hzA : fr.z ∈ fr.A := by
    change fr.b₁ ^ 2 ∈ fr.A
    rw [pow_two]
    exact mul_mem hb1A hb1A
  have hi1 : fr.a₁ * fr.a₂ ∈ invols fr.A :=
    ⟨mul_mem ha1A ha2A, orderOf_eq_prime hi1_sq hi1_ne⟩
  have hi2 : fr.a₁ * fr.b₂ ∈ invols fr.A :=
    ⟨mul_mem ha1A hb2A, orderOf_eq_prime hi2_sq hi2_ne⟩
  have hi4 : fr.b₁ * fr.b₂ ∈ invols fr.A :=
    ⟨mul_mem hb1A hb2A, orderOf_eq_prime hi4_sq hi4_ne⟩
  have hi5 : fr.a₁ * fr.b₁ * fr.a₂ ∈ invols fr.A :=
    ⟨mul_mem (mul_mem ha1A hb1A) ha2A, orderOf_eq_prime hi5_sq hi5_ne⟩
  have hzI : fr.z ∈ invols fr.A := ⟨hzA, orderOf_eq_prime h.z_sq hz⟩
  have hi1C : fr.a₁ * fr.a₂ ∈ closure (invols fr.A) := Subgroup.subset_closure hi1
  have hi2C : fr.a₁ * fr.b₂ ∈ closure (invols fr.A) := Subgroup.subset_closure hi2
  have hi4C : fr.b₁ * fr.b₂ ∈ closure (invols fr.A) := Subgroup.subset_closure hi4
  have hi5C : fr.a₁ * fr.b₁ * fr.a₂ ∈ closure (invols fr.A) := Subgroup.subset_closure hi5
  have hzC : fr.z ∈ closure (invols fr.A) := Subgroup.subset_closure hzI
  have hcomm1'' : fr.a₁ * fr.b₁ * fr.a₁⁻¹ = fr.z * fr.b₁ := by
    have h' : fr.a₁ * fr.b₁ = fr.z * fr.b₁ * fr.a₁ := by
      have hh := h.comm1
      rw [commutatorElement_def] at hh
      calc fr.a₁ * fr.b₁ = fr.a₁ * fr.b₁ * fr.a₁⁻¹ * fr.b₁⁻¹ * (fr.b₁ * fr.a₁) := by
            group
        _ = fr.z * (fr.b₁ * fr.a₁) := by rw [hh]
        _ = fr.z * fr.b₁ * fr.a₁ := by group
    rw [h']
    group
  have hzb1C : fr.z * fr.b₁ ∈ closure (invols fr.A) := by
    have heq : fr.z * fr.b₁ = (fr.a₁ * fr.b₁ * fr.a₂) * (fr.a₁ * fr.a₂)⁻¹ := by
      rw [← hcomm1'']
      group
    rw [heq]
    exact mul_mem hi5C (inv_mem hi1C)
  have hb1C : fr.b₁ ∈ closure (invols fr.A) := by
    have heq : fr.b₁ = fr.z⁻¹ * (fr.z * fr.b₁) := by group
    rw [heq]
    exact mul_mem (inv_mem hzC) hzb1C
  have hb2C : fr.b₂ ∈ closure (invols fr.A) := by
    have heq : fr.b₂ = fr.b₁⁻¹ * (fr.b₁ * fr.b₂) := by group
    rw [heq]
    exact mul_mem (inv_mem hb1C) hi4C
  have ha1C : fr.a₁ ∈ closure (invols fr.A) := by
    have heq : fr.a₁ = (fr.a₁ * fr.b₂) * fr.b₂⁻¹ := by group
    rw [heq]
    exact mul_mem hi2C (inv_mem hb2C)
  have ha2C : fr.a₂ ∈ closure (invols fr.A) := by
    have heq : fr.a₂ = fr.a₁⁻¹ * (fr.a₁ * fr.a₂) := by group
    rw [heq]
    exact mul_mem (inv_mem ha1C) hi1C
  refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) ?_
  change closure ({fr.a₁, fr.b₁, fr.a₂, fr.b₂} : Set Γ) ≤ closure (invols fr.A)
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  exacts [ha1C, hb1C, ha2C, hb2C]

theorem srel_closure_invols_S (h : SRel fr) (hz : fr.z ≠ 1) :
    closure (invols fr.S) = fr.S := by
  have hAS : fr.A ≤ fr.S := by
    change closure ({fr.a₁, fr.b₁, fr.a₂, fr.b₂} : Set Γ) ≤
      closure ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀} : Set Γ)
    exact Subgroup.closure_mono (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto)
  have hAc : fr.A ≤ closure (invols fr.S) := by
    rw [← srel_closure_invols_A h hz]
    exact Subgroup.closure_mono (by
      intro x hx
      exact ⟨hAS hx.1, hx.2⟩)
  have hh0_ne : fr.h₀ ≠ 1 := by
    intro h0
    have h1 : ⁅fr.b₁, fr.h₀⁆ = 1 := by rw [h0]; simp
    rw [h.b1h] at h1
    exact hz h1
  have hh0C : fr.h₀ ∈ closure (invols fr.S) :=
    Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp),
      orderOf_eq_prime h.h0_sq hh0_ne⟩
  refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) ?_
  change closure ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀} : Set Γ) ≤ closure (invols fr.S)
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hAc (Subgroup.subset_closure (by simp))
  · exact hAc (Subgroup.subset_closure (by simp))
  · exact hAc (Subgroup.subset_closure (by simp))
  · exact hAc (Subgroup.subset_closure (by simp))
  · exact hh0C

theorem srel_S_le_normalizer_U (h : SRel fr) :
    fr.S ≤ normalizer ((closure {fr.a₁, fr.b₁} : Subgroup Γ) : Set Γ) := by
  have ca1a2 : Commute fr.a₁ fr.a₂ := commutatorElement_eq_one_iff_commute.mp h.a1a2
  have ca1b2 : Commute fr.a₁ fr.b₂ := commutatorElement_eq_one_iff_commute.mp h.a1b2
  have cb1a2 : Commute fr.b₁ fr.a₂ := commutatorElement_eq_one_iff_commute.mp h.b1a2
  have cb1b2 : Commute fr.b₁ fr.b₂ := commutatorElement_eq_one_iff_commute.mp h.b1b2
  have ha1U : fr.a₁ ∈ (closure {fr.a₁, fr.b₁} : Subgroup Γ) := Subgroup.subset_closure (by simp)
  have hb1U : fr.b₁ ∈ (closure {fr.a₁, fr.b₁} : Subgroup Γ) := Subgroup.subset_closure (by simp)
  have hzU : fr.z ∈ (closure {fr.a₁, fr.b₁} : Subgroup Γ) := by
    change fr.b₁ ^ 2 ∈ (closure {fr.a₁, fr.b₁} : Subgroup Γ)
    rw [pow_two]
    exact mul_mem hb1U hb1U
  have ha2N : fr.a₂ ∈ normalizer ((closure {fr.a₁, fr.b₁} : Subgroup Γ) : Set Γ) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hc : Commute u fr.a₂ := by
      induction hu using Subgroup.closure_induction with
      | mem x hx =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact ca1a2
          · exact cb1a2
      | one => exact Commute.one_left _
      | mul x y hx hy ihx ihy => exact ihx.mul_left ihy
      | inv x hx ih => exact ih.inv_left
    exact hc.eq
  have hb2N : fr.b₂ ∈ normalizer ((closure {fr.a₁, fr.b₁} : Subgroup Γ) : Set Γ) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hc : Commute u fr.b₂ := by
      induction hu using Subgroup.closure_induction with
      | mem x hx =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact ca1b2
          · exact cb1b2
      | one => exact Commute.one_left _
      | mul x y hx hy ihx ihy => exact ihx.mul_left ihy
      | inv x hx ih => exact ih.inv_left
    exact hc.eq
  have hh0 : fr.h₀ * fr.h₀ = 1 := by simpa [pow_two] using h.h0_sq
  have hh0inv : fr.h₀⁻¹ = fr.h₀ := inv_eq_of_mul_eq_one_right hh0
  have hh0a1 : fr.h₀ * fr.a₁ * fr.h₀⁻¹ ∈ (closure {fr.a₁, fr.b₁} : Subgroup Γ) := by
    have hkey : fr.h₀ * fr.a₁⁻¹ * fr.h₀⁻¹ = fr.a₁⁻¹ * fr.b₁ * fr.z := by
      have hh := h.a1h
      rw [commutatorElement_def] at hh
      calc fr.h₀ * fr.a₁⁻¹ * fr.h₀⁻¹
          = fr.a₁⁻¹ * (fr.a₁ * fr.h₀ * fr.a₁⁻¹ * fr.h₀⁻¹) := by group
        _ = fr.a₁⁻¹ * (fr.b₁ * fr.z) := by rw [hh]
        _ = fr.a₁⁻¹ * fr.b₁ * fr.z := by group
    have hmem : fr.a₁⁻¹ * fr.b₁ * fr.z ∈ (closure {fr.a₁, fr.b₁} : Subgroup Γ) :=
      mul_mem (mul_mem (inv_mem ha1U) hb1U) hzU
    rw [show fr.h₀ * fr.a₁ * fr.h₀⁻¹ = (fr.h₀ * fr.a₁⁻¹ * fr.h₀⁻¹)⁻¹ by group, hkey]
    exact inv_mem hmem
  have hh0b1 : fr.h₀ * fr.b₁ * fr.h₀⁻¹ ∈ (closure {fr.a₁, fr.b₁} : Subgroup Γ) := by
    have hkey : fr.h₀ * fr.b₁⁻¹ * fr.h₀⁻¹ = fr.b₁⁻¹ * fr.z := by
      have hh := h.b1h
      rw [commutatorElement_def] at hh
      calc fr.h₀ * fr.b₁⁻¹ * fr.h₀⁻¹
          = fr.b₁⁻¹ * (fr.b₁ * fr.h₀ * fr.b₁⁻¹ * fr.h₀⁻¹) := by group
        _ = fr.b₁⁻¹ * fr.z := by rw [hh]
    have hmem : fr.b₁⁻¹ * fr.z ∈ (closure {fr.a₁, fr.b₁} : Subgroup Γ) :=
      mul_mem (inv_mem hb1U) hzU
    rw [show fr.h₀ * fr.b₁ * fr.h₀⁻¹ = (fr.h₀ * fr.b₁⁻¹ * fr.h₀⁻¹)⁻¹ by group, hkey]
    exact inv_mem hmem
  have hmap0 : ∀ y ∈ (closure {fr.a₁, fr.b₁} : Subgroup Γ),
      fr.h₀ * y * fr.h₀⁻¹ ∈ (closure {fr.a₁, fr.b₁} : Subgroup Γ) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz' =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
        rcases hz' with rfl | rfl
        · exact hh0a1
        · exact hh0b1
    | one => simpa using Subgroup.one_mem (closure {fr.a₁, fr.b₁} : Subgroup Γ)
    | mul y z hy hz' ihy ihz =>
        rw [show fr.h₀ * (y * z) * fr.h₀⁻¹
              = (fr.h₀ * y * fr.h₀⁻¹) * (fr.h₀ * z * fr.h₀⁻¹) by group]
        exact mul_mem ihy ihz
    | inv y hy ihy =>
        rw [show fr.h₀ * y⁻¹ * fr.h₀⁻¹ = (fr.h₀ * y * fr.h₀⁻¹)⁻¹ by group]
        exact inv_mem ihy
  have hh0N : fr.h₀ ∈ normalizer ((closure {fr.a₁, fr.b₁} : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hmap0 x hx
    · intro hx
      have hinv : fr.h₀⁻¹ * fr.h₀⁻¹ = 1 := by rw [hh0inv]; exact hh0
      have hconj : fr.h₀ * (fr.h₀ * x * fr.h₀⁻¹) * fr.h₀⁻¹ = x := by
        calc fr.h₀ * (fr.h₀ * x * fr.h₀⁻¹) * fr.h₀⁻¹
            = fr.h₀ * fr.h₀ * x * (fr.h₀⁻¹ * fr.h₀⁻¹) := by group
          _ = x := by rw [hh0, hinv]; group
      rw [← hconj]
      exact hmap0 _ hx
  have ha1N : fr.a₁ ∈ normalizer ((closure {fr.a₁, fr.b₁} : Subgroup Γ) : Set Γ) :=
    Subgroup.le_normalizer (H := (closure {fr.a₁, fr.b₁} : Subgroup Γ)) ha1U
  have hb1N : fr.b₁ ∈ normalizer ((closure {fr.a₁, fr.b₁} : Subgroup Γ) : Set Γ) :=
    Subgroup.le_normalizer (H := (closure {fr.a₁, fr.b₁} : Subgroup Γ)) hb1U
  change closure ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀} : Set Γ) ≤
    normalizer ((closure {fr.a₁, fr.b₁} : Subgroup Γ) : Set Γ)
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [ha1N, hb1N, ha2N, hb2N, hh0N]

end CFSG.OddStandard.HigherRank.YamadaG23
