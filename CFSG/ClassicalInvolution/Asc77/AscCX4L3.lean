module

public import CFSG.ClassicalInvolution.Asc77.AscCX4L2
public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutFrame
public import CFSG.LieType.HighestRoot.CentChevalleySLThree
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.ClassicalInvolution.Asc77.CX.CX4.L4

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem oddCore_sl2_eq_bot_odd [Finite F] (h2 : (2 : F) ≠ 0) :
    classicalInvolutionOddCore SL(2, F) = ⊥ := by
  by_cases h4 : 4 ≤ Nat.card F
  · exact CFSG.ClassicalInvolution.ModelFacts.LinearAut.oddCore_sl2_eq_bot h2 h4
  have : Fintype F := Fintype.ofFinite F
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have hne2 : Nat.card F ≠ 2 := by
    intro h
    apply h2
    have := FiniteField.cast_card_eq_zero F
    rw [← Nat.card_eq_fintype_card, h] at this
    exact_mod_cast this
  have h3 : Nat.card F = 3 := by omega
  set N := classicalInvolutionOddCore SL(2, F) with hN
  have hodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card SL(2, F)
  by_cases hNZ : N ≤ Subgroup.center SL(2, F)
  · refine eq_bot_iff.mpr fun x hx => ?_
    rcases (mem_center_sl2_iff x).mp (hNZ hx) with rfl | rfl
    · exact Subgroup.one_mem _
    · exfalso
      have hne : (-1 : SL(2, F)) ≠ 1 := by
        intro h
        have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
        simp at this
        apply h2
        linear_combination -this
      have ho : orderOf (⟨-1, hx⟩ : N) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime (by rw [sq]; simp) hne
      have hdvd := orderOf_dvd_natCard (⟨-1, hx⟩ : N)
      rw [ho] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  · exfalso
    have h8 := CFSG.LieType.HighestRoot.eight_le_card_of_normal h3 (MulEquiv.refl _) N hNZ
    have h24 := CFSG.LieType.HighestRoot.card_eq_24 h3 (MulEquiv.refl SL(2, F))
    have hdvd : Nat.card N ∣ 24 := h24 ▸ Subgroup.card_subgroup_dvd_card N
    have hcop : Nat.Coprime (Nat.card N) 8 := by
      have h8' : (8 : ℕ) = 2 ^ 3 := by norm_num
      rw [h8']
      exact Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd)
    have h3' : Nat.card N ∣ 3 := hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
    have := Nat.le_of_dvd (by norm_num) h3'
    omega

theorem eq_one_of_mem_longRoot_of_mem_center {R : Subgroup SL(4, F)} {i : SL(4, F)}
    (hR : IsLongRootSL2 (show 2 ≤ 4 by norm_num) R i) {x : SL(4, F)} (hxR : x ∈ R)
    (hxZ : x ∈ Subgroup.center SL(4, F)) : x = 1 := by
  obtain ⟨g, rfl, -⟩ := hR
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxR
  obtain ⟨M, rfl⟩ := hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxZ ⊢
  have hcomm := Subgroup.mem_center_iff.mp hxZ g
  have hyx : g * blockSL F 4 2 0 (by norm_num) M * g⁻¹ = blockSL F 4 2 0 (by norm_num) M :=
    mul_left_cancel (a := g) (by rw [hcomm]; group)
  rw [hyx] at hxZ ⊢
  rw [← scalars_eq_center] at hxZ
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hxZ
  have e := congrFun (congrFun hc 3) 3
  rw [coe_blockSL, blockMat_four_zero] at e
  simp at e
  apply Subtype.ext
  rw [hc, Matrix.SpecialLinearGroup.coe_one, ← e]
  simp

theorem oddCoreOf_map_longRoot_eq_bot [Finite F] (h2 : (2 : F) ≠ 0) {Y : Type} [Group Y]
    (ψ : SL(4, F) →* Y) (hker : ψ.ker ≤ Subgroup.center SL(4, F)) {R : Subgroup SL(4, F)}
    {i : SL(4, F)} (hR : IsLongRootSL2 (show 2 ≤ 4 by norm_num) R i) :
    oddCoreOf (R.map ψ) = ⊥ := by
  have hinj : Function.Injective (ψ.comp R.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxk : (x : SL(4, F)) ∈ ψ.ker := hx
    exact Subgroup.mem_bot.mpr (Subtype.ext
      (eq_one_of_mem_longRoot_of_mem_center hR x.2 (hker hxk)))
  have hrange : (ψ.comp R.subtype).range = R.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨e⟩ := (hR.isClassicalSL2 h2).nonempty_mulEquiv
  let e₁ : ↥(R.map ψ) ≃* SL(2, F) :=
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans e
  have hO : classicalInvolutionOddCore ↥(R.map ψ) = ⊥ := by
    have h1 : (classicalInvolutionOddCore ↥(R.map ψ)).map e₁.toMonoidHom =
        classicalInvolutionOddCore SL(2, F) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e₁
    rw [oddCore_sl2_eq_bot_odd h2] at h1
    rwa [Subgroup.map_eq_bot_iff_of_injective _ e₁.injective] at h1
  unfold oddCoreOf
  rw [hO, Subgroup.map_bot]
noncomputable abbrev A0 : Subgroup (projectiveSL 4 F) :=
  (blockSL F 4 2 0 (by norm_num)).range.map (proj 4 F)

noncomputable abbrev A2 : Subgroup (projectiveSL 4 F) :=
  (blockSL F 4 2 2 (by norm_num)).range.map (proj 4 F)

theorem fixBlocks_of {β : MulAut (projectiveSL 4 F)} (h0 : ∀ y ∈ A0, β y = y)
    (h2' : ∀ y ∈ A2, β y = y) : FixBlocks β :=
  ⟨fun r hr => h0 _ ⟨r, hr, rfl⟩, fun r hr => h2' _ ⟨r, hr, rfl⟩⟩

theorem fix_pgroup_std [Finite F] (h2 : (2 : F) ≠ 0) (hsq : ¬ IsSquare (-1 : F))
    (P : Subgroup (MulAut (projectiveSL 4 F))) (hP : IsPGroup 2 P)
    (hfix : ∀ β ∈ P, (∀ y ∈ A0, β y = y) ∧ ∀ y ∈ A2, β y = y) :
    (∀ β ∈ P, β * β = 1) ∧ Nat.card P ≤ 4 :=
  fix_pgroup h2 hsq P hP fun β hβ => fixBlocks_of (hfix β hβ).1 (hfix β hβ).2

theorem fix_invol_std [Finite F] (h2 : (2 : F) ≠ 0) (hsq : ¬ IsSquare (-1 : F))
    (β : MulAut (projectiveSL 4 F)) (h0 : ∀ y ∈ A0, β y = y) (h2' : ∀ y ∈ A2, β y = y)
    (hβ2 : β * β = 1) (hβ1 : β ≠ 1) (hβz : β ≠ MulAut.conj zbar) :
    ∃ x : projectiveSL 4 F, β x = x ∧ x * zbar * x⁻¹ ≠ zbar ∧
      x * zbar * x⁻¹ * zbar = zbar * (x * zbar * x⁻¹) := by
  have hk : β ^ (2 ^ 1) = 1 := by rw [pow_one, sq]; exact hβ2
  rcases two_elem_cases h2 hsq (fixBlocks_of h0 h2') hk with (h | h) |
      ⟨A, m, n, hm, hn, hA, rfl⟩
  · exact absurd h hβ1
  · exact absurd h hβz
  · exact graph_witness h2 A hm hn hA

end CFSG.ClassicalInvolution.Asc77.CX.CX4.L4
