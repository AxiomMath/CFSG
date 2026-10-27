module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf18Fuse
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf13Lift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW189b

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Uniform.U4
open scoped commutatorElement MatrixGroups

section NoExitF


theorem pow_four_of_q8 {Y : Type} [Group Y] {K : Subgroup Y}
    (hK : Nonempty (↥K ≃* QuaternionGroup 2)) : ∀ x ∈ K, x ^ 4 = 1 := by
  intro x hx
  obtain ⟨e⟩ := hK
  have hq : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
  have h1 : (⟨x, hx⟩ : ↥K) ^ 4 = 1 := by
    have h2 := congrArg e.symm (hq (e ⟨x, hx⟩))
    rwa [map_pow, MulEquiv.symm_apply_apply, map_one] at h2
  simpa using congrArg (fun z : ↥K => (z : Y)) h1

theorem e189ConclF_noExit {n : ℕ} (hE : Q3T8.Asc77.E189Sect) (hcit : CIT3Below n)
    (hih : Uniform.IH8T 3 1 n) (hP : TL4.TightBelowRPlus 3 n) {Y : Type} [Group Y] [Finite Y]
    {Λ : Set (Subgroup Y)} (hlt : Nat.card Y < n) (hS : TwinDisc.Q8Section Y Λ)
    (hno : TwinDisc.NoExit Y Λ) {K J : Subgroup Y} (hK : K ∈ Λ) (hJ : J ∈ Λ) {z t : Y}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hzt : z * t = t * z)
    (hne : conjSub t K ≠ K) : TwinThmEW.E189ConclF Λ K z t := by
  have hconcl := e189_bar_noExit hE hcit hih hP hlt hS hno hK hJ hz ht hzt hne
  rcases hconcl with ⟨K'', hK''tw, hne'', R₁, R₂, hR₁, hR₂, hc, u, x, hu, hu1, hu2, hux⟩ | h2
  swap
  · exact Or.inr h2
  left
  obtain ⟨h2g, hl, hex⟩ := TwinDisc.lifts_of_noExit hP hlt hS hno
  have hΩ : HypOmegaGen Λ := hS.hyp
  have hK'' : K'' ∈ Λ := hK''tw.1
  have hR₁K : K = R₁ := hR₁.2.2 K le_rfl (h2g K hK) hR₁.1
  have hR₂K : K'' = R₂ := hR₂.2.2 K'' le_rfl (h2g K'' hK'') hR₂.1
  have hz'' : IsUniqueInvolution K'' z := by
    obtain ⟨-, w, hwK, hwK''⟩ := hK''tw
    exact (hz.eq hwK) ▸ hwK''
  obtain ⟨L, u₁, hL⟩ := hl K hK
  obtain ⟨L'', u₂, hL''⟩ := hl K'' hK''
  have hu₁ : z = u₁ := hz.eq hL.inv
  have hu₂ : z = u₂ := hz''.eq hL''.inv
  have hM : satU (.sl2 3 1) L u₁ ∈ liftFam Λ := satU_mem_liftFam hK hL
  have hM'' : satU (.sl2 3 1) L'' u₂ ∈ liftFam Λ := satU_mem_liftFam hK'' hL''
  have hKM : K ≤ satU (.sl2 3 1) L u₁ := hL.le_sat
  have hKM'' : K'' ≤ satU (.sl2 3 1) L'' u₂ := hL''.le_sat
  have hzM : IsUniqueInvolution (satU (.sl2 3 1) L u₁) z := isUniqueInvolution_liftFam_of_le hM hz hKM
  have hzM'' : IsUniqueInvolution (satU (.sl2 3 1) L'' u₂) z :=
    isUniqueInvolution_liftFam_of_le hM'' hz'' hKM''
  have hOdd : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set Y)) = ⊥ := (hno K hK z hz).1
  have hOM : ∀ (L₀ : Subgroup Y) (u₀ : Y), IsLiftOf K L₀ u₀ →
      classicalInvolutionOddCore ↥(satU (.sl2 3 1) L₀ u₀) = ⊥ := by
    intro L₀ u₀ h₀
    have hu₀ : z = u₀ := hz.eq h₀.inv
    have hint := h₀.mem3.intrinsic solvableType_three
    have h1 := oddCoreIn_eq_of_intrinsic h₀.mem3.member hint
    have hOdd' : Balance.oddCoreIn (Subgroup.centralizer ({u₀} : Set Y)) = ⊥ := by
      rw [← hu₀]; exact hOdd
    rw [hOdd'] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1
  have hOM1 := hOM L u₁ hL
  have hOM2 : classicalInvolutionOddCore ↥(satU (.sl2 3 1) L'' u₂) = ⊥ := by
    have h₀ : IsLiftOf K'' L'' u₂ := hL''
    have hint := h₀.mem3.intrinsic solvableType_three
    have h1 := oddCoreIn_eq_of_intrinsic h₀.mem3.member hint
    have hOdd2 : Balance.oddCoreIn (Subgroup.centralizer ({u₂} : Set Y)) = ⊥ := by
      rw [← hu₂]; exact hOdd
    rw [hOdd2] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1
  obtain ⟨eM⟩ := hL.member_sat.nonempty_equiv_sl2 hOM1
  obtain ⟨eM''⟩ := hL''.member_sat.nonempty_equiv_sl2 hOM2
  have hMM : satU (.sl2 3 1) L'' u₂ ≠ satU (.sl2 3 1) L u₁ := by
    intro h
    apply hne''
    exact ExactSylow.core_unique hΩ h2g hex hM hK'' hK (h ▸ hKM'') hKM
  have hco := Q3T7M.HM.comm_le_oddCore_of_twin (hypOmegaModU_liftFam hΩ.conjInvariant) hM hM''
    hMM.symm hzM hzM''
  have hcomm : ∀ m ∈ satU (.sl2 3 1) L u₁, ∀ k ∈ satU (.sl2 3 1) L'' u₂, m * k = k * m := by
    intro m hm k hk
    have h0 := hco (Subgroup.commutator_mem_commutator hm hk)
    obtain ⟨hmem, hbot⟩ := mem_oddCoreOf_iff.mp h0.1
    rw [hOM1, Subgroup.mem_bot] at hbot
    have hb : ⁅m, k⁆ = 1 := congrArg Subtype.val hbot
    rw [commutatorElement_def] at hb
    calc m * k = (m * k * m⁻¹ * k⁻¹) * (k * m) := by group
      _ = k * m := by rw [hb, one_mul]
  have hq8 := fun (J₀ : Subgroup Y) (hJ₀ : J₀ ∈ Λ) =>
    hS.q8 J₀ hJ₀ J₀ ⟨le_rfl, h2g J₀ hJ₀, fun V hV _ hKV => le_antisymm hV hKV⟩
  have hfuse := fusion_core hz hz'' (pow_four_of_q8 (hq8 K hK)) (pow_four_of_q8 (hq8 K'' hK''))
    hKM hKM'' eM eM'' hcomm (by rw [hR₁K, hR₂K]; exact hu) hu1 hu2
  refine ⟨K'', hK''tw, hne'', R₁, R₂, hR₁, hR₂, hc, u, x, hu, hu1, hu2, hux, ?_⟩
  rw [← hR₁K, ← hR₂K]
  exact hfuse

end NoExitF

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
