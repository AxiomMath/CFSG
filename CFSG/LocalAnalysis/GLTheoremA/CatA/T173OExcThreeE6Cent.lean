module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoSL6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE6Orbit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoBalance
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Two9

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open scoped MatrixGroups
open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

private def e6TorusMasks : List (List ℕ) :=
  [wordMask (zword ![1, 0, 0]), wordMask (zword ![0, 1, 0]), wordMask (zword ![0, 0, 1])]

private def e6TorusCubeCheck : Bool :=
  (pl e6TorusMasks 3 5).all fun x35 => (pl e6TorusMasks 0 2).all fun x02 =>
    (pl e6TorusMasks 4 1).all fun x41 =>
      mmul (p3 (asm3 x35 x02 x41)) (p3 (asm3 x35 x02 x41)) == p3 (asm3 x35 x02 x41)

set_option maxRecDepth 100000 in
private theorem e6TorusCubeCheck_eq_true : e6TorusCubeCheck = true := by
  decide +kernel

private theorem p3_idem_of_e6TorusCubeCheck {M : List ℕ} (hM : M.length = 6)
    (hM' : ∀ a ∈ M, a < 64) (hc : ∀ Zm ∈ e6TorusMasks, mmul M Zm = mmul Zm M) :
    mmul (p3 M) (p3 M) = p3 M := by
  have hb : ∀ Zm ∈ e6TorusMasks, bdiag Zm = true := by decide
  have hZ' : ∀ Zm ∈ e6TorusMasks, blockOK Zm 3 5 = true ∧ blockOK Zm 0 2 = true ∧
      blockOK Zm 4 1 = true := by
    intro Zm hZm
    have h := hb Zm hZm
    simp only [bdiag, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have h35 := mem_pl (a := 3) (b := 5) (by decide) (fun Zm h => (hZ' Zm h).1) hM hM' hc
  have h02 := mem_pl (a := 0) (b := 2) (by decide) (fun Zm h => (hZ' Zm h).2.1) hM hM' hc
  have h41 := mem_pl (a := 4) (b := 1) (by decide) (fun Zm h => (hZ' Zm h).2.2) hM hM' hc
  have hchk := e6TorusCubeCheck_eq_true
  simp only [e6TorusCubeCheck, List.all_eq_true] at hchk
  have := hchk _ h35 _ h02 _ h41
  rwa [asm3_getD hM, beq_iff_eq] at this

section SL6

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

private theorem pow_three_eq_one_of_commute_zSL (hK : Nat.card K = 2) {M : SL(6, K)}
    (h₀ : M * zSL ![1, 0, 0] = zSL ![1, 0, 0] * M) (h₁ : M * zSL ![0, 1, 0] = zSL ![0, 1, 0] * M)
    (h₂ : M * zSL ![0, 0, 1] = zSL ![0, 0, 1] * M) : M ^ 3 = 1 := by
  set A := maskOf (M : Matrix (Fin 6) (Fin 6) K) with hA
  have hAl : A.length = 6 := length_maskOf _
  have hAb : ∀ a ∈ A, a < 64 := maskOf_lt _
  have hc : ∀ Zm ∈ e6TorusMasks, mmul A Zm = mmul Zm A := by
    intro Zm hZm
    simp only [e6TorusMasks, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hZm
    rcases hZm with rfl | rfl | rfl
    · exact mmul_comm_of_commute hK (coe_tvSLWord_eq_real _) (length_wordMask _)
        (wordMask_lt _) h₀
    · exact mmul_comm_of_commute hK (coe_tvSLWord_eq_real _) (length_wordMask _)
        (wordMask_lt _) h₁
    · exact mmul_comm_of_commute hK (coe_tvSLWord_eq_real _) (length_wordMask _)
        (wordMask_lt _) h₂
  have hidem := p3_idem_of_e6TorusCubeCheck hAl hAb hc
  have hmat : (M : Matrix (Fin 6) (Fin 6) K) ^ 3 * (M : Matrix (Fin 6) (Fin 6) K) ^ 3 =
      (M : Matrix (Fin 6) (Fin 6) K) ^ 3 := by
    have e := congrArg (real K) hidem
    rwa [real_mmul _ _ (length_p3 hAl), real_p3 hAl, hA, real_maskOf_SL hK M] at e
  have hsl : M ^ 3 * M ^ 3 = M ^ 3 := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow]
    exact hmat
  exact mul_eq_left.1 hsl

end SL6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.StandardType
open CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6ThreeEnd

section Centralizer

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem centralizer_range_torusE6Two_le (h2 : (2 : K) = 0) (hK : Nat.card K = 2) :
    Subgroup.centralizer ((torusE6Two (K := K) h2).range : Set (adjointGroup .E6 K)) ≤
      (torusE6Two (K := K) h2).range := by
  intro c hc
  have hc3 : c ^ 3 = 1 := by
    classical
    haveI : Fintype K := Fintype.ofFinite K
    have hu0mem : uE6Two (K := K) 0 ∈ (torusE6Two (K := K) h2).range :=
      MonoidHom.mem_range.mpr ⟨_, torusE6Two_single_zero h2⟩
    have hu0 : c ∈ Subgroup.centralizer ({uE6Two (K := K) 0} : Set (adjointGroup .E6 K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hc) _ hu0mem).symm
    obtain ⟨y, hy, l, hl, hcyl⟩ := exists_mul_of_mem_centralizer_uE6Two_zero hK hu0
    rw [← range_phi0] at hl
    obtain ⟨M, rfl⟩ := hl
    have hBcomm : IsMulCommutative (torusE6Two (K := K) h2).range :=
      (isElemAbelian_range_torusE6Two h2).1
    have hyB : y ∈ (torusE6Two (K := K) h2).range :=
      Subgroup.zpowers_le.mpr hu0mem hy
    have hyC : y ∈ Subgroup.centralizer ((torusE6Two (K := K) h2).range :
        Set (adjointGroup .E6 K)) :=
      (Subgroup.le_centralizer_iff_isMulCommutative
        (K := (torusE6Two (K := K) h2).range)).mpr hBcomm hyB
    have hphi_eq : phi0 K M = y⁻¹ * c := by
      rw [hcyl]
      group
    have hphiC : phi0 K M ∈ Subgroup.centralizer ((torusE6Two (K := K) h2).range :
        Set (adjointGroup .E6 K)) := by
      rw [hphi_eq]
      exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem hyC) hc
    have hy3 : y ^ 3 = 1 := (isElemAbelian_range_torusE6Two h2).2 y hyB
    have hycomm : Commute y (phi0 K M) :=
      (Subgroup.mem_centralizer_iff.mp hphiC) y hyB
    have hcomm : ∀ v : Fin 3 → ℕ, (∀ k, v k < 3) → M * zSL v = zSL v * M := by
      intro v hv
      have hzB : phi0 K (zSL v) ∈ (torusE6Two (K := K) h2).range := by
        rw [phi0_zSL h2 hv]
        exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
      have hcv : phi0 K M * phi0 K (zSL v) = phi0 K (zSL v) * phi0 K M :=
        ((Subgroup.mem_centralizer_iff.mp hphiC) _ hzB).symm
      refine phi0_injective hK ?_
      rw [map_mul, map_mul, hcv]
    have hM3 : M ^ 3 = 1 :=
      pow_three_eq_one_of_commute_zSL hK (hcomm ![1, 0, 0] (by decide))
        (hcomm ![0, 1, 0] (by decide)) (hcomm ![0, 0, 1] (by decide))
    have hphi3 : (phi0 K M) ^ 3 = 1 := by
      rw [← map_pow, hM3, map_one]
    rw [hcyl, hycomm.mul_pow 3, hy3, hphi3, mul_one]
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two.sc_of_card_eq_E6_three
    (by norm_num [hK]) (isElemAbelian_range_torusE6Two h2)
    (card_range_torusE6Two h2) c hc hc3

end Centralizer

end CFSG.LocalAnalysis.GLTheoremA.T173O
