module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.ClassPkg

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
open scoped Pointwise

set_option linter.unusedSectionVars false


private theorem ov_conj_zW (x : WP) : x * zW * x⁻¹ = zW := by
  rw [zW_comm x, mul_inv_cancel_right]

private noncomputable def ovS1 : Subgroup WP where
  carrier := {x | x * t0 * x⁻¹ = t0 ∨ x * t0 * x⁻¹ = t0 * zW}
  one_mem' := Or.inl (by simp)
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have e : x * y * t0 * (x * y)⁻¹ = x * (y * t0 * y⁻¹) * x⁻¹ := by group
    rw [e]
    rcases hy with hy | hy
    · rw [hy]
      exact hx
    · rw [hy]
      have e2 : x * (t0 * zW) * x⁻¹ = (x * t0 * x⁻¹) * (x * zW * x⁻¹) := by group
      rw [e2, ov_conj_zW]
      rcases hx with hx | hx
      · rw [hx]
        exact Or.inr rfl
      · rw [hx, mul_assoc, zW_mul_self, mul_one]
        exact Or.inl rfl
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [inv_inv]
    rcases hx with hx | hx
    · left
      calc x⁻¹ * t0 * x = x⁻¹ * (x * t0 * x⁻¹) * x := by rw [hx]
        _ = t0 := by group
    · right
      have h1 : x⁻¹ * (x * t0 * x⁻¹) * x = t0 := by group
      rw [hx] at h1
      have e2 : x⁻¹ * (t0 * zW) * x = (x⁻¹ * t0 * x) * (x⁻¹ * zW * x) := by group
      have e3 := ov_conj_zW x⁻¹
      rw [inv_inv] at e3
      rw [e2, e3] at h1
      calc x⁻¹ * t0 * x = x⁻¹ * t0 * x * zW * zW := by
            rw [mul_assoc (x⁻¹ * t0 * x) zW zW, zW_mul_self, mul_one]
        _ = t0 * zW := by rw [h1]

private theorem ov_conj_of_mem_T0 {y : WP} (hy : y ∈ T0) : y * t0 * y⁻¹ = t0 := by
  rw [Subgroup.mem_centralizer_singleton_iff.1 hy, mul_inv_cancel_right]

private theorem ov_wSub_sub : ∀ w ∈ wSub, w ∈ allWords := by
  intro w hw
  simp only [allWords, List.mem_append]
  tauto

private theorem ov_wordOK {w : List ℕ} (hw : w ∈ wSub) : wordOK w = true :=
  wordOK_of_allWords (ov_wSub_sub w hw)

private theorem ov_m15 : 15 < 256 ∧ framePop 15 % 2 = 0 := ⟨by norm_num, by decide⟩

private theorem ov_coe (g : WP) :
    ((g • negSet t0 : Finset (Fin 240)) : Set (Fin 240)) =
      (g : Equiv.Perm (Fin 240)) '' Om1Facts.neg 15 := by
  rw [coe_smul_negSet, coe_negSet ov_m15]

private theorem ov_cover (x : WP) :
    x ∈ ovS1 ∨ ∃ g ∈ wpE '' {w | w ∈ wSub}, ∃ h ∈ MulAction.stabilizer WP (negSet t0),
      x • negSet t0 = (h * g) • negSet t0 := by
  obtain ⟨hCT, hTstab, -, -, -, -, -, horb, -⟩ := classPkg0
  have hx : x • negSet t0 ∈ MulAction.orbit (closureW wX) (negSet t0) := by
    rw [horb]
    exact MulAction.mem_orbit _ x
  obtain ⟨⟨y, hy⟩, hyx⟩ := hx
  have hyx' : y • negSet t0 = x • negSet t0 := hyx
  rcases Certificates.certificate197001.2.2.2.1 (y : Equiv.Perm (Fin 240))
      ((mem_closureW_iff (wordOK_of_sub wX_sub)).1 hy) with h | h | ⟨w, hw, s, hs, h⟩
  · left
    have e : x • negSet t0 = negSet t0 := by
      rw [← hyx']
      apply Finset.coe_injective
      rw [ov_coe, h, coe_negSet ov_m15]
    have hxT : x ∈ T0 := by
      rw [hTstab]
      exact MulAction.mem_stabilizer_iff.2 e
    exact Or.inl (ov_conj_of_mem_T0 hxT)
  · left
    have e : x • negSet t0 = g1 • negSet t0 := by
      rw [← hyx']
      apply Finset.coe_injective
      rw [ov_coe, ov_coe, h, coe_g1]
    have hy1 : g1⁻¹ * x ∈ T0 := by
      rw [hTstab, MulAction.mem_stabilizer_iff, mul_smul, e, inv_smul_smul]
    have e1 := ov_conj_of_mem_T0 hy1
    have e2 : x * t0 * x⁻¹ = g1 * t0 * g1⁻¹ := by
      calc x * t0 * x⁻¹ = g1 * ((g1⁻¹ * x) * t0 * (g1⁻¹ * x)⁻¹) * g1⁻¹ := by group
        _ = g1 * t0 * g1⁻¹ := by rw [e1]
    exact Or.inr (e2.trans g1_conj_t0)
  · right
    obtain ⟨s', hs', rfl⟩ := exists_of_mem_G (wordOK_of_sub wT_sub) hs
    refine ⟨wpE w, ⟨w, hw, rfl⟩, s', ?_, ?_⟩
    · rw [← hTstab, ← hCT]
      exact hs'
    · rw [← hyx']
      apply Finset.coe_injective
      rw [ov_coe, ov_coe, h, Subgroup.coe_mul, coe_wpE_eq_E (ov_wordOK hw)]

private theorem ov_gen {w : List ℕ} (hw : w ∈ wSub) {M : Subgroup WP}
    (hstab : MulAction.stabilizer WP (negSet t0) ≤ M) (hg : wpE w ∈ M) : M = ⊤ := by
  obtain ⟨hCT, hTstab, -, -, -, -, -, -, hncard⟩ := classPkg0
  have hws : ∀ v ∈ wT ++ [w], wordOK v = true := wordOK_of_sub fun v hv => by
    rcases List.mem_append.1 hv with h | h
    · exact wT_sub v h
    · rw [List.mem_singleton.1 h]
      exact ov_wSub_sub w hw
  have hO : 3150 ≤ (MulAction.orbit (closureW (wT ++ [w])) (negSet t0)).ncard :=
    (Certificates.certificate197001.2.2.2.2.1 w hw).trans_eq (ncard_orb_negSet hws ov_m15)
  have hKM : closureW (wT ++ [w]) ≤ M := by
    rw [closureW, Subgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    rcases List.mem_append.1 hv with h | h
    · have hT : wpE v ∈ T0 := hCT ▸ wpE_mem_closureW h
      rw [hTstab] at hT
      exact hstab hT
    · rw [List.mem_singleton.1 h]
      exact hg
  exact OmGen.eq_top_of_orbit_eq (negSet t0) hKM hstab
    (OmGen.orbit_eq_of_ncard_le _ _ (hncard.trans_le hO))

theorem overgroup {M : Subgroup WP} (hM : T0 ≤ M) (hMt : M ≠ ⊤) :
    ∀ m ∈ M, m * t0 * m⁻¹ = t0 ∨ m * t0 * m⁻¹ = t0 * zW := by
  obtain ⟨-, hTstab, -⟩ := classPkg0
  have hstab : MulAction.stabilizer WP (negSet t0) ≤ M := by
    rw [← hTstab]
    exact hM
  have key : M ≤ ovS1 :=
    OmGen.le_of_cover (negSet t0) ovS1 (wpE '' {w | w ∈ wSub}) ov_cover
      (by
        rintro _ ⟨w, hw, rfl⟩ M' hM' hg'
        exact ov_gen hw hM' hg')
      hstab hMt
  exact fun m hm => key hm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1
