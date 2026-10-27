module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenTorus
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenGroup
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenInner
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenFix24
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenO3

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
open CFSG.StandardType.TableBExc.E6Three (gE6 cE6 cE6_pow_three)

set_option linter.unusedSectionVars false

section Census

variable
  {K : Type} [Field K] {ω : Kˣ}

theorem e6Cen_finrank_eq_24_of_zpowers [Finite K] (hK4 : 4 ≤ Nat.card K) (h3 : ω ^ 3 = 1)
    (h1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    {Z : MulAut (adjointGroup Tag.E6 K)} (hZE : Z ∈ E) (hZ : BmMono Z e6CenZ)
    (hab : ∀ a b c : ZMod 3, rootDiagAutHom Tag.E6 K (torV ω (e6CenTz a b c)) ∈ E → a = b)
    {s : adjointGroup Tag.E6 K} (hs : MulAut.conj s ∈ E) (hs1 : s ≠ 1) {v : WeylGroup Tag.E6}
    (hsv : BmMono (MulAut.conj s) v) (hv : v ∈ Subgroup.zpowers e6CenZ) :
    Module.finrank K (LinearMap.ker
      (((s : ModGL .E6 K) : Module.End K (RootModule .E6 K)) - 1)) = 24 := by
  have hs3 := e6Cen_pow_three_of_conj hK4 (hE.2 _ hs)
  have hK3 := e6Cen_ringChar_ne_three h3 h1
  rcases e6Cen_mem_zpowers_three e6CenZ_pow_three hv with rfl | rfl | rfl
  · obtain ⟨a, b, c, hsx⟩ := e6Cen_diag_mem_frame h3 h1 hE hZE hZ hs hsv
    have hab' := hab a b c (by rw [← hsx]; exact hs)
    subst hab'
    have hsx' := e6Cen_coe_eq_of_conj_eq_rootDiag hK4 hsx
    by_cases hac : a = 0 ∧ c = 0
    · obtain ⟨rfl, rfl⟩ := hac
      refine (hs1 (Subtype.ext ?_)).elim
      rw [hsx', e6CenTz_zero, e6Cen_torV_zero, OneMemClass.coe_one]
      exact Units.ext rootDiag_one
    · rw [hsx', e6PW_finrank_torV h3 h1, e6Cen_kerCount_Tz, e6CenTzKc, if_pos rfl, if_neg hac]
  · exact finrank_ker_eq_24_of_bmMono_z hK3 hK4 hs3 (k := 1) (Or.inl rfl)
      (by rw [pow_one]; exact hsv)
  · exact finrank_ker_eq_24_of_bmMono_z hK3 hK4 hs3 (k := 2) (Or.inr rfl) hsv

theorem e6Cen_OT [Finite K] (hK : 3 ∣ Nat.card K - 1) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hcube : E6CenCube K E)
    (hF : E6CenFrame e6CenOT E) : E6CenConcl K E := by
  obtain ⟨hE, -, -, hEi, -, hA⟩ := hcube
  have hK4 := e6Cen_four_le_card hK
  obtain ⟨X, hXE, hX⟩ := hF.2 cE6 (Subgroup.subset_closure (Set.mem_insert _ _))
  obtain ⟨Z, hZE, hZ⟩ := hF.2 e6CenZ
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hc : ∀ Y ∈ E, X * Y = Y * X := fun Y hYE =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨X, hXE⟩ : E) ⟨Y, hYE⟩)
  have hZi := e6Cen_inner_OT hK hX hZ (hE.2 _ hXE) (hE.2 _ hZE) (hc Z hZE)
  have hU : ∀ U ∈ E, U ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) → BmMono U cE6 →
      False := by
    intro U hUE hUi hUv
    refine hEi (e6Cen_le_innerAut_of_frame h3 h1 hE hF hZE hZ ?_)
    rintro _ (rfl | rfl)
    · exact mem_e6CenImage.2 ⟨U, Subgroup.mem_inf.2 ⟨hUE, hUi⟩, hUv⟩
    · exact mem_e6CenImage.2 ⟨Z, Subgroup.mem_inf.2 ⟨hZE, hZi⟩, hZ⟩
  have hcz : cE6 * e6CenZ = e6CenZ * cE6 :=
    e6CenImage_mul_comm hK4 hE (mem_e6CenImage.2 ⟨X, hXE, hX⟩) (mem_e6CenImage.2 ⟨Z, hZE, hZ⟩)
  refine (hA fun s hs hs1 => ?_).elim
  obtain ⟨v, hv, hsv⟩ := hF.1 _ hs
  obtain ⟨m, n, hm, -, rfl⟩ := e6Cen_mem_closure_pair hcz cE6_pow_three e6CenZ_pow_three hv
  have hW := hsv.mul (hZ.pow n).inv
  rw [mul_inv_cancel_right] at hW
  have hWE : MulAut.conj s * (Z ^ n)⁻¹ ∈ E := mul_mem hs (inv_mem (pow_mem hZE n))
  have hWi : MulAut.conj s * (Z ^ n)⁻¹ ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) :=
    mul_mem ⟨s, rfl⟩ (inv_mem (pow_mem hZi n))
  interval_cases m
  · rw [pow_zero, one_mul] at hsv
    exact e6Cen_finrank_eq_24_of_zpowers hK4 h3 h1 hE hZE hZ
      (fun a b c hd => e6Cen_Tz_fix_c h3 h1 hX (hc _ hd)) hs hs1 hsv
      (Subgroup.npow_mem_zpowers _ n)
  · rw [pow_one] at hW
    exact (hU _ hWE hWi hW).elim
  · have h2 := hW.pow 2
    rw [← pow_mul, show cE6 ^ (2 * 2) = cE6 by
      rw [show 2 * 2 = 3 + 1 from rfl, pow_succ, cE6_pow_three, one_mul]] at h2
    exact (hU _ (pow_mem hWE 2) (pow_mem hWi 2) h2).elim

end Census

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
