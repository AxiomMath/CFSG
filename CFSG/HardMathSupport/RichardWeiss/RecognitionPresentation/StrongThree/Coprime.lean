module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open CFSG

variable {X : Type*} [Group X]

theorem le_iSup_centralizer_of_coprime {p : ℕ} [Fact p.Prime] {A U : Subgroup X} [Finite A]
    [Finite U] [IsElementaryAbelian p A] (hcard : p ^ 2 ≤ Nat.card A) (hp : ¬ p ∣ Nat.card U)
    (hAU : A ≤ Subgroup.normalizer (U : Set X)) :
    U ≤ ⨆ a ∈ A, ⨆ (_ : a ≠ 1), U ⊓ Subgroup.centralizer ({a} : Set X) := by
  let : MulDistribMulAction A U := MulDistribMulAction.compHom U (Subgroup.inclusion hAU)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := A) (H := U)
    hcard hp
  have hle : (⨆ (a : A) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) U) ≤
      (⨆ a ∈ A, ⨆ (_ : a ≠ 1), U ⊓ Subgroup.centralizer ({a} : Set X)).comap U.subtype := by
    refine iSup₂_le fun a ha => fun x hx => ?_
    have hfix := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).1 hx
    have hc : (a : X) * x * (a : X)⁻¹ = x := congrArg Subtype.val hfix
    have ha1 : (a : X) ≠ 1 := fun h => ha (Subtype.ext h)
    refine Subgroup.mem_iSup_of_mem (a : X) (Subgroup.mem_iSup_of_mem a.2
      (Subgroup.mem_iSup_of_mem ha1 (Subgroup.mem_inf.2 ⟨x.2, ?_⟩)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x : X) * a = (a : X) * x * (a : X)⁻¹ * a := by rw [hc]
      _ = a * x := by rw [inv_mul_cancel_right]
  intro h hh
  have hmem : (⟨h, hh⟩ : U) ∈
      ⨆ (a : A) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) U := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact hle hmem


theorem isElementaryAbelian_of_isElemAbelian {p : ℕ} {E : Subgroup X}
    (h : CFSG.Open.IsElemAbelian p E) : IsElementaryAbelian p ↥E :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp h

variable [Finite X]

theorem normal_eq_bot_of_not_dvd {M E U : Subgroup X} (hM : GLBStronglyEmbedded 3 M)
    (hcore : M.normalCore = ⊥) (hEM : E ≤ M) (hE : IsElemAbelian 3 E) (hcard : 9 ≤ Nat.card E)
    [U.Normal] (hU : ¬ 3 ∣ Nat.card U) : U = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsElementaryAbelian 3 ↥E := isElementaryAbelian_of_isElemAbelian hE
  have hgen := le_iSup_centralizer_of_coprime (p := 3) (A := E) (U := U) (by simpa using hcard)
    hU (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hUM : U ≤ M := by
    refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
    have h3 : a ^ 3 = 1 := hE.2 a ha
    exact inf_le_right.trans (centralizer_le_of_orderThree hM (hEM ha) (orderOf_eq_prime h3 ha1))
  exact le_bot_iff.mp (hcore ▸ (Subgroup.normal_le_normalCore.mpr hUM))

theorem normal_eq_bot_of_isPGroup {M T : Subgroup X} (hM : GLBStronglyEmbedded 3 M)
    (hcore : M.normalCore = ⊥) [T.Normal] (hT : IsPGroup 3 T) : T = ⊥ := by
  obtain ⟨P, hP⟩ := exists_sylow_le hM
  have hTM : T ≤ M := (hT.le_sylow_of_normal P).trans hP
  exact le_bot_iff.mp (hcore ▸ (Subgroup.normal_le_normalCore.mpr hTM))

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
