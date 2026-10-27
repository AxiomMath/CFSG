module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHFixed
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PspHSU
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.KeyAbstract
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicBlocks

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Module CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCUnitary (commutator_self_le)
open CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks (quasisimple_or_solvable_specialBlock)
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem t6orth_isSolvable_of_commutator_le {F S : Subgroup G} (hFS : ⁅F, F⁆ ≤ S)
    (hS : Group.IsSolvable ↥S) : Group.IsSolvable ↥F := by
  have hle : ∀ n : ℕ, t6orth_dsub F (n + 1) ≤ t6orth_dsub S n := by
    intro n
    induction n with
    | zero => exact hFS
    | succ n ih => exact Subgroup.commutator_mono ih ih
  obtain ⟨d, hd⟩ := t6orth_dsub_eq_bot_of_solvable hS
  refine ⟨⟨d + 1, ?_⟩⟩
  have h' : (derivedSeries ↥F (d + 1)).map F.subtype = ⊥ := by
    rw [t6orth_map_subtype_derivedSeries, eq_bot_iff, ← hd]
    exact hle d
  exact Subgroup.map_injective F.subtype_injective (h'.trans (Subgroup.map_bot _).symm)

theorem t6orth_commutator_eq_of_perfect {F S : Subgroup G} (hSF : S ≤ F) (hFS : ⁅F, F⁆ ≤ S)
    (hS : Group.IsPerfect ↥S) : ⁅F, F⁆ = S := by
  refine le_antisymm hFS ?_
  calc S = ⁅S, S⁆ := (Subgroup.isPerfect_iff.mp hS).symm
    _ ≤ ⁅F, F⁆ := Subgroup.commutator_mono hSF hSF

end Abstract

section Block

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem t6orth_selfDual_equiv (hx : OddOrderIsometry Q p x) (hp2 : p ≠ 2) (hp : p.Prime)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ (ℓ f : ℕ) (hU : UnitaryFieldData ℓ f (AdjoinRoot h))
      (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
        primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h),
      B.IsSymm ∧ B.SeparatingLeft ∧ Nonempty (↥(supportedBlock Q x h) ≃* ↥(sesqUnitaryGroup B)) := by
  classical
  have hp2' : Odd p := hp.odd_of_ne_two hp2
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2' hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (blockGL Q x h).range = sesqUnitaryGroup B := by
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  exact ⟨ℓ, f * d, hU, B, hBsymm, hBl, ⟨(MonoidHom.ofInjective (hx.blockGL_injective hh)).trans
    (MulEquiv.subgroupCongr hrange)⟩⟩

theorem t6orth_factorOK_block (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) {q : ℕ} (hq : 10 ≤ q) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    t6orth_FactorOK q (supportedBlock Q x h) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  set F := supportedBlock Q x h with hF
  set S := specialBlock Q x h with hS
  have hSF : S ≤ F := specialBlock_le_supportedBlock h
  have hFS : ⁅F, F⁆ ≤ S := commutator_supportedBlock_le_specialBlock h
  rcases quasisimple_or_solvable_specialBlock hx hp hp2 hh hne1 with hSq | hSs
  · have heq : ⁅F, F⁆ = S := t6orth_commutator_eq_of_perfect hSF hFS hSq.1
    have hsq : t6psph_HsqProp q F := by
      by_cases hself : h = reciprocalPolynomial h
      · obtain ⟨ℓ, f, hU, B, hBs, hBl, ⟨e⟩⟩ := t6orth_selfDual_equiv hx hp2 hp hh hne1 hself
        exact t6psph_hsqProp_of_equiv F e (t6psph_sqOK_sesqUnitary hO hU hBs hBl hq)
      · have e := pairedBlockEquiv hx hh hself
        haveI : Finite (AdjoinRoot h) := inferInstance
        have h4 : 4 ≤ Nat.card (AdjoinRoot h) := by
          have := hx.p_lt_card_adjoinRoot hp hh hne1
          have := hp.two_le
          omega
        exact t6psph_hsqProp_of_equiv F e
          (t6psph_sqOK_generalLinear hO (exists_finset_card_four_of_card h4) hq)
    refine ⟨1, fun _ => S, fun _ => hSq, fun _ => heq.ge, fun _ => ?_,
      Or.inr (heq.le.trans (le_iSup (fun _ : Fin 1 => S) 0)), ?_⟩
    · rw [heq, Subgroup.subgroupOf_self]
      infer_instance
    · intro j hT b hb hb3
      have hq' : CFSG.IsQuasisimple ↥⁅F, F⁆ := by rw [heq]; exact hSq
      have hT' : IsTypeL2 q ↥⁅F, F⁆ := by rw [heq]; exact hT
      have hb3' : ∀ m ∈ F, b ^ 3 * m = m * b ^ 3 := fun m _ => by rw [hb3, one_mul, mul_one]
      obtain ⟨s, hs, hsm⟩ := key_of_sq_mem (commutator_self_le F) (hsq hq' hT') hb hb3'
      exact ⟨s, by rwa [heq] at hs, fun m hm => hsm m (by rwa [heq])⟩
  · exact t6orth_factorOK_of_solvable q (t6orth_isSolvable_of_commutator_le hFS hSs)

end Block

end CFSG.HardMathSupport.Dickson.Sec6.I1431
