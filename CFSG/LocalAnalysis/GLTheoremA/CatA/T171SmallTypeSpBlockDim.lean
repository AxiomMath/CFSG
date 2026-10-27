module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeSpBlockLayer
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.FixedFreeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open Matrix
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL
  (comSp fixSp ds ds_apply mem_comSp mem_fixSp e_mem_comSp eq_zero_of_mem_comSp_fixed)
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {n : ℕ}

theorem even_finrank_comSp_of_order_three
    (y : SpV n ≃ₗ[ZMod 2] SpV n) (hy3 : y ^ 3 = 1) :
    Even (Module.finrank (ZMod 2) (comSp y)) := by
  classical
  haveI : Fintype ↥(comSp y) := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let f : Function.End ↥(comSp y) := fun z => ⟨y z, e_mem_comSp z.2⟩
  have hf : f ^ 3 ^ 1 = 1 := by
    rw [show f ^ 3 ^ 1 = f * f * f by rw [pow_one, pow_succ, pow_succ, pow_one]]
    funext z
    apply Subtype.ext
    change y (y (y ↑z)) = ↑z
    exact congrArg (fun e : SpV n ≃ₗ[ZMod 2] SpV n => e (z : SpV n)) hy3
  have hfix : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, ?_⟩, ?_⟩
    · apply Subtype.ext
      exact map_zero (y : SpV n →ₗ[ZMod 2] SpV n)
    · rintro ⟨z, hz⟩
      apply Subtype.ext
      apply Subtype.ext
      exact eq_zero_of_mem_comSp_fixed hy3 z.2 (congrArg Subtype.val hz)
  have hcard : Fintype.card ↥(comSp y) = 2 ^ Module.finrank (ZMod 2) (comSp y) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := ↥(comSp y))]
    norm_num
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  rw [hcard, hfix] at hmod
  exact CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.even_of_two_pow_modEq_one hmod

theorem finrank_comSp_le_two_of_coordinate
    (A : Subgroup (SpV n ≃ₗ[ZMod 2] SpV n)) [Fintype A]
    [Fintype (SpNonzeroBlock A)] (hAe : IsElemAbelian 3 A)
    (D0 : SpNonzeroBlock A)
    (hD0 : Module.finrank (ZMod 2) (blockSpace A D0.1.1) = 2)
    (y : ↥A) (hyD0 : y ∉ D0.1.1)
    (hyD : ∀ D : SpNonzeroBlock A, D ≠ D0 → y ∈ D.1.1) :
    Module.finrank (ZMod 2) (comSp (y : SpV n ≃ₗ[ZMod 2] SpV n)) ≤ 2 := by
  classical
  let hp : Nat.Prime 3 := by norm_num
  let hpF : (3 : ZMod 2) ≠ 0 := by decide
  haveI : Fintype {D : SpNonzeroBlock A // D ≠ D0} := Fintype.ofFinite _
  let f : SpNonzeroBlock A → ℕ := fun D => Module.finrank (ZMod 2) (blockSpace A D.1.1)
  let U' : Submodule (ZMod 2) (SpV n) :=
    ⨆ D : {D : SpNonzeroBlock A // D ≠ D0}, blockSpace A D.1.1.1
  let K : Submodule (ZMod 2) (SpV n) := fixedSpaceOf A ⊔ U'
  have hU'le : U' ≤ ⨆ D : SpNonzeroBlock A, blockSpace A D.1.1 := by
    apply iSup_le
    intro D
    exact le_iSup (fun D : SpNonzeroBlock A => blockSpace A D.1.1) D.1
  have hdisj : Disjoint (fixedSpaceOf A) U' := by
    rw [disjoint_iff_inf_le]
    intro x hx
    have hx' : x ∈ fixedSpaceOf A ⊓ (⨆ D : SpNonzeroBlock A, blockSpace A D.1.1) :=
      ⟨hx.1, hU'le hx.2⟩
    rw [inf_fixed_iSup_nonzeroBlock A hAe] at hx'
    exact hx'
  have hind : iSupIndep (fun D : {D : SpNonzeroBlock A // D ≠ D0} =>
      blockSpace A D.1.1.1) :=
    (iSupIndep_blockSpace A hp hpF hAe).comp
      (f := fun D : {D : SpNonzeroBlock A // D ≠ D0} => D.1.1)
      (by intro x y h; exact Subtype.ext (Subtype.ext h))
  have hdimU' : Module.finrank (ZMod 2) U' =
      ∑ D : {D : SpNonzeroBlock A // D ≠ D0}, f D.1 := by
    have h := CFSG.CGT.PushingUpLit.CGT6.WeilJoint.finrank_biSup_eq_sum
      (fun D : {D : SpNonzeroBlock A // D ≠ D0} => blockSpace A D.1.1.1)
      hind Finset.univ
    have hU : (⨆ D ∈ (Finset.univ : Finset {D : SpNonzeroBlock A // D ≠ D0}),
        blockSpace A D.1.1.1) = U' := by simp [U']
    rw [hU] at h
    simpa [f] using h
  have hdim_sup : Module.finrank (ZMod 2) K =
      Module.finrank (ZMod 2) (fixedSpaceOf A) + Module.finrank (ZMod 2) U' := by
    change Module.finrank (ZMod 2) ↥(fixedSpaceOf A ⊔ U') =
      Module.finrank (ZMod 2) ↥(fixedSpaceOf A) + Module.finrank (ZMod 2) ↥U'
    have h := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpaceOf A) U'
    rw [hdisj.eq_bot, finrank_bot, add_zero] at h
    omega
  have hsum_split : (∑ D : SpNonzeroBlock A, f D) =
      f D0 + ∑ D : {D : SpNonzeroBlock A // D ≠ D0}, f D.1 := by
    have h := Finset.sum_subtype (s := (Finset.univ.erase D0))
      (p := fun D : SpNonzeroBlock A => D ≠ D0) (F := inferInstance)
      (h := by intro x; simp) f
    have h2 := Finset.sum_erase_add (s := (Finset.univ : Finset (SpNonzeroBlock A))) f
      (Finset.mem_univ D0)
    rw [← h2, h, add_comm]
  have hdim_all := finrank_eq_fixed_add_nonzeroBlock A hAe
  rw [CFSG.LocalAnalysis.GLTheoremA.CatB.finrank_sp] at hdim_all
  have hfD0 : f D0 = 2 := hD0
  rw [hsum_split, hfD0] at hdim_all
  have hdimK : Module.finrank (ZMod 2) K = 2 * n - 2 := by
    rw [hdim_sup, hdimU']
    omega
  have hKker : K ≤ LinearMap.ker (ds (y : SpV n ≃ₗ[ZMod 2] SpV n)) := by
    apply sup_le
    · intro c hc
      rw [LinearMap.mem_ker, ds_apply]
      have hcy : (y : SpV n ≃ₗ[ZMod 2] SpV n) c = c :=
        (mem_fixedSpaceOf A).mp hc y
      rw [hcy, sub_self]
    · apply iSup_le
      intro D v hv
      rw [LinearMap.mem_ker, ds_apply]
      have hyD' : y ∈ D.1.1.1 := hyD D.1 D.2
      have hvfix : (y : SpV n ≃ₗ[ZMod 2] SpV n) v = v :=
        ((mem_blockSpace A).mp hv).1 y hyD'
      rw [hvfix, sub_self]
  have h := LinearMap.finrank_range_add_finrank_ker
    (ds (y : SpV n ≃ₗ[ZMod 2] SpV n))
  have hk := Submodule.finrank_mono hKker
  rw [CFSG.LocalAnalysis.GLTheoremA.CatB.finrank_sp] at h
  change Module.finrank (ZMod 2) (comSp (y : SpV n ≃ₗ[ZMod 2] SpV n)) ≤ 2
  have hrange : Module.finrank (ZMod 2) (LinearMap.range
      (ds (y : SpV n ≃ₗ[ZMod 2] SpV n))) =
      Module.finrank (ZMod 2) (comSp (y : SpV n ≃ₗ[ZMod 2] SpV n)) := rfl
  rw [hrange] at h
  omega


end CFSG.LocalAnalysis.GLTheoremA.T171S

end
