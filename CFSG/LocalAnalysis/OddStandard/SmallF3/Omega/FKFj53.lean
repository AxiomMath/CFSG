module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKCoreBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAEng
import CFSG.GH74.Uniqueness.Bender.Frame311

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fkFj53 (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1) : Fj53 hQ hs := by
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite (omegaGroup hQ) := Subtype.finite
  intro z K hz2 hP hKs hzπ hzs hzsπ
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) s
  refine ⟨fun h5 h3 => ?_, fun h3 h5 => ?_⟩
  ·
    obtain ⟨a, c, hac, hcases⟩ := fj_pocket_dichotomy hQ (by omega) hs hKs hP.2.2.2 hP.1 hz2 hzπ
      hzs hzsπ
    have hc : c = 1 := by
      rcases hcases with ⟨hc, -⟩ | ⟨-, h⟩
      · exact hc
      · omega
    subst hc
    have hY : ∀ c : OGroup (Q.restrict (commSp s)), Odd (orderOf c) → c ≠ 1 →
        ∃ E : Subgroup (OGroup (Q.restrict (commSp s))),
          (∀ e ∈ E, blockHom hs (1, e) ∈ omegaGroup hQ) ∧ (∀ e ∈ E, e * e = 1) ∧
          (∃ e ∈ E, e ≠ 1) ∧ (∀ e ∈ E, c * e * c⁻¹ ∈ E) ∧
          (∀ e ∈ E, e ≠ 1 → c * e * c⁻¹ ≠ e) := by
      intro c hc hc1
      obtain ⟨E, hEΩ, hE2, hE1, hcE, hfree⟩ :=
        fkFrame_exists (nondegenerate_restrict_commSp hQ hs) h3 hc hc1
      exact ⟨E, fun e he => cl_blockHom_right_mem_omegaGroup hQ hs (hEΩ he), hE2, hE1, hcE,
        hfree⟩
    refine (l34g_le_closure_odd hP.2.2.2).trans ?_
    rw [Subgroup.closure_le]
    rintro k ⟨hkK, hkodd⟩
    have hkc : (k : OGroup Q) ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) := hKs hkK
    rw [← range_blockHom hQ hs] at hkc
    obtain ⟨⟨p, c⟩, hpc⟩ := MonoidHom.mem_range.mp hkc
    have hc1 : c = 1 :=
      fkCore_block (N := omegaGroup hQ) (blockHom hs) (blockHom_injective hs) hz2 hP hac hY hkK
        hkodd hpc
    subst hc1
    have hpodd : Odd (orderOf p) := by
      have h1 : orderOf (p, (1 : OGroup (Q.restrict (commSp s)))) = orderOf k := by
        rw [← orderOf_injective (blockHom hs) (blockHom_injective hs) (p, 1), hpc,
          Subgroup.orderOf_coe]
      have hlcm := Prod.orderOf (p, (1 : OGroup (Q.restrict (commSp s))))
      exact (h1 ▸ hkodd).of_dvd_nat (hlcm ▸ Nat.dvd_lcm_left _ _)
    have hp : p ∈ omegaGroup (nondegenerate_restrict_fixSp hQ hs) :=
      CFSG.GH74.Uniqueness.Bender.mem_of_mul_self_mem_of_odd hpodd (mul_self_mem_omegaGroup _ p)
    exact ⟨⟨p, hp⟩, Subtype.ext hpc⟩
  ·
    obtain ⟨a, c, hac, hcases⟩ := fj_pocket_dichotomy hQ (by omega) hs hKs hP.2.2.2 hP.1 hz2 hzπ
      hzs hzsπ
    have ha : a = 1 := by
      rcases hcases with ⟨-, h⟩ | ⟨ha, -⟩
      · omega
      · exact ha
    subst ha
    let β : OGroup (Q.restrict (commSp s)) × OGroup (Q.restrict (fixSp s)) →* OGroup Q :=
      (blockHom hs).comp (MulEquiv.prodComm).toMonoidHom
    have hβ : Function.Injective β :=
      (blockHom_injective hs).comp (MulEquiv.prodComm).injective
    have hY : ∀ c : OGroup (Q.restrict (fixSp s)), Odd (orderOf c) → c ≠ 1 →
        ∃ E : Subgroup (OGroup (Q.restrict (fixSp s))),
          (∀ e ∈ E, β (1, e) ∈ omegaGroup hQ) ∧ (∀ e ∈ E, e * e = 1) ∧
          (∃ e ∈ E, e ≠ 1) ∧ (∀ e ∈ E, c * e * c⁻¹ ∈ E) ∧
          (∀ e ∈ E, e ≠ 1 → c * e * c⁻¹ ≠ e) := by
      intro c hc hc1
      obtain ⟨E, hEΩ, hE2, hE1, hcE, hfree⟩ :=
        fkFrame_exists (nondegenerate_restrict_fixSp hQ hs) h3 hc hc1
      exact ⟨E, fun e he => cl_blockHom_left_mem_omegaGroup hQ hs (hEΩ he), hE2, hE1, hcE,
        hfree⟩
    refine (l34g_le_closure_odd hP.2.2.2).trans ?_
    rw [Subgroup.closure_le]
    rintro k ⟨hkK, hkodd⟩
    have hkc : (k : OGroup Q) ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) := hKs hkK
    rw [← range_blockHom hQ hs] at hkc
    obtain ⟨⟨p, c'⟩, hpc⟩ := MonoidHom.mem_range.mp hkc
    have hp1 : p = 1 :=
      fkCore_block (N := omegaGroup hQ) β hβ hz2 hP (a := c) hac hY hkK hkodd
        (p := c') (c := p) hpc
    subst hp1
    have hcodd : Odd (orderOf c') := by
      have h1 : orderOf ((1 : OGroup (Q.restrict (fixSp s))), c') = orderOf k := by
        rw [← orderOf_injective (blockHom hs) (blockHom_injective hs) (1, c'), hpc,
          Subgroup.orderOf_coe]
      have hlcm := Prod.orderOf ((1 : OGroup (Q.restrict (fixSp s))), c')
      exact (h1 ▸ hkodd).of_dvd_nat (hlcm ▸ Nat.dvd_lcm_right _ _)
    have hc' : c' ∈ omegaGroup (nondegenerate_restrict_commSp hQ hs) :=
      CFSG.GH74.Uniqueness.Bender.mem_of_mul_self_mem_of_odd hcodd (mul_self_mem_omegaGroup _ c')
    exact ⟨⟨c', hc'⟩, Subtype.ext hpc⟩

end CFSG.OddStandard.SmallF3.Omega
