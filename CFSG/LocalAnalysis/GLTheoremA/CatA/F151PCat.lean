module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158FgExc
import CFSG.LocalAnalysis.GLTheoremA.CatA.I107GChev

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup PerfectInLayer mem_fixSubgroup)

private theorem fixSubgroup_conj_eq_centralizer {G : Type*} [Group G] (u : G) :
    fixSubgroup (MulAut.conj u) = Subgroup.centralizer ({u} : Set G) := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem catLayer_holds
    : CatLayer := by
  intro R _ _ p hp hp2 hcat x hx hxp
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie idx =>
    haveI : IsSimpleGroup idx.Group := (CFSG.Assembly.lie_finite_simple idx).2
    haveI : IsSimpleGroup R := e.isSimpleGroup
    have hna : ∃ a b : R, a * b ≠ b * a :=
      CFSG.LocalAnalysis.GLTheoremA.chevTwoNonabelian_holds R
        (inferInstance : IsSimpleGroup R)
        (Or.inl ⟨TauCeti.CFSGIndex.lie idx, hi, ⟨e⟩⟩)
    have hchar : p ≠ idx.1.characteristic := by rw [hi]; exact hp2
    have hconjp : (MulAut.conj x) ^ p = 1 := by
      rw [← map_pow (MulAut.conj) x p, hxp, map_one]
    have hcenter : Subgroup.center R = ⊥ := by
      obtain ⟨a, b, hab⟩ := hna
      exact center_eq_bot_of_simple_nonab hab
    have hconjne : MulAut.conj x ≠ 1 := by
      intro h1
      have hxmem : x ∈ Subgroup.center R := by
        rw [Subgroup.mem_center_iff]
        intro y
        have hconjy : x * y * x⁻¹ = y := by
          have h := congrArg (fun f : MulAut R => f y) h1
          simpa [MulAut.conj_apply] using h
        have hy : x * y = y * x := by
          calc x * y = (x * y * x⁻¹) * x := by rw [mul_assoc, inv_mul_cancel, mul_one]
            _ = y * x := by rw [hconjy]
        exact hy.symm
      rw [hcenter] at hxmem
      exact hx (Subgroup.mem_bot.mp hxmem)
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent R
      (inferInstance : IsSimpleGroup R) hna idx ⟨e⟩ p hp hp2 hchar (MulAut.conj x) hconjp
      hconjne
  | cyclic _ _ => exact absurd hi (by simp [onLie])
  | alternating _ _ => exact absurd hi (by simp [onLie])
  | sporadic _ => exact absurd hi (by simp [onLie])

theorem catChevComps_holds
    : CatChevComps := by
  intro R _ _ p hp hp2 hcat x hx hxp J hJ
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie idx =>
    haveI : IsSimpleGroup idx.Group := (CFSG.Assembly.lie_finite_simple idx).2
    haveI : IsSimpleGroup R := e.isSimpleGroup
    have hna : ∃ a b : R, a * b ≠ b * a :=
      CFSG.LocalAnalysis.GLTheoremA.chevTwoNonabelian_holds R
        (inferInstance : IsSimpleGroup R)
        (Or.inl ⟨TauCeti.CFSGIndex.lie idx, hi, ⟨e⟩⟩)
    have hchev : IsChevSimple 2 R := Or.inl ⟨TauCeti.CFSGIndex.lie idx, hi, ⟨e⟩⟩
    have hconjp : (MulAut.conj x) ^ p = 1 := by
      rw [← map_pow (MulAut.conj) x p, hxp, map_one]
    have hJ' : GLAPComponent p (fixSubgroup (MulAut.conj x)) J := by
      rwa [fixSubgroup_conj_eq_centralizer]
    exact (CFSG.LocalAnalysis.GLTheoremA.T158.kdChevDownQ_two_holds hp hp2) R
      (inferInstance : IsSimpleGroup R) hna hchev (MulAut.conj x) hconjp J hJ'
  | cyclic _ _ => exact absurd hi (by simp [onLie])
  | alternating _ _ => exact absurd hi (by simp [onLie])
  | sporadic _ => exact absurd hi (by simp [onLie])

end CFSG.LocalAnalysis.GLTheoremA.F151

end
