module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1429Res
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieQHolds
public import CFSG.LocalAnalysis.GLTheoremA.S3.KDChev
public import CFSG.LocalAnalysis.GLTheoremA.S3.KDAmbSolv
public import CFSG.LocalAnalysis.GLTheoremA.PartI.U42
public import CFSG.LocalAnalysis.GLTheoremA.PCompNoncomm
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup glaPComponent_map_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem h1429_map_component {Q : Type} [Group Q] [Finite Q] (q : Q) {I : Subgroup Q}
    (hI : GLAPComponent 3 (fixSubgroup (MulAut.conj q)) I) :
    GLAPComponent 3 (fixSubgroup (MulAut.conj (QuotientGroup.mk' (Subgroup.center Q) q)))
      (I.map (QuotientGroup.mk' (Subgroup.center Q))) :=
  glaPComponent_map_fixSubgroup (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.ker_mk' _).le
    (MulAut.conj q) (MulAut.conj (QuotientGroup.mk' (Subgroup.center Q) q))
    (fun k => by simp [MulAut.conj_apply]) (QuotientGroup.mk'_surjective _) Nat.prime_three hI

section H1429Inner


theorem h1429_kdChevInner_three : KDChevInner 3 :=
  kdChevInner_of Nat.prime_three (by norm_num) (kdCharP_holds Nat.prime_three (by norm_num))
    (kdAmbSolv_holds Nat.prime_three (by norm_num) u42_fixSubgroup_solvable)

theorem i1429InnerRest_holds : I1429InnerRest := by
  intro Q _ _ hQ hChev _ q h3 h1 I hI
  set π : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hI' := h1429_map_component q hI
  have hnc : ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a :=
    exists_mul_ne_mul_of_glaPComponent Nat.prime_three hI'
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  have hZ : Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ := chev_center_eq_bot_of_simple_nonabelian hnc
  have hq3 : q ^ 3 ∈ Subgroup.center Q := by
    have h' : MulAut.conj (q ^ 3) = 1 := by rw [map_pow, h3]
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := congrArg (fun φ : MulAut Q => φ g) h'
    simp only [MulAut.conj_apply, MulAut.one_apply] at hg
    exact (mul_inv_eq_iff_eq_mul.1 hg).symm
  have hβ3 : (MulAut.conj (π q)) ^ 3 = 1 := by
    have hpi : (π q) ^ 3 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 hq3
    rw [← map_pow, hpi, map_one]
  have hβ1 : MulAut.conj (π q) ≠ 1 := by
    intro hβ
    have hmem : π q ∈ Subgroup.center (Q ⧸ Subgroup.center Q) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun φ : MulAut (Q ⧸ Subgroup.center Q) => φ g) hβ
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      exact (mul_inv_eq_iff_eq_mul.1 hg).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    have hq : q ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff q).1 hmem
    apply h1
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply]
    exact mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_center_iff.1 hq g).symm
  have hlay : GLAPLayer 3 (fixSubgroup (MulAut.conj (π q))) = ⊥ :=
    h1429_kdChevInner_three (Q ⧸ Subgroup.center Q) hQ.2 hnc hChev _ hβ3 hβ1 ⟨π q, rfl⟩
  have hle : I.map π ≤ GLAPLayer 3 (fixSubgroup (MulAut.conj (π q))) := by
    unfold GLAPLayer
    exact le_sSup hI'
  rw [hlay, le_bot_iff] at hle
  exact glaPComponent_ne_bot' hI' hle

end H1429Inner

end CFSG.LocalAnalysis.GLTheoremA

end
