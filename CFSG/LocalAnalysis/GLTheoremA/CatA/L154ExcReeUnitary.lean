module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofU38
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import Certificates.Certificate17002
public import Certificates.Certificate17951

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG CFSG.Assembly
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.StandardType (markTag markRank markChar markDeg)

theorem l154_exists_psuConj_of_conjImage {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 n K)
    {x : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))}
    (hx : x ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
      (LargeEvenGUSet (Fin 3) K (2 ^ n))) :
    ∃ A : unitaryIsom3 h,
      MulAut.congr (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)) (psuConj h A) = x := by
  obtain ⟨M, hM, hgraph⟩ := hx
  obtain ⟨u, hu⟩ := CFSG.StandardType.TableBU63.exists_unitary_of_gu h hM
  have hA : (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M : GL (Fin 3) K) ∈ unitaryIsom3 h := by
    rw [mem_unitaryIsom3]
    have hmem := (mem_primeFormUnitary.mp hu)
    simpa only [idGram, Units.val_one, Matrix.mul_one] using hmem
  let e := unitaryPSUEquiv h (by norm_num : 1 ≤ 3)
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * M, hA⟩, ?_⟩
  refine MulEquiv.ext fun z => QuotientGroup.induction_on z fun g => ?_
  show e (psuConj h ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * M, hA⟩
      (e.symm (QuotientGroup.mk g))) = x (QuotientGroup.mk g)
  have hes : e.symm (QuotientGroup.mk g :
        CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) K)) = (g : unitaryPSU h 3) := by
    have h1 : (QuotientGroup.mk g :
          CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) K)) =
        e (unitaryProj h 3 g) :=
      (unitaryPSUEquiv_unitaryProj h (by norm_num : 1 ≤ 3) g).symm
    rw [h1, MulEquiv.symm_apply_apply]
    rfl
  rw [hes, psuConj_mk]
  have hemk : e ((suConj h ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * M, hA⟩ g :
        unitarySU 2 n K 3) : unitaryPSU h 3) =
      (QuotientGroup.mk (suConj h ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * M, hA⟩ g) :
        LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) :=
    unitaryPSUEquiv_unitaryProj h (by norm_num : 1 ≤ 3) _
  rw [hemk]
  have hrel : (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M) * (g : GL (Fin 3) K) *
      (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M)⁻¹ = M * (g : GL (Fin 3) K) * M⁻¹ := by
    rw [show (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M) * (g : GL (Fin 3) K) *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) u * (M * (g : GL (Fin 3) K) * M⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) u)⁻¹ by group]
    rw [(CFSG.StandardType.TypeA.PGLTor.commute_scalar u (M * (g : GL (Fin 3) K) * M⁻¹)).eq]
    group
  have hmem : (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M) * (g : GL (Fin 3) K) *
      (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M)⁻¹ ∈ LargeEvenSUGroup (Fin 3) K (2 ^ n) :=
    conj_mem_unitarySU hA g.2
  have hsu : (⟨(Matrix.GeneralLinearGroup.scalar (Fin 3) u * M) * (g : GL (Fin 3) K) *
        (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M)⁻¹, hmem⟩ :
        ↥(LargeEvenSUGroup (Fin 3) K (2 ^ n))) =
      suConj h ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * M, hA⟩ g :=
    Subtype.ext (by rw [coe_suConj]; rfl)
  rw [← hsu]
  exact (hgraph g (⟨(Matrix.GeneralLinearGroup.scalar (Fin 3) u * M) * (g : GL (Fin 3) K) *
    (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M)⁻¹, hmem⟩) hrel).symm

theorem l154_conjImage_eq_one {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 n K)
    (hn : Odd n) (hq : 2 < 2 ^ n)
    {x : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))}
    (hx : x ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
      (LargeEvenGUSet (Fin 3) K (2 ^ n))) (hx3 : x ^ 3 = 1)
    {y : LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))} (hy : x y = y) (hy4 : y ^ 4 = 1)
    (hy2 : y ^ 2 ≠ 1) : x = 1 := by
  obtain ⟨A, rfl⟩ := l154_exists_psuConj_of_conjImage h hx
  let e := unitaryPSUEquiv h (by norm_num : 1 ≤ 3)
  obtain ⟨y₀, rfl⟩ : ∃ y₀ : unitaryPSU h 3, e y₀ = y := ⟨e.symm y, e.apply_symm_apply y⟩
  have hA3 : psuConj h A ^ 3 = 1 := by
    apply (MulEquiv.map_eq_one_iff (MulAut.congr e)).mp
    rw [map_pow]
    exact hx3
  have hy' : psuConj h A y₀ = y₀ := by
    have h1 : e (psuConj h A (e.symm (e y₀))) = e y₀ := hy
    rw [MulEquiv.symm_apply_apply] at h1
    exact e.injective h1
  have h4' : y₀ ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact hy4
  have h2' : y₀ ^ 2 ≠ 1 := fun h1 => hy2 (by
    have := congrArg e h1
    rw [map_pow, map_one] at this
    exact this)
  rw [CFSG.RankThree.PartTwo.Sec8.Item812Res11.eq_one_of_psuConj_of_fixed h hn hq hA3 hy' h4' h2']
  exact map_one _

theorem l154_label_twA_of_mark {lab : LargeEvenLabel} {n : ℕ} (ht : markTag lab = .PSU)
    (hr : markRank lab = 3) (hc : markChar lab = 2) (hd : markDeg lab = n) :
    lab = ⟨.twA, 2, n⟩ := by
  obtain ⟨t, l, m⟩ := lab
  cases t <;> simp [markTag, markRank, markChar, markDeg] at ht hr hc hd ⊢
  case twA => exact ⟨hr, hd⟩
  case D => split_ifs at ht
  case twD => split_ifs at ht hr <;> omega

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
