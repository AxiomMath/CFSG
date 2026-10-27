module

import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPComp
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin Matrix
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup exists_glaPComponent_map_fixSubgroup)

theorem k1419ClsLinLift {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) {d : ℕ} (hd : 1 ≤ d)
    (A : GL (Fin d) K) (u : MulAut (LargeEvenProj (StatedSL d K)))
    (hu : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (hpow : u ^ 3 = 1) (J : Subgroup (LargeEvenProj (StatedSL d K)))
    (hJ : GLAPComponent 3 (fixSubgroup u) J) :
    ∃ M : Subgroup (GL (Fin d) K),
      CFSG.Open.IsComponentOf M (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSL d K) ∧
      Nonempty (PSimple 3 J ≃* M ⧸ Subgroup.center M) ∧
      (∀ z : GL (Fin d) K, z ∈ M → (∀ y ∈ M, z * y = y * z) → z ^ 3 = 1 →
        z ∉ StatedScalars (Fin d) K →
          ∃ j ∈ J, (∀ j' ∈ J, j * j' = j' * j) ∧ j ^ 3 = 1 ∧ j ≠ 1) := by
  obtain ⟨c, hc⟩ := isScalar_of_pow_trivial h2 A 3 u hu hpow
  have hodd : Odd (orderOf A) :=
    odd_orderOf_of_pow_scalar h2 hd A (Nat.prime_three.odd_of_ne_two (by norm_num)) hc
  have hord : ((orderOf A : ℕ) : K) ≠ 0 := cast_orderOf_ne_zero_of_odd h2 A hodd
  obtain ⟨M₀, hM₀, hM₀J⟩ := exists_glaPComponent_map_fixSubgroup
    (LargeEvenProjMk (StatedSL d K)) ker_projMk_le_center (conjSL A) u
    (fun k => (hu k (conjSL A k) rfl).symm) (QuotientGroup.mk_surjective)
    Nat.prime_three hJ
  have hMinj : Function.Injective (StatedSL d K).subtype := Subtype.val_injective
  have hM' : GLAPComponent 3
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSL d K)
      (M₀.map (StatedSL d K).subtype) := by
    rw [← map_fixSubgroup_conjSL A]
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff Nat.prime_three hMinj).mpr hM₀
  have hcomp : CFSG.Open.IsComponentOf (M₀.map (StatedSL d K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSL d K) :=
    LinPCompIsComp_holds K d 3 Nat.prime_three A hord (M₀.map (StatedSL d K).subtype) hM'
  let M : Subgroup (GL (Fin d) K) := M₀.map (StatedSL d K).subtype
  have hMsl : M ≤ StatedSL d K := fun x hx => (hcomp.1 hx).2
  refine ⟨M, hcomp, ?_, ?_⟩
  · let e : ↥M₀ ≃* ↥M := Subgroup.equivMapOfInjective M₀ (StatedSL d K).subtype hMinj
    have hmemJ : ∀ x : ↥M₀,
        LargeEvenProjMk (StatedSL d K) (x : ↥(StatedSL d K)) ∈ J := fun x => by
      rw [← hM₀J]
      exact Subgroup.mem_map_of_mem _ x.2
    let fJ : ↥M₀ →* ↥J :=
      MonoidHom.codRestrict ((LargeEvenProjMk (StatedSL d K)).comp M₀.subtype) J hmemJ
    have hfJ : Function.Surjective fJ := by
      rintro ⟨y, hy⟩
      rw [← hM₀J] at hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨z, hz⟩, rfl⟩
    let f : ↥M →* PQuot 3 J :=
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)).comp (fJ.comp e.symm.toMonoidHom)
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J) y
      obtain ⟨w, rfl⟩ := hfJ z
      refine ⟨e w, ?_⟩
      change (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) (fJ (e.symm (e w))) =
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) (fJ w)
      rw [MulEquiv.symm_apply_apply]
    have hker : f.ker ≤ Subgroup.center ↥M :=
      le_center_of_normal_of_isQuasisimple hcomp.2.2 (inferInstance : f.ker.Normal) (by
        intro htop
        have htriv : ∀ x : ↥M, f x = 1 := fun x =>
          MonoidHom.mem_ker.mp (by rw [htop]; exact Subgroup.mem_top x)
        haveI hnt : Nontrivial (PQuot 3 J) :=
          isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ)
        obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
        obtain ⟨x, hx⟩ := hf a
        obtain ⟨y, hy⟩ := hf b
        apply hab
        rw [← hx, ← hy, htriv x, htriv y])
    obtain ⟨φ⟩ := center_quot_equiv_of_surjective hcomp.2.2.1 f hf hker
    exact ⟨φ⟩
  · intro z hzM hzcen hz3 hzns
    have hzSL : z ∈ StatedSL d K := hMsl hzM
    let zs : ↥(StatedSL d K) := ⟨z, hzSL⟩
    obtain ⟨m, hmM₀, hmz⟩ := Subgroup.mem_map.mp hzM
    have hmem : LargeEvenProjMk (StatedSL d K) zs = LargeEvenProjMk (StatedSL d K) m :=
      congrArg _ (Subtype.ext hmz.symm)
    have hzJ : LargeEvenProjMk (StatedSL d K) zs ∈ J := by
      rw [← hM₀J]
      exact Subgroup.mem_map.mpr ⟨m, hmM₀, hmem.symm⟩
    refine ⟨LargeEvenProjMk (StatedSL d K) zs, hzJ, ?_, ?_, ?_⟩
    · intro j' hj'
      rw [← hM₀J] at hj'
      obtain ⟨m', hm'M₀, rfl⟩ := Subgroup.mem_map.mp hj'
      rw [← map_mul, ← map_mul]
      apply congrArg (LargeEvenProjMk (StatedSL d K))
      apply Subtype.ext
      show z * (m' : GL (Fin d) K) = (m' : GL (Fin d) K) * z
      exact hzcen (m' : GL (Fin d) K) (Subgroup.mem_map_of_mem _ hm'M₀)
    · have hzs3 : zs ^ 3 = 1 := by
        apply Subtype.ext
        simpa [zs] using hz3
      rw [← map_pow, hzs3, map_one]
    · intro hjeq
      obtain ⟨c, hc⟩ := (projMk_eq_iff zs 1).mp (by simpa using hjeq)
      have hc' : Matrix.GeneralLinearGroup.scalar (Fin d) c = (zs : GL (Fin d) K)⁻¹ := by
        simpa using hc
      apply hzns
      refine (mem_statedScalars_iff z).mpr ⟨c⁻¹, ?_⟩
      have hsc : Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ =
          (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := map_inv _ _
      rw [hsc, hc']
      simp [zs]

end CFSG.LocalAnalysis.GLTheoremA.K1419
