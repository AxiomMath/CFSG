module

import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni Matrix
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup exists_glaPComponent_map_fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU hct_heldSU_eq_statedSU)

theorem k1419ClsUniLift {K : Type} [Field K] [Finite K] {k d : ℕ} {τ : K ≃+* K}
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ k) (hK : Nat.card K = (2 ^ k) ^ 2)
    (hd : 3 ≤ d) (hdQ : (d, 2 ^ k) ≠ (3, 2)) (A : GL (Fin d) K) (hA : A ∈ heldGU d K τ hτ)
    (u : MulAut (LargeEvenProj (StatedSU d (2 ^ k) K)))
    (hu : ∀ h h' : ↥(StatedSU d (2 ^ k) K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ k) K) h) = LargeEvenProjMk (StatedSU d (2 ^ k) K) h')
    (hpow : u ^ 3 = 1) (J : Subgroup (LargeEvenProj (StatedSU d (2 ^ k) K)))
    (hJ : GLAPComponent 3 (fixSubgroup u) J) :
    (∃ c : K, ((A ^ 3 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      c • (1 : Matrix (Fin d) (Fin d) K)) ∧
    ∃ M : Subgroup (GL (Fin d) K),
      CFSG.Open.IsComponentOf M
        (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ heldSU d K τ hτ) ∧
      Nonempty (PSimple 3 J ≃* M ⧸ Subgroup.center M) ∧
      (∀ z : GL (Fin d) K, z ∈ M → (∀ y ∈ M, z * y = y * z) → z ^ 3 = 1 →
        z ∉ StatedScalars (Fin d) K →
          ∃ j ∈ J, (∀ j' ∈ J, j * j' = j' * j) ∧ j ^ 3 = 1 ∧ j ≠ 1) := by
  haveI : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) = 0 := by
    have hcard : Fintype.card K = 2 ^ (2 * k) := by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, Nat.mul_comm]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * k) hcard
    exact CharP.cast_eq_zero K 2
  have hH : heldSU d K τ hτ = StatedSU d (2 ^ k) K :=
    hct_heldSU_eq_statedSU (a := d) hτQ
  have hnorm : ∀ g : GL (Fin d) K, g ∈ heldGU d K τ hτ →
      ∀ x ∈ StatedSU d (2 ^ k) K, g * x * g⁻¹ ∈ StatedSU d (2 ^ k) K := by
    intro g hg x hx
    rw [← hH] at hx ⊢
    exact heldSU_normal_in_heldGU hτ g hg x hx
  let cA : MulAut ↥(StatedSU d (2 ^ k) K) :=
    uniConjSub (StatedSU d (2 ^ k) K) A (hnorm A hA) (hnorm A⁻¹ (inv_mem hA))
  have hpowk : ∀ (m : ℕ) (h h' : ↥(StatedSU d (2 ^ k) K)),
      (h' : GL (Fin d) K) = A ^ m * (h : GL (Fin d) K) * (A ^ m)⁻¹ →
      (u ^ m) (LargeEvenProjMk (StatedSU d (2 ^ k) K) h) =
        LargeEvenProjMk (StatedSU d (2 ^ k) K) h' := by
    intro m
    induction m with
    | zero =>
      intro h h' hk
      have : h' = h := by
        apply Subtype.ext
        simpa using hk
      subst this
      simp
    | succ m ih =>
      intro h h' hk
      have step1 : u (LargeEvenProjMk (StatedSU d (2 ^ k) K) h) =
          LargeEvenProjMk (StatedSU d (2 ^ k) K) (cA h) := hu h (cA h) rfl
      have step2 := ih (cA h) h' (by
        rw [hk, uniConjSub_apply_val, pow_succ]
        group)
      rw [pow_succ, MulAut.mul_apply, step1, step2]
  have hAp : A ^ 3 ∈ heldGU d K τ hτ := pow_mem hA 3
  have hconjB : ∀ g : GL (Fin d) K, g ∈ StatedSU d (2 ^ k) K → ∃ c : K,
      ((A ^ 3 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        (g : Matrix (Fin d) (Fin d) K) *
        (((A ^ 3)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        c • (g : Matrix (Fin d) (Fin d) K) := by
    intro g hg
    let h : ↥(StatedSU d (2 ^ k) K) := ⟨g, hg⟩
    let h' : ↥(StatedSU d (2 ^ k) K) := ⟨A ^ 3 * g * (A ^ 3)⁻¹, hnorm (A ^ 3) hAp g hg⟩
    have hk : (h' : GL (Fin d) K) = A ^ 3 * (h : GL (Fin d) K) * (A ^ 3)⁻¹ := rfl
    have hmk : LargeEvenProjMk (StatedSU d (2 ^ k) K) h' =
        LargeEvenProjMk (StatedSU d (2 ^ k) K) h := by
      have h1 := hpowk 3 h h' hk
      rw [hpow] at h1
      simpa using h1.symm
    obtain ⟨c, hc⟩ := (projMk_eq_iff_uni (StatedSU d (2 ^ k) K) h' h).mp hmk
    have hh' : (h' : GL (Fin d) K) =
        (h : GL (Fin d) K) * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by
      rw [hc]
      group
    have hGL : A ^ 3 * g * (A ^ 3)⁻¹ =
        g * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := hh'
    refine ⟨(c : K)⁻¹, ?_⟩
    have hM := congrArg (fun X : GL (Fin d) K => (X : Matrix (Fin d) (Fin d) K)) hGL
    simp only [Units.val_mul] at hM
    rw [hM, ← map_inv, val_scalar_gl, Units.val_inv_eq_inv_val, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨c0, hc0⟩ := uniScalar_holds K (2 ^ k) d τ hτ hτQ hK hd hdQ (A ^ 3) hconjB
  have hodd : Odd (orderOf A) :=
    odd_orderOf_of_pow_scalar h2 (by omega : 1 ≤ d) A
      (Nat.prime_three.odd_of_ne_two (by norm_num)) hc0
  have hord : ((orderOf A : ℕ) : K) ≠ 0 :=
    cast_orderOf_ne_zero_of_odd h2 A hodd
  obtain ⟨M₀, hM₀, hM₀J⟩ := exists_glaPComponent_map_fixSubgroup
    (LargeEvenProjMk (StatedSU d (2 ^ k) K)) (ker_projMk_uni_le_center (StatedSU d (2 ^ k) K))
    cA u (fun m => (hu m (cA m) rfl).symm) QuotientGroup.mk_surjective Nat.prime_three hJ
  have hMinj : Function.Injective (StatedSU d (2 ^ k) K).subtype := Subtype.val_injective
  have hM' : GLAPComponent 3
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSU d (2 ^ k) K)
      (M₀.map (StatedSU d (2 ^ k) K).subtype) := by
    rw [← map_fixSubgroup_uniConjSub (StatedSU d (2 ^ k) K) A
      (hnorm A hA) (hnorm A⁻¹ (inv_mem hA))]
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff
      Nat.prime_three hMinj).mpr hM₀
  have hcomp : CFSG.Open.IsComponentOf (M₀.map (StatedSU d (2 ^ k) K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSU d (2 ^ k) K) :=
    uniPCompIsComp_holds K (2 ^ k) d 3 τ hτ hτQ hK Nat.prime_three A hA hord _ hM'
  have hcompH : CFSG.Open.IsComponentOf (M₀.map (StatedSU d (2 ^ k) K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ heldSU d K τ hτ) := by
    rw [hH]
    exact hcomp
  let M : Subgroup (GL (Fin d) K) := M₀.map (StatedSU d (2 ^ k) K).subtype
  refine ⟨⟨c0, hc0⟩, M, hcompH, ?_, ?_⟩
  · let e : ↥M₀ ≃* ↥M := Subgroup.equivMapOfInjective M₀ (StatedSU d (2 ^ k) K).subtype hMinj
    have hmemJ : ∀ x : ↥M₀,
        LargeEvenProjMk (StatedSU d (2 ^ k) K) (x : ↥(StatedSU d (2 ^ k) K)) ∈ J := fun x => by
      rw [← hM₀J]
      exact Subgroup.mem_map_of_mem _ x.2
    let fJ : ↥M₀ →* ↥J :=
      MonoidHom.codRestrict ((LargeEvenProjMk (StatedSU d (2 ^ k) K)).comp M₀.subtype) J hmemJ
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
    obtain ⟨m, hmM₀, hmz⟩ := Subgroup.mem_map.mp hzM
    have hzSU : z ∈ StatedSU d (2 ^ k) K := by
      rw [← hmz]
      exact m.2
    let zs : ↥(StatedSU d (2 ^ k) K) := ⟨z, hzSU⟩
    have hmem : LargeEvenProjMk (StatedSU d (2 ^ k) K) zs =
        LargeEvenProjMk (StatedSU d (2 ^ k) K) m := congrArg _ (Subtype.ext hmz.symm)
    have hzJ : LargeEvenProjMk (StatedSU d (2 ^ k) K) zs ∈ J := by
      rw [← hM₀J]
      exact Subgroup.mem_map.mpr ⟨m, hmM₀, hmem.symm⟩
    refine ⟨LargeEvenProjMk (StatedSU d (2 ^ k) K) zs, hzJ, ?_, ?_, ?_⟩
    · intro j' hj'
      rw [← hM₀J] at hj'
      obtain ⟨m', hm'M₀, rfl⟩ := Subgroup.mem_map.mp hj'
      rw [← map_mul, ← map_mul]
      apply congrArg (LargeEvenProjMk (StatedSU d (2 ^ k) K))
      apply Subtype.ext
      show z * (m' : GL (Fin d) K) = (m' : GL (Fin d) K) * z
      exact hzcen (m' : GL (Fin d) K) (Subgroup.mem_map_of_mem _ hm'M₀)
    · have hzs3 : zs ^ 3 = 1 := by
        apply Subtype.ext
        simpa [zs] using hz3
      rw [← map_pow, hzs3, map_one]
    · intro hjeq
      obtain ⟨c, hc⟩ :=
        (projMk_eq_iff_uni (StatedSU d (2 ^ k) K) zs 1).mp (by simpa using hjeq)
      have hc' : Matrix.GeneralLinearGroup.scalar (Fin d) c = (zs : GL (Fin d) K)⁻¹ := by
        simpa using hc
      apply hzns
      refine (mem_statedScalars_iff z).mpr ⟨c⁻¹, ?_⟩
      have hsc : Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ =
          (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := map_inv _ _
      rw [hsc, hc']
      simp [zs]

end CFSG.LocalAnalysis.GLTheoremA.K1419
