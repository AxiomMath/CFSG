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

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni Matrix
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup exists_glaPComponent_map_fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU hct_heldSU_eq_statedSU)

private theorem i167CU_lift_aux1 {K : Type} [Field K] {k d : ℕ} {τ : K ≃+* K}
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ k) (A : GL (Fin d) K)
    (hA : A ∈ heldGU d K τ hτ) (u : MulAut (LargeEvenProj (StatedSU d (2 ^ k) K)))
    (hu : ∀ h h' : ↥(StatedSU d (2 ^ k) K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ k) K) h) = LargeEvenProjMk (StatedSU d (2 ^ k) K) h') :
    ∀ (m : ℕ) (h h' : ↥(StatedSU d (2 ^ k) K)),
      (h' : GL (Fin d) K) = A ^ m * (h : GL (Fin d) K) * (A ^ m)⁻¹ →
      (u ^ m) (LargeEvenProjMk (StatedSU d (2 ^ k) K) h) =
        LargeEvenProjMk (StatedSU d (2 ^ k) K) h' := by
  have hH : heldSU d K τ hτ = StatedSU d (2 ^ k) K := hct_heldSU_eq_statedSU (a := d) hτQ
  have hnorm : ∀ g : GL (Fin d) K, g ∈ heldGU d K τ hτ →
      ∀ x ∈ StatedSU d (2 ^ k) K, g * x * g⁻¹ ∈ StatedSU d (2 ^ k) K := by
    intro g hg x hx
    rw [← hH] at hx ⊢
    exact heldSU_normal_in_heldGU hτ g hg x hx
  let cA : MulAut ↥(StatedSU d (2 ^ k) K) :=
    uniConjSub (StatedSU d (2 ^ k) K) A (hnorm A hA) (hnorm A⁻¹ (inv_mem hA))
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

private theorem i167CU_lift_aux2 {K : Type} [Field K] {k d p : ℕ} {τ : K ≃+* K}
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ k) (A : GL (Fin d) K)
    (hA : A ∈ heldGU d K τ hτ) (u : MulAut (LargeEvenProj (StatedSU d (2 ^ k) K)))
    (hu : ∀ h h' : ↥(StatedSU d (2 ^ k) K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ k) K) h) = LargeEvenProjMk (StatedSU d (2 ^ k) K) h')
    (hpow : u ^ p = 1) :
    ∀ g : GL (Fin d) K, g ∈ StatedSU d (2 ^ k) K → ∃ c : K,
      ((A ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        (g : Matrix (Fin d) (Fin d) K) *
        (((A ^ p)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        c • (g : Matrix (Fin d) (Fin d) K) := by
  have hH : heldSU d K τ hτ = StatedSU d (2 ^ k) K := hct_heldSU_eq_statedSU (a := d) hτQ
  have hnorm : ∀ g : GL (Fin d) K, g ∈ heldGU d K τ hτ →
      ∀ x ∈ StatedSU d (2 ^ k) K, g * x * g⁻¹ ∈ StatedSU d (2 ^ k) K := by
    intro g hg x hx
    rw [← hH] at hx ⊢
    exact heldSU_normal_in_heldGU hτ g hg x hx
  have hAp : A ^ p ∈ heldGU d K τ hτ := pow_mem hA p
  intro g hg
  let h : ↥(StatedSU d (2 ^ k) K) := ⟨g, hg⟩
  let h' : ↥(StatedSU d (2 ^ k) K) := ⟨A ^ p * g * (A ^ p)⁻¹, hnorm (A ^ p) hAp g hg⟩
  have hk : (h' : GL (Fin d) K) = A ^ p * (h : GL (Fin d) K) * (A ^ p)⁻¹ := rfl
  have hmk : LargeEvenProjMk (StatedSU d (2 ^ k) K) h' =
      LargeEvenProjMk (StatedSU d (2 ^ k) K) h := by
    have h1 := i167CU_lift_aux1 hτ hτQ A hA u hu p h h' hk
    rw [hpow] at h1
    simpa using h1.symm
  obtain ⟨c, hc⟩ := (projMk_eq_iff_uni (StatedSU d (2 ^ k) K) h' h).mp hmk
  have hh' : (h' : GL (Fin d) K) =
      (h : GL (Fin d) K) * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by
    rw [hc]
    group
  have hGL : A ^ p * g * (A ^ p)⁻¹ =
      g * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := hh'
  refine ⟨(c : K)⁻¹, ?_⟩
  have hM := congrArg (fun X : GL (Fin d) K => (X : Matrix (Fin d) (Fin d) K)) hGL
  simp only [Units.val_mul] at hM
  rw [hM, ← map_inv, val_scalar_gl, Units.val_inv_eq_inv_val, Matrix.mul_smul, Matrix.mul_one]

private theorem i167CU_lift_aux3 {K : Type} [Field K] [Finite K] {k d p : ℕ} {τ : K ≃+* K}
    (hp : p.Prime) (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ k)
    (hK : Nat.card K = (2 ^ k) ^ 2) (hd : 3 ≤ d) (hdQ : (d, 2 ^ k) ≠ (3, 2))
    (A : GL (Fin d) K) (hA : A ∈ heldGU d K τ hτ)
    (u : MulAut (LargeEvenProj (StatedSU d (2 ^ k) K)))
    (hu : ∀ h h' : ↥(StatedSU d (2 ^ k) K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ k) K) h) = LargeEvenProjMk (StatedSU d (2 ^ k) K) h')
    (hord : ((orderOf A : ℕ) : K) ≠ 0)
    (J : Subgroup (LargeEvenProj (StatedSU d (2 ^ k) K)))
    (hJ : GLAPComponent p (fixSubgroup u) J) :
    ∃ M₀ : Subgroup ↥(StatedSU d (2 ^ k) K),
      M₀.map (LargeEvenProjMk (StatedSU d (2 ^ k) K)) = J ∧
      CFSG.Open.IsComponentOf (M₀.map (StatedSU d (2 ^ k) K).subtype)
        (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ heldSU d K τ hτ) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hH : heldSU d K τ hτ = StatedSU d (2 ^ k) K := hct_heldSU_eq_statedSU (a := d) hτQ
  have hnorm : ∀ g : GL (Fin d) K, g ∈ heldGU d K τ hτ →
      ∀ x ∈ StatedSU d (2 ^ k) K, g * x * g⁻¹ ∈ StatedSU d (2 ^ k) K := by
    intro g hg x hx
    rw [← hH] at hx ⊢
    exact heldSU_normal_in_heldGU hτ g hg x hx
  let cA : MulAut ↥(StatedSU d (2 ^ k) K) :=
    uniConjSub (StatedSU d (2 ^ k) K) A (hnorm A hA) (hnorm A⁻¹ (inv_mem hA))
  obtain ⟨M₀, hM₀, hM₀J⟩ := exists_glaPComponent_map_fixSubgroup
    (LargeEvenProjMk (StatedSU d (2 ^ k) K)) (ker_projMk_uni_le_center (StatedSU d (2 ^ k) K))
    cA u (fun m => (hu m (cA m) rfl).symm) QuotientGroup.mk_surjective hp hJ
  have hMinj : Function.Injective (StatedSU d (2 ^ k) K).subtype := Subtype.val_injective
  have hM' : GLAPComponent p
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSU d (2 ^ k) K)
      (M₀.map (StatedSU d (2 ^ k) K).subtype) := by
    rw [← map_fixSubgroup_uniConjSub (StatedSU d (2 ^ k) K) A
      (hnorm A hA) (hnorm A⁻¹ (inv_mem hA))]
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff
      hp hMinj).mpr hM₀
  have hcomp : CFSG.Open.IsComponentOf (M₀.map (StatedSU d (2 ^ k) K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSU d (2 ^ k) K) :=
    uniPCompIsComp_holds K (2 ^ k) d p τ hτ hτQ hK hp A hA hord _ hM'
  have hcompH : CFSG.Open.IsComponentOf (M₀.map (StatedSU d (2 ^ k) K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ heldSU d K τ hτ) := by
    rw [hH]
    exact hcomp
  exact ⟨M₀, hM₀J, hcompH⟩

private theorem i167CU_lift_aux4 {K : Type} [Field K] {k d p : ℕ}
    {J : Subgroup (LargeEvenProj (StatedSU d (2 ^ k) K))}
    (M₀ : Subgroup ↥(StatedSU d (2 ^ k) K))
    (hM₀J : M₀.map (LargeEvenProjMk (StatedSU d (2 ^ k) K)) = J) :
    ∃ f : (M₀.map (StatedSU d (2 ^ k) K).subtype) →* PQuot p J, Function.Surjective f := by
  let M : Subgroup (GL (Fin d) K) := M₀.map (StatedSU d (2 ^ k) K).subtype
  let e : ↥M₀ ≃* ↥M := Subgroup.equivMapOfInjective M₀ (StatedSU d (2 ^ k) K).subtype Subtype.val_injective
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
  refine ⟨(QuotientGroup.mk' (GLAPPrimeCore p ↥J)).comp (fJ.comp e.symm.toMonoidHom), ?_⟩
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥J) y
  obtain ⟨w, rfl⟩ := hfJ z
  refine ⟨e w, ?_⟩
  change (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) (fJ (e.symm (e w))) =
    (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) (fJ w)
  rw [MulEquiv.symm_apply_apply]

private theorem i167CU_lift_aux5 {K : Type} [Field K] {k d p : ℕ} {τ : K ≃+* K}
    (hτ : ∀ x, τ (τ x) = x) (A : GL (Fin d) K)
    {J : Subgroup (LargeEvenProj (StatedSU d (2 ^ k) K))}
    (hQ : CFSG.Open.IsQuasisimple (PQuot p J))
    (M₀ : Subgroup ↥(StatedSU d (2 ^ k) K))
    (hcompH : CFSG.Open.IsComponentOf (M₀.map (StatedSU d (2 ^ k) K).subtype)
        (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ heldSU d K τ hτ))
    (f : (M₀.map (StatedSU d (2 ^ k) K).subtype) →* PQuot p J)
    (hf : Function.Surjective f) :
    Nonempty (PSimple p J ≃* (M₀.map (StatedSU d (2 ^ k) K).subtype) ⧸
        Subgroup.center (M₀.map (StatedSU d (2 ^ k) K).subtype)) := by
  have hker : f.ker ≤ Subgroup.center ↥(M₀.map (StatedSU d (2 ^ k) K).subtype) :=
    le_center_of_normal_of_isQuasisimple hcompH.2.2 (inferInstance : f.ker.Normal) (by
      intro htop
      have htriv : ∀ x : ↥(M₀.map (StatedSU d (2 ^ k) K).subtype), f x = 1 := fun x =>
        MonoidHom.mem_ker.mp (by rw [htop]; exact Subgroup.mem_top x)
      haveI hnt : Nontrivial (PQuot p J) := isQuasisimple_nontrivial hQ
      obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
      obtain ⟨x, hx⟩ := hf a
      obtain ⟨y, hy⟩ := hf b
      apply hab
      rw [← hx, ← hy, htriv x, htriv y])
  obtain ⟨φ⟩ := center_quot_equiv_of_surjective hcompH.2.2.1 f hf hker
  exact ⟨φ⟩

theorem i167CU_lift {K : Type} [Field K] [Finite K] {k d p : ℕ} {τ : K ≃+* K} (hp : p.Prime) (hp2 : p ≠ 2)
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ k) (hK : Nat.card K = (2 ^ k) ^ 2)
    (hd : 3 ≤ d) (hdQ : (d, 2 ^ k) ≠ (3, 2)) (A : GL (Fin d) K) (hA : A ∈ heldGU d K τ hτ)
    (u : MulAut (LargeEvenProj (StatedSU d (2 ^ k) K)))
    (hu : ∀ h h' : ↥(StatedSU d (2 ^ k) K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ k) K) h) = LargeEvenProjMk (StatedSU d (2 ^ k) K) h')
    (hpow : u ^ p = 1) (J : Subgroup (LargeEvenProj (StatedSU d (2 ^ k) K)))
    (hJ : GLAPComponent p (fixSubgroup u) J) :
    ((orderOf A : ℕ) : K) ≠ 0 ∧ ∃ M : Subgroup (GL (Fin d) K),
      CFSG.Open.IsComponentOf M
        (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ heldSU d K τ hτ) ∧
      Nonempty (PSimple p J ≃* M ⧸ Subgroup.center M) := by
  haveI : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) = 0 := by
    have hcard : Fintype.card K = 2 ^ (2 * k) := by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, Nat.mul_comm]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * k) hcard
    exact CharP.cast_eq_zero K 2
  have hconjB := i167CU_lift_aux2 hτ hτQ A hA u hu hpow
  obtain ⟨c0, hc0⟩ := uniScalar_holds K (2 ^ k) d τ hτ hτQ hK hd hdQ (A ^ p) hconjB
  have hodd : Odd (orderOf A) :=
    odd_orderOf_of_pow_scalar h2 (by omega : 1 ≤ d) A (hp.odd_of_ne_two hp2) hc0
  have hord : ((orderOf A : ℕ) : K) ≠ 0 :=
    cast_orderOf_ne_zero_of_odd h2 A hodd
  obtain ⟨M₀, hM₀J, hcompH⟩ := i167CU_lift_aux3 hp hτ hτQ hK hd hdQ A hA u hu hord J hJ
  refine ⟨hord, M₀.map (StatedSU d (2 ^ k) K).subtype, hcompH, ?_⟩
  obtain ⟨f, hf⟩ := i167CU_lift_aux4 M₀ hM₀J
  exact i167CU_lift_aux5 hτ A (isQuasisimple_pQuot_of_glaPComponent hp hJ) M₀ hcompH f hf

end CFSG.LocalAnalysis.GLTheoremA.I167

end
