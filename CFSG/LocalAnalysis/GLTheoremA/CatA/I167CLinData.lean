module

import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinRed
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA Matrix
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamLin InnDiagKind)

private theorem i167CLin_data_aux1 {S : Type} [Group S] {d : ℕ} {K : Type} [Field K]
    {α : MulAut S} {A : GL (Fin d) K} {u : MulAut (LargeEvenProj (StatedSL d K))}
    {e : S ≃* LargeEvenProj (StatedSL d K)}
    (hA : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (hαu : ∀ l : S, e (α l) = u (e l)) (hα1 : α ≠ 1) :
    ∀ c : K, (A : Matrix (Fin d) (Fin d) K) ≠ c • (1 : Matrix (Fin d) (Fin d) K) := by
  intro c hc
  have hAcenter : A ∈ Subgroup.center (GL (Fin d) K) := by
    rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    exact ⟨c, by rw [hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
  have hconj : ∀ h : ↥(StatedSL d K), (h : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ := by
    intro h
    have hcomm : (h : GL (Fin d) K) * A = A * (h : GL (Fin d) K) :=
      Subgroup.mem_center_iff.mp hAcenter (h : GL (Fin d) K)
    rw [← hcomm]
    group
  have hu1 : u = 1 := by
    ext x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
      (N := (LargeEvenScalars (Fin d) K).subgroupOf (StatedSL d K)) x
    simpa using hA h h (hconj h)
  apply hα1
  ext l
  have h := hαu l
  rw [hu1, MulAut.one_apply] at h
  simpa using e.injective h

private theorem i167CLin_data_aux2 {S : Type} [Group S] {d : ℕ} {K : Type} [Field K]
    {H : Subgroup (GL (Fin d) K)} (hH : H = StatedSL d K) (hcen : Subgroup.center S = ⊥)
    {α : MulAut S} (θ : S ⧸ Subgroup.center S ≃* LargeEvenProj H) (u : MulAut (LargeEvenProj H))
    (A : GL (Fin d) K)
    (hA : ∀ h h' : ↥H, (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk H h) = LargeEvenProjMk H h')
    (hind : ∀ l l' : S, l' = α l → u (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l'))
    (hα1 : α ≠ 1) :
    ∃ (A' : GL (Fin d) K) (e : S ≃* LargeEvenProj (StatedSL d K)),
      (∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A' * (h : GL (Fin d) K) * A'⁻¹ →
        MulAut.congr e α (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h') ∧
      (∀ c : K, (A' : Matrix (Fin d) (Fin d) K) ≠ c • (1 : Matrix (Fin d) (Fin d) K)) := by
  subst hH
  obtain ⟨A', u', e', hα', hg'⟩ :=
    Y10GInnLin.linear_marking_of_eq (H := StatedSL d K) rfl hcen θ u A hA hind
  refine ⟨A', e', ?_, i167CLin_data_aux1 hg' hα' hα1⟩
  have hMEq : MulAut.congr e' α = u' := by
    ext r
    have h1 := hα' (e'.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  intro h h' hh
  rw [hMEq]
  exact hg' h h' hh

private theorem i167CLin_data_aux3 {K : Type} [Field K] [Finite K] {n : ℕ}
    (hcard : Nat.card K = 2 ^ n) : (2 : K) = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨q, hq, m, hqp, hqcard⟩ := FiniteField.card' K
  rw [Nat.card_eq_fintype_card, hqcard] at hcard
  have hdvd : q ∣ 2 ^ n := by
    rw [← hcard]
    exact dvd_pow_self q (PNat.ne_zero m)
  have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
  subst hq2
  exact_mod_cast CharP.cast_eq_zero K 2

private theorem i167CLin_data_aux4 {S : Type} [Group S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labK α) : IsSimpleGroup S := by
  obtain ⟨-, -, -, R, hgrp, I, F, θ, hR, -, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists hin
  letI := hgrp
  haveI : IsSimpleGroup R := hR
  exact MulEquiv.isSimpleGroup
    (((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans θ)

private theorem i167CLin_data_aux5 {S : Type} [Group S] {d : ℕ} {K : Type} [Field K] [Finite K]
    {labK : GLALabel} {α : MulAut S} (hcen : Subgroup.center S = ⊥) (hα1 : α ≠ 1)
    (H : Subgroup (GL (Fin d) K)) (hH : H = StatedSL d K)
    (hd_eq : d = (canonLabel labK).rank + 1) (hd2 : 2 ≤ d)
    (hcardcanon : Nat.card K = 2 ^ (canonLabel labK).n)
    (θ : S ⧸ Subgroup.center S ≃* LargeEvenProj H) (u : MulAut (LargeEvenProj H))
    (A : GL (Fin d) K)
    (hA : ∀ h h' : ↥H, (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk H h) = LargeEvenProjMk H h')
    (hind : ∀ l l' : S, l' = α l → u (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l'))
    (hsimpleS : IsSimpleGroup S) :
    ∃ (d : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (A : GL (Fin d) K)
      (e : S ≃* LargeEvenProj (StatedSL d K)),
      d = (canonLabel labK).rank + 1 ∧ 2 ≤ d ∧ (2 : K) = 0 ∧
      Nat.card K = 2 ^ (canonLabel labK).n ∧
      (∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
        MulAut.congr e α (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h') ∧
      (∀ c : K, (A : Matrix (Fin d) (Fin d) K) ≠ c • (1 : Matrix (Fin d) (Fin d) K)) ∧
      IsSimpleGroup S := by
  obtain ⟨A', e', hg', hns'⟩ := i167CLin_data_aux2 hH hcen θ u A hA hind hα1
  exact ⟨d, K, inferInstance, inferInstance, A', e', hd_eq, hd2,
    i167CLin_data_aux3 hcardcanon, hcardcanon, hg', hns', hsimpleS⟩

theorem i167CLin_data {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hFam : FamLin labK) (hα1 : α ≠ 1) (hin : InnDiagKind S labK α) :
    ∃ (d : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (A : GL (Fin d) K)
      (e : S ≃* LargeEvenProj (StatedSL d K)),
      d = (canonLabel labK).rank + 1 ∧ 2 ≤ d ∧ (2 : K) = 0 ∧ Nat.card K = 2 ^ (canonLabel labK).n ∧
      (∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
        MulAut.congr e α (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h') ∧
      (∀ c : K, (A : Matrix (Fin d) (Fin d) K) ≠ c • (1 : Matrix (Fin d) (Fin d) K)) ∧ IsSimpleGroup S := by
  have hsimpleS := i167CLin_data_aux4 hcen hin
  unfold InnDiagKind at hin
  obtain ⟨-, lab', hlab', hraw⟩ := hin
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  rcases hFam with ht | ⟨ht, hr⟩ | ⟨ht, hr⟩
  · unfold LargeEvenRawDatum at hraw
    simp only [ht] at hraw
    unfold LargeEvenRecipeLinear at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    obtain ⟨A, -, hA⟩ := hu
    refine i167CLin_data_aux5 hcen hα1 _ (largeEvenSLGroup_eq_statedSL (K := K) (labK.rank + 1))
      ?_ ?_ ?_ θ u A hA hind hsimpleS
    · simp [canonLabel, ht]
    · have h1 := hlab'
      simp [LargeEvenInLambda2, ht] at h1
      omega
    · rw [show (canonLabel labK).n = labK.n by simp [canonLabel, ht]]; exact hcard
  · unfold LargeEvenRawDatum at hraw
    simp only [ht, hr, if_true] at hraw
    unfold LargeEvenRecipeLinear at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    obtain ⟨A, -, hA⟩ := hu
    refine i167CLin_data_aux5 hcen hα1 _ (largeEvenSLGroup_eq_statedSL (K := K) 4)
      ?_ ?_ ?_ θ u A hA hind hsimpleS
    · simp [canonLabel, ht, hr]
    · norm_num
    · rw [show (canonLabel labK).n = labK.n by simp [canonLabel, ht, hr]]; exact hcard
  · unfold LargeEvenRawDatum at hraw
    simp only [ht, hr, if_true] at hraw
    unfold LargeEvenRecipeLinear at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    obtain ⟨A, -, hA⟩ := hu
    refine i167CLin_data_aux5 hcen hα1 _ (largeEvenSLGroup_eq_statedSL (K := K) 2)
      ?_ ?_ ?_ θ u A hA hind hsimpleS
    · simp [canonLabel, ht, hr]
    · norm_num
    · rw [show (canonLabel labK).n = 2 * labK.n by simp [canonLabel, ht, hr], hcard, ← pow_mul, mul_comm]

theorem i167CLin_normalize {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) {d : ℕ} (hd : 1 ≤ d) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1) (A : GL (Fin d) K)
    (u : MulAut (LargeEvenProj (StatedSL d K)))
    (hu : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (hpow : u ^ p = 1) (hAns : ∀ c : K, (A : Matrix (Fin d) (Fin d) K) ≠ c • (1 : Matrix (Fin d) (Fin d) K)) :
    ∃ g : GL (Fin d) K, g ^ p = 1 ∧
      (∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = g * (h : GL (Fin d) K) * g⁻¹ →
        u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h') ∧
      (∀ c : K, (g : Matrix (Fin d) (Fin d) K) ≠ c • (1 : Matrix (Fin d) (Fin d) K)) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨c, hc⟩ := Y10GInnLin.isScalar_of_pow_trivial h2 A p u hu hpow
  have hc0 : c ≠ 0 := by
    intro h0
    have hu1 : ((A ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (((A ^ p)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv (A ^ p)
    rw [hc, h0, zero_smul, zero_mul] at hu1
    exact one_ne_zero hu1.symm
  let z : Kˣ := Units.mk0 c hc0
  have hz : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) z :=
    Units.ext (by rw [Y10GInnLin.val_scalar_gl]; exact hc)
  have hcop : (Nat.card Kˣ).Coprime p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (by rwa [Nat.card_units])).symm
  obtain ⟨w, hw⟩ := (Nat.Coprime.pow_left_bijective hcop).2 z
  refine ⟨A * Matrix.GeneralLinearGroup.scalar (Fin d) w⁻¹, ?_, ?_, ?_⟩
  · have hcomm : Commute A (Matrix.GeneralLinearGroup.scalar (Fin d) w⁻¹) :=
      ((commute_iff_eq _ _).mpr (Matrix.GeneralLinearGroup.scalar_commute w⁻¹ A)).symm
    rw [hcomm.mul_pow, hz]
    simp only [← map_pow, ← map_mul, ← hw, inv_pow, mul_inv_cancel, map_one]
  · intro h h' hh
    refine hu h h' ?_
    rw [hh, mul_assoc A, Matrix.GeneralLinearGroup.scalar_commute w⁻¹ (h : GL (Fin d) K)]
    group
  · intro c₀ hc₀
    have hscenter : Matrix.GeneralLinearGroup.scalar (Fin d) w⁻¹ ∈
        Subgroup.center (GL (Fin d) K) := by
      rw [Subgroup.mem_center_iff]
      exact fun y => (Matrix.GeneralLinearGroup.scalar_commute w⁻¹ y).symm
    have hgcenter : A * Matrix.GeneralLinearGroup.scalar (Fin d) w⁻¹ ∈
        Subgroup.center (GL (Fin d) K) := by
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      exact ⟨c₀, by rw [hc₀, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
    have hAcenter : A ∈ Subgroup.center (GL (Fin d) K) := by
      have hAeq : A = (A * Matrix.GeneralLinearGroup.scalar (Fin d) w⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) w⁻¹)⁻¹ := by group
      rw [hAeq]
      exact Subgroup.mul_mem _ hgcenter (Subgroup.inv_mem _ hscenter)
    obtain ⟨a, ha⟩ := (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar).mp hAcenter
    exact hAns a (by rw [ha.symm, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal])

private theorem i167CLin_lift_aux1 {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) {d : ℕ}
    (hd : 1 ≤ d) (A : GL (Fin d) K) (u : MulAut (LargeEvenProj (StatedSL d K)))
    (hu : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpow : u ^ p = 1)
    (J' : Subgroup (LargeEvenProj (StatedSL d K))) (hJ' : GLAPComponent p (fixSubgroup u) J') :
    ∃ M₀ : Subgroup (StatedSL d K),
      M₀.map (LargeEvenProjMk (StatedSL d K)) = J' ∧
      CFSG.Open.IsComponentOf (M₀.map (StatedSL d K).subtype)
        (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSL d K) ∧
      ((orderOf A : ℕ) : K) ≠ 0 := by
  obtain ⟨c, hc⟩ := Y10GInnLin.isScalar_of_pow_trivial h2 A p u hu hpow
  have hodd : Odd (orderOf A) :=
    Y10GInnLin.odd_orderOf_of_pow_scalar h2 hd A (hp.odd_of_ne_two hp2) hc
  have hord : ((orderOf A : ℕ) : K) ≠ 0 := Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 A hodd
  obtain ⟨M₀, hM₀, hM₀J⟩ := HardMathSupport.Solomon.Coordinator.exists_glaPComponent_map_fixSubgroup
    (LargeEvenProjMk (StatedSL d K)) Y10GInnLin.ker_projMk_le_center (Y10GInnLin.conjSL A) u
    (fun k => (hu k (Y10GInnLin.conjSL A k) rfl).symm) (QuotientGroup.mk_surjective) hp hJ'
  have hMinj : Function.Injective (StatedSL d K).subtype := Subtype.val_injective
  have hM' : GLAPComponent p
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSL d K)
      (M₀.map (StatedSL d K).subtype) := by
    rw [← Y10GInnLin.map_fixSubgroup_conjSL A]
    exact (Y10F.glaPComponent_map_iff hp hMinj).mpr hM₀
  exact ⟨M₀, hM₀J,
    Y10GInnLin.LinPCompIsComp_holds K d p hp A hord (M₀.map (StatedSL d K).subtype) hM', hord⟩

private theorem i167CLin_lift_aux2 {K : Type} [Field K] [Finite K] {d : ℕ} {p : ℕ} (hp : p.Prime)
    {A : GL (Fin d) K} {M₀ : Subgroup (StatedSL d K)}
    {X : Subgroup (LargeEvenProj (StatedSL d K))} {J' : Subgroup (LargeEvenProj (StatedSL d K))}
    (hM₀J : M₀.map (LargeEvenProjMk (StatedSL d K)) = J')
    (hJ' : GLAPComponent p X J')
    (hcomp : CFSG.Open.IsComponentOf (M₀.map (StatedSL d K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSL d K)) :
    Nonempty (PSimple p J' ≃* (M₀.map (StatedSL d K).subtype) ⧸
      Subgroup.center (M₀.map (StatedSL d K).subtype)) := by
  let M : Subgroup (GL (Fin d) K) := M₀.map (StatedSL d K).subtype
  change Nonempty (PSimple p J' ≃* M ⧸ Subgroup.center M)
  let e : ↥M₀ ≃* ↥M := Subgroup.equivMapOfInjective M₀ (StatedSL d K).subtype Subtype.val_injective
  have hmemJ : ∀ x : ↥M₀, LargeEvenProjMk (StatedSL d K) (x : ↥(StatedSL d K)) ∈ J' := fun x => by
    rw [← hM₀J]
    exact Subgroup.mem_map_of_mem _ x.2
  let fJ : ↥M₀ →* ↥J' :=
    MonoidHom.codRestrict ((LargeEvenProjMk (StatedSL d K)).comp M₀.subtype) J' hmemJ
  have hfJ : Function.Surjective fJ := by
    rintro ⟨y, hy⟩
    rw [← hM₀J] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, rfl⟩
  let f : ↥M →* PQuot p J' :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥J')).comp (fJ.comp e.symm.toMonoidHom)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥J') y
    obtain ⟨w, rfl⟩ := hfJ z
    refine ⟨e w, ?_⟩
    change (QuotientGroup.mk' (GLAPPrimeCore p ↥J')) (fJ (e.symm (e w))) =
      (QuotientGroup.mk' (GLAPPrimeCore p ↥J')) (fJ w)
    rw [MulEquiv.symm_apply_apply]
  have hker : f.ker ≤ Subgroup.center ↥M :=
    le_center_of_normal_of_isQuasisimple (by simpa [M] using hcomp.2.2)
      (inferInstance : f.ker.Normal) (by
        intro htop
        have htriv : ∀ x : ↥M, f x = 1 := fun x =>
          MonoidHom.mem_ker.mp (by rw [htop]; exact Subgroup.mem_top x)
        haveI hnt : Nontrivial (PQuot p J') :=
          isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent hp hJ')
        obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
        obtain ⟨x, hx⟩ := hf a
        obtain ⟨y, hy⟩ := hf b
        apply hab
        rw [← hx, ← hy, htriv x, htriv y])
  exact Y10GInnLin.center_quot_equiv_of_surjective (by simpa [M] using hcomp.2.2.1) f hf hker

theorem i167CLin_lift {S : Type} [Group S] [Finite S] {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) {d : ℕ}
    (hd : 1 ≤ d) (A : GL (Fin d) K) (e : S ≃* LargeEvenProj (StatedSL d K)) {α : MulAut S} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hgr : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      MulAut.congr e α (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (hpow : α ^ p = 1) {J : Subgroup S} (hJ : GLAPComponent p (fixSubgroup α) J) :
    ∃ M : Subgroup (GL (Fin d) K),
      CFSG.Open.IsComponentOf M (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSL d K) ∧
      ((orderOf A : ℕ) : K) ≠ 0 ∧ Nonempty (PSimple p J ≃* M ⧸ Subgroup.center M) ∧
      (∀ x ∈ J, ∃ m ∈ M, ∃ hm : m ∈ StatedSL d K, e x = LargeEvenProjMk (StatedSL d K) ⟨m, hm⟩) := by
  let u : MulAut (LargeEvenProj (StatedSL d K)) := MulAut.congr e α
  have hupow : u ^ p = 1 := by
    change MulAut.congr e α ^ p = 1
    rw [← map_pow, hpow, map_one]
  have hJ' : GLAPComponent p (fixSubgroup u) (J.map e.toMonoidHom) := by
    change GLAPComponent p (fixSubgroup (MulAut.congr e α)) (J.map e.toMonoidHom)
    rw [← Y10F.fixSubgroup_map_congr e α]
    exact (Y10F.glaPComponent_map_iff hp e.injective).2 hJ
  obtain ⟨M₀, hM₀J, hcomp, hord⟩ :=
    i167CLin_lift_aux1 h2 hd A u hgr hp hp2 hupow (J.map e.toMonoidHom) hJ'
  obtain ⟨φ⟩ := i167CLin_lift_aux2 hp hM₀J hJ' hcomp
  have hN : ¬ p ∣ Nat.card (e.toMonoidHom.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective, Subgroup.card_bot]
    exact hp.not_dvd_one
  obtain ⟨e1⟩ := nonempty_pQuot_equiv_map hp hN J
  obtain ⟨e2⟩ : Nonempty (PSimple p J ≃* PSimple p (J.map e.toMonoidHom)) :=
    ⟨QuotientGroup.congr _ _ e1 (Subgroup.map_center_eq e1)⟩
  refine ⟨M₀.map (StatedSL d K).subtype, hcomp, hord, ⟨e2.trans φ⟩, ?_⟩
  intro x hx
  have hx' : e x ∈ J.map e.toMonoidHom := by
    simpa using Subgroup.mem_map_of_mem e.toMonoidHom hx
  rw [← hM₀J] at hx'
  obtain ⟨m, hmM₀, hmx⟩ := Subgroup.mem_map.mp hx'
  exact ⟨(m : GL (Fin d) K), Subgroup.mem_map_of_mem _ hmM₀, m.2, hmx.symm⟩

end CFSG.LocalAnalysis.GLTheoremA.I167

end
