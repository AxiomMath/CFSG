module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInUniTransPow

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Open.StatedAPI CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SemisimpleCentralizers.Held
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.StandardType.TableB
open scoped commutatorElement

private theorem isComponentOf_centralizer_gu_normal {Q n : ℕ} {L : Type} [Field L] [Finite L]
    {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q)
    (hL : Nat.card L = Q ^ 2) (s : GL (Fin n) L) (hs : s ∈ heldGU n L τ hτ)
    (hord : (orderOf s : L) ≠ 0) (J : Subgroup (GL (Fin n) L))
    (hJ : IsComponentOf J (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ)) :
    (J.subgroupOf (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ)).Normal := by
  classical
  obtain ⟨r, H, hgrp, hfinH, hblk, ⟨ε⟩⟩ := centralizerDecomposition_gu hτ hτQ hL s hs hord
  have hbl : ∀ k, ∃ S : Subgroup (H k), (∀ x y : H k, ⁅x, y⁆ ∈ S) ∧
      (∀ X : Subgroup S, IsComponentOf X ⊤ → X = ⊤) ∧ S.Normal ∧
      ((∃ (a d : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ : M ≃+* M)
          (hτ : ∀ x, τ (τ x) = x),
          (∀ x : M, τ x = x ^ (Q ^ d)) ∧ Nat.card M = (Q ^ d) ^ 2 ∧
            Nonempty (S ≃* heldSU a M τ hτ)) ∨
        (∃ (b e : ℕ) (M : Type) (_ : Field M) (_ : Finite M), Nat.card M = Q ^ (2 * e) ∧
          Nonempty (S ≃* StatedSL b M))) :=
    fun k => exists_blockSub_sized SUComponentsTrivial_holds SLComponentsTrivial_holds (hblk k)
  choose S hS hSt hSn hty using hbl
  let C : Subgroup (GL (Fin n) L) :=
    Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ
  let ψ : (∀ k, H k) →* GL (Fin n) L := C.subtype.comp ε.symm.toMonoidHom
  have hψinj : Function.Injective ψ := fun x y h => ε.symm.injective (Subtype.ext h)
  have hrange : ψ.range = C := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact (ε.symm w).2
    · intro hx
      refine ⟨ε ⟨x, hx⟩, ?_⟩
      simp [ψ]
  have hJle : J ≤ ψ.range := by
    rw [hrange]
    exact hJ.1
  have hJmap : (J.comap ψ).map ψ = J := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hJle]
  have hJ'top : IsComponentOf (J.comap ψ) ⊤ := by
    apply isComponentOf_of_map_injective ψ hψinj
    rw [hJmap, ← MonoidHom.range_eq_map, hrange]
    exact hJ
  obtain ⟨k, hk⟩ := component_eq_factor_image S hS hSt hJ'top
  have hJeq : J = ((S k).map (MonoidHom.mulSingle H k)).map ψ := by
    rw [← hk, hJmap]
  have hfacN : ((S k).map (MonoidHom.mulSingle H k)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    rw [uni_mulSingle_conj]
    exact Subgroup.mem_map.mpr ⟨_, (hSn k).conj_mem w hw (g k), rfl⟩
  rw [hJeq]
  have hJleC : ((S k).map (MonoidHom.mulSingle H k)).map ψ ≤ C := by
    rintro x ⟨w, -, rfl⟩
    exact (ε.symm w).2
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJleC]
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨d, rfl⟩ : ∃ d, ψ d = c := by
      have : c ∈ ψ.range := hrange ▸ hc
      exact this
    exact Subgroup.mem_map.mpr
      ⟨d * w * d⁻¹, hfacN.conj_mem w hw d, by rw [map_mul, map_mul, map_inv]⟩
  · rintro hx
    obtain ⟨d, hd⟩ : ∃ d, ψ d = c := by
      have : c ∈ ψ.range := hrange ▸ hc
      exact this
    rw [← hd] at hx
    have hx' : ψ d * h * ψ d⁻¹ ∈ ((S k).map (MonoidHom.mulSingle H k)).map ψ := by
      simpa only [map_inv] using hx
    have hxJ : ψ d * h * ψ d⁻¹ ∈ J := by rwa [← hJeq] at hx'
    obtain ⟨u, hu⟩ : ∃ u, ψ u = ψ d * h * ψ d⁻¹ := by
      have : ψ d * h * ψ d⁻¹ ∈ ψ.range := hJle hxJ
      exact this
    have hh : h = ψ (d⁻¹ * u * d) := by
      have h1 : ψ (d⁻¹ * u * d) = (ψ d)⁻¹ * ψ u * ψ d := by
        rw [map_mul, map_mul, map_inv]
      rw [h1, hu]
      simp only [map_inv]
      group
    rw [hh]
    have hthis : ψ (d * (d⁻¹ * u * d) * d⁻¹) ∈
        ((S k).map (MonoidHom.mulSingle H k)).map ψ := by
      rw [show d * (d⁻¹ * u * d) * d⁻¹ = u by group, hu]
      exact hx'
    obtain ⟨w', hw', hw''⟩ := Subgroup.mem_map.mp hthis
    have heq : d * (d⁻¹ * u * d) * d⁻¹ = w' := hψinj hw''.symm
    have hmem : d⁻¹ * u * d ∈ (S k).map (MonoidHom.mulSingle H k) := by
      have h1 := hfacN.conj_mem w' hw' d⁻¹
      rw [inv_inv] at h1
      rw [← heq] at h1
      convert h1 using 1
      group
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩

private theorem glaPComponent_centralizer_su_normal {Q n p : ℕ} {L : Type} [Field L] [Finite L]
    {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q)
    (hL : Nat.card L = Q ^ 2) (hp : p.Prime) (s : GL (Fin n) L)
    (hs : s ∈ heldGU n L τ hτ) (hord : (orderOf s : L) ≠ 0)
    (M : Subgroup (GL (Fin n) L))
    (hM : GLAPComponent p (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓
      StatedSU n Q L) M) :
    (M.subgroupOf (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ StatedSU n Q L)).Normal := by
  have hSU : heldSU n L τ hτ = StatedSU n Q L := hct_heldSU_eq_statedSU hτQ
  have hcomp : IsComponentOf M (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓
      StatedSU n Q L) :=
    uniPCompIsComp_holds L Q n p τ hτ hτQ hL hp s hs hord M hM
  have hcomp' : IsComponentOf M (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓
      heldSU n L τ hτ) := by
    rwa [hSU]
  have hcompGU : IsComponentOf M (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓
      heldGU n L τ hτ) :=
    isComponentOf_centralizer_gu_of_su hτ s hcomp'
  have hnormGU := isComponentOf_centralizer_gu_normal hτ hτQ hL s hs hord M hcompGU
  have hMle : M ≤ Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ StatedSU n Q L := hM.1
  have hMleGU : M ≤ Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ :=
    hcompGU.1
  have hle : Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ StatedSU n Q L ≤
      Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ := by
    intro z hz
    exact ⟨hz.1, (Subgroup.mem_inf.mp (hSU ▸ hz.2)).1⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMle]
  exact hle.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hMleGU).1 hnormGU)

private theorem shapeModelNormAt_of_not_dvd_card {R : Type} [Group R] [Finite R] {p : ℕ}
    (hp : p.Prime) (h : ¬ p ∣ Nat.card R) : ShapeModelNormAt R p := by
  intro x y hx1 hxp hyp hcomm J hJ
  exfalso
  have h1 : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.2 hxp
  rcases (Nat.dvd_prime hp).1 h1 with h2 | h2
  · exact hx1 (orderOf_eq_one_iff.1 h2)
  · exact h (h2 ▸ orderOf_dvd_natCard x)

private theorem fixSubgroup_conj {R : Type} [Group R] (x : R) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set R) := by
  ext z
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro hz
    calc z * x = (x * z * x⁻¹) * x := by rw [hz]
      _ = x * z := by group
  · intro hz
    calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [hz]
      _ = z := by group

theorem uniNormModel_holds : UniNormModel := by
  intro N n K _ _ hdata hN p hp hp2 hnot
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [hdata.card, ← pow_mul]
    congr 1
    ring
  by_cases hdq : (N, 2 ^ n) = (3, 2)
  ·
    have hN3 : N = 3 := (Prod.ext_iff.mp hdq).1
    have h2n : 2 ^ n = 2 := (Prod.ext_iff.mp hdq).2
    have hcardR : Nat.card (CFSG.Assembly.LargeEvenProj (unitarySU 2 n K N)) = 72 := by
      have h := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul
        (p := 2) (n := n) hdata
      rw [h2n] at h
      norm_num at h
      have h72 : Nat.card (StatedProj (StatedSU 3 2 K)) = 72 := by omega
      have h72' : Nat.card (StatedProj (StatedSU 3 (2 ^ n) K)) = 72 := by
        rw [h2n]; exact h72
      rw [hN3]
      exact h72'
    have hnot3 : ¬ p ∣ 3 := by
      intro hd
      apply hnot
      rw [hN3, h2n]
      norm_num
      exact hd
    have hp3 : p ≠ 3 := fun h3 => hnot3 (by rw [h3])
    have hnot72 : ¬ p ∣ 72 := by
      intro hd
      have hd' : p ∣ 2 ^ 3 * 3 ^ 2 := by
        rwa [show (2 : ℕ) ^ 3 * 3 ^ 2 = 72 by norm_num]
      rcases hp.dvd_mul.mp hd' with hd2 | hd3
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd2))
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd3))
    exact shapeModelNormAt_of_not_dvd_card hp (by rw [hcardR]; exact hnot72)
  ·
    haveI : CharP K 2 := hdata.charP
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    obtain ⟨τ, hτq, hτ⟩ := exists_frob_equiv (K := K) hK
    let H : Subgroup (GL (Fin N) K) := unitarySU 2 n K N
    change ShapeModelNormAt (CFSG.Assembly.LargeEvenProj H) p
    intro x y hx1 hxp hyp hcomm J hJ
    obtain ⟨A, hA⟩ : ∃ A : ↥H, CFSG.Assembly.LargeEvenProjMk H A = x :=
      QuotientGroup.mk'_surjective _ x
    obtain ⟨B, hB⟩ : ∃ B : ↥H, CFSG.Assembly.LargeEvenProjMk H B = y :=
      QuotientGroup.mk'_surjective _ y
    have hAN : (A : GL (Fin N) K) ∈ Subgroup.normalizer (H : Set (GL (Fin N) K)) :=
      Subgroup.le_normalizer A.2
    have hBN : (B : GL (Fin N) K) ∈ Subgroup.normalizer (H : Set (GL (Fin N) K)) :=
      Subgroup.le_normalizer B.2
    have hAproj : projConj H ⟨(A : GL (Fin N) K), hAN⟩ = MulAut.conj x := by
      rw [projConj_of_mem H (A : GL (Fin N) K) A.2]
      exact congrArg MulAut.conj hA
    have hBproj : projConj H ⟨(B : GL (Fin N) K), hBN⟩ = MulAut.conj y := by
      rw [projConj_of_mem H (B : GL (Fin N) K) B.2]
      exact congrArg MulAut.conj hB
    have hAprojp : projConj H ⟨(A : GL (Fin N) K), hAN⟩ ^ p = 1 := by
      rw [hAproj, ← map_pow, hxp, map_one]
    have hBprojp : projConj H ⟨(B : GL (Fin N) K), hBN⟩ ^ p = 1 := by
      rw [hBproj, ← map_pow, hyp, map_one]
    have hcommproj : projConj H ⟨(A : GL (Fin N) K), hAN⟩ *
        projConj H ⟨(B : GL (Fin N) K), hBN⟩ =
        projConj H ⟨(B : GL (Fin N) K), hBN⟩ *
          projConj H ⟨(A : GL (Fin N) K), hAN⟩ := by
      rw [hAproj, hBproj, ← map_mul, ← map_mul, hcomm.eq]
    have hAhu : (A : GL (Fin N) K) ∈ heldSU N K τ hτ := by
      rw [hct_heldSU_eq_statedSU (Q := 2 ^ n) hτq]
      exact A.2
    have hAgu : (A : GL (Fin N) K) ∈ heldGU N K τ hτ := (Subgroup.mem_inf.mp hAhu).1
    have hBhu : (B : GL (Fin N) K) ∈ heldSU N K τ hτ := by
      rw [hct_heldSU_eq_statedSU (Q := 2 ^ n) hτq]
      exact B.2
    have hBgu : (B : GL (Fin N) K) ∈ heldGU N K τ hτ := (Subgroup.mem_inf.mp hBhu).1
    have hnd : ¬ p ∣ N ∨ ¬ p ∣ 2 ^ n + 1 := by
      by_cases hpd : p ∣ N
      · exact Or.inr (fun hq => hnot (Nat.dvd_gcd hpd hq))
      · exact Or.inl hpd
    have hABcomm : (A : GL (Fin N) K) * (B : GL (Fin N) K) =
        (B : GL (Fin N) K) * (A : GL (Fin N) K) :=
      CFSG.LocalAnalysis.GLTheoremA.T171Sh.commute_of_mem_heldGU hdata hτ hτq (by omega) hdq hp
        hnd hAgu hBgu hAN hBN hAprojp hBprojp hcommproj
    have hApmem : (A : GL (Fin N) K) ^ p ∈ CFSG.Assembly.LargeEvenScalars (Fin N) K := by
      have hANp : (A : GL (Fin N) K) ^ p ∈ Subgroup.normalizer (H : Set (GL (Fin N) K)) :=
        Subgroup.le_normalizer (Subgroup.pow_mem H A.2 p)
      refine CFSG.LocalAnalysis.GLTheoremA.T171Sh.mem_scalars_of_projConj_eq_one
        hdata (by omega) hdq hANp ?_
      have h1 : (⟨(A : GL (Fin N) K) ^ p, hANp⟩ :
            Subgroup.normalizer (H : Set (GL (Fin N) K))) =
          (⟨(A : GL (Fin N) K), hAN⟩ :
            Subgroup.normalizer (H : Set (GL (Fin N) K))) ^ p := Subtype.ext rfl
      rw [h1, map_pow, hAprojp]
    rw [CFSG.Assembly.largeEvenScalars_def] at hApmem
    obtain ⟨c, hc⟩ := hApmem
    have hc' : (A : GL (Fin N) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c := hc.symm
    have hmat : (((A : GL (Fin N) K) ^ p : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) = (c : K) • 1 := by
      rw [hc', val_scalar_gl']
    have hodd : Odd (orderOf (A : GL (Fin N) K)) :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.odd_orderOf_of_pow_scalar h2 (by omega)
        (A : GL (Fin N) K) (hp.odd_of_ne_two hp2) hmat
    have hord : (((orderOf (A : GL (Fin N) K)) : ℕ) : K) ≠ 0 :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 _ hodd
    have hAconj : ∀ z ∈ H, (A : GL (Fin N) K) * z * (A : GL (Fin N) K)⁻¹ ∈ H :=
      fun z hz => H.mul_mem (H.mul_mem A.2 hz) (H.inv_mem A.2)
    have hAconj' : ∀ z ∈ H, (A : GL (Fin N) K)⁻¹ * z * (A : GL (Fin N) K)⁻¹⁻¹ ∈ H :=
      fun z hz => H.mul_mem (H.mul_mem (H.inv_mem A.2) hz) (H.inv_mem (H.inv_mem A.2))
    let α : MulAut ↥H := uniConjSub H (A : GL (Fin N) K) hAconj hAconj'
    let β : MulAut (CFSG.Assembly.LargeEvenProj H) := MulAut.conj x
    have hαβ : ∀ k : ↥H,
        CFSG.Assembly.LargeEvenProjMk H (α k) = β (CFSG.Assembly.LargeEvenProjMk H k) := by
      intro k
      show CFSG.Assembly.LargeEvenProjMk H (α k) = MulAut.conj x (CFSG.Assembly.LargeEvenProjMk H k)
      have h1 : (α k : ↥H) =
          (⟨(A : GL (Fin N) K) * (k : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹,
            hAconj k k.2⟩ : ↥H) :=
        Subtype.ext (uniConjSub_apply_val H (A : GL (Fin N) K) hAconj hAconj' k)
      rw [h1]
      show CFSG.Assembly.LargeEvenProjMk H
          (⟨(A : GL (Fin N) K) * (k : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹,
            hAconj k k.2⟩ : ↥H) = MulAut.conj x (CFSG.Assembly.LargeEvenProjMk H k)
      rw [show (⟨(A : GL (Fin N) K) * (k : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹,
            hAconj k k.2⟩ : ↥H) = (A : ↥H) * k * (A : ↥H)⁻¹ from Subtype.ext rfl]
      rw [map_mul, map_mul, map_inv, hA, MulAut.conj_apply]
    have hfix : fixSubgroup β = Subgroup.centralizer ({x} : Set (CFSG.Assembly.LargeEvenProj H)) :=
      fixSubgroup_conj x
    have hJ' : GLAPComponent p (fixSubgroup β) J := by rw [hfix]; exact hJ
    obtain ⟨J₀, hJ₀, hJ₀map⟩ :=
      exists_glaPComponent_map_fixSubgroup (CFSG.Assembly.LargeEvenProjMk H)
        (ker_projMk_uni_le_center H) α β hαβ (QuotientGroup.mk'_surjective _) hp hJ'
    let M : Subgroup (GL (Fin N) K) := J₀.map H.subtype
    have hfixmap : (fixSubgroup α).map H.subtype =
        Subgroup.centralizer ({(A : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ H :=
      map_fixSubgroup_uniConjSub H (A : GL (Fin N) K) hAconj hAconj'
    have hM : GLAPComponent p
        (Subgroup.centralizer ({(A : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ H) M := by
      have h := (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff hp
        (hι := Subgroup.subtype_injective H)).mpr hJ₀
      rw [hfixmap] at h
      exact h
    have hMnorm : (M.subgroupOf (Subgroup.centralizer
        ({(A : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ H)).Normal :=
      glaPComponent_centralizer_su_normal hτ hτq hK hp (A : GL (Fin N) K) hAgu hord M hM
    have hJ₀conj : ∀ b : ↥H, b ∈ fixSubgroup α → ∀ j₀ ∈ J₀, b * j₀ * b⁻¹ ∈ J₀ := by
      intro b hb j₀ hj₀
      have hbGL : (A : GL (Fin N) K) * (b : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹ =
          (b : GL (Fin N) K) := by
        have h1 := congrArg (fun z : ↥H => (z : GL (Fin N) K)) (mem_fixSubgroup.mp hb)
        change ((A : GL (Fin N) K) * (b : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹ :
            GL (Fin N) K) = (b : GL (Fin N) K) at h1
        exact h1
      have hjGL : (A : GL (Fin N) K) * (j₀ : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹ =
          (j₀ : GL (Fin N) K) := by
        have h1 := congrArg (fun z : ↥H => (z : GL (Fin N) K))
          (mem_fixSubgroup.mp (hJ₀.1 hj₀))
        change ((A : GL (Fin N) K) * (j₀ : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹ :
            GL (Fin N) K) = (j₀ : GL (Fin N) K) at h1
        exact h1
      have hbY : (b : GL (Fin N) K) ∈
          Subgroup.centralizer ({(A : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ H := by
        refine Subgroup.mem_inf.mpr ⟨?_, b.2⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (b : GL (Fin N) K) * (A : GL (Fin N) K) =
              ((A : GL (Fin N) K) * (b : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹) *
                (A : GL (Fin N) K) := by rw [hbGL]
          _ = (A : GL (Fin N) K) * (b : GL (Fin N) K) := by group
      have hjY : (j₀ : GL (Fin N) K) ∈
          Subgroup.centralizer ({(A : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ H := by
        refine Subgroup.mem_inf.mpr ⟨?_, j₀.2⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (j₀ : GL (Fin N) K) * (A : GL (Fin N) K) =
              ((A : GL (Fin N) K) * (j₀ : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹) *
                (A : GL (Fin N) K) := by rw [hjGL]
          _ = (A : GL (Fin N) K) * (j₀ : GL (Fin N) K) := by group
      have hconj := hMnorm.conj_mem
        (⟨(j₀ : GL (Fin N) K), hjY⟩ :
          ↥(Subgroup.centralizer ({(A : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ H))
        (by rw [Subgroup.mem_subgroupOf]; exact Subgroup.mem_map.mpr ⟨j₀, hj₀, rfl⟩)
        (⟨(b : GL (Fin N) K), hbY⟩ :
          ↥(Subgroup.centralizer ({(A : GL (Fin N) K)} : Set (GL (Fin N) K)) ⊓ H))
      have hmem : (b : GL (Fin N) K) * (j₀ : GL (Fin N) K) * (b : GL (Fin N) K)⁻¹ ∈ M := by
        have := Subgroup.mem_subgroupOf.mp hconj
        simpa using this
      obtain ⟨j', hj', hj'eq⟩ := Subgroup.mem_map.mp hmem
      have hjeq : j' = b * j₀ * b⁻¹ := by
        apply Subtype.ext
        simpa using hj'eq
      rwa [← hjeq]
    have hBfix : B ∈ fixSubgroup α := by
      apply mem_fixSubgroup.mpr
      apply Subtype.ext
      change ((A : GL (Fin N) K) * (B : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹ :
          GL (Fin N) K) = (B : GL (Fin N) K)
      rw [hABcomm]; group
    have hconjJ : ∀ j ∈ J, y * j * y⁻¹ ∈ J := by
      intro j hj
      rw [← hJ₀map] at hj
      obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.mp hj
      rw [← hJ₀map]
      refine Subgroup.mem_map.mpr ⟨B * j₀ * B⁻¹, hJ₀conj B hBfix j₀ hj₀, ?_⟩
      rw [map_mul, map_mul, map_inv, hB]
    have hconjJinv : ∀ j ∈ J, y⁻¹ * j * y ∈ J := by
      have hBinvfix : B⁻¹ ∈ fixSubgroup α := (fixSubgroup α).inv_mem hBfix
      intro j hj
      rw [← hJ₀map] at hj
      obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.mp hj
      rw [← hJ₀map]
      refine Subgroup.mem_map.mpr ⟨B⁻¹ * j₀ * B, hJ₀conj B⁻¹ hBinvfix j₀ hj₀, ?_⟩
      rw [map_mul, map_mul, map_inv, hB]
    rw [Subgroup.mem_normalizer_iff]
    intro j
    exact ⟨hconjJ j, fun hj => by
      have := hconjJinv (y * j * y⁻¹) hj
      rwa [show y⁻¹ * (y * j * y⁻¹) * y = j by group] at this⟩

end CFSG.LocalAnalysis.GLTheoremA.F151

end
