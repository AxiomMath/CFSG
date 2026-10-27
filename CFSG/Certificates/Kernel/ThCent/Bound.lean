module

public import CFSG.Certificates.Kernel.ThCent.Orbit
public import CFSG.Certificates.Kernel.DceTwCore
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.DceS CFSG.KC.Th.Spec.Dce CFSG.Certificates.DceTw

section Orb

variable {M : Subgroup Mat24ˣ} {NORD : ℕ} {θ : Finset Vec24} {ω : ℕ → Finset Vec24} {g : ℕ → M}
  {NO I0 : ℕ} {σ : ℕ → M} {nT : ℕ}

theorem stab_eq_of_orb (o : Orb M NORD (Finset Vec24) actP θ ω g NO I0 σ nT) (s : M)
    (hs : actP θ (s : Mat24ˣ) = θ) : ∃ e < nT, s = σ e := by
  classical
  obtain ⟨-, hdec⟩ := decompO o
  have key : ∀ t : M, actP θ (t : Mat24ˣ) = θ → ∃ e < nT, t = σ e * g I0 := by
    intro t ht
    obtain ⟨e, he, j, hj, rfl⟩ := hdec t
    have : ω j = θ := by
      rw [← o.orbit j hj]
      calc actP θ (g j : Mat24ˣ) = actP (actP θ (σ e : Mat24ˣ)) (g j) := by rw [o.stab e he]
        _ = actP θ ((σ e : Mat24ˣ) * g j) := o.act_mul _ _ _
        _ = θ := by simpa using ht
    rw [← o.ωI0] at this
    rw [o.ω_inj j hj I0 o.I0_lt this]
    exact ⟨e, he, rfl⟩
  obtain ⟨e1, he1, rfl⟩ := key s hs
  let f : ℕ → ℕ := fun e => if hx : ∃ e' < nT, σ e = σ e' * g I0 then Classical.choose hx else 0
  have hf : ∀ e < nT, f e < nT ∧ σ e = σ (f e) * g I0 := by
    intro e he
    have hx := key (σ e) (o.stab e he)
    simp only [f, dite_eq_left hx]
    exact Classical.choose_spec hx
  have hinj : Set.InjOn f (Finset.range nT : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have e1 := (hf a ha).2
    have e2 := (hf b hb).2
    rw [hab, ← e2] at e1
    exact o.σ_inj a ha b hb e1
  have hmaps : Set.MapsTo f (Finset.range nT : Set ℕ) (Finset.range nT : Set ℕ) := by
    intro a ha
    simp only [Finset.coe_range, Set.mem_Iio] at ha ⊢
    exact (hf a ha).1
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range nT) (t := Finset.range nT)
    (fun a _ => f a) (fun a ha => Finset.mem_coe.1 (hmaps (Finset.mem_coe.2 ha)))
    (fun a b ha hb hab => hinj (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hab) (le_refl _)
  obtain ⟨e, he, hfe⟩ := hsurj e1 (Finset.mem_range.2 he1)
  have he' := Finset.mem_range.1 he
  refine ⟨e, he', ?_⟩
  rw [(hf e he').2, ← hfe]

theorem orbit_of_orb (o : Orb M NORD (Finset Vec24) actP θ ω g NO I0 σ nT) (m : M) :
    ∃ j < NO, actP θ (m : Mat24ˣ) = ω j := by
  obtain ⟨-, hdec⟩ := decompO o
  obtain ⟨e, he, j, hj, rfl⟩ := hdec m
  refine ⟨j, hj, ?_⟩
  rw [Subgroup.coe_mul, ← o.act_mul, o.stab e he, o.orbit j hj]

end Orb

@[expose] def ptSet (SV : ℕ → ℕ) (N : ℕ) : Set Vec24 := {u | ∃ k < N, toVec (SV k) = u}

theorem actP_single (v : Vec24) (y : Mat24ˣ) : actP {v} y = {Matrix.vecMul v (y : Mat24)} := by
  simp [actP]

theorem ptS_one {P : ℕ} (hP : P < 2 ^ 24) : ptS 1 P = {toVec P} := by
  simp [ptS, rowOf_zero_eq hP]

theorem inv_comm_of {G : Type*} [Group G] {n t : G} (h : n * t = t * n) : n⁻¹ * t = t * n⁻¹ :=
  calc n⁻¹ * t = n⁻¹ * (t * n) * n⁻¹ := by rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
    _ = n⁻¹ * (n * t) * n⁻¹ := by rw [h]
    _ = t * n⁻¹ := by rw [← mul_assoc, inv_mul_cancel, one_mul]

section Main

variable {M : Subgroup Mat24ˣ} {NORD NO I0 nT : ℕ} {OB HB GB TB : ℕ → ℕ} {osh owd om : ℕ}

theorem card_cent_le
    (o : Orb M NORD (Finset Vec24) actP (ptS 1 (pt OB osh owd om I0))
      (fun j => ptS 1 (pt OB osh owd om j)) (fun j => mEl M (gm HB GB j)) NO I0
      (fun e => mEl M (tSig HB TB e)) nT)
    (hpt : ∀ j, pt OB osh owd om j < 2 ^ 24)
    (hGM : ∀ j < NO, InM M (gm HB GB j)) (hTS : ∀ e < nT, InM M (tSig HB TB e))
    {SV : ℕ → ℕ} (hinc : ∀ k, k + 1 < NO → SV k < SV (k + 1)) (hSV24 : ∀ k < NO, SV k < 2 ^ 24)
    (hsv : ∀ k < NO, ∃ j < NO, SV k = pt OB osh owd om j)
    (hptk : ∀ j < NO, ∃ k < NO, SV k = pt OB osh owd om j)
    {T : ℕ} (hT : InM M T) {B : ℕ}
    (hB : ∀ m : M, ((m : Mat24ˣ) : Mat24) * toMat B * ((m : Mat24ˣ) : Mat24).transpose = toMat B)
    {Ps FL : List ℕ}
    (hPs : ∀ m : M, ((m : Mat24ˣ) : Mat24) * toMat T = toMat T * ((m : Mat24ˣ) : Mat24) →
      ∀ P ∈ Ps, ((m : Mat24ˣ) : Mat24) * toMat P = toMat P * ((m : Mat24ˣ) : Mat24))
    (hFLn : (FL.map toMat).Nodup)
    (hFLc : ∀ m : M, ((m : Mat24ˣ) : Mat24) * toMat T = toMat T * ((m : Mat24ˣ) : Mat24) →
      ∀ Y ∈ FL.map toMat, ((m : Mat24ˣ) : Mat24) * Y * (((m⁻¹ : M) : Mat24ˣ) : Mat24) ∈
        FL.map toMat)
    {R H1 : ℕ → ℕ} {i1 j1 Hi N1 m1 : ℕ}
    (hdiff : ∀ k < NO, diffOK SV R H1 NO B Ps FL i1 k = true)
    (hN1 : ((Finset.range NO).filter fun k => selAt R 0 k = true).card ≤ N1)
    (hi1 : i1 < NO) (hj1 : j1 < NO) (hv1 : SV i1 = pt OB osh owd om j1)
    (hHi : mul24 (gm HB GB j1) Hi = ident24) (hHi' : Hi < 2 ^ 576)
    (hm1 : ((Finset.range nT).filter fun e =>
      commAt HB TB (mul24 (mul24 (gm HB GB j1) T) Hi) 0 e = true).card ≤ m1) :
    Nat.card (Subgroup.centralizer ({mEl M T} : Set M)) ≤ N1 * m1 := by
  classical
  have hfinM : Finite M := o.finM
  have ht : ((mEl M T : Mat24ˣ) : Mat24) = toMat T := mEl_val hT
  generalize mEl M T = t at ht ⊢
  have hcomm : ∀ c : M, c * t = t * c →
      ((c : Mat24ˣ) : Mat24) * toMat T = toMat T * ((c : Mat24ˣ) : Mat24) := by
    intro c hc
    have := congrArg (fun x : M => ((x : Mat24ˣ) : Mat24)) hc
    simp only [Subgroup.coe_mul, Units.val_mul, ht] at this
    exact this
  have hθ : ∀ j, ptS 1 (pt OB osh owd om j) = {toVec (pt OB osh owd om j)} := fun j => ptS_one (hpt j)
  have hmove : ∀ j < NO, ∀ m : M, ∃ j' < NO,
      Matrix.vecMul (toVec (pt OB osh owd om j)) ((m : Mat24ˣ) : Mat24) =
        toVec (pt OB osh owd om j') := by
    intro j hj m
    obtain ⟨j', hj', e⟩ := orbit_of_orb o (mEl M (gm HB GB j) * m)
    refine ⟨j', hj', ?_⟩
    rw [Subgroup.coe_mul, ← o.act_mul, o.orbit j hj] at e
    rw [hθ, hθ, actP_single] at e
    exact Finset.singleton_injective e
  let S : Set Vec24 := ptSet SV NO
  have hSmove : ∀ m : M, ∀ u ∈ S, Matrix.vecMul u ((m : Mat24ˣ) : Mat24) ∈ S := by
    rintro m u ⟨k, hk, rfl⟩
    obtain ⟨j, hj, e⟩ := hsv k hk
    obtain ⟨j', hj', e'⟩ := hmove j hj m
    obtain ⟨k', hk', e''⟩ := hptk j' hj'
    exact ⟨k', hk', by rw [e, e', e'']⟩
  have hSiff : ∀ m : M, ∀ u, Matrix.vecMul u ((m : Mat24ˣ) : Mat24) ∈ S ↔ u ∈ S := by
    intro m u
    refine ⟨fun h => ?_, hSmove m u⟩
    have := hSmove m⁻¹ _ h
    rwa [Matrix.vecMul_vecMul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one, Matrix.vecMul_one] at this
  let _ : Fintype M := Fintype.ofFinite M
  let CM : Finset M := Finset.univ.filter fun c : M => c * t = t * c
  let Cf : Finset Mat24ˣ := CM.map ⟨fun c : M => (c : Mat24ˣ), Subtype.val_injective⟩
  have hmemC : ∀ c ∈ Cf, ∃ m : M, (m : Mat24ˣ) = c ∧ m * t = t * m := by
    intro c hc
    rw [Finset.mem_map] at hc
    obtain ⟨m, hm, rfl⟩ := hc
    exact ⟨m, rfl, (Finset.mem_filter.1 hm).2⟩
  have hcard : Nat.card (Subgroup.centralizer ({t} : Set M)) = Cf.card := by
    rw [Finset.card_map]
    have e : Nat.card (Subgroup.centralizer ({t} : Set M)) = Nat.card {c : M // c * t = t * c} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c => by
        rw [Subgroup.mem_centralizer_singleton_iff])
    rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  let V : Finset Vec24 := (Finset.range NO).image fun k => toVec (SV k)
  have hVS : ∀ u, u ∈ V ↔ u ∈ S := by
    intro u
    simp only [V, Finset.mem_image, Finset.mem_range, S, ptSet, Set.mem_setOf_eq]
  let f : Vec24 → ℕ → ℕ := fun u =>
    compM S (toMat B) (Ps.map toMat) (FL.map toMat) u
  have hgrp : ∀ c ∈ Cf, ∀ d ∈ Cf, c * d⁻¹ ∈ Cf := by
    intro c hc d hd
    obtain ⟨m, rfl, hm⟩ := hmemC c hc
    obtain ⟨n, rfl, hn⟩ := hmemC d hd
    rw [Finset.mem_map]
    refine ⟨m * n⁻¹, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    swap
    · change ((m * n⁻¹ : M) : Mat24ˣ) = (m : Mat24ˣ) * (n : Mat24ˣ)⁻¹
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have hn' : n⁻¹ * t = t * n⁻¹ := inv_comm_of hn
    rw [mul_assoc, hn', ← mul_assoc, hm, mul_assoc]
  have hV : ∀ c ∈ Cf, ∀ u ∈ V, Matrix.vecMul u c.val ∈ V := by
    intro c hc u hu
    obtain ⟨m, rfl, -⟩ := hmemC c hc
    rw [hVS] at hu ⊢
    exact hSmove m u hu
  have hf : ∀ c ∈ Cf, ∀ u, f (Matrix.vecMul u c.val) = f u := by
    intro c hc u
    obtain ⟨m, rfl, hm⟩ := hmemC c hc
    have hmT := hcomm m hm
    have hmT' : (((m⁻¹ : M) : Mat24ˣ) : Mat24) * toMat T =
        toMat T * (((m⁻¹ : M) : Mat24ˣ) : Mat24) := by
      have hm' : m⁻¹ * t = t * m⁻¹ := inv_comm_of hm
      exact hcomm _ hm'
    funext q
    refine compM_invariant S _ _ _ (m : Mat24ˣ) ?_ (hB m) (hSiff m) hFLn ?_ ?_ u q
    · intro P hP
      obtain ⟨P', hP', rfl⟩ := List.mem_map.1 hP
      exact hPs m hmT P' hP'
    · intro Y hY
      exact hFLc m hmT Y hY
    · intro Y hY
      have := hFLc m⁻¹ hmT' Y hY
      simpa using this
  have hu1 : toVec (SV i1) ∈ V := Finset.mem_image.2 ⟨i1, Finset.mem_range.2 hi1, rfl⟩
  have key := card_le_mul Cf hgrp V hV f hf hu1
  refine key.trans (Nat.mul_le_mul ?_ ?_)
  ·
    refine le_trans ?_ hN1
    have hsub : V.filter (fun u => f u = f (toVec (SV i1))) ⊆
        ((Finset.range NO).filter fun k => selAt R 0 k = true).image fun k => toVec (SV k) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨huV, hfu⟩ := hu
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 huV
      rw [Finset.mem_range] at hk
      refine Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, ?_⟩, rfl⟩
      by_contra hs
      have hs' : Nat.land (R k) 63 ≠ 63 := by
        intro e
        apply hs
        unfold selAt
        have e0 : Nat.add 0 k = k := Nat.zero_add k
        rw [e0, show Nat.land (R k) (nat_lit 63) = 63 from e]
        exact Nat.beq_refl _
      obtain ⟨q, hq⟩ := diffOK_ne hinc hSV24 hk hi1 (hdiff k hk) hs'
      exact hq (congrFun hfu q)
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  ·
    refine le_trans ?_ hm1
    let g1 : M := mEl M (gm HB GB j1)
    have hg1 : ((g1 : Mat24ˣ) : Mat24) = toMat (gm HB GB j1) := mEl_val (hGM j1 hj1)
    have hHiM : toMat (gm HB GB j1) * toMat Hi = 1 := by
      rw [← toMat_mul24, hHi, toMat_ident24]
    have hg1i : (((g1⁻¹ : M) : Mat24ˣ) : Mat24) = toMat Hi := by
      have h1 : ((g1 : Mat24ˣ) : Mat24) * (((g1⁻¹ : M) : Mat24ˣ) : Mat24) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
      have h2 : (((g1⁻¹ : M) : Mat24ˣ) : Mat24) * ((g1 : Mat24ˣ) : Mat24) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
      calc (((g1⁻¹ : M) : Mat24ˣ) : Mat24)
          = (((g1⁻¹ : M) : Mat24ˣ) : Mat24) * (toMat (gm HB GB j1) * toMat Hi) := by
            rw [hHiM, Matrix.mul_one]
        _ = toMat Hi := by rw [← Matrix.mul_assoc, ← hg1, h2, Matrix.one_mul]
    have hθv : Matrix.vecMul (toVec (pt OB osh owd om I0)) ((g1 : Mat24ˣ) : Mat24) =
        toVec (SV i1) := by
      have e := o.orbit j1 hj1
      rw [hθ, hθ, actP_single] at e
      rw [hv1]
      exact Finset.singleton_injective e
    have hst : ∀ c ∈ Cf.filter (fun c : Mat24ˣ => Matrix.vecMul (toVec (SV i1)) c.val =
        toVec (SV i1)), ∃ e < nT, ∃ m : M, (m : Mat24ˣ) = c ∧ g1 * m * g1⁻¹ = mEl M (tSig HB TB e) ∧
          m * t = t * m := by
      intro c hc
      rw [Finset.mem_filter] at hc
      obtain ⟨m, rfl, hm⟩ := hmemC c hc.1
      have hfix : actP (ptS 1 (pt OB osh owd om I0)) ((g1 * m * g1⁻¹ : M) : Mat24ˣ) =
          ptS 1 (pt OB osh owd om I0) := by
        have hv : Matrix.vecMul (toVec (pt OB osh owd om I0))
            (((g1 * m * g1⁻¹ : M) : Mat24ˣ) : Mat24) = toVec (pt OB osh owd om I0) := by
          simp only [Subgroup.coe_mul, Units.val_mul, ← Matrix.vecMul_vecMul]
          rw [hθv, hc.2, ← hθv, Matrix.vecMul_vecMul, ← Units.val_mul, ← Subgroup.coe_mul,
            mul_inv_cancel, Subgroup.coe_one, Units.val_one, Matrix.vecMul_one]
        rw [hθ, actP_single, hv]
      obtain ⟨e, he, hse⟩ := stab_eq_of_orb o _ hfix
      exact ⟨e, he, m, rfl, hse, hm⟩
    choose! eF heF mF hmF hgF hcF using hst
    refine Finset.card_le_card_of_injOn eF ?_ ?_
    · intro c hc
      have hc' := Finset.mem_coe.1 hc
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_range.2 (heF c hc'), ?_⟩)
      unfold commAt
      have e0 : Nat.add 0 (eF c) = eF c := Nat.zero_add _
      rw [e0, commB_iff]
      refine eq_of_toMat_eq (mul24_lt _ _) (mul24_lt _ _) ?_
      have hS : toMat (tSig HB TB (eF c)) = (((g1 * mF c * g1⁻¹ : M) : Mat24ˣ) : Mat24) := by
        rw [hgF c hc', mEl_val (hTS _ (heF c hc'))]
      have hmT := hcomm (mF c) (hcF c hc')
      rw [toMat_mul24, toMat_mul24, toMat_mul24, toMat_mul24, toMat_mul24, toMat_mul24, hS,
        ← hg1, ← hg1i]
      simp only [Subgroup.coe_mul, Units.val_mul]
      have hgi : (((g1⁻¹ : M) : Mat24ˣ) : Mat24) * ((g1 : Mat24ˣ) : Mat24) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (((g1⁻¹ : M) : Mat24ˣ) : Mat24) ((g1 : Mat24ˣ) : Mat24), hgi,
        Matrix.one_mul, ← Matrix.mul_assoc (((mF c : M) : Mat24ˣ) : Mat24) (toMat T), hmT]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (((g1⁻¹ : M) : Mat24ˣ) : Mat24) ((g1 : Mat24ˣ) : Mat24), hgi,
        Matrix.one_mul]
    · intro c hc d hd hcd
      have hc' := Finset.mem_coe.1 hc
      have hd' := Finset.mem_coe.1 hd
      have e1 := hgF c hc'
      have e2 := hgF d hd'
      rw [hcd, ← e2] at e1
      have : mF c = mF d := by
        have := congrArg (fun x : M => g1⁻¹ * x * g1) e1
        simpa [mul_assoc] using this
      rw [← hmF c hc', ← hmF d hd', this]

end Main

end CFSG.KC.ThCent

end
