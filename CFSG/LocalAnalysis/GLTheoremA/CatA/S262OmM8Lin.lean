module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.Centralizer
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

import CFSG.GroupTheory.Commutator.SubgroupOf
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

namespace OmM8

open Polynomial Module QuadraticMap CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth
open CFSG.AGLEmbedding.ToralCensus (PerfectThreeIn)
open CFSG.AGLEmbedding.ToralCensus

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem three_ne_zero : ((3 : ℕ) : K) ≠ 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [show ((3 : ℕ) : K) = 2 + 1 by norm_num, h2, zero_add]
  exact one_ne_zero

theorem two_eq_zero_end : (2 : Module.End K V) = 0 := by
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [← Nat.cast_two, ← map_natCast (algebraMap K (Module.End K V))]
  exact (congrArg (algebraMap K (Module.End K V)) h2K).trans (map_zero _)

theorem eIdem_ring_identity {X Y : Module.End K V} (hX : X ^ 3 = 1) (hY : Y ^ 3 = 1)
    (hXY : X * Y = Y * X) (h2 : (2 : Module.End K V) = 0) :
    (1 + X + X ^ 2) + (1 + Y + Y ^ 2) + (1 + X * Y + (X * Y) ^ 2) +
      (1 + X * Y ^ 2 + (X * Y ^ 2) ^ 2) + (1 + X + X ^ 2) * (1 + Y + Y ^ 2) = 1 := by
  have hcomm : Commute X Y := hXY
  have hXY2 : (X * Y) ^ 2 = X ^ 2 * Y ^ 2 := hcomm.mul_pow 2
  have hXY22 : (X * Y ^ 2) ^ 2 = X ^ 2 * Y ^ 4 := by
    rw [pow_two, pow_two]
    exact (hcomm.pow_right 2).mul_pow 2
  have hY4 : Y ^ 4 = Y := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hY, one_mul]
  rw [hXY2, hXY22, hY4]
  have hmain : (1 + X + X ^ 2) + (1 + Y + Y ^ 2) + (1 + X * Y + X ^ 2 * Y ^ 2) +
      (1 + X * Y ^ 2 + X ^ 2 * Y) + (1 + X + X ^ 2) * (1 + Y + Y ^ 2) =
      (5 : ℕ) • (1 : Module.End K V) + (2 : ℕ) •
        (X + X ^ 2 + Y + Y ^ 2 + X * Y + X ^ 2 * Y ^ 2 + X * Y ^ 2 + X ^ 2 * Y) := by
    noncomm_ring
  have h5 : (5 : ℕ) • (1 : Module.End K V) = 1 := by
    have : (5 : Module.End K V) = 2 + 2 + 1 := by norm_num
    change (5 : Module.End K V) = 1
    rw [this, h2]
    norm_num
  have h2z : (2 : ℕ) • (X + X ^ 2 + Y + Y ^ 2 + X * Y + X ^ 2 * Y ^ 2 + X * Y ^ 2 +
      X ^ 2 * Y) = 0 := by
    change (2 : Module.End K V) * (X + X ^ 2 + Y + Y ^ 2 + X * Y + X ^ 2 * Y ^ 2 +
      X * Y ^ 2 + X ^ 2 * Y) = 0
    rw [h2, zero_mul]
  rw [hmain, h5, h2z, add_zero]

@[expose] noncomputable def eIdem (g : V ≃ₗ[K] V) : Module.End K V :=
  1 + (g : Module.End K V) + (g : Module.End K V) ^ 2

theorem coe_mul_eIdem {g : V ≃ₗ[K] V} (hg : g ^ 3 = 1) :
    (g : Module.End K V) * eIdem g = eIdem g := by
  have h3 : (g : Module.End K V) ^ 3 = 1 := by
    have hcoe : ((g ^ 3 : V ≃ₗ[K] V) : Module.End K V) = (g : Module.End K V) ^ 3 := rfl
    rw [← hcoe, hg]
    rfl
  unfold eIdem
  rw [mul_add, mul_add, mul_one,
    show (g : Module.End K V) * (g : Module.End K V) ^ 2 = (g : Module.End K V) ^ 3 from
      (pow_succ' (g : Module.End K V) 2).symm, h3]
  noncomm_ring

theorem eIdem_apply_mem_fixedSpace {g : V ≃ₗ[K] V} (hg : g ^ 3 = 1) (v : V) :
    eIdem g v ∈ fixedSpace g := by
  rw [mem_fixedSpace]
  show (g : Module.End K V) (eIdem g v) = eIdem g v
  rw [← Module.End.mul_apply, coe_mul_eIdem hg]

theorem sup_fixedSpace_eq_top_of_commute {x y : V ≃ₗ[K] V} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hcomm : Commute x y) :
    fixedSpace x ⊔ fixedSpace y ⊔ fixedSpace (x * y) ⊔ fixedSpace (x * y ^ 2) = ⊤ := by
  have hXY : (x : Module.End K V) * (y : Module.End K V) =
      (y : Module.End K V) * (x : Module.End K V) :=
    congrArg (fun e : V ≃ₗ[K] V => (e : Module.End K V)) hcomm.eq
  have hxy3 : (x * y) ^ 3 = 1 := by
    rw [hcomm.mul_pow 3, hx, hy, one_mul]
  have hy23 : (y ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hy]; simp
  have hxy23 : (x * y ^ 2) ^ 3 = 1 := by
    rw [(hcomm.pow_right 2).mul_pow 3, hx, hy23, one_mul]
  have hxE : (x : Module.End K V) ^ 3 = 1 := by
    have hcoe : ((x ^ 3 : V ≃ₗ[K] V) : Module.End K V) = (x : Module.End K V) ^ 3 := rfl
    rw [← hcoe, hx]
    rfl
  have hyE : (y : Module.End K V) ^ 3 = 1 := by
    have hcoe : ((y ^ 3 : V ≃ₗ[K] V) : Module.End K V) = (y : Module.End K V) ^ 3 := rfl
    rw [← hcoe, hy]
    rfl
  have hring := eIdem_ring_identity hxE hyE hXY two_eq_zero_end
  rw [eq_top_iff]
  intro v _
  have hv : v = eIdem x v + eIdem y v + eIdem (x * y) v + eIdem (x * y ^ 2) v +
      (eIdem x * eIdem y) v := by
    have h := congrArg (fun f : Module.End K V => f v) hring
    exact h.symm
  have hB : (eIdem x * eIdem y) v ∈ fixedSpace x := by
    rw [Module.End.mul_apply]
    exact eIdem_apply_mem_fixedSpace hx (eIdem y v)
  have hv' : v = (eIdem x v + (eIdem x * eIdem y) v) + eIdem y v + eIdem (x * y) v +
      eIdem (x * y ^ 2) v := by
    nth_rewrite 1 [hv]
    abel
  rw [hv']
  refine Submodule.add_mem_sup ?_ ?_
  · refine Submodule.add_mem_sup ?_ ?_
    · refine Submodule.add_mem_sup ?_ ?_
      · exact (fixedSpace x).add_mem (eIdem_apply_mem_fixedSpace hx v) hB
      · exact eIdem_apply_mem_fixedSpace hy v
    · exact eIdem_apply_mem_fixedSpace hxy3 v
  · exact eIdem_apply_mem_fixedSpace hxy23 v

theorem finrank_le_sum_finrank_sub_four {U₁ U₂ U₃ U₄ W : Submodule K V}
    (h1 : W ≤ U₁) (h2 : W ≤ U₂) (h3 : W ≤ U₃) (h4 : W ≤ U₄)
    (hsup : U₁ ⊔ U₂ ⊔ U₃ ⊔ U₄ = ⊤) :
    finrank K V ≤ finrank K U₁ + finrank K U₂ + finrank K U₃ + finrank K U₄ -
      3 * finrank K W := by
  have hW12 : W ≤ (U₁ ⊔ U₂ : Submodule K V) := le_trans h1 le_sup_left
  have hW123 : W ≤ (U₁ ⊔ U₂ ⊔ U₃ : Submodule K V) := le_trans hW12 le_sup_left
  have h12 : finrank K (U₁ ⊔ U₂ : Submodule K V) ≤
      finrank K U₁ + finrank K U₂ - finrank K W := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
    have hle : finrank K W ≤ finrank K (U₁ ⊓ U₂ : Submodule K V) :=
      Submodule.finrank_mono (le_inf h1 h2)
    omega
  have h123 : finrank K (U₁ ⊔ U₂ ⊔ U₃ : Submodule K V) ≤
      finrank K (U₁ ⊔ U₂ : Submodule K V) + finrank K U₃ - finrank K W := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (U₁ ⊔ U₂ : Submodule K V) U₃
    have hle : finrank K W ≤ finrank K ((U₁ ⊔ U₂ : Submodule K V) ⊓ U₃ : Submodule K V) :=
      Submodule.finrank_mono (le_inf hW12 h3)
    omega
  have h1234 : finrank K (U₁ ⊔ U₂ ⊔ U₃ ⊔ U₄ : Submodule K V) ≤
      finrank K (U₁ ⊔ U₂ ⊔ U₃ : Submodule K V) + finrank K U₄ - finrank K W := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (U₁ ⊔ U₂ ⊔ U₃ : Submodule K V) U₄
    have hle : finrank K W ≤ finrank K ((U₁ ⊔ U₂ ⊔ U₃ : Submodule K V) ⊓ U₄ : Submodule K V) :=
      Submodule.finrank_mono (le_inf hW123 h4)
    omega
  have htop : finrank K V = finrank K (U₁ ⊔ U₂ ⊔ U₃ ⊔ U₄ : Submodule K V) := by
    rw [hsup, finrank_top]
  have hwa : finrank K W ≤ finrank K U₁ := Submodule.finrank_mono h1
  have hwb : finrank K W ≤ finrank K U₂ := Submodule.finrank_mono h2
  have hwc : finrank K W ≤ finrank K U₃ := Submodule.finrank_mono h3
  have hwd : finrank K W ≤ finrank K U₄ := Submodule.finrank_mono h4
  omega

theorem even_finrank_inf_fixedSpace (hQ : (polarBilin Q).Nondegenerate)
    {x y : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) (hy3 : y ^ 3 = 1)
    (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hcomm : Commute x y) :
    Even (finrank K (fixedSpace x ⊓ fixedSpace y : Submodule K V)) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hyC : y ∈ isometryCentralizer Q x := by
    refine Subgroup.mem_inf.mpr ⟨hyO, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.eq.symm
  let y' : fixedSpace x ≃ₗ[K] fixedSpace x := isometryRestrictFixed Q x ⟨y, hyC⟩
  have hcoe : ∀ u : fixedSpace x, ((y' u : fixedSpace x) : V) = y (u : V) := fun u =>
    coe_isometryRestrictFixed (x := x) ⟨y, hyC⟩ u
  have hy' : OddOrderIsometry (Q.comp (fixedSpace x).subtype) 3 y' := by
    refine ⟨isometryRestrictFixed_mem_orthogonalGroup ⟨y, hyC⟩, ?_, three_ne_zero, ?_⟩
    · have h3 : (⟨y, hyC⟩ : ↥(isometryCentralizer Q x)) ^ 3 = 1 := by
        apply Subtype.ext
        change y ^ 3 = 1
        exact hy3
      have hmap := congrArg (isometryRestrictFixed Q x) h3
      rw [map_pow, map_one] at hmap
      simpa [y'] using hmap
    · intro v hv
      exact (hx.polarBilin_fixed_nondegenerate).1 v fun w =>
        (by simpa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype] using hv w)
  have hfix : fixedSpace y' = (fixedSpace x ⊓ fixedSpace y).comap (fixedSpace x).subtype := by
    ext u
    simp only [mem_fixedSpace, Submodule.mem_comap, Submodule.mem_inf, Subtype.ext_iff, hcoe]
    exact ⟨fun h => ⟨mem_fixedSpace.mp u.2, h⟩, fun h => h.2⟩

  have hW := CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine.even_finrank_fixedSpace hy' h2
  have he := (Submodule.comapSubtypeEquivOfLe
    (inf_le_left : fixedSpace x ⊓ fixedSpace y ≤ fixedSpace x)).finrank_eq
  rw [hfix, he] at hW
  exact hW

theorem charSum_modEq_one_of_disjoint [Fintype V] (hK : Nat.card K = 2)
    {x y : V ≃ₗ[K] V} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hcomm : Commute x y)
    (hxQ : ∀ v, Q (x v) = Q v) (hyQ : ∀ v, Q (y v) = Q v)
    (hW : fixedSpace x ⊓ fixedSpace y = ⊥) :
    (∑ v, chi (Q v)) ≡ 1 [ZMOD 3] := by
  classical
  letI : Fintype ↥(fixedSpace x) := Fintype.ofFinite _
  have hyC : y ∈ isometryCentralizer Q x := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      exact hyQ
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm.eq.symm
  let y' : fixedSpace x ≃ₗ[K] fixedSpace x := isometryRestrictFixed Q x ⟨y, hyC⟩
  let Q₁ : QuadraticForm K ↥(fixedSpace x) := Q.comp (fixedSpace x).subtype
  have hcoe : ∀ u : fixedSpace x, ((y' u : fixedSpace x) : V) = y (u : V) := fun u =>
    coe_isometryRestrictFixed (x := x) ⟨y, hyC⟩ u
  have hy'Q : ∀ u : fixedSpace x, Q₁ (y' u) = Q₁ u := by
    intro u
    change Q ((y' u : fixedSpace x) : V) = Q ((u : fixedSpace x) : V)
    rw [hcoe]
    exact hyQ (u : V)
  have hy'3 : y' ^ 3 = 1 := by
    have h3 : (⟨y, hyC⟩ : ↥(isometryCentralizer Q x)) ^ 3 = 1 := by
      apply Subtype.ext
      change y ^ 3 = 1
      exact hy3
    have hmap := congrArg (isometryRestrictFixed Q x) h3
    rw [map_pow, map_one] at hmap
    simpa [y'] using hmap
  have hfix : fixedSpace y' =
      (fixedSpace x ⊓ fixedSpace y).comap (fixedSpace x).subtype := by
    ext u
    simp only [mem_fixedSpace, Submodule.mem_comap, Submodule.mem_inf, Subtype.ext_iff, hcoe]
    exact ⟨fun h => ⟨mem_fixedSpace.mp u.2, h⟩, fun h => h.2⟩
  have hbot : fixedSpace y' = ⊥ := by
    rw [hfix, hW]
    simp
  have hg : ∀ a : fixedSpace x, y' (y' (y' a)) = a := by
    intro a
    have := congrArg (fun e : fixedSpace x ≃ₗ[K] fixedSpace x => e a) hy'3
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  have hmodz := card_filter_modEq_three (fun a : fixedSpace x => y' a) hg
    (fun a => Q₁ a = 0) (fun a => by rw [hy'Q])
  have hnz := card_filter_modEq_three (fun a : fixedSpace x => y' a) hg
    (fun a => ¬ Q₁ a = 0) (fun a => by rw [hy'Q])
  have hInt : ((Finset.univ.filter (fun a : fixedSpace x => Q₁ a = 0)).card : ℤ) -
      ((Finset.univ.filter (fun a : fixedSpace x => ¬ Q₁ a = 0)).card : ℤ) ≡
      ((Finset.univ.filter (fun a : fixedSpace x => Q₁ a = 0 ∧ y' a = a)).card : ℤ) -
      ((Finset.univ.filter (fun a : fixedSpace x => ¬ Q₁ a = 0 ∧ y' a = a)).card : ℤ) [ZMOD 3] :=
    Int.ModEq.sub (Int.natCast_modEq_iff.mpr hmodz) (Int.natCast_modEq_iff.mpr hnz)
  have hz0 : (Finset.univ.filter (fun a : fixedSpace x => Q₁ a = 0 ∧ y' a = a)) = {0} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨by simp, ?_⟩
    intro v hv
    rw [Finset.mem_filter] at hv
    have hmem : v ∈ fixedSpace y' := mem_fixedSpace.mpr hv.2.2
    rw [hbot] at hmem
    simpa using hmem
  have hnz0 : (Finset.univ.filter (fun a : fixedSpace x => ¬ Q₁ a = 0 ∧ y' a = a)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro v _ hv
    have hmem : v ∈ fixedSpace y' := mem_fixedSpace.mpr hv.2
    rw [hbot] at hmem
    have hv0 : v = 0 := by simpa using hmem
    rw [hv0] at hv
    exact hv.1 (by simp [Q₁])
  have hval : ((Finset.univ.filter (fun a : fixedSpace x => Q₁ a = 0 ∧ y' a = a)).card : ℤ) -
      ((Finset.univ.filter (fun a : fixedSpace x => ¬ Q₁ a = 0 ∧ y' a = a)).card : ℤ) = 1 := by
    rw [hz0, hnz0]
    simp
  have hU : (∑ u : fixedSpace x, chi (Q₁ u)) =
      ((Finset.univ.filter (fun a : fixedSpace x => Q₁ a = 0)).card : ℤ) -
      ((Finset.univ.filter (fun a : fixedSpace x => ¬ Q₁ a = 0)).card : ℤ) :=
    sum_chi_eq_card_sub Q₁ Finset.univ
  have h2 : (∑ u : fixedSpace x, chi (Q₁ u)) ≡ 1 [ZMOD 3] := by
    rw [hU]
    exact hInt.trans (by rw [hval])
  have h1 := charSum_modEq_fixed Q x hxQ hx3
  have hsub1 : (∑ v ∈ Finset.univ.filter (fun v : V => x v = v), chi (Q v)) =
      ∑ u : fixedSpace x, chi (Q₁ u) :=
    Finset.sum_subtype (p := (· ∈ fixedSpace x)) _ (fun v => by simp [mem_fixedSpace, Q₁]) _
  rw [hsub1] at h1
  exact h1.trans h2

theorem false_of_fixedSpace_le_three [Fintype V]
    (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank K V = 8) (hS : (∑ v, chi (Q v)) = -16)
    {x y : V ≃ₗ[K] V} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hcomm : Commute x y)
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx : finrank K (fixedSpace x) ≤ 3) (hy : finrank K (fixedSpace y) ≤ 3)
    (hxy : finrank K (fixedSpace (x * y)) ≤ 3)
    (hxy2 : finrank K (fixedSpace (x * y ^ 2)) ≤ 3) : False := by
  have hxQ : ∀ v, Q (x v) = Q v := fun v =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hxO v
  have hyQ : ∀ v, Q (y v) = Q v := fun v =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hyO v
  have hxodd : OddOrderIsometry Q 3 x :=
    ⟨hxO, hx3, three_ne_zero, fun v hv => hQ.1 v hv⟩
  have hsup := sup_fixedSpace_eq_top_of_commute hx3 hy3 hcomm
  have hWx : (fixedSpace x ⊓ fixedSpace y : Submodule K V) ≤ fixedSpace x := inf_le_left
  have hWy : (fixedSpace x ⊓ fixedSpace y : Submodule K V) ≤ fixedSpace y := inf_le_right
  have hWxy : (fixedSpace x ⊓ fixedSpace y : Submodule K V) ≤ fixedSpace (x * y) := by
    intro v hv
    obtain ⟨hvx, hvy⟩ := Submodule.mem_inf.mp hv
    rw [mem_fixedSpace] at hvx
    rw [mem_fixedSpace, LinearEquiv.mul_apply, mem_fixedSpace.mp hvy, hvx]
  have hWxy2 : (fixedSpace x ⊓ fixedSpace y : Submodule K V) ≤ fixedSpace (x * y ^ 2) := by
    intro v hv
    obtain ⟨hvx, hvy⟩ := Submodule.mem_inf.mp hv
    rw [mem_fixedSpace] at hvx
    have hyv : y v = v := mem_fixedSpace.mp hvy
    rw [mem_fixedSpace, show (x * y ^ 2) v = x (y (y v)) by
      rw [pow_two, LinearEquiv.mul_apply, LinearEquiv.mul_apply]]
    rw [hyv, hyv, hvx]
  have hdimle := finrank_le_sum_finrank_sub_four hWx hWy hWxy hWxy2 hsup
  have hw : finrank K (fixedSpace x ⊓ fixedSpace y : Submodule K V) ≤ 1 := by
    omega
  have heven := even_finrank_inf_fixedSpace hQ hxodd hy3 hyO hcomm
  have hWbot : fixedSpace x ⊓ fixedSpace y = ⊥ := by
    obtain ⟨k, hk⟩ := heven
    have h0 : finrank K (fixedSpace x ⊓ fixedSpace y : Submodule K V) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp h0
  have hmod := charSum_modEq_one_of_disjoint hK hx3 hy3 hcomm hxQ hyQ hWbot
  rw [hS] at hmod
  norm_num at hmod

theorem exists_fixedSpace_finrank_ge_four [Fintype V]
    (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank K V = 8) (hS : (∑ v, chi (Q v)) = -16)
    {A : Subgroup (V ≃ₗ[K] V)} (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hA : IsElemAbelian 3 A) (h9 : Nat.card A = 9) :
    ∃ a ∈ A, a ≠ 1 ∧ 4 ≤ finrank K (fixedSpace (a : V ≃ₗ[K] V)) := by
  by_contra hcon
  push Not at hcon
  have h3 : ∀ a ∈ A, a ≠ 1 → finrank K (fixedSpace (a : V ≃ₗ[K] V)) ≤ 3 := by
    intro a ha ha1
    have := hcon a ha ha1
    omega
  haveI : Nontrivial ↥A := by
    rw [← Finite.one_lt_card_iff_nontrivial, h9]
    norm_num
  obtain ⟨x, hxA, hx1⟩ := Subgroup.exists_ne_one_of_nontrivial A
  have hx3 : x ^ 3 = 1 := hA.2 x hxA
  have hz3 : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hnotle : ¬ A ≤ Subgroup.zpowers x := by
    intro hle
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨y, hyA, hyx⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hy3 : y ^ 3 = 1 := hA.2 y hyA
  have hcomm : Commute (x : V ≃ₗ[K] V) (y : V ≃ₗ[K] V) := by
    have h := hA.1.is_comm.comm ⟨x, hxA⟩ ⟨y, hyA⟩
    exact congrArg Subtype.val h
  have hxy1 : (x : V ≃ₗ[K] V) * y ≠ 1 := by
    intro h
    apply hyx
    have hyx' : (y : V ≃ₗ[K] V) = (x : V ≃ₗ[K] V)⁻¹ := by
      have hh := congrArg (fun e : V ≃ₗ[K] V => (x : V ≃ₗ[K] V)⁻¹ * e) h
      simpa [mul_assoc] using hh
    rw [hyx']
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
  have hxy21 : (x : V ≃ₗ[K] V) * y ^ 2 ≠ 1 := by
    intro h
    apply hyx
    have hy4 : (y : V ≃ₗ[K] V) ^ 4 = y := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hy3, one_mul]
    have hy2eq : (y : V ≃ₗ[K] V) ^ 2 = (x : V ≃ₗ[K] V)⁻¹ := by
      have hh := congrArg (fun e : V ≃ₗ[K] V => (x : V ≃ₗ[K] V)⁻¹ * e) h
      simpa [pow_two, mul_assoc] using hh
    have hyx' : (y : V ≃ₗ[K] V) = ((x : V ≃ₗ[K] V)⁻¹) ^ 2 := by
      calc (y : V ≃ₗ[K] V) = (y ^ 2) ^ 2 := by
            rw [← pow_mul, show 2 * 2 = 4 from rfl, hy4]
        _ = ((x : V ≃ₗ[K] V)⁻¹) ^ 2 := by rw [hy2eq]
    rw [hyx']
    exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) 2
  exact false_of_fixedSpace_le_three hK hQ hdim hS hx3 hy3 hcomm (hAO hxA) (hAO hyA)
    (h3 x hxA hx1) (h3 y hyA hy1)
    (h3 (x * y) (A.mul_mem hxA hyA) hxy1)
    (h3 (x * y ^ 2) (A.mul_mem hxA (Subgroup.pow_mem A hyA 2)) hxy21)

theorem not_exists_totallySingular_fixed_minus_four [Fintype V]
    (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank K V = 8) (hS : (∑ v, chi (Q v)) = -16)
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) (hd : finrank K (fixedSpace x) = 4) :
    ¬ ∃ W : Submodule K V, W ≤ fixedSpace x ∧ finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0 := by
  classical
  letI : Fintype ↥(fixedSpace x) := Fintype.ofFinite _
  rintro ⟨W, hWle, hWdim, hWQ⟩
  let W' : Submodule K ↥(fixedSpace x) := W.comap (fixedSpace x).subtype
  have hW'dim : finrank K W' = 2 := by
    rw [← hWdim]
    exact (Submodule.comapSubtypeEquivOfLe hWle).finrank_eq
  have hW'Q : ∀ w ∈ W', (Q.comp (fixedSpace x).subtype) w = 0 := fun w hw => hWQ w hw
  have hB : (polarBilin (Q.comp (fixedSpace x).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hcard : Nat.card W' = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hK, hW'dim]
    norm_num
  have hS₁ : (∑ v : fixedSpace x, chi ((Q.comp (fixedSpace x).subtype) v)) = 4 := by
    rw [charSum_eq_of_totallySingular hK hB hW'Q (by rw [hd, hW'dim]), hcard]
    norm_num
  have hmod := charSum_modEq_fixed Q x
    (fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem v) hx.pow_eq_one
  have hsub : (∑ v ∈ Finset.univ.filter (fun v : V => x v = v), chi (Q v)) =
      ∑ v : fixedSpace x, chi ((Q.comp (fixedSpace x).subtype) v) :=
    Finset.sum_subtype (p := (· ∈ fixedSpace x)) _ (fun v => by simp [mem_fixedSpace]) _
  rw [hS, hsub, hS₁] at hmod
  norm_num at hmod

theorem perfectThreeIn_subgroupOf_commutator {G : Type*} [Group G] {C O : Subgroup G}
    (h : PerfectThreeIn C) (hCO : C ≤ O) : PerfectThreeIn (C.subgroupOf ⁅O, O⁆) := by
  obtain ⟨V, hVC, hV, x, hxV, hx3, hx1⟩ := h
  have hVO : V ≤ O := hVC.trans hCO
  have hVD : V ≤ ⁅O, O⁆ := hV ▸ Subgroup.commutator_mono hVO hVO
  refine ⟨V.subgroupOf ⁅O, O⁆, Subgroup.subgroupOf_mono _ hVC, ?_,
    ⟨x, hVD hxV⟩, hxV, ?_, ?_⟩
  · rw [CFSG.GroupTheory.commutator_subgroupOf_eq hVD hVD, hV]
  · apply Subtype.ext
    change x ^ 3 = 1
    exact hx3
  · intro h1
    exact hx1 (congrArg Subtype.val h1)

theorem perfectThreeIn_of_four_le_finrank_fixedSpace [Fintype V]
    (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank K V = 8) (hS : (∑ v, chi (Q v)) = -16)
    {x : V ≃ₗ[K] V} (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (h4 : 4 ≤ finrank K (fixedSpace x)) :
    PerfectThreeIn ((isometryCentralizer Q x).subgroupOf (orthDerived Q)) := by
  have hx : OddOrderIsometry Q 3 x :=
    ⟨hxO, hx3, three_ne_zero, fun v hv => hQ.1 v hv⟩
  have heven := CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine.even_finrank_fixedSpace hx
    (CharP.cast_eq_zero K 2)
  have hne : fixedSpace x ≠ ⊤ := by
    intro htop
    apply hx1
    ext v
    have hv : v ∈ fixedSpace x := by rw [htop]; exact Submodule.mem_top
    simpa [mem_fixedSpace] using hv
  have hproper : fixedSpace x < (⊤ : Submodule K V) := lt_of_le_of_ne le_top hne
  have hlt : finrank K (fixedSpace x) < 8 := by
    rw [← hdim]
    exact Submodule.finrank_lt hne
  have hle6 : finrank K (fixedSpace x) ≤ 6 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hcases : finrank K (fixedSpace x) = 4 ∨ finrank K (fixedSpace x) = 6 := by
    obtain ⟨k, hk⟩ := heven
    have hk2 : k ≤ 3 := by omega
    have hk1 : 2 ≤ k := by omega
    interval_cases k <;> omega
  rcases hcases with h4' | h6
  · have hts := not_exists_totallySingular_fixed_minus_four hK hQ hdim hS hx h4'
    have hP := perfectThreeIn_orthFixed_of_card_two_minus hx h4' hts
    exact perfectThreeIn_subgroupOf_commutator
      (hP.mono (supportedBlock_le_isometryCentralizer (Q := Q) (x := x) (X - 1)))
      (inf_le_left : isometryCentralizer Q x ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
  · have hPN := perfectNoncycThreeIn_orthFixed (Q := Q) (x := x) hx (by omega)
    have hP3 : PerfectThreeIn (isometryCentralizer Q x) :=
      PerfectNoncycThreeIn.perfectThreeIn
        (hPN.mono (supportedBlock_le_isometryCentralizer (Q := Q) (x := x) (X - 1)))
    exact perfectThreeIn_subgroupOf_commutator hP3
      (inf_le_left : isometryCentralizer Q x ≤ TauCeti.QuadraticMap.orthogonalGroup Q)

theorem exists_perfectThreeIn_orthDerived [Fintype V]
    (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank K V = 8) (hS : (∑ v, chi (Q v)) = -16)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) (hA : IsElemAbelian 3 A)
    (h9 : Nat.card A = 9) :
    ∃ a ∈ A, a ≠ 1 ∧
      PerfectThreeIn ((isometryCentralizer Q (a : V ≃ₗ[K] V)).subgroupOf (orthDerived Q)) := by
  have hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hAΩ.trans (Subgroup.commutator_le_self _)
  obtain ⟨a, haA, ha1, h4⟩ := exists_fixedSpace_finrank_ge_four hK hQ hdim hS hAO hA h9
  exact ⟨a, haA, ha1, perfectThreeIn_of_four_le_finrank_fixedSpace hK hQ hdim hS
    (hAO haA) (hA.2 a haA) ha1 h4⟩

end OmM8

end CFSG.LocalAnalysis.GLTheoremA.S262

end
