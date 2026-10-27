module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyDef
public import CFSG.Permutation.SymmetricCoxeter
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Permutation.SymmetricCoxeter

namespace ThetaHom

section Hom

variable {G : Type*} [Group G]

@[expose] def zmodPow (n : ℕ) [NeZero n] (g : G) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G where
  toFun k := g ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hg).symm

theorem zmodPow_apply (n : ℕ) [NeZero n] (g : G) (hg : g ^ n = 1) (k : Multiplicative (ZMod n)) :
    zmodPow n g hg k = g ^ (Multiplicative.toAdd k).val := rfl

variable {f yr : G}

theorem yr_mul_pow (hyf : yr * f * yr⁻¹ = f⁻¹) (n : ℕ) : yr * f ^ n = (f ^ n)⁻¹ * yr := by
  have h : yr * f ^ n * yr⁻¹ = (f ^ n)⁻¹ := by rw [← conj_pow, hyf, inv_pow]
  exact mul_inv_eq_iff_eq_mul.1 h

@[expose] def dihHom (hf : f ^ 4 = 1) (hy : yr * yr = 1) (hyf : yr * f * yr⁻¹ = f⁻¹) :
    DihedralGroup 4 →* G where
  toFun
    | .r k => f ^ k.val
    | .sr k => (f ^ k.val)⁻¹ * yr
  map_one' := by
    rw [DihedralGroup.one_def]
    simp
  map_mul' a b := by
    have hρ : ∀ k : ZMod 4, f ^ k.val = zmodPow 4 f hf (Multiplicative.ofAdd k) := fun k => rfl
    have hneg : ∀ k : ZMod 4, f ^ (-k).val = (f ^ k.val)⁻¹ := by
      intro k
      rw [hρ, hρ, ofAdd_neg, map_inv]
    have hconj : ∀ k : ZMod 4, yr * f ^ k.val = (f ^ k.val)⁻¹ * yr := fun k => yr_mul_pow hyf _
    have hconj' : ∀ k : ZMod 4, yr * (f ^ k.val)⁻¹ = f ^ k.val * yr := by
      intro k
      rw [← hneg k, hconj (-k), ← hneg (-k), neg_neg]
    have hsub : ∀ i j : ZMod 4, f ^ (j - i).val = f ^ j.val * (f ^ i.val)⁻¹ := by
      intro i j
      rw [hρ, hρ, hρ, ofAdd_sub, map_div, div_eq_mul_inv]
    have hadd : ∀ i j : ZMod 4, f ^ (i + j).val = f ^ i.val * f ^ j.val := by
      intro i j
      rw [hρ, hρ, hρ, ofAdd_add, map_mul]
    have hcomm : ∀ i j : ZMod 4, f ^ i.val * f ^ j.val = f ^ j.val * f ^ i.val :=
      fun i j => (Commute.pow_pow_self f _ _).eq
    rcases a with i | i <;> rcases b with j | j
    · show f ^ (i + j).val = f ^ i.val * f ^ j.val
      exact hadd i j
    · show (f ^ (j - i).val)⁻¹ * yr = f ^ i.val * ((f ^ j.val)⁻¹ * yr)
      rw [hsub, mul_inv_rev, inv_inv, mul_assoc]
    · show (f ^ (i + j).val)⁻¹ * yr = (f ^ i.val)⁻¹ * yr * f ^ j.val
      rw [hadd, hcomm, mul_inv_rev, mul_assoc ((f ^ i.val)⁻¹) yr, hconj, ← mul_assoc]
    · show f ^ (j - i).val = (f ^ i.val)⁻¹ * yr * ((f ^ j.val)⁻¹ * yr)
      have e : (f ^ i.val)⁻¹ * yr * ((f ^ j.val)⁻¹ * yr) = (f ^ i.val)⁻¹ * f ^ j.val :=
        calc (f ^ i.val)⁻¹ * yr * ((f ^ j.val)⁻¹ * yr)
            = (f ^ i.val)⁻¹ * ((yr * (f ^ j.val)⁻¹) * yr) := by simp only [mul_assoc]
          _ = (f ^ i.val)⁻¹ * ((f ^ j.val * yr) * yr) := by rw [hconj']
          _ = (f ^ i.val)⁻¹ * f ^ j.val := by rw [mul_assoc, hy, mul_one]
      rw [e, hsub]
      exact ((Commute.pow_pow_self f j.val i.val).inv_right).eq

theorem dihHom_r (hf : f ^ 4 = 1) (hy : yr * yr = 1) (hyf : yr * f * yr⁻¹ = f⁻¹) (k : ZMod 4) :
    dihHom hf hy hyf (DihedralGroup.r k) = f ^ k.val := rfl

theorem dihHom_sr (hf : f ^ 4 = 1) (hy : yr * yr = 1) (hyf : yr * f * yr⁻¹ = f⁻¹) (k : ZMod 4) :
    dihHom hf hy hyf (DihedralGroup.sr k) = (f ^ k.val)⁻¹ * yr := rfl

end Hom

section Commute

variable {G : Type*} [Group G]

theorem commute_perm {ΘS : Equiv.Perm (Fin 5) →* G} {x : ℕ → G}
    (hΘS : ∀ i < 4, ΘS (adjSwap 4 i) = x i) {g : G} (hg : ∀ i < 4, g * x i = x i * g)
    (σ : Equiv.Perm (Fin 5)) : Commute g (ΘS σ) := by
  have htop : (Subgroup.centralizer ({g} : Set G)).comap ΘS = ⊤ := by
    rw [eq_top_iff, ← closure_adjSwap 4, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < 4 := hi
    simp only [SetLike.mem_coe, Subgroup.mem_comap, hΘS i hi',
      Subgroup.mem_centralizer_singleton_iff]
    exact (hg i hi').symm
  have hσ : σ ∈ (Subgroup.centralizer ({g} : Set G)).comap ΘS := by
    rw [htop]
    exact Subgroup.mem_top σ
  exact (Subgroup.mem_centralizer_singleton_iff.1 hσ).symm

variable {f yr : G}

theorem commute_dihHom {hf : f ^ 4 = 1} {hy : yr * yr = 1} {hyf : yr * f * yr⁻¹ = f⁻¹} {g : G}
    (hgf : Commute g f) (hgy : Commute g yr) (d : DihedralGroup 4) :
    Commute g (dihHom hf hy hyf d) := by
  rcases d with k | k
  · exact hgf.pow_right _
  · exact (hgf.pow_right _).inv_right.mul_right hgy

end Commute

section Perm

open Equiv Equiv.Perm

theorem sign_adjSwap {i : ℕ} (hi : i < 4) : sign (adjSwap 4 i) = -1 := by
  rw [adjSwap_of_lt hi, sign_swap]
  simp [Fin.ext_iff]

theorem adjSwap_mul_mem_alternatingGroup :
    adjSwap 4 0 * adjSwap 4 1 ∈ alternatingGroup (Fin 5) := by
  rw [mem_alternatingGroup, sign_mul, sign_adjSwap (by norm_num), sign_adjSwap (by norm_num)]
  rfl

variable {G : Type*} [Group G]

theorem perm_five_injective (ΘS : Perm (Fin 5) →* G) (h3 : ΘS (adjSwap 4 0 * adjSwap 4 1) ≠ 1) :
    Function.Injective ΘS := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let φ : alternatingGroup (Fin 5) →* G := ΘS.comp (alternatingGroup (Fin 5)).subtype
  have hA : ∀ a ∈ alternatingGroup (Fin 5), ΘS a = 1 → a = 1 := by
    rcases φ.normal_ker.eq_bot_or_eq_top with hk | hk
    · intro a ha h1
      have hmem : (⟨a, ha⟩ : alternatingGroup (Fin 5)) ∈ φ.ker := h1
      rw [hk, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exfalso
      refine h3 ?_
      have hmem : (⟨adjSwap 4 0 * adjSwap 4 1, adjSwap_mul_mem_alternatingGroup⟩ :
          alternatingGroup (Fin 5)) ∈ φ.ker := by
        rw [hk]
        exact Subgroup.mem_top _
      exact hmem
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine CFSG.perm_eq_one_of_forall_commute (by simp) fun τ => ?_
  have hc : σ * τ * σ⁻¹ * τ⁻¹ = 1 := by
    refine hA _ ?_ ?_
    · rw [mem_alternatingGroup]
      simp only [map_mul, map_inv]
      exact (by decide : ∀ a b : ℤˣ, a * b * a⁻¹ * b⁻¹ = 1) _ _
    · simp [hσ]
  rwa [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc

end Perm

section Assembly

open Equiv Equiv.Perm

variable {G : Type*} [Group G]

theorem exists_prod_hom (ΘD : DihedralGroup 4 →* G) (ΘZ : Z3 →* G) (ΘS : Perm (Fin 5) →* G)
    (h1 : ∀ d c, Commute (ΘD d) (ΘZ c)) (h2 : ∀ d σ, Commute (ΘD d) (ΘS σ))
    (h3 : ∀ c σ, Commute (ΘZ c) (ΘS σ)) :
    ∃ Θ : HModel →* G, ∀ d c σ, Θ (d, c, σ) = ΘD d * ΘZ c * ΘS σ := by
  refine ⟨ΘD.noncommCoprod (ΘZ.noncommCoprod ΘS h3) fun d p => ?_, fun d c σ => ?_⟩
  · simpa using (h1 d p.1).mul_right (h2 d p.2)
  · simp [mul_assoc]

theorem prod_hom_injective (Θ : HModel →* G) (ΘD : DihedralGroup 4 →* G) (ΘZ : Z3 →* G)
    (ΘS : Perm (Fin 5) →* G) (hΘ : ∀ d c σ, Θ (d, c, σ) = ΘD d * ΘZ c * ΘS σ)
    (h2 : ∀ d σ, Commute (ΘD d) (ΘS σ)) (h3 : ∀ c σ, Commute (ΘZ c) (ΘS σ))
    (hD : Function.Injective ΘD) (hZ : Function.Injective ΘZ) (hS : Function.Injective ΘS) :
    Function.Injective Θ := by
  rw [injective_iff_map_eq_one]
  rintro ⟨d, c, σ⟩ h
  rw [hΘ] at h
  have hσ : σ = 1 := by
    refine CFSG.perm_eq_one_of_forall_commute (by simp) fun τ => hS ?_
    have e : ΘS σ = (ΘD d * ΘZ c)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [map_mul, map_mul, e]
    exact (((h2 d τ).mul_left (h3 c τ)).inv_left).eq
  subst hσ
  rw [map_one, mul_one] at h
  have hd : ΘD d = (ΘZ c)⁻¹ := eq_inv_of_mul_eq_one_left h
  have h3' : ΘD d ^ 3 = 1 := by
    rw [hd, inv_pow, ← map_pow, (by decide : ∀ c : Z3, c ^ 3 = 1) c, map_one, inv_one]
  have h4' : ΘD d ^ 4 = 1 := by
    rw [← map_pow, (by decide : ∀ d : DihedralGroup 4, d ^ 4 = 1) d, map_one]
  have hD1 : ΘD d = 1 :=
    calc ΘD d = ΘD d ^ 4 * (ΘD d ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4', h3', inv_one, mul_one]
  have hZ1 : ΘZ c = 1 := by
    rw [hD1, one_mul] at h
    exact h
  have hd1 : d = 1 := hD (hD1.trans (map_one ΘD).symm)
  have hc1 : c = 1 := hZ (hZ1.trans (map_one ΘZ).symm)
  subst hd1 hc1
  rfl

end Assembly

end ThetaHom

end CFSG.EvenSporadicStandard.TwoHS
