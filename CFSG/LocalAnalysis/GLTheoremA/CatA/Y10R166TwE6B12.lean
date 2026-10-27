module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6Eight
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A2
public import CFSG.Quasithin.H13.NQCatCartanL3

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups Matrix
open CFSG.HardMathSupport.Lang.E6Descent
open CFSG.StandardType.TableBExc.E6Three
open scoped commutatorElement

section Helpers

variable {Ω : Type} [Field Ω] {q : ℕ} [NeZero q]

theorem twE6QVec_nsmul (ζ : Ωˣ) (hζ : ζ ^ q = 1) (n : ℕ) (v : Fin 6 → ZMod q) :
    twE6QVec ζ hζ (n • v) = twE6QVec ζ hζ v ^ n := by
  induction n with
  | zero => rw [zero_nsmul, twE6QVec_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, twE6QVec_add, ih, pow_succ]

theorem twE6QVec_zmod_smul (ζ : Ωˣ) (hζ : ζ ^ q = 1) (c : ZMod q) (v : Fin 6 → ZMod q) :
    twE6QVec ζ hζ (c • v) = twE6QVec ζ hζ v ^ c.val := by
  have hcv : c • v = (c.val : ℕ) • v := by
    funext i
    simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, ZMod.natCast_zmod_val]
  rw [hcv, twE6QVec_nsmul]

theorem zpow_eq_zpow_val_zmod_three {u : Ωˣ} (hu : u ^ 3 = 1) (m : ℤ) :
    u ^ ((m : ZMod 3).val) = u ^ m := by
  rw [← zpow_natCast, ZMod.val_intCast]
  exact (zpow_eq_zpow_emod' m hu).symm

end Helpers

section Certs

local instance e6TwE6BNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

variable {Ω : Type} [Field Ω] [CharP Ω 2]

namespace TwE6B

theorem torusElt_eq_commutator_weylElt (i : Fin Tag.E6.rank) {t : Ωˣ} (ht : t ^ 3 = 1) :
    torusElt Tag.E6 Ω i t = ⁅weylElt Tag.E6 Ω i 1, torusElt Tag.E6 Ω i t⁆ := by
  have ht2 : t ^ (-2 : ℤ) = t := by
    have h3 : t ^ (3 : ℤ) = 1 := by simpa using ht
    calc t ^ (-2 : ℤ) = t ^ (-2 : ℤ) * 1 := (mul_one _).symm
      _ = t ^ (-2 : ℤ) * t ^ (3 : ℤ) := by rw [h3]
      _ = t ^ (-2 + 3 : ℤ) := (_root_.zpow_add _ _ _).symm
      _ = t ^ (1 : ℤ) := by norm_num
      _ = t := zpow_one t
  have h := weylElt_one_mul_torusElt_mul_inv (τ := Tag.E6) (R := Ω) i i t
  rw [Tag.E6.cartan_self, ht2] at h
  rw [show ⁅weylElt Tag.E6 Ω i 1, torusElt Tag.E6 Ω i t⁆ =
      weylElt Tag.E6 Ω i 1 * torusElt Tag.E6 Ω i t *
        (weylElt Tag.E6 Ω i 1)⁻¹ * (torusElt Tag.E6 Ω i t)⁻¹ from rfl, h]
  group

theorem weylElt_one_sq_eq_one (i : Fin Tag.E6.rank) :
    weylElt Tag.E6 Ω i 1 * weylElt Tag.E6 Ω i 1 = 1 := by
  rw [weylElt_one_mul_self]
  have h : (-1 : Ωˣ) = 1 := by
    ext
    rw [Units.val_neg, Units.val_one]
    exact CharTwo.neg_eq 1
  rw [h, torusElt_one]

theorem torusElt_mem_twE6C {Fr : Ω →+* Ω} {n : ℕ} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (hod : Odd n) {t : Ωˣ} (ht : t ^ 3 = 1) (i : Fin Tag.E6.rank) :
    torusElt Tag.E6 Ω i t ∈ twE6C Fr := by
  rw [torusElt_eq_commutator_weylElt i ht]
  have hR : torusElt Tag.E6 Ω i t ∈ TwistedDiag.thetaFixed Fr := by
    rw [TwistedDiag.mem_thetaFixed]
    exact ⟨torusElt_mem_adjointGroup i t,
      theta_torusElt_eq hFr (pow_two_pow_add_one_eq_one ht hod) i⟩
  exact mem_twE6C.2 (Subgroup.commutator_mem_commutator (weylElt_mem_thetaFixed Fr i) hR)

theorem weylElt_mem_twE6C {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {σ : K →+* K} {Fr : Ω →+* Ω} {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (i : Fin Tag.E6.rank) :
    weylElt Tag.E6 Ω i 1 ∈ twE6C Fr := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, hgn⟩ := twE6EnnolaConj (ℓ := 2) Nat.prime_two hn hK hFr
  have h3 : (weylElt Tag.E6 Ω i 1) ^ 3 ∈ ⁅TwistedDiag.thetaFixed Fr, TwistedDiag.thetaFixed Fr⁆ :=
    rgrp_pow_three_mem_derived Nat.prime_two hn hK (fun c => hσ c) hFr hg hgn
      (weylElt_mem_thetaFixed Fr i)
  have hcube : (weylElt Tag.E6 Ω i 1) ^ 3 = weylElt Tag.E6 Ω i 1 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, weylElt_one_sq_eq_one, one_mul]
  rw [hcube] at h3
  exact mem_twE6C.2 h3

theorem le_twE6C_of_isPGroup_two {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {σ : K →+* K} {Fr : Ω →+* Ω} {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) {S : Subgroup (ModGL Tag.E6 Ω)}
    (hSR : S ≤ TwistedDiag.thetaFixed Fr) (hS2 : IsPGroup 2 ↥S) : S ≤ twE6C Fr := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, hgn⟩ := twE6EnnolaConj (ℓ := 2) Nat.prime_two hn hK hFr
  intro x hx
  obtain ⟨e, he⟩ := hS2 ⟨x, hx⟩
  have hx3 : x ^ 3 ∈ ⁅TwistedDiag.thetaFixed Fr, TwistedDiag.thetaFixed Fr⁆ :=
    rgrp_pow_three_mem_derived Nat.prime_two hn hK (fun c => hσ c) hFr hg hgn (hSR hx)
  have hpow : x ^ 2 ^ e = 1 := by
    simpa using congrArg Subtype.val he
  exact mem_twE6C.2 (CFSG.Quasithin.H13.NQCat.CartanL3.mem_of_pow_three_mem hx3 hpow)

private theorem torusElt_eq_twE6QVec_cartan (i : Fin Tag.E6.rank) {ω : Ωˣ}
    (hω3 : ω ^ 3 = 1) :
    twE6QVec (q := 3) ω hω3 (fun j : Fin 6 => (Tag.E6.cartan i j : ZMod 3)) =
      torusElt Tag.E6 Ω i ω := by
  rw [torusElt_eq_rootDiagUnit, twE6QVec]
  congr 1
  funext j
  rw [zetaVec_apply]
  have hcast : twE6Cast (q := 3) (fun j : Fin 6 => (Tag.E6.cartan i j : ZMod 3)) j
      = (Tag.E6.cartan i j : ZMod 3) := rfl
  rw [hcast]
  exact zpow_eq_zpow_val_zmod_three hω3 (Tag.E6.cartan i j)

private theorem twE6B0Vec_zero_eq :
    twE6B0Vec (q := 3) 0 = fun j : Fin 6 => (Tag.E6.cartan 1 j : ZMod 3) := by
  funext j
  fin_cases j <;> decide

private theorem twE6B0Vec_one_eq :
    twE6B0Vec (q := 3) 1 = fun j : Fin 6 => (Tag.E6.cartan 2 j : ZMod 3) := by
  funext j
  fin_cases j <;> decide

private theorem twE6B0Vec_two_eq :
    twE6B0Vec (q := 3) 2 = fun j : Fin 6 => (Tag.E6.cartan 3 j : ZMod 3) := by
  funext j
  fin_cases j <;> decide

private theorem twE6B0Vec_three_eq :
    twE6B0Vec (q := 3) 3 =
      (2 : ℕ) • (fun j : Fin 6 => (Tag.E6.cartan 4 j : ZMod 3)) +
        (fun j : Fin 6 => (Tag.E6.cartan 5 j : ZMod 3)) := by
  funext j
  fin_cases j <;> decide

private theorem torusElt_sq (i : Fin Tag.E6.rank) (u : Ωˣ) :
    torusElt Tag.E6 Ω i (u ^ 2) = (torusElt Tag.E6 Ω i u) ^ 2 := by
  calc torusElt Tag.E6 Ω i (u ^ 2) = torusElt Tag.E6 Ω i (u * u) := by rw [pow_two]
    _ = torusElt Tag.E6 Ω i u * torusElt Tag.E6 Ω i u := torusElt_mul i u u
    _ = (torusElt Tag.E6 Ω i u) ^ 2 := (pow_two _).symm

private theorem twE6QVec_b0Vec_zero {ω : Ωˣ} (hω3 : ω ^ 3 = 1) :
    twE6QVec (q := 3) ω hω3 (twE6B0Vec 0) = torusElt Tag.E6 Ω 1 ω := by
  rw [twE6B0Vec_zero_eq]
  exact torusElt_eq_twE6QVec_cartan 1 hω3

private theorem twE6QVec_b0Vec_one {ω : Ωˣ} (hω3 : ω ^ 3 = 1) :
    twE6QVec (q := 3) ω hω3 (twE6B0Vec 1) = torusElt Tag.E6 Ω 2 ω := by
  rw [twE6B0Vec_one_eq]
  exact torusElt_eq_twE6QVec_cartan 2 hω3

private theorem twE6QVec_b0Vec_two {ω : Ωˣ} (hω3 : ω ^ 3 = 1) :
    twE6QVec (q := 3) ω hω3 (twE6B0Vec 2) = torusElt Tag.E6 Ω 3 ω := by
  rw [twE6B0Vec_two_eq]
  exact torusElt_eq_twE6QVec_cartan 3 hω3

private theorem twE6QVec_b0Vec_three {ω : Ωˣ} (hω3 : ω ^ 3 = 1) :
    twE6QVec (q := 3) ω hω3 (twE6B0Vec 3) =
      torusElt Tag.E6 Ω 4 (ω ^ 2) * torusElt Tag.E6 Ω 5 ω := by
  have hA : twE6QVec (q := 3) ω hω3
      ((2 : ℕ) • (fun j : Fin 6 => (Tag.E6.cartan 4 j : ZMod 3))) =
      (torusElt Tag.E6 Ω 4 ω) ^ 2 :=
    (twE6QVec_nsmul ω hω3 2 (fun j : Fin 6 => (Tag.E6.cartan 4 j : ZMod 3))).trans
      (congrArg (fun x => x ^ 2) (torusElt_eq_twE6QVec_cartan 4 hω3))
  have hB : twE6QVec (q := 3) ω hω3 (fun j : Fin 6 => (Tag.E6.cartan 5 j : ZMod 3)) =
      torusElt Tag.E6 Ω 5 ω := torusElt_eq_twE6QVec_cartan 5 hω3
  have hsplit : twE6QVec (q := 3) ω hω3
      (((2 : ℕ) • (fun j : Fin 6 => (Tag.E6.cartan 4 j : ZMod 3))) +
        (fun j : Fin 6 => (Tag.E6.cartan 5 j : ZMod 3))) =
      twE6QVec (q := 3) ω hω3 ((2 : ℕ) • (fun j : Fin 6 => (Tag.E6.cartan 4 j : ZMod 3))) *
        twE6QVec (q := 3) ω hω3 (fun j : Fin 6 => (Tag.E6.cartan 5 j : ZMod 3)) :=
    twE6QVec_add ω hω3 _ _
  calc twE6QVec (q := 3) ω hω3 (twE6B0Vec 3)
      = twE6QVec (q := 3) ω hω3
          (((2 : ℕ) • (fun j : Fin 6 => (Tag.E6.cartan 4 j : ZMod 3))) +
            (fun j : Fin 6 => (Tag.E6.cartan 5 j : ZMod 3))) := by
        rw [twE6B0Vec_three_eq]
    _ = twE6QVec (q := 3) ω hω3 ((2 : ℕ) • (fun j : Fin 6 => (Tag.E6.cartan 4 j : ZMod 3))) *
          twE6QVec (q := 3) ω hω3 (fun j : Fin 6 => (Tag.E6.cartan 5 j : ZMod 3)) := hsplit
    _ = (torusElt Tag.E6 Ω 4 ω) ^ 2 * torusElt Tag.E6 Ω 5 ω := by rw [hA, hB]
    _ = torusElt Tag.E6 Ω 4 (ω ^ 2) * torusElt Tag.E6 Ω 5 ω := by rw [torusElt_sq]

theorem twE6BZero_le_of_gens {ω : Ωˣ} (hω3 : ω ^ 3 = 1) {H : Subgroup (ModGL Tag.E6 Ω)}
    (h1 : torusElt Tag.E6 Ω 1 ω ∈ H) (h2 : torusElt Tag.E6 Ω 2 ω ∈ H)
    (h3 : torusElt Tag.E6 Ω 3 ω ∈ H)
    (h45 : torusElt Tag.E6 Ω 4 (ω ^ 2) * torusElt Tag.E6 Ω 5 ω ∈ H) :
    twE6BZero ω hω3 ≤ H := by
  intro b hb
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hb
  change twE6QVec (q := 3) ω hω3
    (∑ j : Fin 4, Multiplicative.toAdd c j • twE6B0Vec j) ∈ H
  rw [Fin.sum_univ_four, twE6QVec_add, twE6QVec_add, twE6QVec_add,
    twE6QVec_zmod_smul, twE6QVec_zmod_smul, twE6QVec_zmod_smul, twE6QVec_zmod_smul,
    twE6QVec_b0Vec_zero hω3, twE6QVec_b0Vec_one hω3, twE6QVec_b0Vec_two hω3,
    twE6QVec_b0Vec_three hω3]
  exact mul_mem (mul_mem (mul_mem (Subgroup.pow_mem H h1 _) (Subgroup.pow_mem H h2 _))
    (Subgroup.pow_mem H h3 _)) (Subgroup.pow_mem H h45 _)

private theorem eBar_vec_eq :
    (fun j : Fin 6 => (Tag.E6.cartan 4 j : ZMod 3)) +
        (2 : ℕ) • (fun j : Fin 6 => (Tag.E6.cartan 5 j : ZMod 3)) =
      (2 : ℕ) • twE6B0Vec (q := 3) 3 := by
  funext j
  fin_cases j <;> decide

private theorem eBar_comb_eq :
    (2 : ℕ) • twE6B0Vec (q := 3) 3 = twE6B0Comb (q := 3) (Pi.single 3 2) := by
  funext j
  fin_cases j <;> decide

private theorem fBar_comb_eq :
    twE6B0Vec (q := 3) 1 = twE6B0Comb (q := 3) (Pi.single 1 1) := by
  funext j
  fin_cases j <;> decide

private theorem eBar_eq_twE6QVec {ω : Ωˣ} (hω3 : ω ^ 3 = 1) :
    eBar (Ω := Ω) ω = twE6QVec (q := 3) ω hω3 ((2 : ℕ) • twE6B0Vec 3) := by
  have h4 : torusElt Tag.E6 Ω 4 ω =
      twE6QVec (q := 3) ω hω3 (fun j : Fin 6 => (Tag.E6.cartan 4 j : ZMod 3)) :=
    (torusElt_eq_twE6QVec_cartan 4 hω3).symm
  have h5 : torusElt Tag.E6 Ω 5 (ω ^ 2) =
      twE6QVec (q := 3) ω hω3
        ((2 : ℕ) • (fun j : Fin 6 => (Tag.E6.cartan 5 j : ZMod 3))) := by
    rw [torusElt_sq]
    rw [show torusElt Tag.E6 Ω 5 ω = twE6QVec (q := 3) ω hω3
        (fun j : Fin 6 => (Tag.E6.cartan 5 j : ZMod 3)) from
      (torusElt_eq_twE6QVec_cartan 5 hω3).symm]
    exact (twE6QVec_nsmul ω hω3 2 (fun j : Fin 6 => (Tag.E6.cartan 5 j : ZMod 3))).symm
  have hsplit := (twE6QVec_add ω hω3
    (fun j : Fin 6 => (Tag.E6.cartan 4 j : ZMod 3))
    ((2 : ℕ) • (fun j : Fin 6 => (Tag.E6.cartan 5 j : ZMod 3)))).symm
  have hvec := eBar_vec_eq
  calc eBar (Ω := Ω) ω = torusElt Tag.E6 Ω 4 ω * torusElt Tag.E6 Ω 5 (ω ^ 2) :=
        eBar_eq_torusElt hω3
    _ = twE6QVec (q := 3) ω hω3 (fun j : Fin 6 => (Tag.E6.cartan 4 j : ZMod 3)) *
          twE6QVec (q := 3) ω hω3
            ((2 : ℕ) • (fun j : Fin 6 => (Tag.E6.cartan 5 j : ZMod 3))) := by
        rw [h4, h5]
    _ = twE6QVec (q := 3) ω hω3
          ((fun j : Fin 6 => (Tag.E6.cartan 4 j : ZMod 3)) +
            (2 : ℕ) • (fun j : Fin 6 => (Tag.E6.cartan 5 j : ZMod 3))) := hsplit
    _ = twE6QVec (q := 3) ω hω3 ((2 : ℕ) • twE6B0Vec 3) := by rw [hvec]

theorem eBar_mem_twE6BZero {ω : Ωˣ} (hω3 : ω ^ 3 = 1) :
    eBar (Ω := Ω) ω ∈ twE6BZero ω hω3 := by
  have hmem := twE6B0Comb_mem ω hω3 (Pi.single 3 2)
  rw [← eBar_comb_eq] at hmem
  rwa [← eBar_eq_twE6QVec (Ω := Ω) hω3] at hmem

theorem fBar_mem_twE6BZero {ω : Ωˣ} (hω3 : ω ^ 3 = 1) :
    fBar (Ω := Ω) ω ∈ twE6BZero ω hω3 := by
  have hfb : fBar (Ω := Ω) ω = twE6QVec (q := 3) ω hω3 (twE6B0Vec 1) :=
    (fBar_eq_torusElt hω3).trans (twE6QVec_b0Vec_one hω3).symm
  have hmem := twE6B0Comb_mem ω hω3 (Pi.single 1 1)
  rw [← fBar_comb_eq] at hmem
  rwa [← hfb] at hmem

theorem exists_kernelComponent_omega1 {ω : Ωˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    Nonempty (KernelComponent (rootCharHom (twE6omega1Tuple ω))) := by
  have hmem : (Pi.single (1 : Fin Tag.E6.rank) 1) ∈
      kernelRoots (rootCharHom (twE6omega1Tuple ω)) := by
    rw [kernelRoots_omega1 Nat.prime_three hω3 hω1]
    refine ⟨isRoot_single Tag.E6 1, ?_⟩
    rw [Pi.single_eq_of_ne (show (0 : Fin Tag.E6.rank) ≠ 1 by decide)]
  exact ⟨⟦⟨_, hmem⟩⟧⟩

end TwE6B

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
