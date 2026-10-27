module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar
public import CFSG.LieType.Chevalley.SignStabilizerQuotients
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag}

theorem card_charQuotient_le_of_orbitCheck3
    {reps : List (List ℕ)} {entries : List ℕ}
    (hO : orbitCheck3 τ reps entries = true) {B : ℕ}
    (hB : ∀ ρ < reps.length,
      Nat.card (kernelPosStabilizer (triChar (vec3 (τ := τ) (reps.getD ρ [])))) ≤ B)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Z3) : Nat.card (CharQuotient χ) ≤ B := by
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck3 hO χ
  rw [← Nat.card_congr (quotientMulEquivOfIsCharConj ht).toEquiv]
  exact card_quotient_le_card_kernelPosStabilizer.trans (hB ρ hρ)

section Kernel

variable {M M' : Type*} [CommGroup M] [CommGroup M']
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}

theorem charStabilizer_congr_ker (h : ∀ x, χ x = 1 ↔ χ' x = 1) :
    charStabilizer χ = charStabilizer χ' := by
  ext w
  have key : ∀ v : Fin τ.rank → ℤ, χ (Multiplicative.ofAdd (w • v)) = χ (Multiplicative.ofAdd v) ↔
      χ' (Multiplicative.ofAdd (w • v)) = χ' (Multiplicative.ofAdd v) := by
    intro v
    have h1 : χ (Multiplicative.ofAdd (w • v)) = χ (Multiplicative.ofAdd v) ↔
        χ (Multiplicative.ofAdd (w • v) * (Multiplicative.ofAdd v)⁻¹) = 1 := by
      rw [map_mul, map_inv, mul_inv_eq_one]
    have h2 : χ' (Multiplicative.ofAdd (w • v)) = χ' (Multiplicative.ofAdd v) ↔
        χ' (Multiplicative.ofAdd (w • v) * (Multiplicative.ofAdd v)⁻¹) = 1 := by
      rw [map_mul, map_inv, mul_inv_eq_one]
    rw [h1, h2]
    exact h _
  exact forall_congr' key

theorem kernelRoots_congr_ker (h : ∀ x, χ x = 1 ↔ χ' x = 1) : kernelRoots χ = kernelRoots χ' := by
  ext α
  exact and_congr_right fun _ => h _

theorem kernelWeylGroup_congr_ker (h : ∀ x, χ x = 1 ↔ χ' x = 1) :
    kernelWeylGroup χ = kernelWeylGroup χ' := by
  rw [kernelWeylGroup, kernelWeylGroup, kernelRoots_congr_ker h]

end Kernel

theorem exists_triChar_ker_eq {K : Type*} [Field K]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Kˣ) (h3 : ∀ x, χ x ^ 3 = 1) :
    ∃ χ' : Multiplicative (Fin τ.rank → ℤ) →* Z3, ∀ x, χ x = 1 ↔ χ' x = 1 := by
  classical
  by_cases hall : ∀ x, χ x = 1
  · exact ⟨1, fun x => by simp [hall x]⟩
  obtain ⟨x0, hx0⟩ : ∃ x, χ x ≠ 1 := by
    by_contra hc
    exact hall fun x => by
      by_contra h
      exact hc ⟨x, h⟩
  set ω : Kˣ := χ x0 with hω
  have hω3 : ω ^ 3 = 1 := h3 x0
  have hω1 : ω ≠ 1 := hx0
  have h1 : (ω : K) ^ 3 = 1 := by simpa using congrArg Units.val hω3
  have hsum : ((1 : K) + ω + ω ^ 2) = 0 := by
    have h2 : (ω : K) ≠ 1 := fun h => hx0 (Units.ext h)
    have : ((ω : K) - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h2)
  have hcases : ∀ y : Kˣ, y ^ 3 = 1 → y = 1 ∨ y = ω ∨ y = ω ^ 2 := by
    intro y hy
    have hy' : (y : K) ^ 3 = 1 := by simpa using congrArg Units.val hy
    have : ((y : K) - 1) * ((y : K) - ω) * ((y : K) - ω ^ 2) = 0 := by
      linear_combination hy' + ((y : K) - (y : K) ^ 2) * hsum + ((y : K) - 1) * h1
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (Units.ext (sub_eq_zero.1 h))
      · exact Or.inr (Or.inl (Units.ext (sub_eq_zero.1 h)))
    · exact Or.inr (Or.inr (Units.ext (by simpa using sub_eq_zero.1 h)))
  have hpow : ∀ m : ℕ, ω ^ m = ω ^ (m % 3) := fun m => pow_eq_pow_mod m hω3
  let ψ : Z3 →* Kˣ :=
    { toFun := fun z => ω ^ (Z3.toAdd z).val
      map_one' := by
        change ω ^ (0 : ZMod 3).val = 1
        simp
      map_mul' := fun a b => by
        change ω ^ (Z3.toAdd a + Z3.toAdd b).val = ω ^ (Z3.toAdd a).val * ω ^ (Z3.toAdd b).val
        rw [ZMod.val_add, ← pow_add, ← hpow] }
  have hψ : ∀ z : Z3, ψ z = 1 → z = 1 := by
    intro z hz
    change ω ^ (Z3.toAdd z).val = 1 at hz
    have hv : (Z3.toAdd z).val < 3 := ZMod.val_lt _
    have h0 : Z3.toAdd z = 0 := by
      interval_cases h : (Z3.toAdd z).val
      · exact (ZMod.val_eq_zero _).1 h
      · exact absurd (by simpa using hz) hω1
      · exfalso
        apply hω1
        have : ω ^ 3 = ω ^ 2 * ω := pow_succ ω 2
        rw [hω3, hz, one_mul] at this
        exact this.symm
    rw [← Z3.ofAdd_toAdd z, h0]
    rfl
  let k : Fin τ.rank → ZMod 3 := fun j =>
    if χ (Multiplicative.ofAdd (Pi.single j 1)) = 1 then 0
    else if χ (Multiplicative.ofAdd (Pi.single j 1)) = ω then 1 else 2
  have hfac : χ = ψ.comp (triChar k) := by
    refine lattice_hom_ext fun j => ?_
    have hk : triPairing k (Pi.single j 1) = k j := by
      have := triPairing_zsmul_single k 1 j
      rwa [one_smul, Int.cast_one, mul_one] at this
    change _ = ω ^ (triPairing k (Pi.single j 1)).val
    rw [hk]
    have v0 : (0 : ZMod 3).val = 0 := rfl
    have v1 : (1 : ZMod 3).val = 1 := rfl
    have v2 : (2 : ZMod 3).val = 2 := rfl
    by_cases hA : χ (Multiplicative.ofAdd (Pi.single j 1)) = 1
    · have : k j = 0 := by simp [k, hA]
      rw [this, v0, pow_zero, hA]
    by_cases hB : χ (Multiplicative.ofAdd (Pi.single j 1)) = ω
    · have : k j = 1 := by simp [k, hB, hω1]
      rw [this, v1, pow_one, hB]
    · have hC : χ (Multiplicative.ofAdd (Pi.single j 1)) = ω ^ 2 :=
        ((hcases _ (h3 (Multiplicative.ofAdd (Pi.single j 1)))).resolve_left hA).resolve_left hB
      have : k j = 2 := by simp [k, hA, hB]
      rw [this, v2, hC]
  refine ⟨triChar k, fun x => ?_⟩
  have hx : χ x = ψ (triChar k x) := by rw [hfac]; rfl
  rw [hx]
  exact ⟨hψ _, fun h => by rw [h, map_one]⟩

@[expose] def rootCharHom3 {K : Type} [Field K] (a : Fin τ.rank → Kˣ) :
    Multiplicative (Fin τ.rank → ℤ) →* Kˣ where
  toFun v := rootChar a (Multiplicative.toAdd v)
  map_one' := rootChar_zero a
  map_mul' _ _ := rootChar_add a _ _

theorem rootCharHom3_pow_three {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (h3 : ∀ i, a i ^ 3 = 1) (x : Multiplicative (Fin τ.rank → ℤ)) : rootCharHom3 a x ^ 3 = 1 := by
  change rootChar a (Multiplicative.toAdd x) ^ 3 = 1
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3 i, one_zpow]

theorem rootCharStabilizerSubgroup_eq_kernelReflectionGroup_of_triChar
    (hZ3 : ∀ χ : Multiplicative (Fin τ.rank → ℤ) →* Z3, charStabilizer χ ≤ kernelWeylGroup χ)
    {K : Type} [Field K] (a : Fin τ.rank → Kˣ) (h3 : ∀ i, a i ^ 3 = 1) :
    rootCharStabilizerSubgroup a = kernelReflectionGroup a := by
  obtain ⟨χ', hker⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a h3)
  have hS : rootCharStabilizerSubgroup a = charStabilizer (rootCharHom3 a) :=
    Subgroup.ext fun w => Iff.rfl
  have hW : kernelReflectionGroup a = kernelWeylGroup (rootCharHom3 a) := rfl
  rw [hS, hW]
  refine le_antisymm ?_ kernelWeylGroup_le
  rw [charStabilizer_congr_ker hker, kernelWeylGroup_congr_ker hker]
  exact hZ3 χ'

end CFSG.HardMathSupport.Timmesfeld.Steinberg
