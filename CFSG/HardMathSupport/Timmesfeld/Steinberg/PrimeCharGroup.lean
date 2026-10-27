module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeChar
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharStabilizer

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {p : ℕ}

theorem exists_pChar_ker_eq (hp : p.Prime) {K : Type*} [Field K]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Kˣ) (hpow : ∀ x, χ x ^ p = 1) :
    ∃ χ' : Multiplicative (Fin τ.rank → ℤ) →* Zp p, ∀ x, χ x = 1 ↔ χ' x = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases hall : ∀ x, χ x = 1
  · exact ⟨1, fun x => by simp [hall x]⟩
  obtain ⟨x0, hx0⟩ : ∃ x, χ x ≠ 1 := by
    by_contra hc
    exact hall fun x => by
      by_contra h
      exact hc ⟨x, h⟩
  set ω : Kˣ := χ x0 with hω
  have hω1 : ω ≠ 1 := hx0
  have hord : orderOf ω = p := orderOf_eq_prime (hpow x0) hω1
  have hprim : IsPrimitiveRoot ω p := IsPrimitiveRoot.iff_orderOf.2 hord
  have hprimK : IsPrimitiveRoot (ω : K) p := IsPrimitiveRoot.coe_units_iff.2 hprim
  have hcases : ∀ y : Kˣ, y ^ p = 1 → ∃ i < p, ω ^ i = y := by
    intro y hy
    have hy' : (y : K) ^ p = 1 := by simpa using congrArg Units.val hy
    obtain ⟨i, hi, hiy⟩ := hprimK.eq_pow_of_pow_eq_one hy'
    exact ⟨i, hi, Units.ext (by simpa using hiy)⟩
  have hpow' : ∀ m : ℕ, ω ^ m = ω ^ (m % p) := fun m => pow_eq_pow_mod m (hpow x0)
  let ψ : Zp p →* Kˣ :=
    { toFun := fun z => ω ^ (Zp.toAdd z).val
      map_one' := by
        change ω ^ (0 : ZMod p).val = 1
        simp
      map_mul' := fun a b => by
        change ω ^ (Zp.toAdd a + Zp.toAdd b).val = ω ^ (Zp.toAdd a).val * ω ^ (Zp.toAdd b).val
        rw [ZMod.val_add, ← pow_add, ← hpow'] }
  have hψ : ∀ z : Zp p, ψ z = 1 → z = 1 := by
    intro z hz
    change ω ^ (Zp.toAdd z).val = 1 at hz
    have hv : (Zp.toAdd z).val < p := ZMod.val_lt _
    have hdvd : p ∣ (Zp.toAdd z).val := by
      have := orderOf_dvd_of_pow_eq_one hz
      rwa [hord] at this
    have h0 : (Zp.toAdd z).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hv
    have h1 : Zp.toAdd z = 0 := (ZMod.val_eq_zero _).1 h0
    rw [← Zp.ofAdd_toAdd z, h1]
    rfl
  choose idx hidx hωidx using fun j : Fin τ.rank =>
    hcases (χ (Multiplicative.ofAdd (Pi.single j 1))) (hpow _)
  let k : Fin τ.rank → ZMod p := fun j => (idx j : ZMod p)
  have hfac : χ = ψ.comp (pChar k) := by
    refine lattice_hom_ext fun j => ?_
    have hk : pPairing k (Pi.single j 1) = k j := by
      have := pPairing_zsmul_single k 1 j
      rwa [one_smul, Int.cast_one, mul_one] at this
    change _ = ω ^ (pPairing k (Pi.single j 1)).val
    rw [hk]
    simp only [k]
    rw [ZMod.val_natCast_of_lt (hidx j), hωidx j]
  refine ⟨pChar k, fun x => ?_⟩
  have hx : χ x = ψ (pChar k x) := by rw [hfac]; rfl
  rw [hx]
  exact ⟨hψ _, fun h => by rw [h, map_one]⟩

@[expose] def rootCharHomP {K : Type} [Field K] (a : Fin τ.rank → Kˣ) :
    Multiplicative (Fin τ.rank → ℤ) →* Kˣ where
  toFun v := rootChar a (Multiplicative.toAdd v)
  map_one' := rootChar_zero a
  map_mul' _ _ := rootChar_add a _ _

theorem rootCharHomP_pow {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (hp : ∀ i, a i ^ p = 1) (x : Multiplicative (Fin τ.rank → ℤ)) : rootCharHomP a x ^ p = 1 := by
  change rootChar a (Multiplicative.toAdd x) ^ p = 1
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp i, one_zpow]

theorem rootCharStabilizerSubgroup_eq_kernelReflectionGroup_of_pChar (hp : p.Prime)
    (hZ : ∀ χ : Multiplicative (Fin τ.rank → ℤ) →* Zp p, charStabilizer χ ≤ kernelWeylGroup χ)
    {K : Type} [Field K] (a : Fin τ.rank → Kˣ) (hpa : ∀ i, a i ^ p = 1) :
    rootCharStabilizerSubgroup a = kernelReflectionGroup a := by
  obtain ⟨χ', hker⟩ := exists_pChar_ker_eq hp (rootCharHomP a) (rootCharHomP_pow a hpa)
  have hS : rootCharStabilizerSubgroup a = charStabilizer (rootCharHomP a) :=
    Subgroup.ext fun w => Iff.rfl
  have hW : kernelReflectionGroup a = kernelWeylGroup (rootCharHomP a) := rfl
  rw [hS, hW]
  refine le_antisymm ?_ kernelWeylGroup_le
  rw [charStabilizer_congr_ker hker, kernelWeylGroup_congr_ker hker]
  exact hZ χ'

end CFSG.HardMathSupport.Timmesfeld.Steinberg
