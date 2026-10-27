module

public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KE.CTTorus

open scoped Matrix

variable {τ : Tag} {L : Type} [Field L]

@[expose] def expTuple (ζ : Lˣ) {p : ℕ} (z : Fin τ.rank → ZMod p) : Fin τ.rank → Lˣ :=
  fun i => ζ ^ (z i).val

theorem rootChar_expTuple {ζ : Lˣ} {p : ℕ} (z : Fin τ.rank → ZMod p) (u : Fin τ.rank → ℤ) :
    rootChar (expTuple ζ z) u = ζ ^ (∑ i, ((z i).val : ℤ) * u i) := by
  unfold rootChar expTuple
  have : ∀ i, (ζ ^ (z i).val) ^ u i = ζ ^ (((z i).val : ℤ) * u i) := fun i => by
    rw [← zpow_natCast, ← zpow_mul]
  simp only [this]
  induction (Finset.univ : Finset (Fin τ.rank)) using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, zpow_add, ih]

@[expose] def modMat (p : ℕ) (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) :
    Matrix (Fin τ.rank) (Fin τ.rank) (ZMod p) :=
  M.map (Int.castRingHom (ZMod p))

theorem cast_rootChar_exponent {p : ℕ} [NeZero p] (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (z : Fin τ.rank → ZMod p) (u : Fin τ.rank → ℤ) (q : ℕ) :
    ((∑ i, ((z i).val : ℤ) * (M *ᵥ u) i - (∑ i, ((z i).val : ℤ) * u i) * q : ℤ) : ZMod p) =
      ∑ j, ((u j : ℤ) : ZMod p) * ((modMat p M)ᵀ *ᵥ z - (q : ZMod p) • z) j := by
  simp only [Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
    Matrix.mulVec, dotProduct, Int.cast_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, modMat,
    Matrix.transpose_apply, Matrix.map_apply, eq_intCast, Int.cast_natCast]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem expTuple_mem_fixedCharTuples_iff {ζ : Lˣ} {p : ℕ} [NeZero p] (hζ : IsPrimitiveRoot ζ p)
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (Fr : L →+* L) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (z : Fin τ.rank → ZMod p) :
    expTuple ζ z ∈ fixedCharTuples M Fr ↔ (modMat p M)ᵀ *ᵥ z = (q : ZMod p) • z := by
  rw [mem_fixedCharTuples_iff]
  have key : ∀ u : Fin τ.rank → ℤ,
      rootChar (expTuple ζ z) (M *ᵥ u) = Units.map Fr.toMonoidHom (rootChar (expTuple ζ z) u) ↔
        ∑ j, ((u j : ℤ) : ZMod p) * ((modMat p M)ᵀ *ᵥ z - (q : ZMod p) • z) j = 0 := by
    intro u
    rw [map_units_eq_pow hFr, rootChar_expTuple, rootChar_expTuple, ← zpow_natCast, ← zpow_mul,
      ← cast_rootChar_exponent M z u q, ZMod.intCast_zmod_eq_zero_iff_dvd _ p,
      ← hζ.zpow_eq_one_iff_dvd, zpow_sub, mul_inv_eq_one]
  simp only [key]
  constructor
  · intro h
    ext j
    have := h (Pi.single j 1)
    simp only [Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
    simpa [sub_eq_zero] using this
  · intro h u
    have h0 : ∀ j, ((modMat p M)ᵀ *ᵥ z - (q : ZMod p) • z) j = 0 := fun j => by
      rw [sub_eq_zero.2 h]
      rfl
    exact Finset.sum_eq_zero fun j _ => by rw [h0 j, mul_zero]

theorem exists_primitiveRoot_units [IsAlgClosed L] {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) {p : ℕ}
    (hp : p.Prime) (hpℓ : p ≠ ℓ) : ∃ ζ : Lˣ, IsPrimitiveRoot ζ p := by
  have hpL : (p : L) ≠ 0 := fun h =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 ((CharP.cast_eq_zero_iff L ℓ p).1 h)).symm
  have : NeZero (p : L) := ⟨hpL⟩
  have : HasEnoughRootsOfUnity L p := IsSepClosed.hasEnoughRootsOfUnity L p
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  exact ⟨(hζ₀.isUnit hp.ne_zero).unit, IsPrimitiveRoot.coe_units_iff.mp (by
    rw [IsUnit.unit_spec]
    exact hζ₀)⟩

theorem natCard_fixedTorsion [IsAlgClosed L] (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (Fr : L →+* L) {q ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) (hFr : ∀ c, Fr c = c ^ q) {p : ℕ}
    (hp : p.Prime) (hpℓ : p ≠ ℓ) :
    Nat.card {a : fixedCharTuples M Fr // ∀ i, (a : Fin τ.rank → Lˣ) i ^ p = 1} =
      Nat.card {z : Fin τ.rank → ZMod p // (modMat p M)ᵀ *ᵥ z = (q : ZMod p) • z} := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_units (L := L) hℓ hp hpℓ
  have hζL : IsPrimitiveRoot (ζ : L) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  let Φ : {z : Fin τ.rank → ZMod p // (modMat p M)ᵀ *ᵥ z = (q : ZMod p) • z} →
      {a : fixedCharTuples M Fr // ∀ i, (a : Fin τ.rank → Lˣ) i ^ p = 1} := fun z =>
    ⟨⟨expTuple ζ z.1, (expTuple_mem_fixedCharTuples_iff hζ M Fr hFr _).2 z.2⟩, fun i => by
      show (ζ ^ (z.1 i).val) ^ p = 1
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro z z' h
      apply Subtype.ext
      funext i
      have h1 := congrFun (congrArg (fun a : {a : fixedCharTuples M Fr // _} =>
        (a.1 : Fin τ.rank → Lˣ)) h) i
      have h2 : ζ ^ (z.1 i).val = ζ ^ (z'.1 i).val := h1
      have := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2
      exact ZMod.val_injective p this
    · rintro ⟨⟨a, ha⟩, hap⟩
      have hex : ∀ i, ∃ k : ℕ, k < p ∧ ζ ^ k = a i := fun i => by
        obtain ⟨k, hk, hk'⟩ := hζL.eq_pow_of_pow_eq_one (by
          have := congrArg (fun x : Lˣ => (x : L)) (hap i)
          simpa using this)
        exact ⟨k, hk, Units.ext (by simpa using hk')⟩
      choose k hk hka using hex
      let z : Fin τ.rank → ZMod p := fun i => (k i : ZMod p)
      have hz : expTuple ζ z = a := funext fun i => by
        show ζ ^ ((k i : ZMod p)).val = a i
        rw [ZMod.val_natCast_of_lt (hk i), hka i]
      exact ⟨⟨z, (expTuple_mem_fixedCharTuples_iff hζ M Fr hFr z).1 (hz ▸ ha)⟩,
        Subtype.ext (Subtype.ext hz)⟩
  exact (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm

end CFSG.LieType.SeitzGeneration
