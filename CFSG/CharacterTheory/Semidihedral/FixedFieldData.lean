module

public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Galois.IsGaloisGroup

public section

namespace CFSG.Semidihedral.FixedFieldData

noncomputable section

universe u

theorem finite_of_prime_power_card (F : Type u) [Field F] {p n : ℕ}
    (hp : p.Prime) (hcard : Nat.card F = p ^ n) : Finite F :=
  Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero n hp.ne_zero)

theorem characteristic_of_prime_power_card (F : Type u) [Field F] {p n : ℕ}
    (hp : p.Prime) (hcard : Nat.card F = p ^ n) : CharP F p := by
  let : Finite F := finite_of_prime_power_card F hp hcard
  let : Fintype F := Fintype.ofFinite F
  let : Fact p.Prime := ⟨hp⟩
  exact charP_of_card_eq_prime_pow (by simpa only [Fintype.card_eq_nat_card] using hcard)

@[expose] def primeFieldAutEquiv (p : ℕ) (F : Type u) [Field F] [Fact p.Prime]
    [Algebra (ZMod p) F] : (F ≃+* F) ≃* (F ≃ₐ[ZMod p] F) where
  toFun e :=
    { e with
      commutes' := fun r => DFunLike.congr_fun
        (RingHom.ext_zmod (e.toRingHom.comp (algebraMap (ZMod p) F))
          (algebraMap (ZMod p) F)) r }
  invFun e := e.toRingEquiv
  left_inv _ := rfl
  right_inv e := by ext x; rfl
  map_mul' e f := by ext x; rfl

@[expose] def frobeniusAut (p : ℕ) (F : Type u) [Field F] [Finite F]
    [Fact p.Prime] [CharP F p] : F ≃+* F := by
  letI : Algebra (ZMod p) F := ZMod.algebra _ _
  exact (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F).toRingEquiv

theorem frobeniusAut_apply (p : ℕ) (F : Type u) [Field F] [Finite F]
    [Fact p.Prime] [CharP F p] (x : F) : frobeniusAut p F x = x ^ p := by
  let : Algebra (ZMod p) F := ZMod.algebra _ _
  change (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F) x = x ^ p
  rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ZMod.card]

theorem prime_field_finrank (p n : ℕ) (F : Type u) [Field F] [Finite F]
    [Fact p.Prime] [Algebra (ZMod p) F] (hcard : Nat.card F = p ^ n) :
    Module.finrank (ZMod p) F = n := by
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  exact (FiniteField.pow_finrank_eq_natCard p F).trans hcard

theorem frobeniusAut_order (p n : ℕ) (F : Type u) [Field F] [Finite F]
    [Fact p.Prime] [CharP F p] (hcard : Nat.card F = p ^ n) :
    orderOf (frobeniusAut p F) = n := by
  let : Algebra (ZMod p) F := ZMod.algebra _ _
  let e := primeFieldAutEquiv p F
  have he : e (frobeniusAut p F) =
      FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F := by ext x; rfl
  calc
    orderOf (frobeniusAut p F) = orderOf (e (frobeniusAut p F)) :=
      (orderOf_injective e.toMonoidHom e.injective _).symm
    _ = Module.finrank (ZMod p) F := by
      rw [he, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
    _ = n := prime_field_finrank p n F hcard

theorem frobeniusAut_zpowers (p : ℕ) (F : Type u) [Field F] [Finite F]
    [Fact p.Prime] [CharP F p] :
    (⊤ : Subgroup (F ≃+* F)) = Subgroup.zpowers (frobeniusAut p F) := by
  let : Algebra (ZMod p) F := ZMod.algebra _ _
  let e := primeFieldAutEquiv p F
  have he : e (frobeniusAut p F) =
      FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F := by ext x; rfl
  symm
  apply top_unique
  intro g _
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    (ZMod p) F).surjective (e g)
  have hpow : frobeniusAut p F ^ i.val = g := by
    apply e.injective
    simpa only [map_pow, he] using hi
  rw [← hpow]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem nat_card_eq_fixedSubfield_card_pow (F : Type u) [Field F] [Finite F]
    (A : Subgroup (F ≃+* F)) :
    Nat.card F = Nat.card (FixedPoints.subfield A F) ^ Nat.card A := by
  let : Finite (F ≃+* F) := Finite.of_injective (fun e : F ≃+* F => (e : F → F))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  let R := FixedPoints.subfield A F
  let : IsGaloisGroup A R F := IsGaloisGroup.fixedPoints A F
  have hrank : Module.finrank R F = Nat.card A :=
    (IsGaloisGroup.card_eq_finrank A R F).symm
  calc
    Nat.card F = Nat.card R ^ Module.finrank R F := Module.natCard_eq_pow_finrank
    _ = Nat.card R ^ Nat.card A := by rw [hrank]

theorem mem_fixedSubfield_iff (F : Type u) [Field F] (A : Subgroup (F ≃+* F)) (x : F) :
    x ∈ FixedPoints.subfield A F ↔ ∀ a : A, (a : F ≃+* F) x = x := Iff.rfl

theorem fixedSubfield_card (p n : ℕ) (F : Type u) [Field F] [Finite F]
    [Fact p.Prime] [CharP F p] (hcard : Nat.card F = p ^ n)
    (A : Subgroup (F ≃+* F)) :
    Nat.card (FixedPoints.subfield A F) = p ^ (n / Nat.card A) := by
  let : Finite (F ≃+* F) := Finite.of_injective (fun e : F ≃+* F => (e : F → F))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  let R := FixedPoints.subfield A F
  let : Algebra (ZMod p) R := ZMod.algebra _ _
  let : IsGaloisGroup A R F := IsGaloisGroup.fixedPoints A F
  have hR : p ^ Module.finrank (ZMod p) R = Nat.card R :=
    FiniteField.pow_finrank_eq_natCard p R
  have hmul : Module.finrank (ZMod p) R * Nat.card A = n := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    calc
      p ^ (Module.finrank (ZMod p) R * Nat.card A) =
          Nat.card R ^ Nat.card A := by rw [pow_mul, hR]
      _ = Nat.card F := (nat_card_eq_fixedSubfield_card_pow F A).symm
      _ = p ^ n := hcard
  have hA : 0 < Nat.card A := Nat.card_pos
  have hdiv : n / Nat.card A = Module.finrank (ZMod p) R := by
    rw [← hmul, Nat.mul_div_cancel _ hA]
  exact hR.symm.trans (congrArg (p ^ ·) hdiv.symm)

theorem finite_field_automorphism_fixed_field_cardinality
    (p n : ℕ) (hp : p.Prime) (_hn : 1 ≤ n) (F : Type u) [Field F]
    (hcard : Nat.card F = p ^ n) :
    ∃ sigma : F ≃+* F,
      (∀ x : F, sigma x = x ^ p) ∧ orderOf sigma = n ∧
      (⊤ : Subgroup (F ≃+* F)) = Subgroup.zpowers sigma ∧
      Nat.card (F ≃+* F) = n ∧ IsCyclic (F ≃+* F) ∧
      ∀ A : Subgroup (F ≃+* F),
        Nat.card A ∣ n ∧
        (∀ x : F, x ∈ FixedPoints.subfield A F ↔ ∀ a : A, (a : F ≃+* F) x = x) ∧
        Nat.card (FixedPoints.subfield A F) = p ^ (n / Nat.card A) ∧
        Nat.card F = Nat.card (FixedPoints.subfield A F) ^ Nat.card A := by
  let : Finite F := finite_of_prime_power_card F hp hcard
  let : Fact p.Prime := ⟨hp⟩
  let : CharP F p := characteristic_of_prime_power_card F hp hcard
  let sigma := frobeniusAut p F
  have htop := frobeniusAut_zpowers p F
  have horder := frobeniusAut_order p n F hcard
  have haut : Nat.card (F ≃+* F) = n := by
    rw [← horder]
    exact (orderOf_eq_card_of_zpowers_eq_top htop.symm).symm
  refine ⟨sigma, frobeniusAut_apply p F, horder, htop, haut,
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨sigma, htop.symm⟩, ?_⟩
  intro A
  refine ⟨haut ▸ A.card_subgroup_dvd_card, mem_fixedSubfield_iff F A,
    fixedSubfield_card p n F hcard A, nat_card_eq_fixedSubfield_card_pow F A⟩

theorem finite_field_automorphism_fixed_field_cardinality_int
    (p : ℕ) (n : ℤ) (hp : p.Prime) (hn : 1 ≤ n) (F : Type u) [Field F]
    (hcard : Nat.card F = p ^ n.toNat) :
    ∃ sigma : F ≃+* F,
      (∀ x : F, sigma x = x ^ p) ∧ (orderOf sigma : ℤ) = n ∧
      (⊤ : Subgroup (F ≃+* F)) = Subgroup.zpowers sigma ∧
      (Nat.card (F ≃+* F) : ℤ) = n ∧ IsCyclic (F ≃+* F) ∧
      ∀ A : Subgroup (F ≃+* F),
        (Nat.card A : ℤ) ∣ n ∧
        (∀ x : F, x ∈ FixedPoints.subfield A F ↔ ∀ a : A, (a : F ≃+* F) x = x) ∧
        Nat.card (FixedPoints.subfield A F) = p ^ (n / (Nat.card A : ℤ)).toNat ∧
        Nat.card F = Nat.card (FixedPoints.subfield A F) ^ Nat.card A := by
  have hn0 : 0 ≤ n := by omega
  have hnN : 1 ≤ n.toNat := by omega
  obtain ⟨sigma, happly, horder, htop, haut, hcyclic, hfixed⟩ :=
    finite_field_automorphism_fixed_field_cardinality p n.toNat hp hnN F hcard
  refine ⟨sigma, happly, ?_, htop, ?_, hcyclic, ?_⟩
  · rw [horder, Int.toNat_of_nonneg hn0]
  · rw [haut, Int.toNat_of_nonneg hn0]
  · intro A
    obtain ⟨hdvd, hmem, hsize, hpower⟩ := hfixed A
    refine ⟨?_, hmem, ?_, hpower⟩
    · rw [← Int.toNat_of_nonneg hn0]
      exact_mod_cast hdvd
    · rw [← Int.toNat_of_nonneg hn0, ← Int.natCast_ediv, Int.toNat_natCast]
      exact hsize

theorem odd_square_mod_eight {q0 : ℕ} (hodd : Odd q0) : q0 ^ 2 % 8 = 1 := by
  have hmod : q0 % 8 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd q0 (by decide : 2 ∣ 8)]
    exact Nat.odd_iff.mp hodd
  have hlt : q0 % 8 < 8 := Nat.mod_lt _ (by decide)
  have hres : q0 % 8 = 1 ∨ q0 % 8 = 3 ∨ q0 % 8 = 5 ∨ q0 % 8 = 7 := by omega
  rcases hres with hres | hres | hres | hres <;> rw [Nat.pow_mod, hres]

theorem odd_power_mod_eight {q0 d : ℕ} (hodd : Odd q0) (hd : Odd d) :
    q0 ^ d % 8 = q0 % 8 := by
  obtain ⟨m, rfl⟩ := hd
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, odd_square_mod_eight hodd, one_pow]
  simp

theorem odd_geometric_sum {q0 d : ℕ} (hodd : Odd q0) (hd : Odd d) :
    Odd (∑ i ∈ Finset.range d, (q0 ^ 2) ^ i) := by
  apply (Finset.odd_sum_iff_odd_card_odd fun i => (q0 ^ 2) ^ i).mpr
  simpa only [hodd.pow.pow, Finset.filter_true, Finset.card_range] using hd

theorem odd_extension_square_sub_one_factorization {q0 d : ℕ}
    (hq0 : 3 ≤ q0) (hodd : Odd q0) (hd : Odd d) :
    ((q0 ^ d) ^ 2 - 1).factorization 2 = (q0 ^ 2 - 1).factorization 2 := by
  let s := ∑ i ∈ Finset.range d, (q0 ^ 2) ^ i
  have hsodd : Odd s := odd_geometric_sum hodd hd
  have hs : s ≠ 0 := hsodd.pos.ne'
  have hbase : q0 ^ 2 - 1 ≠ 0 := by
    have : 1 < q0 ^ 2 := by nlinarith
    omega
  have hgeom : s * (q0 ^ 2 - 1) = (q0 ^ d) ^ 2 - 1 := by
    have h := geom_sum_mul_of_one_le (show 1 ≤ q0 ^ 2 by nlinarith) d
    simpa only [s, ← pow_mul, Nat.mul_comm 2 d] using h
  rw [← hgeom, Nat.factorization_mul hs hbase, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hsodd.not_two_dvd_nat, zero_add]

theorem odd_field_extension_arithmetic {q0 d : ℕ}
    (hq0 : 3 ≤ q0) (hodd : Odd q0) (hd : Odd d) :
    q0 ^ d % 8 = q0 % 8 ∧
      ((q0 ^ d) ^ 2 - 1).factorization 2 = (q0 ^ 2 - 1).factorization 2 ∧
      2 ^ ((q0 ^ d) ^ 2 - 1).factorization 2 = 2 ^ (q0 ^ 2 - 1).factorization 2 := by
  have hfactor := odd_extension_square_sub_one_factorization hq0 hodd hd
  exact ⟨odd_power_mod_eight hodd hd, hfactor, congrArg (2 ^ ·) hfactor⟩

theorem odd_field_extension_arithmetic_of_card {q q0 d : ℕ}
    (hq0 : 3 ≤ q0) (hodd : Odd q0) (hd : Odd d) (hq : q = q0 ^ d) :
    q % 8 = q0 % 8 ∧ (q ^ 2 - 1).factorization 2 = (q0 ^ 2 - 1).factorization 2 ∧
      2 ^ (q ^ 2 - 1).factorization 2 = 2 ^ (q0 ^ 2 - 1).factorization 2 := by
  rw [hq]
  exact odd_field_extension_arithmetic hq0 hodd hd

theorem odd_fixed_field_data
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (F : Type u) [Field F] (hcard : Nat.card F = p ^ f)
    (A : Subgroup (F ≃+* F)) (hd : Odd (Nat.card A)) :
    let d := Nat.card A
    let q0 := p ^ (f / d)
    d ∣ f ∧ 1 ≤ d ∧ 3 ≤ q0 ∧ Odd q0 ∧
      (∀ x : F, x ∈ FixedPoints.subfield A F ↔ ∀ a : A, (a : F ≃+* F) x = x) ∧
      Nat.card (FixedPoints.subfield A F) = q0 ∧ Nat.card F = q0 ^ d ∧
      Nat.card F % 8 = q0 % 8 ∧
      (Nat.card F ^ 2 - 1).factorization 2 = (q0 ^ 2 - 1).factorization 2 ∧
      2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 ^ (q0 ^ 2 - 1).factorization 2 := by
  obtain ⟨sigma, _, _, _, _, _, hfixed⟩ :=
    finite_field_automorphism_fixed_field_cardinality p f hp hf F hcard
  obtain ⟨hdvd, hmem, hsize, hpower⟩ := hfixed A
  have hdpos : 0 < Nat.card A := hd.pos
  have hdiv : 1 ≤ f / Nat.card A := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hdpos
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    have := Nat.odd_iff.mp hpodd
    omega
  have hq0 : 3 ≤ p ^ (f / Nat.card A) := hp3.trans
    (Nat.le_self_pow (by omega) p)
  have hqodd : Odd (p ^ (f / Nat.card A)) := hpodd.pow
  have hq : Nat.card F = (p ^ (f / Nat.card A)) ^ Nat.card A := by
    simpa only [hsize] using hpower
  obtain ⟨hmod, hfactor, htwo⟩ := odd_field_extension_arithmetic_of_card hq0 hqodd hd hq
  exact ⟨hdvd, hdpos, hq0, hqodd, hmem, hsize, hq, hmod, hfactor, htwo⟩

end

end CFSG.Semidihedral.FixedFieldData
