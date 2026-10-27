module

public import CFSG.LieType.Universal.Unitary.BinaryModel.Weight
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Digits

public section

namespace CFSG.LieType.SpecialLinear

open CFSG.LieType.Universal.Unitary
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

theorem sum_testBit_fin_eq {f a : ℕ} (ha : a < 2 ^ f) :
    ∑ r : Fin f, (if Nat.testBit a r then 2 ^ (r : ℕ) else 0) = a := by
  let T : Finset ℕ := (Finset.univ.filter fun r : Fin f => Nat.testBit a r).image
    (fun r : Fin f => (r : ℕ))
  have hT : T = a.bitIndices.toFinset := by
    ext i
    simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset, Nat.mem_bitIndices]
    constructor
    · rintro ⟨r, hr, hri⟩
      rw [← hri]
      exact hr
    · intro hi
      have hif : i < f := by
        by_contra hge
        have h2 : 2 ^ f ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h3 : 2 ^ i ≤ a := Nat.ge_two_pow_of_testBit hi
        omega
      exact ⟨⟨i, hif⟩, hi, rfl⟩
  calc
    ∑ r : Fin f, (if Nat.testBit a r then 2 ^ (r : ℕ) else 0)
        = ∑ i ∈ T, 2 ^ i := by
          dsimp only [T]
          rw [Finset.sum_image (fun r _ q _ h => Fin.ext h), Finset.sum_filter]
    _ = ∑ i ∈ a.bitIndices.toFinset, 2 ^ i := by rw [hT]
    _ = a := by
          rw [List.sum_toFinset (f := fun i => 2 ^ i) Nat.bitIndices_nodup]
          exact Nat.sum_map_two_pow_bitIndices a

theorem le_mul_popcount_of_dvd {f s a : ℕ} (hs : 1 ≤ s) (ha0 : 0 < a) (ha : a < 2 ^ f)
    (hdvd : 2 ^ f - 1 ∣ a * (2 ^ s - 1)) :
    f ≤ s * (Finset.univ.filter fun r : Fin f => Nat.testBit a r).card := by
  let S : Finset (Fin f) := Finset.univ.filter fun r => Nat.testBit a r
  let S' : Finset ℕ := S.image (fun r : Fin f => (r : ℕ))
  have hf : 0 < f := by
    by_contra h
    have h0 : f = 0 := by omega
    rw [h0] at ha
    simp at ha
    omega
  have hsum : ∑ i ∈ S', 2 ^ i = a := by
    dsimp only [S', S]
    rw [Finset.sum_image (fun r _ q _ h => Fin.ext h), Finset.sum_filter]
    exact sum_testBit_fin_eq ha
  have hne : S'.Nonempty := by
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.ne_of_gt ha0)
    have hif : i < f := by
      by_contra hge
      have h2 : 2 ^ f ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : 2 ^ i ≤ a := Nat.ge_two_pow_of_testBit hi
      omega
    refine ⟨i, ?_⟩
    dsimp only [S', S]
    exact Finset.mem_image.mpr ⟨⟨i, hif⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  have hsub : ∀ i ∈ S', i < f := by
    intro i hi
    dsimp only [S', S] at hi
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hi
    exact r.isLt
  let g := Nat.gcd s f
  let A := 2 ^ f - 1
  let B := 2 ^ s - 1
  let D := 2 ^ g - 1
  have hgpos : 0 < g := by
    dsimp only [g]
    exact Nat.gcd_pos_of_pos_left f (by omega)
  have hgf : g ∣ f := by
    dsimp only [g]
    exact Nat.gcd_dvd_right s f
  have hgs : g ∣ s := by
    dsimp only [g]
    exact Nat.gcd_dvd_left s f
  have hDvdA : D ∣ A := by
    dsimp only [D, A]
    exact Nat.pow_sub_one_dvd_pow_sub_one (x := 2) hgf
  have hDvdB : D ∣ B := by
    dsimp only [D, B]
    exact Nat.pow_sub_one_dvd_pow_sub_one (x := 2) hgs
  have hDpos : 0 < D := by
    dsimp only [D]
    have h2 : 2 ≤ 2 ^ g := by
      simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 1 ≤ g)
    omega
  have hAeq : A = D * (A / D) := (Nat.mul_div_cancel' hDvdA).symm
  have hBeq : B = D * (B / D) := (Nat.mul_div_cancel' hDvdB).symm
  have hgcdAB : Nat.gcd A B = D := by
    have h := Nat.pow_sub_one_gcd_pow_sub_one 2 f s
    have h' : Nat.gcd (2 ^ f - 1) (2 ^ s - 1) = 2 ^ Nat.gcd s f - 1 := by
      rw [← Nat.gcd_comm f s]
      exact h
    simpa only [A, B, D, g] using h'
  have hcop : Nat.Coprime (A / D) (B / D) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have h := Nat.gcd_mul_left D (A / D) (B / D)
    rw [← hAeq, ← hBeq, hgcdAB] at h
    have h' : D * 1 = D * Nat.gcd (A / D) (B / D) := by simpa using h
    exact Nat.eq_of_mul_eq_mul_left hDpos h'.symm
  have hA' : A / D ∣ a := by
    have hB' : A / D ∣ a * (B / D) := by
      have h2 : A ∣ a * B := hdvd
      have h3 : D * (A / D) ∣ a * (D * (B / D)) := by
        rw [← hAeq, ← hBeq]
        exact h2
      have h4 : D * (A / D) ∣ D * (a * (B / D)) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h3
      exact Nat.dvd_of_mul_dvd_mul_left hDpos h4
    exact hcop.dvd_of_dvd_mul_right hB'
  have hAdivD : A ∣ a * D := by
    have h5 : D * (A / D) ∣ D * a := Nat.mul_dvd_mul_left D hA'
    rwa [← hAeq, Nat.mul_comm D a] at h5
  have hper : A ∣ D * ∑ i ∈ S', 2 ^ i := by
    rw [hsum, Nat.mul_comm D a]
    exact hAdivD
  have hbound := card_ge_of_periodic (n := f) (g := g) (J := S') hgpos hgf hsub hne hper
  rw [show S'.card = S.card from
    Finset.card_image_of_injective S (fun _ _ h => Fin.ext h)] at hbound
  have hgle : g ≤ s := by
    dsimp only [g]
    exact Nat.gcd_le_left f (by omega)
  have hmain : f ≤ s * S.card := by
    calc
      f = g * (f / g) := (Nat.mul_div_cancel' hgf).symm
      _ ≤ s * (f / g) := Nat.mul_le_mul_right _ hgle
      _ ≤ s * S.card := Nat.mul_le_mul_left _ hbound
  simpa only [S] using hmain

variable (m : ℕ) {F : Type} [Field F] [Finite F] {f : ℕ} {k : Type} [Field k]

theorem le_mul_card_of_values_mem (hF : Nat.card F = 2 ^ f) {E : Type*} [Field E] [Fintype E]
    [Algebra E k] {s : ℕ} (hE : Fintype.card E = 2 ^ s) (hs : 1 ≤ s) (φ : F →+* k)
    (ε : Fin f → Finset (Fin (m + 1))) (j : Fin (m + 1)) (hj : bDigit ε j ≠ 0)
    (hval : ∀ u : Fˣ, φ (u : F) ^ bDigit ε j ∈ (algebraMap E k).range) :
    f ≤ s * (Finset.univ.filter fun r => j ∈ ε r).card := by
  let a := bDigit ε j
  have ha_lt : a < 2 ^ f := bDigit_lt ε j
  have ha0 : 0 < a := Nat.pos_of_ne_zero hj
  have hdvd : 2 ^ f - 1 ∣ a * (2 ^ s - 1) := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hord : orderOf g = Nat.card F - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
    have hprim : IsPrimitiveRoot (φ (g : F)) (Nat.card F - 1) := by
      have h1 : IsPrimitiveRoot ((g : F)) (Nat.card F - 1) := by
        rw [← hord, ← orderOf_units]
        exact IsPrimitiveRoot.orderOf _
      exact h1.map_of_injective φ.injective
    have hpow : φ (g : F) ^ (a * (2 ^ s - 1)) = 1 := by
      obtain ⟨y, hy⟩ := hval g
      have hy0 : y ≠ 0 := by
        intro h0
        have hzero : φ (g : F) ^ a = 0 := by rw [← hy, h0, map_zero]
        have hφg : φ (g : F) ≠ 0 := by
          intro h
          exact g.ne_zero (φ.injective (h.trans (map_zero φ).symm))
        exact (pow_ne_zero _ hφg) hzero
      have hyE : y ^ (2 ^ s - 1) = 1 := by
        have h := FiniteField.pow_card_sub_one_eq_one y hy0
        rwa [hE] at h
      have hx : (φ (g : F) ^ a) ^ (2 ^ s - 1) = 1 := by
        rw [← hy, ← map_pow, hyE, map_one]
      rwa [← pow_mul] at hx
    have hdvdN : Nat.card F - 1 ∣ a * (2 ^ s - 1) := hprim.dvd_of_pow_eq_one _ hpow
    rwa [hF] at hdvdN
  have hpop : (Finset.univ.filter fun r : Fin f => Nat.testBit a r).card =
      (Finset.univ.filter fun r => j ∈ ε r).card := by
    let S : Finset (Fin f) := Finset.univ.filter fun r => j ∈ ε r
    let S' : Finset ℕ := S.image (fun r : Fin f => (r : ℕ))
    have hS'sum : ∑ i ∈ S', 2 ^ i = a := by
      dsimp only [S', S, a]
      rw [Finset.sum_image (fun r _ q _ h => Fin.ext h), bDigit, ← Finset.sum_filter]
    have hbits : a.bitIndices.toFinset = S' := by
      rw [← hS'sum]
      exact Finset.toFinset_bitIndices_sum_two_pow S'
    have hbit : ∀ r : Fin f, Nat.testBit a r ↔ j ∈ ε r := by
      intro r
      have h1 : Nat.testBit a r ↔ (r : ℕ) ∈ a.bitIndices.toFinset := by
        rw [List.mem_toFinset, Nat.mem_bitIndices]
      rw [h1, hbits]
      simp only [S', S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨q, hq, hqv⟩
        have hqr : q = r := Fin.ext hqv
        simpa [hqr] using hq
      · intro hr
        exact ⟨r, hr, rfl⟩
    have hfilter : (Finset.univ.filter fun r : Fin f => Nat.testBit a r) = S := by
      ext r
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hbit r
    rw [hfilter]
  have hle := le_mul_popcount_of_dvd hs ha0 ha_lt hdvd
  rwa [hpop] at hle

end CFSG.LieType.SpecialLinear
