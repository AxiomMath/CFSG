module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen

public section

namespace CFSG.QuasithinUnique.Setup.X1

section Sylow

variable {S : Type} [Group S] [Finite S]

theorem exists_conj_le_of_card (U : Subgroup S) {a m : ℕ} (hU : Nat.card U = 2 ^ a)
    (hS : Nat.card S = 2 ^ a * m) (hm : Odd m) (B : Subgroup S) (hB : ∀ x ∈ B, x * x = 1) :
    ∃ g : S, ∀ x ∈ B, g * x * g⁻¹ ∈ U := by
  have hidx : U.index = m := by
    have := Subgroup.card_mul_index U
    rw [hU, hS] at this
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hodd : ¬ 2 ∣ U.index := by
    rw [hidx]
    intro hd
    obtain ⟨k, hk⟩ := hm
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 U := IsPGroup.of_card hU
  have hBp : IsPGroup 2 B := by
    intro x
    refine ⟨1, ?_⟩
    have := hB x x.2
    apply Subtype.ext
    simpa [sq] using this
  obtain ⟨Q, hQ⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S Q (hpg.toSylow hodd)
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup S) := hQ hx
  have hmem : g * x * g⁻¹ ∈ ((g • Q : Sylow 2 S) : Set S) := by
    rw [Sylow.coe_smul]
    exact ⟨x, hxQ, rfl⟩
  rw [hg] at hmem
  exact hmem

theorem card_le_of_sylow_idx {a m : ℕ} (hS : Nat.card S = 2 ^ a * m) (hm : Odd m) (E : ℕ → S)
    (hinj : ∀ i < 2 ^ a, ∀ j < 2 ^ a, E i = E j → i = j)
    (hU : ∃ U : Subgroup S, ∀ x, x ∈ U ↔ ∃ i < 2 ^ a, x = E i) (pl : List (ℕ × ℕ))
    (hpl : ∀ i < 2 ^ a, ∀ j < 2 ^ a, E i ≠ 1 → E i * E i = 1 → E j ≠ 1 → E j * E j = 1 →
      i ≠ j → E i * E j = E j * E i → (i, j) ∈ pl)
    (r : ℕ) (hcount : pl.length < (2 ^ (r + 1) - 1) * (2 ^ (r + 1) - 2)) :
    ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r := by
  classical
  obtain ⟨U, hUmem⟩ := hU
  have hUcard : Nat.card U = 2 ^ a := by
    have hbij : Function.Bijective
        (fun i : Fin (2 ^ a) => (⟨E i, (hUmem _).2 ⟨i, i.2, rfl⟩⟩ : U)) := by
      constructor
      · intro i j hij
        exact Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val hij))
      · rintro ⟨x, hx⟩
        obtain ⟨i, hi, rfl⟩ := (hUmem x).1 hx
        exact ⟨⟨i, hi⟩, rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_fin]
  intro B hcomm hsq
  by_contra hgt
  push Not at hgt
  have hpg : IsPGroup 2 B := by
    intro x
    refine ⟨1, ?_⟩
    have := hsq x x.2
    apply Subtype.ext
    simpa [sq] using this
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hpg
  have hrn : r + 1 ≤ n := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ n ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨g, hg⟩ := exists_conj_le_of_card U hUcard hS hm B hsq
  obtain ⟨P, hPcard, hP⟩ := card_distinct_nonid_pairs B
  have hsqc : ∀ z : S, z * z = 1 → (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := fun z hz => by
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz]; group
  set T : Finset (S × S) := pl.toFinset.image (fun q : ℕ × ℕ => (E q.1, E q.2)) with hT
  have hsub : P.image (fun q : S × S => (g * q.1 * g⁻¹, g * q.2 * g⁻¹)) ⊆ T := by
    intro q' hq'
    obtain ⟨q, hqP, rfl⟩ := Finset.mem_image.1 hq'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hP q hqP
    obtain ⟨i, hi, hix⟩ := (hUmem _).1 (hg q.1 h1)
    obtain ⟨j, hj, hjy⟩ := (hUmem _).1 (hg q.2 h2)
    have hq1 : q.1 * q.1 = 1 := hsq q.1 h1
    have hq2 : q.2 * q.2 = 1 := hsq q.2 h2
    have hmem : (i, j) ∈ pl := by
      refine hpl i hi j hj ?_ ?_ ?_ ?_ ?_ ?_
      · rw [← hix]; exact fun h => h3 (conj_eq_one_iff.1 h)
      · rw [← hix]; exact hsqc _ hq1
      · rw [← hjy]; exact fun h => h4 (conj_eq_one_iff.1 h)
      · rw [← hjy]; exact hsqc _ hq2
      · intro hij
        apply h5
        subst hij
        have : g * q.1 * g⁻¹ = g * q.2 * g⁻¹ := hix.trans hjy.symm
        simpa using this
      · rw [← hix, ← hjy]
        calc (g * q.1 * g⁻¹) * (g * q.2 * g⁻¹) = g * (q.1 * q.2) * g⁻¹ := by group
          _ = g * (q.2 * q.1) * g⁻¹ := by rw [hcomm q.1 h1 q.2 h2]
          _ = _ := by group
    rw [hT, Finset.mem_image]
    exact ⟨(i, j), List.mem_toFinset.2 hmem, by rw [← hix, ← hjy]⟩
  have hinjc : Function.Injective (fun q : S × S => (g * q.1 * g⁻¹, g * q.2 * g⁻¹)) := by
    intro q q' hqq
    simp only [Prod.mk.injEq, mul_left_inj, mul_right_inj] at hqq
    exact Prod.ext hqq.1 hqq.2
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinjc] at h1
  have h2 : T.card ≤ pl.toFinset.card := Finset.card_image_le
  have h3 := List.toFinset_card_le pl
  have h4 : 2 ^ (r + 1) ≤ Nat.card B := by
    rw [hn]
    exact Nat.pow_le_pow_right (by norm_num) hrn
  have h5 : (2 ^ (r + 1) - 1) * (2 ^ (r + 1) - 2) ≤ (Nat.card B - 1) * (Nat.card B - 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

end Sylow

end CFSG.QuasithinUnique.Setup.X1
