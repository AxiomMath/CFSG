module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverAltBlock

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem cycleType_eq_two_two_of_sq_eq_one {n : ℕ} (hn : n ≤ 7) {σ : Perm (Fin n)}
    (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) (hs : sign σ = 1) : σ.cycleType = {2, 2} := by
  have ho : orderOf σ = 2 := orderOf_eq_prime h2 h1
  obtain ⟨k, hk⟩ := cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hsum : σ.cycleType.sum ≤ n := by
    rw [sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hsign := sign_of_cycleType σ
  rw [hs, hk, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  · exact absurd hsign (by decide)
  · rw [hk]
    rfl
  · exact absurd hsign (by decide)

theorem isConj_of_sq_eq_one_of_le_seven {n : ℕ} (hn : n ≤ 7) {σ τ : alternatingGroup (Fin n)}
    (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1) : IsConj σ τ := by
  have hc : ∀ ρ : alternatingGroup (Fin n), ρ ^ 2 = 1 → ρ ≠ 1 →
      (ρ : Perm (Fin n)).cycleType = {2, 2} := fun ρ h2 h1 =>
    cycleType_eq_two_two_of_sq_eq_one hn (by rw [← Subgroup.coe_pow, h2]; rfl)
      (fun h => h1 (Subtype.ext h)) (mem_alternatingGroup.mp ρ.2)
  obtain ⟨c, hcστ⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr
    ((hc σ hσ2 hσ1).trans (hc τ hτ2 hτ1).symm))
  set s : Perm (Fin n) := (σ : Perm (Fin n)) with hs
  obtain ⟨a, ha⟩ : ∃ a, s a ≠ a := by
    by_contra h
    push Not at h
    exact hσ1 (Subtype.ext (Equiv.ext h))
  have hss : s * s = 1 := by
    rw [hs, ← Subgroup.coe_mul, ← sq, hσ2]
    rfl
  have hsa : s (s a) = a := by
    have := congrArg (fun f : Perm (Fin n) => f a) hss
    simpa using this
  have hcomm : s * swap a (s a) = swap a (s a) * s := by
    rw [mul_swap_eq_swap_mul, hsa, swap_comm]
  obtain ⟨c', hc'1, hc'⟩ : ∃ c' : Perm (Fin n), sign c' = 1 ∧ c' * s * c'⁻¹ = τ := by
    by_cases hcs : sign c = 1
    · exact ⟨c, hcs, hcστ⟩
    · refine ⟨c * swap a (s a), ?_, ?_⟩
      · rcases Int.units_eq_one_or (sign c) with h | h
        · exact absurd h hcs
        · rw [map_mul, h, sign_swap (Ne.symm ha)]
          decide
      · calc c * swap a (s a) * s * (c * swap a (s a))⁻¹
            = c * (swap a (s a) * s * (swap a (s a))⁻¹) * c⁻¹ := by group
          _ = c * s * c⁻¹ := by rw [← hcomm, mul_inv_cancel_right]
          _ = τ := hcστ
  refine isConj_iff.mpr ⟨⟨c', mem_alternatingGroup.mpr hc'1⟩, Subtype.ext ?_⟩
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hc'

variable {P : Type*} [Group P] [Finite P] [Group.IsPerfect P]

theorem alternatingCover_mem_ker_of_sq_eq_one_of_isPGroup {m : ℕ} (hm3 : 3 ≤ m) (hm5 : m ≤ 5)
    (η : P →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ center P) (hK2 : IsPGroup 2 η.ker) (hne : η.ker ≠ ⊥) {a : P}
    (ha : a ^ 2 = 1) : a ∈ η.ker := by
  obtain ⟨x, z, hxη, -, hzc, hz1, -, hzij⟩ :=
    CFSG.QuasithinUnique.Ch1.alt_cover_structure hm3 η hη hK hK2 hne
  have hk2 : ∀ k ∈ η.ker, k ^ 2 = 1 := by
    intro k hk
    have hcard := card_ker_le_two_of_alternating hm3 η hη hK hK2
    have hpow := pow_card_eq_one' (G := η.ker) (x := ⟨k, hk⟩)
    have hpos : 0 < Nat.card η.ker := Nat.card_pos
    have h : (⟨k, hk⟩ : η.ker) ^ 2 = 1 := by
      interval_cases h : Nat.card η.ker
      · rw [pow_one] at hpow
        rw [hpow, one_pow]
      · exact hpow
    exact congrArg Subtype.val h
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  set y := x i₀ * x i₁ with hy
  have hy2 : y ^ 2 = z := hzij i₀ i₁ h01
  have hτ2 : η y ^ 2 = 1 := by rw [hy, map_mul, hxη, hxη, altThreeCycle_mul_sq h01]
  have hτ1 : η y ≠ 1 := fun h => hz1 (by rw [← hy2]; exact hk2 y (MonoidHom.mem_ker.mpr h))
  by_contra haK
  have hη1 : η a ≠ 1 := fun h => haK (MonoidHom.mem_ker.mpr h)
  have ha2 : η a ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_sq_eq_one_of_le_seven (by omega) hτ2 hτ1 ha2 hη1)
  obtain ⟨h, rfl⟩ := hη g
  set y' := h * y * h⁻¹ with hy'
  have hk : y'⁻¹ * a ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy', map_mul, map_mul, map_inv, hg, inv_mul_cancel]
  have hkc : Commute y' (y'⁻¹ * a) := mem_center_iff.mp (hK hk) y'
  have hy'2 : y' ^ 2 = z := by
    rw [hy', conj_pow, hy2, mem_center_iff.mp hzc h, mul_inv_cancel_right]
  apply hz1
  calc z = y' ^ 2 := hy'2.symm
    _ = y' ^ 2 * (y'⁻¹ * a) ^ 2 := by rw [hk2 _ hk, mul_one]
    _ = (y' * (y'⁻¹ * a)) ^ 2 := (hkc.mul_pow 2).symm
    _ = a ^ 2 := by rw [mul_inv_cancel_left]
    _ = 1 := ha

theorem alternatingCover_mem_ker_of_sq_eq_one {n : ℕ} (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    (η : P →* alternatingGroup (Fin n)) (hη : Function.Surjective η)
    (hK : η.ker ≤ center P) (heven : Even (Nat.card η.ker)) {a : P} (ha : a ^ 2 = 1) :
    a ∈ η.ker := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hcomm : ∀ k ∈ η.ker, ∀ l : P, Commute k l := fun k hk l =>
    (mem_center_iff.mp (hK hk) l).symm
  let N : Subgroup P :=
    { carrier := {x | ∃ k ∈ η.ker, k ^ 2 = x}
      mul_mem' := by
        rintro _ _ ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
        exact ⟨k * l, mul_mem hk hl, (hcomm k hk l).mul_pow 2⟩
      one_mem' := ⟨1, one_mem _, one_pow 2⟩
      inv_mem' := by
        rintro _ ⟨k, hk, rfl⟩
        exact ⟨k⁻¹, inv_mem hk, inv_pow k 2⟩ }
  have hNK : N ≤ η.ker := by
    rintro _ ⟨k, hk, rfl⟩
    exact pow_mem hk 2
  have : N.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hK (hNK hx)) g, mul_inv_cancel_right]
    exact hx⟩
  set η' : P ⧸ N →* alternatingGroup (Fin (m + 2)) := QuotientGroup.lift N η hNK
  have hη'mk : ∀ x : P, η' (x : P ⧸ N) = η x := fun x => rfl
  have hη' : Function.Surjective η' := fun s => by
    obtain ⟨x, rfl⟩ := hη s
    exact ⟨x, hη'mk x⟩
  have hker : η'.ker = η.ker.map (QuotientGroup.mk' N) := QuotientGroup.ker_lift N η hNK
  have hK' : η'.ker ≤ center (P ⧸ N) := by
    rw [hker]
    exact (map_mono hK).trans (map_center_le_center (QuotientGroup.mk'_surjective N))
  have hK2' : IsPGroup 2 η'.ker := by
    rintro ⟨q, hq⟩
    rw [hker] at hq
    obtain ⟨k, hk, rfl⟩ := hq
    refine ⟨1, Subtype.ext ?_⟩
    show QuotientGroup.mk' N k ^ 2 ^ 1 = 1
    rw [pow_one, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨k, hk, rfl⟩
  have hne' : η'.ker ≠ ⊥ := by
    intro hbot
    have hsq : ∀ k : η.ker, ∃ l : η.ker, l ^ 2 = k := by
      rintro ⟨k, hk⟩
      have hk' : QuotientGroup.mk' N k ∈ η'.ker := by
        rw [hker]
        exact ⟨k, hk, rfl⟩
      rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk'
      obtain ⟨l, hl, hlk⟩ := hk'
      exact ⟨⟨l, hl⟩, Subtype.ext (by rw [Subgroup.coe_pow]; exact hlk)⟩
    have hsurj : Function.Surjective fun l : η.ker => l ^ 2 := fun k => hsq k
    have hinj := Finite.injective_iff_surjective.mpr hsurj
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k₀, hk₀⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    have hk₀2 : k₀ ^ 2 = 1 := by
      have h := pow_orderOf_eq_one k₀
      rwa [hk₀] at h
    have h1 : k₀ = 1 := hinj (show k₀ ^ 2 = 1 ^ 2 by rw [one_pow, hk₀2])
    rw [h1, orderOf_one] at hk₀
    exact absurd hk₀ (by norm_num)
  have h := alternatingCover_mem_ker_of_sq_eq_one_of_isPGroup (by omega) (by omega) η' hη' hK' hK2'
    hne' (a := (a : P ⧸ N)) (by rw [← QuotientGroup.mk_pow, ha, QuotientGroup.mk_one])
  rw [MonoidHom.mem_ker, hη'mk] at h
  exact MonoidHom.mem_ker.mpr h

end CFSG.ComponentClassification.RankTwoAlt
