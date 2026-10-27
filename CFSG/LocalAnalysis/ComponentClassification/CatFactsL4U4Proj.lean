module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Order
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open Matrix CFSG.ComponentClassification.CatalogueBProjectiveInvolution

theorem mem_of_index_le_two {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (hN : N.index ≤ 2) {x : G} (hx : Odd (orderOf x)) : x ∈ N := by
  have hi0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  set y : G ⧸ N := QuotientGroup.mk x with hy
  have h1 : orderOf y ∣ orderOf x := orderOf_map_dvd (QuotientGroup.mk' N) x
  have h2 : orderOf y ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard y
  have hodd : Odd (orderOf y) := Odd.of_dvd_nat hx h1
  have hy1 : orderOf y = 1 := by
    have hle : orderOf y ≤ 2 := (Nat.le_of_dvd (by omega) h2).trans hN
    rcases Nat.lt_or_ge (orderOf y) 2 with h | h
    · have : 0 < orderOf y := hodd.pos
      omega
    · have : orderOf y = 2 := le_antisymm hle h
      rw [this] at hodd
      exact absurd hodd (by decide)
  have : y = 1 := orderOf_eq_one_iff.1 hy1
  exact (QuotientGroup.eq_one_iff x).1 this

variable {F : Type*} [Field F] [Fintype F]

theorem exists_pow_eq_one_mk_eq {n s : ℕ} [NeZero n] (hs : s.Prime)
    (hsq : ¬ s ∣ Fintype.card F - 1) {B : GL (Fin n) F}
    (hB : (ProjGenLinGroup.mk B) ^ s = 1) :
    ∃ m : ℕ, (B ^ m) ^ s = 1 ∧ ProjGenLinGroup.mk (B ^ m) = ProjGenLinGroup.mk B := by
  have hc : B ^ s ∈ Subgroup.center (GL (Fin n) F) := by
    rw [← ProjGenLinGroup.mk_eq_one, map_pow]
    exact hB
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨c, hc⟩ := hc
  set m := (Fintype.card F - 1) ^ (s - 1) with hm
  have hs1 : 1 ≤ s - 1 := by have := hs.two_le; omega
  refine ⟨m, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, ← hc, ← map_pow]
    have hc1 : c ^ (Fintype.card F - 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact FiniteField.pow_card_sub_one_eq_one _ c.ne_zero
    have hpow : c ^ m = 1 := by
      rw [hm, show s - 1 = (s - 1 - 1) + 1 by omega, pow_succ', pow_mul, hc1, one_pow]
    rw [hpow, map_one]
  · rw [map_pow]
    have hfermat : m % s = 1 := by
      have hcop : Nat.Coprime s (Fintype.card F - 1) := (Nat.Prime.coprime_iff_not_dvd hs).2 hsq
      have h1 := Nat.ModEq.pow_totient hcop.symm
      rw [Nat.totient_prime hs] at h1
      unfold Nat.ModEq at h1
      rw [Nat.mod_eq_of_lt hs.one_lt] at h1
      rw [hm]
      exact h1
    rw [pow_eq_pow_mod m hB, hfermat, pow_one]

theorem not_isSquare_of_comm_odd_order {n s e : ℕ} (hn : 2 ≤ n) (hq : Odd (Fintype.card F))
    (hs : s.Prime) (hs2 : s ≠ 2) (hsq : s ∣ (Fintype.card F) ^ 2 ^ e + 1)
    (hne : n ≤ 2 ^ (e + 1)) (A : GL (Fin n) F) (hA1 : ProjGenLinGroup.mk A ≠ 1)
    (hA2 : ProjGenLinGroup.mk A ^ 2 = 1) (g : GL (Fin n) F) (hg1 : ProjGenLinGroup.mk g ≠ 1)
    (hgs : ProjGenLinGroup.mk g ^ s = 1)
    (hcomm : ProjGenLinGroup.mk g * ProjGenLinGroup.mk A =
      ProjGenLinGroup.mk A * ProjGenLinGroup.mk g) :
    ∃ l : Fˣ, A ^ 2 = GeneralLinearGroup.scalar (Fin n) l ∧ ¬ IsSquare (l : F) := by
  have : NeZero n := ⟨by omega⟩
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hc : ringChar F ∣ 2 := (ringChar.spec F 2).1 (by exact_mod_cast h)
    have hc2 : ringChar F = 2 :=
      (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F (ringChar F)) Nat.prime_two).1 hc
    have : ringChar F ∣ Fintype.card F := by
      obtain ⟨n', hp, hn'⟩ := FiniteField.card F (ringChar F)
      rw [hn']
      exact dvd_pow_self _ (Nat.pos_iff_ne_zero.1 n'.2)
    rw [hc2] at this
    exact (Nat.not_even_iff_odd.2 hq) (even_iff_two_dvd.2 this)
  obtain ⟨l, hl, -, hidx, hcase⟩ :=
    projective_involution_centralizer_matrix_structure n hn A h2 hA1 hA2
  refine ⟨l, hl, fun hsqr => ?_⟩
  rcases hcase with ⟨-, hsplit⟩ | ⟨hns, -⟩
  swap
  · exact hns hsqr
  have := Fact.mk hs
  have : Finite (ProjGenLinGroup (Fin n) F) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  obtain ⟨b, -, hr, hs', hrs, eC, -, -, -, -⟩ := hsplit
  set x : Subgroup.centralizer {ProjGenLinGroup.mk A} :=
    ⟨ProjGenLinGroup.mk g, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩ with hx
  have hxs : orderOf x = s := by
    rw [hx, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hgs hg1
  have hxN : x ∈ (ordinaryCentralizerProjection A).range := by
    have := ordinaryCentralizerProjection_range_normal A
    exact mem_of_index_le_two hidx (hxs ▸ hs.odd_of_ne_two hs2)
  obtain ⟨B, hB⟩ := hxN
  have hBg : ProjGenLinGroup.mk (B : GL (Fin n) F) = ProjGenLinGroup.mk g :=
    congrArg Subtype.val hB
  have hq1 : ¬ s ∣ Fintype.card F - 1 := by
    have := not_dvd_pow_sub_one (j := 1) hs hs2 Fintype.card_pos hsq le_rfl
      (by have := Nat.one_lt_two_pow (n := e + 1) (by omega); omega)
    simpa using this
  obtain ⟨m, hm1, hm2⟩ := exists_pow_eq_one_mk_eq hs hq1 (B := (B : GL (Fin n) F))
    (by rw [hBg]; exact hgs)
  have hBm : (B ^ m) ^ s = 1 := Subtype.ext (by simpa using hm1)
  have he1 : (eC (B ^ m)).1 = 1 := by
    apply eq_one_of_pow_eq_one_of_not_dvd hs
      (not_dvd_card_GL hs hs2 hsq (by omega))
    rw [← Prod.pow_fst, ← map_pow, hBm, map_one, Prod.fst_one]
  have he2 : (eC (B ^ m)).2 = 1 := by
    apply eq_one_of_pow_eq_one_of_not_dvd hs
      (not_dvd_card_GL hs hs2 hsq (by omega))
    rw [← Prod.pow_snd, ← map_pow, hBm, map_one, Prod.snd_one]
  have hBm1 : B ^ m = 1 := eC.injective (by rw [map_one]; exact Prod.ext he1 he2)
  apply hg1
  rw [← hBg, ← hm2]
  have : ((B ^ m : Subgroup.centralizer {A}) : GL (Fin n) F) = 1 := by rw [hBm1]; rfl
  rw [← Subgroup.coe_pow, this, map_one]

end CFSG.ComponentClassification.CatFactsL4U4
