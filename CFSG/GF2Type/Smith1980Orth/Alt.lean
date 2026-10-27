module

public import CFSG.GF2Type.Smith1980Orth.Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.Open Finset
open scoped Nat

@[expose] def fourPowSubOneProd (m : ℕ) : ℕ := ∏ j ∈ Icc 1 m, (2 ^ (2 * j) - 1)

private theorem fourPowSubOneProd_ne_zero (m : ℕ) : fourPowSubOneProd m ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have : 2 ^ 1 ≤ 2 ^ (2 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private theorem padicValNat_three_four_pow_sub_one {j : ℕ} (hj : j ≠ 0) :
    padicValNat 3 (2 ^ (2 * j) - 1) = 1 + padicValNat 3 j := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1) (by decide) (by norm_num)
    (by norm_num) (by norm_num) hj
  rw [one_pow] at h
  rw [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, h]
  norm_num

private theorem padicValNat_fourPowSubOneProd (m : ℕ) :
    padicValNat 3 (fourPowSubOneProd m) = m + padicValNat 3 (m)! := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  induction m with
  | zero => simp [fourPowSubOneProd]
  | succ k ih =>
    have hprod : fourPowSubOneProd (k + 1) =
        fourPowSubOneProd k * (2 ^ (2 * (k + 1)) - 1) := by
      simp only [fourPowSubOneProd]
      rw [Finset.prod_Icc_succ_top (by omega)]
    have hne : 2 ^ (2 * (k + 1)) - 1 ≠ 0 := by
      have : 2 ^ 1 ≤ 2 ^ (2 * (k + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hprod, padicValNat.mul (fourPowSubOneProd_ne_zero k) hne, ih,
      padicValNat_three_four_pow_sub_one (by omega), Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero k)]
    ring

private theorem div_three_le_padicValNat_factorial (x : ℕ) : x / 3 ≤ padicValNat 3 (x)! := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [← padicValNat_mul_div_factorial x, padicValNat_factorial_mul]
  omega

private theorem padicValNat_le_of_dvd {p a b : ℕ} [Fact p.Prime] (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat p a ≤ padicValNat p b :=
  (padicValNat_dvd_iff_le hb).mp ((pow_padicValNat_dvd (p := p) (n := a)).trans h)

private theorem finite_check (m ε : ℕ) (hm : 2 ≤ m) (hm7 : m ≤ 7) (hε : ε ≤ 1) :
    ∀ n < 80,
      (2 ^ ((m + 1) * (m + 2) + ε + 1) ∣ (n)! ∧ ¬ 2 ^ ((m + 1) * (m + 2) + ε + 2) ∣ (n)!) →
      ∀ K ≤ n / 2, 1 ≤ K →
        ¬ (2 ^ K * (K)! * (n - 2 * K)! ∣
          2 ^ ((m + 1) * (m + 2) + ε + 1) * (3 * fourPowSubOneProd m)) := by
  interval_cases m <;> interval_cases ε <;> decide +kernel

private theorem false_of_arith {m n K ε : ℕ} (hm : 2 ≤ m) (hε : ε ≤ 1) (hK : 1 ≤ K)
    (hKn : 2 * K ≤ n) (hA : (n)!.factorization 2 = (m + 1) * (m + 2) + ε + 1)
    (hB : 2 ^ K * (K)! * (n - 2 * K)! ∣
      2 ^ ((m + 1) * (m + 2) + ε + 1) * (3 * fourPowSubOneProd m)) : False := by
  have hn0 : (n)! ≠ 0 := Nat.factorial_ne_zero n
  have hA1 : 2 ^ ((m + 1) * (m + 2) + ε + 1) ∣ (n)! :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hn0).mpr hA.ge
  have hA2 : ¬ 2 ^ ((m + 1) * (m + 2) + ε + 2) ∣ (n)! := fun h =>
    absurd ((Nat.prime_two.pow_dvd_iff_le_factorization hn0).mp h) (by omega)
  by_cases hm7 : m ≤ 7
  · have hn : n < 80 := by
      by_contra hn
      push Not at hn
      apply hA2
      refine dvd_trans ?_ (Nat.factorial_dvd_factorial hn)
      refine dvd_trans (pow_dvd_pow 2 ?_) (by decide : 2 ^ 75 ∣ (80)!)
      have := Nat.mul_le_mul (by omega : m + 1 ≤ 8) (by omega : m + 2 ≤ 9)
      omega
    exact finite_check m ε hm hm7 hε n hn ⟨hA1, hA2⟩ K (by omega) hK hB
  · push Not at hm7
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hn : (m + 1) * (m + 2) + 1 < n := by
      have h := padicValNat_factorial_lt_of_ne_zero (p := 2) (n := n) (by omega)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [← Nat.factorization_def _ Nat.prime_two] at h
      omega
    have hBne : 2 ^ ((m + 1) * (m + 2) + ε + 1) * (3 * fourPowSubOneProd m) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num))
        (mul_ne_zero (by norm_num) (fourPowSubOneProd_ne_zero m))
    have h3 := padicValNat_le_of_dvd (p := 3) hBne hB
    have h2K : padicValNat 3 (2 ^ K) = 0 := by
      rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
      simp
    have h2V : padicValNat 3 (2 ^ ((m + 1) * (m + 2) + ε + 1)) = 0 := by
      rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
      simp
    rw [padicValNat.mul (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _), padicValNat.mul (pow_ne_zero _ (by norm_num))
        (Nat.factorial_ne_zero _), padicValNat.mul (pow_ne_zero _ (by norm_num))
        (mul_ne_zero (by norm_num) (fourPowSubOneProd_ne_zero m)),
      padicValNat.mul (by norm_num) (fourPowSubOneProd_ne_zero m),
      padicValNat_fourPowSubOneProd, h2K, h2V] at h3
    have hK3 := div_three_le_padicValNat_factorial K
    have ha3 := div_three_le_padicValNat_factorial (n - 2 * K)
    have hm3 : padicValNat 3 (m)! ≤ m / 2 := by
      have := Nat.factorization_factorial_le_div_pred Nat.prime_three m
      rwa [Nat.factorization_def _ Nat.prime_three] at this
    have hmm : 8 * m ≤ m * m := Nat.mul_le_mul_right m hm7
    have hexp : (m + 1) * (m + 2) = m * m + 3 * m + 2 := by ring
    have hp3 : padicValNat 3 3 = 1 := padicValNat_self
    omega

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private theorem OrthData.exists_card_M (O : OrthData S) :
    ∃ ε r : ℕ, ε ≤ 1 ∧ r ∣ fourPowSubOneProd (S.width / 2) ∧
      Nat.card S.M = 2 ^ ((S.width / 2 + 1) * (S.width / 2 + 2) + ε) * (3 * r) ∧
      (Nat.card G).factorization 2 = (S.width / 2 + 1) * (S.width / 2 + 2) + ε := by
  obtain ⟨r, hr, hΩ⟩ := O.card_omega
  have hw := O.width_eq_two_mul
  have h4 := O.four_le
  have hM := O.card_M
  have hF := O.factorization_card
  have hdvd : r ∣ fourPowSubOneProd (S.width / 2) := by
    have h1 := S12DW.card_orthogonalGroup_mul_ncard_eq O.polarBilin_nondegenerate
      (m := S.width / 2) O.finrank_eq
    have h2 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup O.q) =
        2 * Nat.card (timmesfeldOmega O.q) := by
      rw [← S7.timmesfeldIsometries_eq]
      exact O.card_isometries
    rw [h2, hΩ] at h1
    have h3 : r ∣ 2 ^ ((S.width / 2) ^ 2) * fourPowSubOneProd (S.width / 2) := by
      rw [fourPowSubOneProd, ← h1]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_mul_left r _) 2) _
    exact (Nat.Coprime.pow_right _ hr.coprime_two_right).dvd_of_dvd_mul_left h3
  generalize hm : S.width / 2 = m at hw hΩ hdvd hF ⊢
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : k + 2 - 1 = k + 1 := by omega
  rw [hk] at hΩ
  rcases O.iso with h | h
  · refine ⟨0, r, by omega, hdvd, ?_, (hF.1 h)⟩
    rw [hM.1 h, hΩ, hw]
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    ring
  · refine ⟨1, r, by omega, hdvd, ?_, (hF.2 h)⟩
    rw [hM.2 h, hΩ, hw]
    rw [show (12 : ℕ) = 2 * 2 * 3 by norm_num]
    ring

open Subgroup Equiv in
private theorem exists_card_centralizer_involution {n : ℕ} {σ : Perm (Fin n)}
    (hσ : orderOf σ = 2) :
    ∃ K : ℕ, 1 ≤ K ∧ 2 * K ≤ n ∧
      Nat.card (centralizer ({σ} : Set (Perm (Fin n)))) = 2 ^ K * (K)! * (n - 2 * K)! := by
  have hp : (orderOf σ).Prime := hσ ▸ Nat.prime_two
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order hp
  rw [hσ] at hk
  have hle := Perm.sum_cycleType_le σ
  rw [hk, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hle
  refine ⟨k + 1, by omega, by omega, ?_⟩
  rw [Perm.nat_card_centralizer, hk]
  simp only [Multiset.sum_replicate, Multiset.prod_replicate, Fintype.card_fin, smul_eq_mul,
    Multiset.toFinset_replicate, Nat.add_one_ne_zero, ↓reduceIte, Finset.prod_singleton,
    Multiset.count_replicate_self]
  rw [mul_comm (k + 1) 2]
  ring

omit [Finite G] in
open Subgroup Equiv in
private theorem card_centralizer_dvd {z : G} {n : ℕ} (e : G ≃* alternatingGroup (Fin n)) :
    Nat.card (centralizer ({((e z : alternatingGroup (Fin n)) : Perm (Fin n))} :
      Set (Perm (Fin n)))) ∣ 2 * Nat.card (centralizer ({z} : Set G)) := by
  set σ : Perm (Fin n) := ((e z : alternatingGroup (Fin n)) : Perm (Fin n)) with hσdef
  set M := centralizer ({z} : Set G) with hM
  set C := centralizer ({σ} : Set (Perm (Fin n))) with hCdef
  let ψ0 : M →* Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp (e.toMonoidHom.comp M.subtype)
  have hψ0 : ∀ x : M, ψ0 x ∈ C := by
    intro x
    rw [hCdef, mem_centralizer_singleton_iff]
    have hx : (x : G) * z = z * (x : G) := mem_centralizer_singleton_iff.mp x.2
    have := congrArg (fun y : G => ((e y : alternatingGroup (Fin n)) : Perm (Fin n))) hx
    simpa [ψ0, hσdef, map_mul] using this
  let ψ : M →* C := ψ0.codRestrict C hψ0
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : ψ0 x = ψ0 y := congrArg (fun c : C => (c : Perm (Fin n))) hxy
    have : (e (x : G) : alternatingGroup (Fin n)) = e (y : G) := Subtype.ext h1
    exact Subtype.ext (e.injective this)
  let f : C →* ℤˣ := Perm.sign.comp C.subtype
  have hker : f.ker = ψ.range := by
    ext g
    simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro hg
      have hgA : (g : Perm (Fin n)) ∈ alternatingGroup (Fin n) :=
        Perm.mem_alternatingGroup.mpr hg
      refine ⟨⟨e.symm ⟨g, hgA⟩, ?_⟩, ?_⟩
      · rw [hM, mem_centralizer_singleton_iff]
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        apply Subtype.ext
        have := mem_centralizer_singleton_iff.mp g.2
        simpa [hσdef] using this
      · apply Subtype.ext
        show ((e (e.symm ⟨g, hgA⟩) : alternatingGroup (Fin n)) : Perm (Fin n)) = g
        rw [MulEquiv.apply_symm_apply]
    · rintro ⟨x, rfl⟩
      exact Perm.mem_alternatingGroup.mp (e (x : G)).2
  have hcard : Nat.card C = Nat.card M * Nat.card f.range := by
    rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker, hker,
      ← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
  have hrange : Nat.card f.range ∣ 2 := by
    have := Subgroup.card_subgroup_dvd_card f.range
    rwa [Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at this
  rw [hcard, mul_comm 2]
  exact Nat.mul_dvd_mul_left _ hrange

omit [Finite G] in
private theorem exists_card_dvd_centralizer {z : G} (hz : orderOf z = 2) {n : ℕ}
    (e : G ≃* alternatingGroup (Fin n)) :
    ∃ K : ℕ, 1 ≤ K ∧ 2 * K ≤ n ∧
      2 ^ K * (K)! * (n - 2 * K)! ∣ 2 * Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  have hσ : orderOf ((e z : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hz]
  obtain ⟨K, hK, hKn, hC⟩ := exists_card_centralizer_involution hσ
  exact ⟨K, hK, hKn, hC ▸ card_centralizer_dvd e⟩

theorem altInput : AltInput := by
  intro G _ _ S O n ⟨e⟩
  obtain ⟨ε, r, hε, hr, hM, hF⟩ := O.exists_card_M
  obtain ⟨K, hK, hKn, hdvd⟩ := exists_card_dvd_centralizer S.orderOf_z e
  have hn2 : 2 ≤ n := by omega
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
  have hG : Nat.card G = (n)! / 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
  have hne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hA : (n)!.factorization 2 = (S.width / 2 + 1) * (S.width / 2 + 2) + ε + 1 := by
    have h2 : 2 ∣ (n)! := Nat.dvd_factorial (by norm_num) hn2
    calc (n)!.factorization 2 = (2 * Nat.card G).factorization 2 := by
          rw [hG, Nat.mul_div_cancel' h2]
      _ = (2 : ℕ).factorization 2 + (Nat.card G).factorization 2 := by
          rw [Nat.factorization_mul two_ne_zero hne, Finsupp.add_apply]
      _ = (S.width / 2 + 1) * (S.width / 2 + 2) + ε + 1 := by
          rw [Nat.prime_two.factorization_self, hF]; ring
  have hB : 2 ^ K * (K)! * (n - 2 * K)! ∣
      2 ^ ((S.width / 2 + 1) * (S.width / 2 + 2) + ε + 1) *
        (3 * fourPowSubOneProd (S.width / 2)) := by
    refine hdvd.trans ?_
    rw [show Nat.card (Subgroup.centralizer ({S.z} : Set G)) = Nat.card S.M from rfl, hM,
      show 2 * (2 ^ ((S.width / 2 + 1) * (S.width / 2 + 2) + ε) * (3 * r)) =
        2 ^ ((S.width / 2 + 1) * (S.width / 2 + 2) + ε + 1) * (3 * r) by ring]
    exact mul_dvd_mul_left _ (mul_dvd_mul_left 3 hr)
  have h4 := O.four_le
  exact false_of_arith (by omega) hε hK hKn hA hB

end CFSG.GF2Type.Smith1980Orth
