module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive
public import CFSG.CharacterTheory.Semidihedral.Principal.NormalPrimeInversionInvolutionSum
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionPrincipalTransport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u

variable {H : Type u} [Group H] [Fintype H]

theorem inverts_of_not_mem_centralizer_of_prime {ℓ : ℕ} [Fact ℓ.Prime] (W : Subgroup H) [W.Normal]
    (hW : Nat.card W = ℓ) (hindex : (Subgroup.centralizer (W : Set H)).index = 2) (h : H)
    (hh : h ∉ Subgroup.centralizer (W : Set H)) : ∀ w ∈ W, h * w * h⁻¹ = w⁻¹ := by
  have hp : ℓ.Prime := Fact.out
  obtain ⟨u, huW, hu1⟩ : ∃ u ∈ W, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : W = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [hbot, Subgroup.card_bot] at hW
    exact hp.one_lt.ne hW
  have hu : orderOf u = ℓ := by
    have hdvd : orderOf u ∣ ℓ := by
      rw [← hW]
      exact Subgroup.orderOf_dvd_natCard _ huW
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hu1
    · exact h1
  have hWu : W = Subgroup.zpowers u := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huW)
    rw [Nat.card_zpowers, hu, hW]
  have hrel : (Subgroup.centralizer (Subgroup.zpowers u : Set H)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set H)) = 2 := by
    rw [← hWu, Subgroup.normalizer_eq_top, Subgroup.relIndex_top_right]
    exact hindex
  have hnorm : h ∈ Subgroup.normalizer (Subgroup.zpowers u : Set H) := by
    rw [← hWu, Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top h
  have hinvu : h * u * h⁻¹ = u⁻¹ := by
    rcases conj_eq_or_inv_of_mem_normalizer (ℓ := ℓ) hu hrel hnorm with h1 | h1
    · exfalso
      apply hh
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : w ∈ W := hw
      rw [hWu] at hw'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
      have hcomm : Commute u h := by
        have : h * u = u * h := by
          calc h * u = h * u * h⁻¹ * h := by group
            _ = u * h := by rw [h1]
        exact this.symm
      exact (hcomm.zpow_left k).eq
    · exact h1
  intro w hw
  rw [hWu] at hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  calc h * u ^ k * h⁻¹ = (h * u * h⁻¹) ^ k := by
        rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    _ = (u ^ k)⁻¹ := by rw [hinvu, inv_zpow]

omit [Fintype H] in
theorem involution_mem_of_odd_direct [Finite H] {W J K : Subgroup H} [W.Normal]
    (hodd : Odd (Nat.card W)) (hsup : W ⊔ J = K) (hinf : W ⊓ J = ⊥)
    (hcomm : ∀ w ∈ W, ∀ j ∈ J, w * j = j * w) {x : H} (hxK : x ∈ K) (hx : orderOf x = 2) :
    x ∈ J := by
  rw [← hsup] at hxK
  obtain ⟨w, hw, j, hj, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxK
  have hsq : (w * j) ^ 2 = 1 := by rw [← hx, pow_orderOf_eq_one]
  have hww : w ^ 2 = (j ^ 2)⁻¹ := by
    have hwj := hcomm w hw j hj
    have h' : (w * j) ^ 2 = w ^ 2 * j ^ 2 := by
      rw [pow_two, pow_two, pow_two]
      calc w * j * (w * j) = w * (j * w) * j := by group
        _ = w * (w * j) * j := by rw [hwj]
        _ = w * w * (j * j) := by group
    rw [h'] at hsq
    exact eq_inv_of_mul_eq_one_left hsq
  have hw2 : w ^ 2 = 1 := by
    have hmemW : w ^ 2 ∈ W := W.pow_mem hw 2
    have hmemJ : w ^ 2 ∈ J := by rw [hww]; exact J.inv_mem (J.pow_mem hj 2)
    have : w ^ 2 ∈ W ⊓ J := ⟨hmemW, hmemJ⟩
    rwa [hinf, Subgroup.mem_bot] at this
  have hw1 : w = 1 := by
    have hdvd2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hw2
    have hodd' : Odd (orderOf w) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard W hw)
    have h1 : orderOf w = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact h
      · rw [h] at hodd'
        exact absurd hodd' (by decide)
    exact orderOf_eq_one_iff.mp h1
  rw [hw1, one_mul]
  exact hj

theorem prime_not_dvd_one_twenty {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ) : ¬ ℓ ∣ 120 := by
  have hp : ℓ.Prime := Fact.out
  intro h
  have h' : ℓ ∣ 2 ^ 3 * (3 * 5) := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h2 | h35
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega
  · rcases (Nat.Prime.dvd_mul hp).mp h35 with h3 | h5
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
    · have := Nat.le_of_dvd (by norm_num) h5
      omega

theorem normal_prime_dihedral_eight_small_alternating_quotient_involution_counts (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ) (W : Subgroup H) [W.Normal] [IsCyclic W] (hW : Nat.card W = ℓ)
    (hindex : (Subgroup.centralizer (W : Set H)).index = 2)
    (hdihedral : ∃ P : Sylow 2 H, Nonempty ((P : Subgroup H) ≃* DihedralGroup 4)) (d : ℕ)
    (hd : d = 4 ∨ d = 5)
    (hquot : Nonempty (Subgroup.centralizer (W : Set H) ⧸
      W.subgroupOf (Subgroup.centralizer (W : Set H)) ≃* alternatingGroup (Fin d))) :
    (∃ P : Sylow ℓ H, (P : Subgroup H) = W) ∧
    (∃ σ : H ⧸ W ≃* Equiv.Perm (Fin d), ∀ h : H,
      h ∈ Subgroup.centralizer (W : Set H) ↔ σ (h : H ⧸ W) ∈ alternatingGroup (Fin d)) ∧
    (d = 4 → Nat.card (Subgroup.centralizer (W : Set H)) = 12 * ℓ ∧ Nat.card H = 24 * ℓ ∧
      Nat.card {x : H // x ∈ Subgroup.centralizer (W : Set H) ∧ orderOf x = 2} = 3 ∧
      Nat.card {x : H // x ∉ Subgroup.centralizer (W : Set H) ∧ orderOf x = 2} = 6 * ℓ) ∧
    (d = 5 → Nat.card (Subgroup.centralizer (W : Set H)) = 60 * ℓ ∧ Nat.card H = 120 * ℓ ∧
      Nat.card {x : H // x ∈ Subgroup.centralizer (W : Set H) ∧ orderOf x = 2} = 15 ∧
      Nat.card {x : H // x ∉ Subgroup.centralizer (W : Set H) ∧ orderOf x = 2} = 10 * ℓ) ∧
    ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
      [CharP (ComplexAlgebraicIntegers ⧸ ideal) ℓ] (basis : FiniteIrreducibleCharacterBasis H)
      (principal : basis.index), (basis.representation principal).character = 1 →
      ∀ w ∈ W, w ≠ 1 →
        ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
            ((Nat.card H : ℂ)⁻¹ * ∑ x ∈ Finset.univ.filter (fun x : H => orderOf x = 2),
              (basis.representation θ).character x) ^ 2 *
              (basis.representation θ).character w / (basis.representation θ).character 1 =
          if d = 4 then 1 / 8 else 1 / 72 := by
  have hp : ℓ.Prime := Fact.out
  set K := Subgroup.centralizer (W : Set H) with hK
  have hodd : Odd (Nat.card W) := by
    rw [hW]
    exact hp.odd_of_ne_two (by omega)
  have hWK : W ≤ K := CyclicInversion.le_centralizer_of_isCyclic W
  obtain ⟨P2, ⟨eP2⟩⟩ := hdihedral
  obtain ⟨ψ⟩ := hquot
  have hperm : ∃ σH : H →* Equiv.Perm (Fin d), Function.Surjective σH ∧
      (∀ h, σH h = 1 ↔ h ∈ W) ∧ ∀ h, h ∈ K ↔ σH h ∈ alternatingGroup (Fin d) := by
    rcases hd with rfl | rfl
    · exact CyclicAlternatingFive.exists_perm_hom W (by norm_num) CyclicSymmetricFour.autEquiv
        CyclicSymmetricFour.autEquiv_apply CyclicSymmetricFour.alternating_eq_one_of_forall_commute
        hodd hWK hindex ψ P2 eP2
    · exact CyclicAlternatingFive.exists_perm_hom W (by norm_num) CyclicAlternatingFive.autEquiv
        CyclicAlternatingFive.autEquiv_apply
        CyclicAlternatingFive.alternating_eq_one_of_forall_commute hodd hWK hindex ψ P2 eP2
  obtain ⟨σH, hσsurj, hσker, hσK⟩ := hperm
  have hkerW : W = σH.ker := by
    ext h
    rw [MonoidHom.mem_ker, hσker]
  have hcounts : (d = 4 → Nat.card K = 12 * ℓ ∧ Nat.card H = 24 * ℓ ∧
        Nat.card {x : H // x ∈ K ∧ orderOf x = 2} = 3 ∧
        Nat.card {x : H // x ∉ K ∧ orderOf x = 2} = 6 * ℓ) ∧
      (d = 5 → Nat.card K = 60 * ℓ ∧ Nat.card H = 120 * ℓ ∧
        Nat.card {x : H // x ∈ K ∧ orderOf x = 2} = 15 ∧
        Nat.card {x : H // x ∉ K ∧ orderOf x = 2} = 10 * ℓ) := by
    rcases hd with rfl | rfl
    · refine ⟨fun _ => ?_, fun h => absurd h (by norm_num)⟩
      obtain ⟨basis0⟩ := finiteIrreducibleCharacterBasis_exists (G := H)
      obtain ⟨principal0, hprincipal0⟩ :=
        finiteIrreducibleCharacterBasis_exists_principal_label basis0
      obtain ⟨J, -, -, -, hJK, -, -, hsup, hinf, hcomm, -, -, -, -, -, -, -, -, -, hKc, hHc, hJ3,
          hout, -⟩ := cyclic_prime_power_A4_centralizer_inversion_normalizer_sign_S4_column_sum ℓ
        (by omega) 1 W (by rw [hW, pow_one]) hindex ⟨ψ⟩ ⟨P2, ⟨eP2⟩⟩ basis0 principal0
          hprincipal0
      have hinvJ : ∀ x, x ∈ K → orderOf x = 2 → x ∈ J := fun x hx hx2 =>
        involution_mem_of_odd_direct hodd hsup hinf hcomm hx hx2
      refine ⟨by rw [hKc, pow_one], by rw [hHc, pow_one], ?_, ?_⟩
      · rw [← hJ3]
        apply Nat.card_congr
        exact Equiv.subtypeEquivRight fun x =>
          ⟨fun h => ⟨hinvJ x h.1 h.2, h.2⟩, fun h => ⟨hJK h.1, h.2⟩⟩
      · rw [show 6 * ℓ = 6 * ℓ ^ 1 by rw [pow_one], ← hout]
        apply Nat.card_congr
        exact Equiv.subtypeEquivRight fun x =>
          ⟨fun h => ⟨fun hJ => h.1 (hJK hJ), h.2⟩,
            fun h => ⟨fun hKx => h.1 (hinvJ x hKx h.2), h.2⟩⟩
    · refine ⟨fun h => absurd h (by norm_num), fun _ => ?_⟩
      have hinv : ∀ h, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹ :=
        fun h hh => inverts_of_not_mem_centralizer_of_prime W hW hindex h hh
      obtain ⟨J, x, E, σ, -, hsup, hinf, hcomm, -, -, -, -, -, -, -, -, -, hKc, hHc, hinvol, hJ15,
          hout, -⟩ := odd_cyclic_inversion_normalizer_alternating_five_centralizer_splits_by_sign
        W hodd hindex hinv ⟨ψ⟩ ⟨P2, ⟨eP2⟩⟩
      have hJK : J ≤ K := by rw [hK, ← hsup]; exact le_sup_right
      refine ⟨by rw [hKc, hW], by rw [hHc, hW], ?_, by rw [hout, hW]⟩
      rw [← hJ15]
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight fun y =>
        ⟨fun h => ⟨(hinvol y h.2).resolve_right (not_not.mpr h.1), h.2⟩,
          fun h => ⟨hJK h.1, h.2⟩⟩
  have hHcard : Nat.card H = (if d = 4 then 24 else 120) * ℓ := by
    rcases hd with rfl | rfl
    · simpa using (hcounts.1 rfl).2.1
    · simpa using (hcounts.2 rfl).2.1
  have hsylow : Nat.card W = ℓ ^ (Nat.card H).factorization ℓ := by
    have hnd : ¬ ℓ ∣ (if d = 4 then 24 else 120) := by
      split_ifs
      · exact CyclicSymmetricFour.prime_not_dvd_twenty_four (by omega)
      · exact prime_not_dvd_one_twenty hℓ
    rw [hHcard, Nat.factorization_mul (by split_ifs <;> norm_num) hp.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, Nat.Prime.factorization_self hp, zero_add, pow_one,
      hW]
  let Wsyl : Sylow ℓ H := Sylow.ofCard W hsylow
  have hWsyl : (Wsyl : Subgroup H) = W := rfl
  refine ⟨⟨Wsyl, hWsyl⟩, ⟨(QuotientGroup.quotientMulEquivOfEq hkerW).trans
      (QuotientGroup.quotientKerEquivOfSurjective σH hσsurj), fun h => ?_⟩, hcounts.1,
    hcounts.2, ?_⟩
  · rw [hσK h]
    rfl
  intro ideal _ _ basis principal hprincipal w hw hw1
  have hWn : (Wsyl : Subgroup H).Normal := by rw [hWsyl]; infer_instance
  obtain ⟨hsum, -⟩ := normal_prime_inversion_principal_block_involution_sum basis ideal ℓ
    (by omega) principal hprincipal Wsyl hWn hW hindex
  have h := hsum w hw hw1
  rw [h]
  change 2 * (((Finset.univ.filter fun x : H => x ∉ K ∧ orderOf x = 2).card : ℕ) : ℂ) ^ 2 /
    (Nat.card H : ℂ) ^ 2 = _
  have hbcard : ((Finset.univ.filter fun x : H => x ∉ K ∧ orderOf x = 2).card : ℂ) =
      Nat.card {x : H // x ∉ K ∧ orderOf x = 2} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hℓ0 : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rcases hd with rfl | rfl
  · rw [hbcard, (hcounts.1 rfl).2.2.2, (hcounts.1 rfl).2.1]
    simp only [↓reduceIte]
    push_cast
    field_simp
    ring
  · rw [hbcard, (hcounts.2 rfl).2.2.2, (hcounts.2 rfl).2.1]
    simp only [show (5 : ℕ) ≠ 4 by norm_num, ↓reduceIte]
    push_cast
    field_simp
    ring

end CFSG.Semidihedral.Principal
