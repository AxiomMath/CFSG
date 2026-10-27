module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_orth3_solvable_aux (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 3) :
    Group.IsSolvable (OGroup Q) := by
  letI : Fintype (OGroup Q) := Fintype.ofFinite _
  refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (p := 2) (q := 3) (a := 4) (b := 1)
    Nat.prime_two Nat.prime_three (by decide) ?_
  rw [← Nat.card_eq_fintype_card, natCard_oGroup_three hQ hdim]
  norm_num

private theorem isPGroup_three_twoRes_of_card_dvd_six {H : Type} [Group H] [Finite H]
    (hcard : Nat.card H ∣ 6) : IsPGroup 3 ↥(twoRes (⊤ : Subgroup H)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 H))
  haveI : Finite (Sylow 3 H) := P.finite_of_finiteIndex
  have hn_dvd : Nat.card (Sylow 3 H) ∣ 6 :=
    P.card_dvd_index.trans P.index_dvd_card |>.trans hcard
  have hn1 : Nat.card (Sylow 3 H) = 1 := by
    have hmod := card_sylow_modEq_one 3 H
    have hnmem : Nat.card (Sylow 3 H) ∈ ({1, 2, 3, 6} : Finset ℕ) := by
      have hmem : Nat.card (Sylow 3 H) ∈ Nat.divisors 6 := by
        rw [Nat.mem_divisors]; exact ⟨hn_dvd, by norm_num⟩
      rwa [show Nat.divisors 6 = {1, 2, 3, 6} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnmem
    rcases hnmem with h | h | h | h
    · exact h
    · exact absurd (h ▸ hmod) (by decide)
    · exact absurd (h ▸ hmod) (by decide)
    · exact absurd (h ▸ hmod) (by decide)
  haveI : Subsingleton (Sylow 3 H) :=
    Finite.card_le_one_iff_subsingleton.mp (by omega)
  have hmem : ∀ y : H, Odd (orderOf y) → y ∈ (P : Subgroup H) := by
    intro y hodd
    have hdvd6 : orderOf y ∣ 6 := (orderOf_dvd_natCard y).trans hcard
    have hdvd3 : orderOf y ∣ 3 := by
      have h2 : orderOf y ∣ 3 * 2 := by rwa [show (6 : ℕ) = 3 * 2 by norm_num] at hdvd6
      exact (Nat.coprime_two_right.mpr hodd).dvd_of_dvd_mul_right h2
    have hsub : IsPGroup 3 (Subgroup.zpowers y) := by
      refine IsPGroup.of_card_dvd_pow (p := 3) (n := 1) ?_
      rw [pow_one, Nat.card_zpowers]
      exact hdvd3
    obtain ⟨Q, hQ⟩ := hsub.exists_le_sylow
    have hQP : Q = P := Subsingleton.elim Q P
    rw [hQP] at hQ
    exact hQ (Subgroup.mem_zpowers y)
  have hE_le : twoRes (⊤ : Subgroup H) ≤ (P : Subgroup H) := by
    refine (Subgroup.closure_le (K := (P : Subgroup H))).mpr ?_
    rintro y ⟨-, hodd⟩
    exact hmem y hodd
  exact P.isPGroup'.of_injective (Subgroup.inclusion hE_le) (Subgroup.inclusion_injective hE_le)

private theorem exists_normal_two_series_card_48 {G : Type} [Group G] [Finite G]
    (hcard : Nat.card G = 48) :
    ∃ (N : Subgroup G) (_ : N.Normal), IsPGroup 2 N ∧
      IsPGroup 3 ↥(twoRes (⊤ : Subgroup (G ⧸ N))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 G))
  haveI : Finite (Sylow 2 G) := P.finite_of_finiteIndex
  have hP16 : Nat.card (P : Subgroup G) = 16 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have h1 : 2 ^ 4 ∣ Nat.card (P : Subgroup G) :=
      P.pow_dvd_card_of_pow_dvd_card (by rw [hcard]; norm_num)
    have h2 : Nat.card (P : Subgroup G) ∣ 48 := by
      rw [← hcard]; exact P.1.card_subgroup_dvd_card
    rw [hk] at h1 h2
    have hle : 4 ≤ k := by
      rwa [Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)] at h1
    have hdvd : 2 ^ k ∣ 2 ^ 4 := by
      have hcop : Nat.Coprime (2 ^ k) 3 :=
        (Nat.coprime_primes Nat.prime_two Nat.prime_three).mpr (by decide) |>.pow_left k
      refine hcop.dvd_of_dvd_mul_right ?_
      rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num] at h2
      exact h2
    have hle' : k ≤ 4 := by
      rwa [Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)] at hdvd
    rw [hk, le_antisymm hle' hle]
    norm_num
  have hPindex : (P : Subgroup G).index = 3 := by
    have h := (P : Subgroup G).card_mul_index
    rw [hP16, hcard] at h
    omega
  have hn : Nat.card (Sylow 2 G) = 1 ∨ Nat.card (Sylow 2 G) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (by rw [← hPindex]; exact P.card_dvd_index)
  rcases hn with hn | hn
  ·
    haveI : Subsingleton (Sylow 2 G) :=
      Finite.card_le_one_iff_subsingleton.mp (by omega)
    refine ⟨(P : Subgroup G), Sylow.normal_of_subsingleton P, P.isPGroup', ?_⟩
    have hq : Nat.card (G ⧸ (P : Subgroup G)) = 3 := hPindex
    exact (IsPGroup.of_card (p := 3) (n := 1) (by rw [hq]; norm_num)).to_subgroup _
  ·
    let φ : G →* Equiv.Perm (Sylow 2 G) := MulAction.toPermHom G (Sylow 2 G)
    have hNG : Nat.card (Subgroup.normalizer (P : Set G)) = 16 := by
      have hidx : (Subgroup.normalizer (P : Set G)).index = 3 := by
        have h2 := P.card_eq_index_normalizer
        rw [hn] at h2
        exact h2.symm
      have h := (Subgroup.normalizer (P : Set G)).card_mul_index
      rw [hidx, hcard] at h
      omega
    have hNormEq : (P : Subgroup G) = Subgroup.normalizer (P : Set G) :=
      Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (by rw [hNG, hP16])
    have hKP : φ.ker ≤ (P : Subgroup G) := by
      intro k hk
      have hfix : k • P = P := by
        change (φ k) P = P
        have hk1 : φ k = 1 := MonoidHom.mem_ker.mp hk
        simpa using congrArg (fun e : Equiv.Perm (Sylow 2 G) => e P) hk1
      have hmem : k ∈ Subgroup.normalizer (P : Set G) :=
        (Sylow.smul_eq_iff_mem_normalizer).mp hfix
      rwa [← hNormEq] at hmem
    have hK2 : IsPGroup 2 φ.ker :=
      P.isPGroup'.of_injective (Subgroup.inclusion hKP) (Subgroup.inclusion_injective hKP)
    refine ⟨φ.ker, MonoidHom.normal_ker φ, hK2, ?_⟩
    refine isPGroup_three_twoRes_of_card_dvd_six ?_
    have hperm : Nat.card (Equiv.Perm (Sylow 2 G)) = 6 := by
      rw [Nat.card_perm, hn]; norm_num
    have hinj : Function.Injective (QuotientGroup.kerLift φ) := QuotientGroup.kerLift_injective φ
    have hcongr : Nat.card (G ⧸ φ.ker) = Nat.card (QuotientGroup.kerLift φ).range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [hcongr, ← hperm]
    exact Subgroup.card_subgroup_dvd_card _

theorem ff_orth3_series_aux (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 3) :
    ∃ (N : Subgroup (OGroup Q)) (_ : N.Normal), IsPGroup 2 N ∧
      IsPGroup 3 ↥(twoRes (⊤ : Subgroup (OGroup Q ⧸ N))) :=
  exists_normal_two_series_card_48 (natCard_oGroup_three hQ hdim)

end CFSG.OddStandard.SmallF3.Omega
