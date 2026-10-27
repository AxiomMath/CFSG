module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem aor_exists_mul_of_mem_sup {M W : Subgroup G}
    (hW : ∀ w ∈ W, ∀ m ∈ M, w * m * w⁻¹ ∈ M) {x : G} (hx : x ∈ M ⊔ W) :
    ∃ m ∈ M, ∃ w ∈ W, x = m * w := by
  let D : Subgroup G :=
    { carrier := {x | ∃ m ∈ M, ∃ w ∈ W, x = m * w}
      one_mem' := ⟨1, M.one_mem, 1, W.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨m, hm, w, hw, rfl⟩ ⟨m', hm', w', hw', rfl⟩
        refine ⟨m * (w * m' * w⁻¹), M.mul_mem hm (hW w hw m' hm'), w * w',
          W.mul_mem hw hw', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨m, hm, w, hw, rfl⟩
        refine ⟨w⁻¹ * m⁻¹ * (w⁻¹)⁻¹, hW w⁻¹ (W.inv_mem hw) m⁻¹ (M.inv_mem hm),
          w⁻¹, W.inv_mem hw, ?_⟩
        group }
  have hle : M ⊔ W ≤ D :=
    sup_le (fun m hm => ⟨m, hm, 1, W.one_mem, by simp⟩)
      (fun w hw => ⟨1, M.one_mem, w, hw, by simp⟩)
  exact hle hx

theorem aor_le_of_le_sup_odd {M W P : Subgroup G}
    (hMW : ∀ w ∈ W, ∀ m ∈ M, w * m * w⁻¹ ∈ M) (hW : ∀ w ∈ W, Odd (orderOf w))
    (hP : IsPGroup 2 P) (hle : P ≤ M ⊔ W) : P ≤ M := by
  intro y hy
  obtain ⟨a, ha⟩ := hP ⟨y, hy⟩
  have ha' : y ^ 2 ^ a = 1 := by
    simpa [Subgroup.coe_pow] using congrArg (fun z : P => (z : G)) ha
  obtain ⟨m, hm, w, hw, hyw⟩ := aor_exists_mul_of_mem_sup hMW (hle hy)
  rw [hyw] at ha'
  have hclaim : ∀ n : ℕ, ∃ m' ∈ M, (m * w) ^ n = m' * w ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, M.one_mem, by simp⟩
    | succ n ih =>
        obtain ⟨m', hm', heq⟩ := ih
        refine ⟨m' * (w ^ n * m * (w ^ n)⁻¹),
          M.mul_mem hm' (hMW (w ^ n) (W.pow_mem hw n) m hm), ?_⟩
        rw [pow_succ, heq]
        group
  obtain ⟨m', hm', heq2⟩ := hclaim (2 ^ a)
  have hmw : w ^ (2 ^ a) ∈ M := by
    have h1 : m' * w ^ (2 ^ a) = 1 := by rw [← heq2]; exact ha'
    have h2 : w ^ (2 ^ a) = m'⁻¹ := by
      simpa using congrArg (fun z => m'⁻¹ * z) h1
    rw [h2]
    exact M.inv_mem hm'
  have hcop : Nat.Coprime (2 ^ a) (orderOf w) :=
    ((hW w hw).coprime_two_left).pow_left a
  have hwmem : w ∈ Subgroup.zpowers (w ^ (2 ^ a)) :=
    mem_zpowers_pow_iff.mpr hcop
  have hwM : w ∈ M := Subgroup.zpowers_le.mpr hmw hwmem
  rw [hyw]
  exact M.mul_mem hm hwM

theorem aor_exists_subgroup_odd_elems [Finite G] (Y : Subgroup G)
    (hcyc : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Y → IsCyclic P) :
    ∃ N : Subgroup G, ∀ x : G, x ∈ N ↔ x ∈ Y ∧ Odd (orderOf x) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hodd : Odd (Nat.card Y)
  · refine ⟨Y, fun x => ⟨fun hx => ⟨hx, ?_⟩, fun h => h.1⟩⟩
    exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard Y hx)
  · have heven : Even (Nat.card ↥Y) := Nat.not_odd_iff_even.mp hodd
    have hmin : (Nat.card ↥Y).minFac = 2 :=
      (Nat.minFac_eq_two_iff _).mpr (even_iff_two_dvd.mp heven)
    have hcyc' : ∀ P : Sylow 2 ↥Y, IsCyclic (P : Subgroup ↥Y) := by
      intro Q
      have hQp : IsPGroup 2 ((Q : Subgroup ↥Y).map Y.subtype) :=
        Q.isPGroup'.map Y.subtype
      have hQle : (Q : Subgroup ↥Y).map Y.subtype ≤ Y := Subgroup.map_subtype_le _
      haveI : IsCyclic ↥((Q : Subgroup ↥Y).map Y.subtype) := hcyc _ hQp hQle
      exact isCyclic_of_surjective
        (Subgroup.equivMapOfInjective (Q : Subgroup ↥Y) Y.subtype Y.subtype_injective).symm
        (MulEquiv.surjective _)
    obtain ⟨Sy⟩ := (inferInstance : Nonempty (Sylow 2 ↥Y))
    obtain ⟨Kc, hKn, hcomp⟩ :
        ∃ Kc : Subgroup ↥Y, Kc.Normal ∧ Kc.IsComplement' (Sy : Subgroup ↥Y) :=
      ⟨_, MonoidHom.normal_ker _, IsCyclic.isComplement' hmin (hcyc' Sy)⟩
    haveI : Kc.Normal := hKn
    have hKodd : Odd (Nat.card Kc) := by
      rw [← hcomp.index_eq_card]
      exact Nat.not_even_iff_odd.mp
        (fun hevenIndex => Sy.not_dvd_index (even_iff_two_dvd.mp hevenIndex))
    have hcard : Nat.card (↥Y ⧸ Kc) = 2 ^ Nat.factorization (Nat.card ↥Y) 2 := by
      rw [← Subgroup.index_eq_card, hcomp.symm.index_eq_card]
      exact Sylow.card_eq_multiplicity Sy
    refine ⟨Kc.map Y.subtype, fun x => ⟨?_, ?_⟩⟩
    · rintro ⟨y, hyK, rfl⟩
      refine ⟨y.2, ?_⟩
      change Odd (orderOf ((y : ↥Y) : G))
      rw [Subgroup.orderOf_coe y]
      exact Odd.of_dvd_nat hKodd (Subgroup.orderOf_dvd_natCard Kc hyK)
    · rintro ⟨hxY, hxodd⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxY⟩, ?_, rfl⟩
      have hdvd : orderOf (QuotientGroup.mk' Kc (⟨x, hxY⟩ : ↥Y)) ∣
          orderOf (⟨x, hxY⟩ : ↥Y) := by
        rw [orderOf_dvd_iff_pow_eq_one]
        show (QuotientGroup.mk' Kc (⟨x, hxY⟩ : ↥Y)) ^ orderOf (⟨x, hxY⟩ : ↥Y) = 1
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      have hoddq : Odd (orderOf (QuotientGroup.mk' Kc (⟨x, hxY⟩ : ↥Y))) :=
        Odd.of_dvd_nat (by rw [Subgroup.orderOf_mk x hxY]; exact hxodd) hdvd
      have hdvd2 : orderOf (QuotientGroup.mk' Kc (⟨x, hxY⟩ : ↥Y)) ∣
          2 ^ Nat.factorization (Nat.card ↥Y) 2 := by
        rw [← hcard]
        exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime (orderOf (QuotientGroup.mk' Kc (⟨x, hxY⟩ : ↥Y)))
          (2 ^ Nat.factorization (Nat.card ↥Y) 2) :=
        (Nat.coprime_two_right.mpr hoddq).pow_right _
      have hone : orderOf (QuotientGroup.mk' Kc (⟨x, hxY⟩ : ↥Y)) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd2
      have hone' : QuotientGroup.mk' Kc (⟨x, hxY⟩ : ↥Y) = 1 := orderOf_eq_one_iff.mp hone
      exact (QuotientGroup.eq_one_iff (N := Kc) (⟨x, hxY⟩ : ↥Y)).mp (by simpa using hone')

end CFSG.OddStandard.SmallF3.Omega
