module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Chevalley
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem exists_subgroup_odd_elems [Finite G] (Y : Subgroup G)
    (hcyc : ∀ P : Sylow 2 ↥Y, IsCyclic (P : Subgroup ↥Y)) :
    ∃ N : Subgroup G, Odd (Nat.card N) ∧ ∀ x : G, x ∈ N ↔ x ∈ Y ∧ Odd (orderOf x) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hodd : Odd (Nat.card Y)
  · refine ⟨Y, hodd, fun x => ⟨fun hx => ⟨hx, ?_⟩, fun h => h.1⟩⟩
    exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard Y hx)
  · have heven : Even (Nat.card ↥Y) := Nat.not_odd_iff_even.mp hodd
    have hmin : (Nat.card ↥Y).minFac = 2 :=
      (Nat.minFac_eq_two_iff _).mpr (even_iff_two_dvd.mp heven)
    obtain ⟨Sy⟩ := (inferInstance : Nonempty (Sylow 2 ↥Y))
    obtain ⟨Kc, hKn, hcomp⟩ :
        ∃ Kc : Subgroup ↥Y, Kc.Normal ∧ Kc.IsComplement' (Sy : Subgroup ↥Y) :=
      ⟨_, MonoidHom.normal_ker _, IsCyclic.isComplement' hmin (hcyc Sy)⟩
    haveI : Kc.Normal := hKn
    have hKodd : Odd (Nat.card Kc) := by
      rw [← hcomp.index_eq_card]
      exact Nat.not_even_iff_odd.mp
        (fun hevenIndex => Sy.not_dvd_index (even_iff_two_dvd.mp hevenIndex))
    have hcard : Nat.card (↥Y ⧸ Kc) = 2 ^ Nat.factorization (Nat.card ↥Y) 2 := by
      rw [← Subgroup.index_eq_card, hcomp.symm.index_eq_card]
      exact Sylow.card_eq_multiplicity Sy
    refine ⟨Kc.map Y.subtype, ?_, fun x => ⟨?_, ?_⟩⟩
    · rw [Subgroup.card_map_of_injective Y.subtype_injective]
      exact hKodd
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

theorem isCyclic_sylow_of_le [Finite G] {D C : Subgroup G} (hDC : D ≤ C)
    (hC : ∀ P : Sylow 2 ↥C, IsCyclic (P : Subgroup ↥C)) :
    ∀ P : Sylow 2 ↥D, IsCyclic (P : Subgroup ↥D) := by
  intro P
  have hinj : Function.Injective (Subgroup.inclusion hDC) := Subgroup.inclusion_injective hDC
  obtain ⟨Q, hle⟩ := (P.isPGroup'.map (Subgroup.inclusion hDC)).exists_le_sylow
  haveI : IsCyclic ↥(Q : Subgroup ↥C) := hC Q
  have hcyc' : IsCyclic ↥((P : Subgroup ↥D).map (Subgroup.inclusion hDC)) :=
    Subgroup.isCyclic_of_le hle
  exact isCyclic_of_surjective
    (Subgroup.equivMapOfInjective (P : Subgroup ↥D) (Subgroup.inclusion hDC) hinj).symm
    (MulEquiv.surjective _)

theorem exists_mul_of_mem_sup_of_commute {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let D : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        refine ⟨h * h', H.mul_mem hh hh', k * k', K.mul_mem hk hk', ?_⟩
        have hcomm : k * h' = h' * k := (hc h' hh' k hk).symm
        calc h * k * (h' * k') = h * (k * h') * k' := by simp only [mul_assoc]
          _ = h * (h' * k) * k' := by rw [hcomm]
          _ = h * h' * (k * k') := by simp only [mul_assoc]
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        calc (h * k)⁻¹ = k⁻¹ * h⁻¹ := by rw [mul_inv_rev]
          _ = h⁻¹ * k⁻¹ := (hc h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk)).symm }
  have hle : H ⊔ K ≤ D :=
    sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩)
      (fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩)
  exact hle hx

theorem mem_of_odd_orderOf_of_relIndex_le_two [Finite G] {N X : Subgroup G} (hNX : N ≤ X)
    (hI : N.relIndex X ≤ 2) {x : G} (hx : x ∈ X) (hodd : Odd (orderOf x)) : x ∈ N := by
  have hne : N.relIndex X ≠ 0 :=
    (inferInstance : (N.subgroupOf X).FiniteIndex).index_ne_zero
  have hn : ∀ m, 0 < m → m ≤ N.relIndex X → m ∣ 2 := by
    intro m _ hml
    have hm2 : m ≤ 2 := le_trans hml hI
    have hm12 : m = 1 ∨ m = 2 := by omega
    rcases hm12 with rfl | rfl <;> norm_num
  have hx2 : x ^ 2 ∈ N :=
    (Subgroup.mem_inf.mp
      (Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd (H := N) (K := X) hne hx hn)).1
  obtain ⟨k, hk⟩ := hodd
  have hxeq : x = (x ^ 2) ^ (k + 1) := by
    rw [← pow_mul]
    rw [show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [hxeq]
  exact pow_mem hx2 (k + 1)

end CFSG.OddStandard.SmallF3.Omega
