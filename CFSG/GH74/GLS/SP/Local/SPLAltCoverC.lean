module

public import CFSG.GH74.GLS.SP.Local.SPLAltCoverB
public import CFSG.GH74.Uniqueness.SU.SU13TA1Invol

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.Uniqueness.SU.SU13.TA

theorem altCover_two_pow_succ_dvd_normalizer {X : Type} [Group X] [Finite X] {L : Subgroup X} {z : X}
    (hz : z ∈ normalizer (L : Set X)) (hzL : z ∉ L) (hz2 : z * z = 1) {k : ℕ}
    (hk : 2 ^ k ∣ Nat.card ↥L) : 2 ^ (k + 1) ∣ Nat.card ↥(normalizer (L : Set X)) := by
  have hLM : L ≤ normalizer (L : Set X) := Subgroup.le_normalizer
  have hNcard : Nat.card ↥(L.subgroupOf (normalizer (L : Set X))) = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (L.subgroupOf (normalizer (L : Set X)))
  let x : ↥(normalizer (L : Set X)) := ⟨z, hz⟩
  have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa [sq] using hz2)
  have hx1 : (x : ↥(normalizer (L : Set X)) ⧸ L.subgroupOf (normalizer (L : Set X))) ≠ 1 := by
    intro h
    exact hzL (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff x).mp h))
  have hord : orderOf (x : ↥(normalizer (L : Set X)) ⧸ L.subgroupOf (normalizer (L : Set X))) = 2 :=
    orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hx2]; rfl) hx1
  have h2 : 2 ∣ Nat.card (↥(normalizer (L : Set X)) ⧸ L.subgroupOf (normalizer (L : Set X))) :=
    hord ▸ orderOf_dvd_natCard _
  rw [hmul, hNcard, pow_succ']
  exact mul_dvd_mul h2 hk

theorem altCover_mem_normalizer_of_sq_eq_one {X : Type} [Group X] {L : Subgroup X} {z : X} (hz2 : z * z = 1)
    (hst : ∀ x ∈ L, z * x * z⁻¹ ∈ L) : z ∈ normalizer (L : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hst h, fun hh => ?_⟩
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have h2 := hst _ hh
  have h3 : z * (z * h * z⁻¹) * z⁻¹ = h := by
    rw [hz]
    calc z * (z * h * z) * z = (z * z) * h * (z * z) := by group
      _ = h := by rw [hz2]; group
  rwa [h3] at h2

theorem altCover_card_facts {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11) :
    n.factorial / 2 ∣ 19958400 ∧ 2 ^ 7 ∣ n.factorial / 2 * 2 := by
  have h : n ∈ Finset.Icc 8 11 := Finset.mem_Icc.mpr ⟨hn8, hn11⟩
  revert h
  decide +revert

theorem altCover_factorial_mul_dvd {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11) :
    (n - 8).factorial * 384 ∣ 2304 := by
  have h : n ∈ Finset.Icc 8 11 := Finset.mem_Icc.mpr ⟨hn8, hn11⟩
  revert h
  decide +revert

theorem altCover_card_alternatingGroup {n : ℕ} (hn : 2 ≤ n) :
    Nat.card ↥(alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem altCover_card_centralizer_cycleType {n : ℕ} (ρ : Equiv.Perm (Fin n))
    (hρ : ρ.cycleType = {2, 2, 2, 2}) :
    Nat.card ↥(centralizer ({ρ} : Set (Equiv.Perm (Fin n)))) = (n - 8).factorial * 384 := by
  rw [Equiv.Perm.nat_card_centralizer, hρ]
  have h1 : ({2, 2, 2, 2} : Multiset ℕ).sum = 8 := by decide
  have h2 : ({2, 2, 2, 2} : Multiset ℕ).prod = 16 := by decide
  have h3 : ({2, 2, 2, 2} : Multiset ℕ).toFinset = {2} := by decide
  have h4 : Multiset.count 2 ({2, 2, 2, 2} : Multiset ℕ) = 4 := by decide
  rw [Fintype.card_fin, h1, h2, h3, Finset.prod_singleton, h4]
  norm_num [Nat.factorial]
  ring

theorem altCover_false_of_not_mem {X : Type} [Group X] [Finite X] {z t : X} {A T₁ L : Subgroup X}
    {n : ℕ} (ctx : XCtx X z t A T₁) (hL : StableL z A L) (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hD : IsDoubleCoverOfAlt ↥L n) (hzL : z ∉ L) : False := by
  obtain ⟨π, hπ⟩ := TwoCover.exists_of_isTwoAlt (H := ↥L) ⟨hD.1, inferInstance, hD.2.1, hD.2.2⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hAZ⟩ := ctx.altCover_A_facts
  obtain ⟨hdvdN, h2pow⟩ := altCover_card_facts hn8 hn11
  have hAdvd : Nat.card ↥A ∣ 19958400 := by
    have h := altCover_card_dvd_of_ker_le_center hL.A_le hAZ π hπ.ker_le_center
    rw [altCover_card_alternatingGroup (by omega)] at h
    exact h.trans hdvdN
  have hLcard : Nat.card ↥L = Nat.card ↥(alternatingGroup (Fin n)) * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L), hD.2.1,
      Nat.card_congr hD.2.2.some.toEquiv]
  have h27 : 2 ^ 7 ∣ Nat.card ↥L := by
    rw [hLcard, altCover_card_alternatingGroup (by omega)]
    exact h2pow
  have hz2 := ctx.z_sq
  have hzN : z ∈ normalizer (L : Set X) := altCover_mem_normalizer_of_sq_eq_one hz2 hL.stable
  have h28 := altCover_two_pow_succ_dvd_normalizer hzN hzL hz2 h27
  obtain ⟨P, hP, hPcard⟩ := altCover_exists_twoSubgroup_of_pow_dvd _ h28
  have := ctx.altCover_card_le_one_two_eight hAdvd hP
  norm_num at hPcard
  omega

theorem altCover_false_of_mem {X : Type} [Group X] [Finite X] {z : X} {A L : Subgroup X} {n : ℕ}
    (hn8 : 8 ≤ n) (hn11 : n ≤ 11) {π : ↥L →* alternatingGroup (Fin n)} (hπ : TwoCover π)
    (hAL : A ≤ L) (hAZ : center ↥A = ⊥) (hAcen : ∀ a ∈ A, z * a = a * z) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hzL : z ∈ L) (hmove : ∃ x ∈ L, z * x ≠ x * z) {q : ℕ} (hqodd : Odd q)
    (hq5 : 5 ≤ q) (hAcard : Nat.card ↥A = q * (q ^ 2 - 1) / 2) : False := by
  let zL : ↥L := ⟨z, hzL⟩
  have hzL2 : zL ^ 2 = 1 := Subtype.ext (by simpa [sq] using hz2)
  have hzL1 : zL ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzker : zL ∉ π.ker := by
    intro hk
    obtain ⟨x, hxL, hx⟩ := hmove
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp (hπ.ker_le_center hk) ⟨x, hxL⟩)
    exact hx h2.symm
  have hcyc := hπ.cycleType_of_orderOf_eq_two hn8 hn11 (orderOf_eq_prime hzL2 hzL1) hzker
  let ρ : Equiv.Perm (Fin n) := ((π zL : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
  let ψ : ↥A →* Equiv.Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp (π.comp (Subgroup.inclusion hAL))
  have hψc : ∀ a : ↥A, ψ a ∈ centralizer ({ρ} : Set (Equiv.Perm (Fin n))) := by
    intro a
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : Subgroup.inclusion hAL a * zL = zL * Subgroup.inclusion hAL a :=
      Subtype.ext (hAcen a a.2).symm
    have h := congrArg (fun y => ((π y : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))) hcomm
    simpa [map_mul, ψ, ρ] using h
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : π (Subgroup.inclusion hAL a) = 1 := Subtype.ext ha
    have h2 : Subgroup.inclusion hAL a ∈ π.ker := h1
    exact Subtype.ext (altCover_eq_one_of_mem_center hAL hAZ a.2 (hπ.ker_le_center h2))
  have hinj : Function.Injective (ψ.codRestrict _ hψc) := by
    intro a b h
    have h' := congrArg Subtype.val h
    exact hψinj h'
  have hdvd : Nat.card ↥A ∣ Nat.card ↥(centralizer ({ρ} : Set (Equiv.Perm (Fin n)))) :=
    Subgroup.card_dvd_of_injective (ψ.codRestrict _ hψc) hinj
  rw [hAcard, altCover_card_centralizer_cycleType ρ hcyc] at hdvd
  exact altCover_l2Order_not_dvd hqodd hq5 (hdvd.trans (altCover_factorial_mul_dvd hn8 hn11))

end CFSG.GH74.GLS.SP.Local
