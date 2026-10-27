module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Wreath

public section

namespace CFSG.EvenSporadicStandard.M24Std.GenX

open MulAction Subgroup CFSG.EvenSporadicStandard

variable {G : Type*} [Group G]

theorem even_card_fixed_neg' {H : Subgroup G} (φ : H →* ℤˣ) {z : G} (hz : z * z = 1)
    (hGz : ∀ ψ : G →* ℤˣ, ψ z = 1) [H.FiniteIndex] [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)] :
    Even (Finset.univ.filter fun q : G ⧸ H => z • q = q ∧
      valAt H φ q.out (z * q.out) = -1).card := by
  classical
  have h1 : φ.transfer z = 1 := hGz φ.transfer
  rw [transfer_involution_eq_prod φ hz] at h1
  have h2 : ∀ q : G ⧸ H, valAt H φ q.out (z * q.out) =
      if valAt H φ q.out (z * q.out) = -1 then -1 else 1 := by
    intro q
    rcases Int.units_eq_one_or (valAt H φ q.out (z * q.out)) with h | h <;> simp [h]
  rw [Finset.prod_congr rfl fun q _ => h2 q, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one, Finset.filter_filter] at h1
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have := (neg_one_pow_eq_one_iff_even hne).1 h1
  simpa [and_comm] using this

theorem even_nat_card_fixed_neg' {H : Subgroup G} (φ : H →* ℤˣ) {z : G} (hz : z * z = 1)
    (hGz : ∀ ψ : G →* ℤˣ, ψ z = 1) [H.FiniteIndex] [Finite G] :
    Even (Nat.card {q : G ⧸ H // z • q = q ∧ valAt H φ q.out (z * q.out) = -1}) := by
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite _
  have := even_card_fixed_neg' φ hz hGz
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact this

theorem odd_card_fixed [Finite G] {T : Subgroup G} {z : G} (hz : z * z = 1)
    (hTidx : ¬ 2 ∣ T.index) [Fintype (G ⧸ T)] [DecidableEq (G ⧸ T)] :
    Odd (Finset.univ.filter fun q : G ⧸ T => z • q = q).card := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (zpowers z) := by
    have hd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hmod := hp.card_modEq_card_fixedPoints (G ⧸ T)
  have hfix : Nat.card (fixedPoints (zpowers z) (G ⧸ T)) =
      (Finset.univ.filter fun q : G ⧸ T => z • q = q).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun q => ?_)
    rw [Finset.mem_filter, mem_fixedPoints]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h
      exact h ⟨z, mem_zpowers z⟩
    · rintro h ⟨g, hg⟩
      exact (zpowers_le.2 (show z ∈ MulAction.stabilizer G q from h)) hg
  rw [hfix, ← Subgroup.index_eq_card] at hmod
  rw [Nat.odd_iff]
  unfold Nat.ModEq at hmod
  omega

theorem exists_hom_neg [Finite G] {T U : Subgroup G} {z : G} (hz : z * z = 1)
    (hTidx : ¬ 2 ∣ T.index) (hU : U.relIndex T = 2) (hconj : ∀ g : G, g⁻¹ * z * g ∉ U) :
    ∃ ψ : G →* ℤˣ, ψ z = -1 := by
  classical
  obtain ⟨φ, hφ⟩ := exists_hom_of_index_two (U.subgroupOf T) hU
  let _ : Fintype (G ⧸ T) := Fintype.ofFinite _
  refine ⟨φ.transfer, ?_⟩
  rw [transfer_involution_eq_prod φ hz]
  have hval : ∀ q ∈ (Finset.univ.filter fun q : G ⧸ T => z • q = q),
      valAt T φ q.out (z * q.out) = -1 := by
    intro q hq
    have hq' : z • q = q := (Finset.mem_filter.1 hq).2
    have h1 := out_inv_mul_mem_of_smul_eq hq'
    rw [valAt_of_mem φ h1]
    refine (Int.units_eq_one_or _).resolve_left fun h => ?_
    have h2 := (hφ _).1 h
    rw [Subgroup.mem_subgroupOf] at h2
    exact hconj q.out (by rw [mul_assoc]; exact h2)
  rw [Finset.prod_congr rfl hval, Finset.prod_const]
  exact (odd_card_fixed hz hTidx).neg_one_pow

variable [Finite G]

theorem false_of_fusion_control' {z : G} (hGz : ∀ ψ : G →* ℤˣ, ψ z = 1) (hz : z * z = 1)
    (H : Subgroup G) (hzH : z ∈ H) (φ : H →* ℤˣ) (hφz : φ ⟨z, hzH⟩ = -1)
    (hfuse : ∀ y : H, φ y = -1 → (∃ g : G, g * z * g⁻¹ = y) → ∃ h ∈ H, h * z * h⁻¹ = y)
    (hodd : ¬ 2 ∣ H.relIndex (centralizer ({z} : Set G))) : False := by
  classical
  have hTL := even_nat_card_fixed_neg' φ hz hGz
  let C : Subgroup G := centralizer ({z} : Set G)
  let base : G ⧸ H := ((1 : G) : G ⧸ H)
  have hmkc : ∀ c : C, c • base = ((c : G) : G ⧸ H) := fun c => by
    rw [Subgroup.smul_def]
    show (c : G) • ((1 : G) : G ⧸ H) = _
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have hset : {q : G ⧸ H | z • q = q ∧ valAt H φ q.out (z * q.out) = -1} =
      MulAction.orbit C base := by
    ext q
    constructor
    · rintro ⟨hz1, hval⟩
      have h1 := out_inv_mul_mem_of_smul_eq hz1
      have hy : φ ⟨q.out⁻¹ * (z * q.out), h1⟩ = -1 := by
        rw [← valAt_of_mem φ h1]
        exact hval
      obtain ⟨h, hh, hhz⟩ := hfuse ⟨q.out⁻¹ * (z * q.out), h1⟩ hy
        ⟨q.out⁻¹, by simp [mul_assoc]⟩
      have hc : q.out * h ∈ C := by
        rw [mem_centralizer_singleton_iff]
        have : h * z * h⁻¹ = q.out⁻¹ * (z * q.out) := hhz
        calc q.out * h * z = q.out * (h * z * h⁻¹) * h := by group
          _ = q.out * (q.out⁻¹ * (z * q.out)) * h := by rw [this]
          _ = z * (q.out * h) := by group
      refine ⟨⟨q.out * h, hc⟩, ?_⟩
      show (⟨q.out * h, hc⟩ : C) • base = q
      rw [hmkc]
      show ((q.out * h : G) : G ⧸ H) = q
      calc ((q.out * h : G) : G ⧸ H) = ((q.out : G) : G ⧸ H) :=
            QuotientGroup.eq.2 (by simpa using H.inv_mem hh)
        _ = q := QuotientGroup.out_eq' q
    · rintro ⟨c', rfl⟩
      have hq : c' • base = ((c' : G) : G ⧸ H) := hmkc c'
      have hcz : (c' : G) * z = z * (c' : G) := mem_centralizer_singleton_iff.1 c'.2
      have hfz : z • ((c' : G) : G ⧸ H) = ((c' : G) : G ⧸ H) := by
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← hcz]
        exact QuotientGroup.eq.2 (by simpa using H.inv_mem hzH)
      refine ⟨?_, ?_⟩
      · show z • (c' • base) = c' • base
        rw [hq]
        exact hfz
      · show valAt H φ (c' • base).out (z * (c' • base).out) = -1
        rw [hq]
        have h1 := out_inv_mul_mem_of_smul_eq hfz
        rw [valAt_of_mem φ h1]
        have h2 : (↑(((c' : G) : G ⧸ H).out) : G ⧸ H) = ((c' : G) : G ⧸ H) :=
          QuotientGroup.out_eq' _
        have hm : (((c' : G) : G ⧸ H).out)⁻¹ * (c' : G) ∈ H := QuotientGroup.eq.mp h2
        have key : (⟨(((c' : G) : G ⧸ H).out)⁻¹ * (z * ((c' : G) : G ⧸ H).out), h1⟩ : H) =
            ⟨_, hm⟩ * ⟨z, hzH⟩ * (⟨_, hm⟩ : H)⁻¹ := by
          ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          have hcz' : (c' : G)⁻¹ * z * c' = z := by
            calc (c' : G)⁻¹ * z * c' = (c' : G)⁻¹ * (z * c') := by group
              _ = (c' : G)⁻¹ * (c' * z) := by rw [← hcz]
              _ = z := by group
          calc (((c' : G) : G ⧸ H).out)⁻¹ * (z * ((c' : G) : G ⧸ H).out)
              = ((((c' : G) : G ⧸ H).out)⁻¹ * c') * ((c' : G)⁻¹ * z * c') *
                ((((c' : G) : G ⧸ H).out)⁻¹ * c')⁻¹ := by group
            _ = _ := by rw [hcz']
        rw [key, map_mul, map_mul, map_inv, mul_comm (φ _) (φ _), mul_assoc, mul_inv_cancel,
          mul_one]
        exact hφz
  have hcard : Nat.card {q : G ⧸ H // z • q = q ∧ valAt H φ q.out (z * q.out) = -1} =
      H.relIndex C := by
    have h1 : Nat.card {q : G ⧸ H // z • q = q ∧ valAt H φ q.out (z * q.out) = -1} =
        Nat.card (MulAction.orbit C base) := by
      rw [← hset]
      rfl
    have hstab : MulAction.stabilizer C base = H.subgroupOf C := by
      ext c
      rw [MulAction.mem_stabilizer_iff, hmkc, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have := QuotientGroup.eq.mp h
        simpa using H.inv_mem this
      · intro h
        exact QuotientGroup.eq.2 (by simpa using H.inv_mem h)
    rw [h1, Nat.card_coe_set_eq, ← MulAction.index_stabilizer C base, hstab]
    rfl
  rw [hcard] at hTL
  exact hodd (even_iff_two_dvd.1 hTL)

end CFSG.EvenSporadicStandard.M24Std.GenX
