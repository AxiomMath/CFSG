module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModel

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private theorem ds_odd_card_oddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem sec8t84_sylow_model {G : Type} [Group G] [Finite G] {L P : Subgroup G} (hL : IsOm6M L)
    (hP : IsSylow2Of P L) :
    Nat.card ↥P = 2 ^ 7 ∧ ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V)
      (_ : FiniteDimensional (ZMod 3) V) (Q : QuadraticForm (ZMod 3) V)
      (hQ : Q.Nondegenerate), Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 ∧
        ∃ P' : Subgroup (ProjOrth Q), IsSylow2Of P' (omegaProj hQ) ∧ Nonempty (↥P ≃* ↥P') := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hsgn, ⟨e⟩⟩ := ff_isOmegaStar_center_six_minus hL
  letI := i1
  letI := i2
  letI := i3
  let π : ↥L →* ↥(omegaProj hQ) := e.toMonoidHom.comp (QuotientGroup.mk' (center ↥L))
  let ψ : ↥P →* ↥(omegaProj hQ) := π.comp (Subgroup.inclusion hP.1)
  let PM : Subgroup ↥(omegaProj hQ) := ψ.range
  let P' : Subgroup (ProjOrth Q) := PM.map (omegaProj hQ).subtype
  have hZ : center ↥L = oddCore ↥L := ff_center_eq_oddCore_six_minus hL
  have hZodd : Odd (Nat.card (center ↥L)) := by
    rw [hZ]
    exact ds_odd_card_oddCore ↥L
  have hctr : Nat.card (↥L ⧸ center ↥L) = 3265920 := by
    have h := ctrQ_of_u43 (G := G) (Y := L) hL.1 hL.2
    unfold ctrQ at h
    exact h
  have hidx : (center ↥L).index = 3265920 := by
    rw [Subgroup.index_eq_card]
    exact hctr
  have hLcard : Nat.card ↥L = Nat.card (center ↥L) * 3265920 := by
    rw [← Subgroup.card_mul_index (H := center ↥L), hidx]
  have hcardPL : Nat.card ↥(P.subgroupOf L) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv
  have hmul : Nat.card ↥P * P.relIndex L = Nat.card ↥L := by
    have h := Subgroup.card_mul_index (H := P.subgroupOf L)
    rw [hcardPL] at h
    exact h
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥P)).mp hP.2.1
  have hrel_ne : P.relIndex L ≠ 0 := by
    intro h0
    apply hP.2.2
    rw [h0]
    exact dvd_zero 2
  have hZne : Nat.card (center ↥L) ≠ 0 := by
    haveI : Nonempty ↥(center ↥L) := ⟨⟨1, (center ↥L).one_mem⟩⟩
    exact (Nat.card_pos (α := ↥(center ↥L))).ne'
  have hprod_ne : Nat.card (center ↥L) * 25515 ≠ 0 :=
    Nat.mul_ne_zero hZne (by norm_num)
  have hprod_not_two : ¬ 2 ∣ Nat.card (center ↥L) * 25515 := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h1 | h2
    · exact hZodd.not_two_dvd_nat h1
    · exact (by norm_num : ¬ 2 ∣ (25515 : ℕ)) h2
  have hprod_val : padicValNat 2 (Nat.card (center ↥L) * 25515) = 0 :=
    padicValNat.eq_zero_of_not_dvd hprod_not_two
  have hn_eq : n = 7 := by
    have heq : 2 ^ n * P.relIndex L = 2 ^ 7 * (Nat.card (center ↥L) * 25515) := by
      rw [← hn, hmul, hLcard]
      ring
    have hpad := congrArg (padicValNat 2) heq
    rw [padicValNat_base_pow_mul (p := 2) (n := P.relIndex L) (by norm_num : 1 < 2) hrel_ne n,
      padicValNat_base_pow_mul (p := 2) (n := Nat.card (center ↥L) * 25515)
        (by norm_num : 1 < 2) hprod_ne 7,
      padicValNat.eq_zero_of_not_dvd hP.2.2, hprod_val] at hpad
    omega
  have hcard : Nat.card ↥P = 2 ^ 7 := by
    rw [hn, hn_eq]
  have hψker : ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    have hx' : e ((QuotientGroup.mk' (center ↥L)) (Subgroup.inclusion hP.1 x)) = 1 := hx
    have h2 : (QuotientGroup.mk' (center ↥L)) (Subgroup.inclusion hP.1 x) = 1 :=
      e.injective (by rw [hx', map_one])
    have hyCenter : Subgroup.inclusion hP.1 x ∈ center ↥L := by
      have hk : Subgroup.inclusion hP.1 x ∈ (QuotientGroup.mk' (center ↥L)).ker :=
        MonoidHom.mem_ker.mpr h2
      rwa [QuotientGroup.ker_mk'] at hk
    have hyOdd : Subgroup.inclusion hP.1 x ∈ oddCore ↥L := by
      rw [← hZ]
      exact hyCenter
    have hyPL : Subgroup.inclusion hP.1 x ∈ P.subgroupOf L := x.2
    have hcardP : Nat.card (P.subgroupOf L) = 2 ^ n := by
      rw [hcardPL, hn]
    have hdvdP : orderOf (Subgroup.inclusion hP.1 x) ∣ Nat.card (P.subgroupOf L) :=
      Subgroup.orderOf_dvd_natCard (P.subgroupOf L) hyPL
    have hdvdO : orderOf (Subgroup.inclusion hP.1 x) ∣ Nat.card (oddCore ↥L) :=
      Subgroup.orderOf_dvd_natCard (oddCore ↥L) hyOdd
    have hcop : Nat.Coprime (Nat.card (P.subgroupOf L)) (Nat.card (oddCore ↥L)) := by
      rw [hcardP]
      exact (Nat.coprime_two_left.mpr (ds_odd_card_oddCore ↥L)).pow_left n
    have hy1 : Subgroup.inclusion hP.1 x = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvdP hdvdO)
    exact Subtype.ext (by simpa using congrArg (fun z : ↥L => (z : G)) hy1)
  have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hψker
  have eψ : ↥P ≃* PM := MonoidHom.ofInjective hψinj
  have hPM2 : IsPGroup 2 PM := hP.2.1.of_equiv eψ
  have hP'2 : IsPGroup 2 P' := hPM2.map (omegaProj hQ).subtype
  have hP'le : P' ≤ omegaProj hQ := Subgroup.map_subtype_le (H := omegaProj hQ) PM
  have hPMcard : Nat.card PM = Nat.card ↥P := Nat.card_congr eψ.toEquiv.symm
  have hXcard : Nat.card ↥(omegaProj hQ) = 3265920 :=
    (Nat.card_congr e.toEquiv).symm.trans hctr
  have hPMindex : PM.index = 25515 := by
    have h := Subgroup.card_mul_index PM
    rw [hXcard, hPMcard, hcard] at h
    have h2 : 2 ^ 7 * PM.index = 2 ^ 7 * 25515 := by
      rw [h]
      norm_num
    exact Nat.mul_left_cancel (by norm_num : 0 < 2 ^ 7) h2
  have hsub : P'.subgroupOf (omegaProj hQ) = PM := by
    show (PM.map (omegaProj hQ).subtype).comap (omegaProj hQ).subtype = PM
    exact Subgroup.comap_map_eq_self_of_injective (f := (omegaProj hQ).subtype)
      (Subgroup.subtype_injective _) PM
  have hP'idx : ¬ 2 ∣ P'.relIndex (omegaProj hQ) := by
    show ¬ 2 ∣ (P'.subgroupOf (omegaProj hQ)).index
    rw [hsub, hPMindex]
    norm_num
  have ePM : PM ≃* P' :=
    Subgroup.equivMapOfInjective PM (omegaProj hQ).subtype (Subgroup.subtype_injective _)
  refine ⟨hcard, V, i1, i2, i3, Q, hQ, hdim, hsgn, P', ?_, ?_⟩
  · exact ⟨hP'le, hP'2, hP'idx⟩
  · exact ⟨eψ.trans ePM⟩

end CFSG.OddStandard.SmallF3.Omega
