module

public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.GriessGeneral
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open Subgroup

namespace CFSG.LieType.Steinberg.CentralExt.F4Two

theorem isPGroup_two_ker_of_odd_split {H : Type*} [Group H]
    (hsplit : ∀ (P : Type) [Group P] [Finite P] (η : P →* H), Function.Surjective η →
      η.ker ≤ center P → Odd (Nat.card η.ker) → ∃ σ : H →* P, ∀ g, η (σ g) = g)
    {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* H)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center E) : IsPGroup 2 π.ker := by
  refine IsPGroup.of_card
    (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {ℓ} hℓ hdvd => ?_)
  by_contra hℓ2
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set N := CoprimeSplit.copPart ℓ π.ker hcen
  have hNker : N ≤ π.ker := fun _ h => h.1
  let π₁ : E ⧸ N →* H := QuotientGroup.lift N π hNker
  have hπ₁e : ∀ e : E, π₁ (e : E ⧸ N) = π e := fun e => rfl
  have hπ₁ : Function.Surjective π₁ := fun g => by
    obtain ⟨e, rfl⟩ := hπ g
    exact ⟨(e : E ⧸ N), rfl⟩
  have hker₁ : π₁.ker ≤ center (E ⧸ N) := by
    intro y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπ₁e]
      exact hy
    rw [mem_center_iff]
    intro z
    obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 (hcen he) z']
  have hp₁ : IsPGroup ℓ π₁.ker := by
    rintro ⟨y, hy⟩
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective y
    have he : e ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπ₁e]
      exact hy
    obtain ⟨a, ha⟩ := CoprimeSplit.exists_pow_prime_pow_mem_copPart (p := ℓ) hcen he
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  have : Group.IsPerfect (E ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hodd : Odd (Nat.card π₁.ker) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp₁
    rw [hn]
    exact (hℓ.eq_two_or_odd'.resolve_left hℓ2).pow
  obtain ⟨σ, hσ⟩ := hsplit (E ⧸ N) π₁ hπ₁ hker₁ hodd
  have h0 := SL2Closed.ker_eq_bot_of_section π₁ hker₁ σ hσ
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hgN : (g : E) ∈ N := by
    have hmem : ((g : E) : E ⧸ N) ∈ π₁.ker := by
      rw [MonoidHom.mem_ker, hπ₁e]
      exact g.2
    rw [h0, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  have hcop := hgN.2
  rw [Subgroup.orderOf_coe, hg] at hcop
  exact hℓ.one_lt.ne' ((Nat.coprime_self ℓ).1 hcop)

section F4

variable {K : Type} [Field K]

theorem f4_exists_section_of_coprime [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (E : Type)
    [Group E] [Finite E] (π : E →* adjointGroup .F4 K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (hC : p.Coprime (Nat.card π.ker)) :
    ∃ σ : adjointGroup .F4 K →* E, ∀ g, π (σ g) = g := by
  obtain ⟨-, ⟨O⟩, -, -⟩ := f4_conclusionB K
  obtain ⟨C, -, hC'⟩ := f4_commutatorFormula K O
  exact FieldFour.exists_section_of_coprime (f4_isCTGroupDatum K) (f4_steinbergExtras K)
    (f4_chevalleyExtras K O C hC') E π hπ hcen hC

theorem f4_two_exists_section_of_odd (hK : Nat.card K = 2) (E : Type) [Group E] [Finite E]
    (π : E →* adjointGroup .F4 K) (hπ : Function.Surjective π) (hcen : π.ker ≤ center E)
    (hodd : Odd (Nat.card π.ker)) : ∃ σ : adjointGroup .F4 K →* E, ∀ g, π (σ g) = g := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl (by rw [hK, pow_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact f4_exists_section_of_coprime E π hπ hcen (Nat.coprime_two_left.2 hodd)

theorem f4_two_card_ker_le_two (hK : Nat.card K = 2) {E : Type} [Group E] [Finite E]
    [Group.IsPerfect E] (η : E →* adjointGroup .F4 K) (hη : Function.Surjective η)
    (hC : η.ker ≤ center E) : Nat.card η.ker ≤ 2 :=
  CFSG.EvenSmallLie.FFourTwo.General.card_ker_le_two hK η hη hC
    (isPGroup_two_ker_of_odd_split (fun P _ _ η' hη' hC' hodd =>
      f4_two_exists_section_of_odd hK P η' hη' hC' hodd) η hη hC)

theorem f4_two_card_griessHopfMultiplier_le (hK : Nat.card K = 2) :
    Group.IsPerfect ↥(adjointGroup .F4 K) ∧
      Nat.card (CFSG.Open.griessHopfMultiplier ↥(adjointGroup .F4 K)) ≤ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hperf : Group.IsPerfect ↥(adjointGroup .F4 K) := isPerfect_f4 K
  refine ⟨hperf, ?_⟩
  have : Finite (CFSG.RankThree.PerfectCover.HopfCover ↥(adjointGroup .F4 K)) :=
    CFSG.RankThree.PerfectCover.finite_hopfCover hperf
  have : Group.IsPerfect (CFSG.RankThree.PerfectCover.HopfCover ↥(adjointGroup .F4 K)) :=
    CFSG.RankThree.PerfectCover.hopfCover_isPerfect
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv]
  exact f4_two_card_ker_le_two hK _ CFSG.RankThree.PerfectCover.hopfCoverMap_surjective
    CFSG.RankThree.PerfectCover.hopfMultiplier_le_center

theorem f4_two_hopfMultiplier (hK : Nat.card K = 2) :
    commutator (AdjointQuotient .F4 K) = ⊤ ∧
      Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) ≤ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨hperf, hle⟩ := f4_two_card_griessHopfMultiplier_le hK
  have : Group.IsPerfect (AdjointQuotient .F4 K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  let e : AdjointQuotient .F4 K ≃* ↥(adjointGroup .F4 K) :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot
  rw [Nat.card_congr (griessHopfMultiplierCongr e).toEquiv]
  exact hle

end F4

end CFSG.LieType.Steinberg.CentralExt.F4Two
