module

public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.CoverBound
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LieType.Steinberg.RankTwo.G2Extras
public import CFSG.LieType.Steinberg.RankTwo.G2Comm

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open Subgroup

namespace CFSG.LieType.Steinberg.CentralExt.G2Four

theorem isPGroup_two_ker_of_forall_odd_prime {H : Type*} [Group H]
    (htriv : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∀ (P : Type) [Group P] [Finite P] [Group.IsPerfect P]
      (η : P →* H), Function.Surjective η → η.ker ≤ center P → IsPGroup ℓ η.ker → η.ker = ⊥)
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
  have h0 := htriv ℓ hℓ hℓ2 (E ⧸ N) π₁ hπ₁ hker₁ hp₁
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

section G2

variable {K : Type} [Field K]

theorem g2_exists_section_of_coprime [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (E : Type)
    [Group E] [Finite E] (π : E →* adjointGroup .G2 K) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (hC : p.Coprime (Nat.card π.ker)) :
    ∃ σ : adjointGroup .G2 K →* E, ∀ g, π (σ g) = g := by
  obtain ⟨-, ⟨O⟩, -, -⟩ :=
    RankTwo.g2_conclusionB_of_comm fun O => RankTwo.g2_exists_commutatorFormula K O
  obtain ⟨C, -, hC'⟩ := RankTwo.g2_exists_commutatorFormula K O
  exact FieldFour.exists_section_of_coprime (g2_isCTGroupDatum K) (g2_steinbergExtras K)
    (RankTwo.g2_chevalleyExtras K O C hC') E π hπ hcen hC

theorem g2_four_exists_section_of_odd (hK : Nat.card K = 4) (E : Type) [Group E] [Finite E]
    (π : E →* adjointGroup .G2 K) (hπ : Function.Surjective π) (hcen : π.ker ≤ center E)
    (hodd : Odd (Nat.card π.ker)) : ∃ σ : adjointGroup .G2 K →* E, ∀ g, π (σ g) = g := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 2) (by norm_num) (by rw [hK]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact g2_exists_section_of_coprime E π hπ hcen (Nat.coprime_two_left.2 hodd)

theorem g2_four_ker_eq_bot_of_odd_prime (hK : Nat.card K = 4) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (P : Type) [Group P] [Finite P] [Group.IsPerfect P]
    (η : P →* adjointGroup .G2 K) (hη : Function.Surjective η) (hC : η.ker ≤ center P)
    (hp : IsPGroup ℓ η.ker) : η.ker = ⊥ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  have hodd : Odd (Nat.card η.ker) := by
    rw [hn]
    exact (hℓ.eq_two_or_odd'.resolve_left hℓ2).pow
  obtain ⟨σ, hσ⟩ := g2_four_exists_section_of_odd hK P η hη hC hodd
  exact SL2Closed.ker_eq_bot_of_section η hC σ hσ

theorem g2_four_card_ker_le_two (hK : Nat.card K = 4) {E : Type}
    [Group E] [Finite E] [Group.IsPerfect E] (η : E →* adjointGroup .G2 K)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) : Nat.card η.ker ≤ 2 :=
  CFSG.EvenSmallLie.GTwoFour.card_ker_le_two K hK η hη hC
    (isPGroup_two_ker_of_forall_odd_prime (fun _ hℓ hℓ2 P _ _ _ η' hη' hC' hp =>
      g2_four_ker_eq_bot_of_odd_prime hK hℓ hℓ2 P η' hη' hC' hp) η hη hC)

theorem g2_four_card_griessHopfMultiplier_le
    (hK : Nat.card K = 4) : Group.IsPerfect ↥(adjointGroup .G2 K) ∧
      Nat.card (CFSG.Open.griessHopfMultiplier ↥(adjointGroup .G2 K)) ≤ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hperf : Group.IsPerfect ↥(adjointGroup .G2 K) := isPerfect_g2_of_three_le_card K (by omega)
  refine ⟨hperf, ?_⟩
  have : Finite (CFSG.RankThree.PerfectCover.HopfCover ↥(adjointGroup .G2 K)) :=
    CFSG.RankThree.PerfectCover.finite_hopfCover hperf
  have : Group.IsPerfect (CFSG.RankThree.PerfectCover.HopfCover ↥(adjointGroup .G2 K)) :=
    CFSG.RankThree.PerfectCover.hopfCover_isPerfect
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv]
  exact g2_four_card_ker_le_two hK _ CFSG.RankThree.PerfectCover.hopfCoverMap_surjective
    CFSG.RankThree.PerfectCover.hopfMultiplier_le_center

theorem g2_four_hopfMultiplier (hK : Nat.card K = 4) :
    commutator (AdjointQuotient .G2 K) = ⊤ ∧
      Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 K)) ≤ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨hperf, hle⟩ := g2_four_card_griessHopfMultiplier_le hK
  have : Group.IsPerfect (AdjointQuotient .G2 K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  let e : AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot
  rw [Nat.card_congr (griessHopfMultiplierCongr e).toEquiv]
  exact hle

end G2

end CFSG.LieType.Steinberg.CentralExt.G2Four
