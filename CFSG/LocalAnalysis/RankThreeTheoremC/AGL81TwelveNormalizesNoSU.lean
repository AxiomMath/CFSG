module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeOTwoZOf
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveOneNormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

namespace TwelveNoSU

open CFSG.GH74.QTGen4.Leaves.F112 KFactProofs.SUThreeTwoShape in
theorem exists_cube_not_comm {X : Type} [Group X] (h : IsSymThreeOrSUThreeTwo X)
    (h3 : IsEmpty (X ≃* Equiv.Perm (Fin 3))) :
    ∃ a b : X, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b ≠ b * a := by
  rcases h with he | ⟨K, _, _, hK, ⟨e⟩⟩
  · exact (h3.false he.some).elim
  obtain ⟨ω, hω, h2⟩ := exists_omega hK
  let o : OmegaData K := ⟨ω, hω, h2⟩
  have hrel : Heis3Rel (OmegaData.sS o) (OmegaData.sD o) (sZ o) :=
    ⟨sZ_central o, sZ_cube o, OmegaData.sS_cube o, OmegaData.sD_cube o, sS_mul_sD o⟩
  refine ⟨e.symm (OmegaData.sS o), e.symm (OmegaData.sD o), ?_, ?_, fun hc => ?_⟩
  · rw [← map_pow, OmegaData.sS_cube, map_one]
  · rw [← map_pow, OmegaData.sD_cube, map_one]
  · refine hrel.S_mul_D_ne (sZ_ne_one o) (e.symm.injective ?_)
    rw [map_mul, map_mul, hc]

theorem not_forall_of_suThreeTwo {G : Type} [Group G] [Finite G] {I₀ L : Subgroup G}
    (hIL : I₀ ≤ L) (hsym : IsSymThreeOrSUThreeTwo (↥I₀ ⧸ CFSG.pCore 2 ↥I₀))
    (h3 : IsEmpty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* Equiv.Perm (Fin 3)))
    (h : ∀ x ∈ I₀, x ^ 3 = 1 → ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) : False := by
  set O := CFSG.pCore 2 ↥I₀
  set π := QuotientGroup.mk' O
  obtain ⟨a, b, ha, hb, hab⟩ := exists_cube_not_comm hsym h3
  obtain ⟨e, he⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I₀)).exists_card_eq
  have hlift : ∀ c : ↥I₀ ⧸ O, c ^ 3 = 1 →
      ∃ x : ↥I₀, (x : G) ^ 3 = 1 ∧ π x ^ (2 ^ e) = c := by
    intro c hc
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective O c
    have hx'O : x' ^ 3 ∈ O := by
      rw [← QuotientGroup.eq_one_iff, ← hc]
      rfl
    refine ⟨x' ^ (2 ^ e), ?_, ?_⟩
    · have h1 := pow_card_eq_one' (G := ↥O) (x := ⟨x' ^ 3, hx'O⟩)
      rw [he] at h1
      have h2 : (x' ^ 3) ^ (2 ^ e) = 1 := by simpa using congrArg Subtype.val h1
      rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, h2, Subgroup.coe_one]
    · have h4 : 2 ^ (e * 2) % 3 = 1 := by rw [pow_mul', Nat.pow_mod]; norm_num
      rw [map_pow, ← pow_mul, pow_eq_pow_mod _ hc, ← pow_two, ← pow_mul, h4, pow_one]
  have hcomm : ∀ x y : ↥I₀, (x : G) ^ 3 = 1 → π x * π y = π y * π x := by
    intro x y hx
    have hc : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 I₀ :=
      TenThreeOTwoZ.mem_pCoreOf_of_le hIL (x * y * x⁻¹ * y⁻¹).2 (h x x.2 hx y (hIL y.2))
    obtain ⟨c, hc', hcc⟩ := hc
    have hc1 : π c = 1 := (QuotientGroup.eq_one_iff _).mpr hc'
    have hceq : c = x * y * x⁻¹ * y⁻¹ := Subtype.ext (by simpa using hcc)
    rw [hceq, map_mul, map_mul, map_mul, map_inv, map_inv] at hc1
    have := congrArg (· * π y * π x) hc1
    simp only [one_mul, inv_mul_cancel_right, mul_assoc] at this
    rw [← this]
    group
  obtain ⟨x, hx3, hxa⟩ := hlift a ha
  obtain ⟨y, -, hyb⟩ := hlift b hb
  refine hab ?_
  rw [← hxa, ← hyb]
  exact ((Commute.pow_pow (hcomm x y hx3) (2 ^ e) (2 ^ e)) : _)

theorem false_of_forall_commutator_mem {G : Type} [Group G] [Finite G] {H L I₀ : Subgroup G}
    (hI₀ : I₀ ∈ cZero (H ⊓ L)) (h3 : 3 ∣ Nat.card (CFSG.ComponentClassification.AS76b.oUpperTwo I₀))
    (key : ∀ x ∈ CFSG.ComponentClassification.AS76b.oUpperTwo I₀, (∃ k : ℕ, x ^ 3 ^ k = 1) →
      ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) : False := by
  have hI₀' : IsCZeroMember (H ⊓ L) I₀ := hI₀
  have hI₀L : I₀ ≤ L := hI₀'.le.trans inf_le_right
  have hO2 : ∀ x ∈ I₀, ∀ k : ℕ, x ^ 3 ^ k = 1 →
      x ∈ CFSG.ComponentClassification.AS76b.oUpperTwo I₀ := fun x hx k hk =>
    Subgroup.subset_closure ⟨hx, Odd.of_dvd_nat (Odd.pow (by decide : Odd 3))
      (orderOf_dvd_of_pow_eq_one hk)⟩
  rcases hI₀'.shape with hperf | ⟨-, hsym⟩
  · exact not_three_dvd_card_of_perfect hI₀L hperf.perfect
      (fun x hx ⟨k, hk⟩ => key x (hO2 x hx k hk) ⟨k, hk⟩)
      (h3.trans (Subgroup.card_dvd_of_le (oUpperTwo_le_self I₀)))
  by_cases hs3 : Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* Equiv.Perm (Fin 3))
  · obtain ⟨e⟩ := hs3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hx' : orderOf (x : G) = 3 := by rwa [Subgroup.orderOf_coe]
    have hx3 : (x : G) ^ 3 ^ 1 = 1 := by rw [pow_one, ← hx', pow_orderOf_eq_one]
    have hxI : (x : G) ∈ I₀ := oUpperTwo_le_self I₀ x.2
    have hO := TenThreeOTwoZ.mem_pCoreOf_of_symThree hI₀L e hxI (key x x.2 ⟨1, hx3⟩)
    obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 _ ⟨(x : G), hO⟩
    have hm' : (x : G) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hdvd : 3 ∣ 2 ^ m := hx' ▸ orderOf_dvd_of_pow_eq_one hm'
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by decide)
  · exact not_forall_of_suThreeTwo hI₀L hsym (not_nonempty_iff.mp hs3)
      fun x hx hx3 => key x (hO2 x hx 1 (by rwa [pow_one])) ⟨1, by rwa [pow_one]⟩

end TwelveNoSU

variable {G : Type} [Group G] [Finite G]

theorem agl81TwelveNormalizes_of_tenThreeOne (h1031 : AGL81TenThreeOneAt G) :
    AGL81TwelveNormalizes G := by
  intro hS P M H Q K b L hc
  obtain ⟨hd, -, -, -, ⟨hbHM, hbX, -, -, -⟩, hL, I₀, hI₀, hI₀K⟩ := hc
  have hI₀' : IsCZeroMember (H ⊓ L) I₀ := hI₀
  rw [Subgroup.zpowers_le]
  by_contra hbL
  have hI₀L : I₀ ≤ L := hI₀'.le.trans inf_le_right
  exact TwelveNoSU.false_of_forall_commutator_mem hI₀ (h1031 hS 3 P M H Q K hd L hL I₀ hI₀)
    fun x hx ⟨k, hk⟩ =>
      commutator_mem_pCoreOf_of_not_mem_normalizer hL.toIsTwoPrimeComponent hbHM.2 hbX hbL
        (hI₀L (oUpperTwo_le_self I₀ hx)) (hI₀K hx) hk

end CFSG.LocalAnalysis.RankThreeTheoremC
