module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryActionRankAlternatives
import CFSG.LocalAnalysis.RankThreeUC.Section5.SymmetryReduction
import CFSG.LocalAnalysis.RankThreeUC.Section5.SpecialBlocks
import CFSG.LocalAnalysis.RankThreeUC.Section5.FreeTranslatesSupport
import CFSG.LocalAnalysis.RankThreeUC.Section5.FreeTranslatesNumeric
import TauCeti.RepresentationTheory.Irreducible
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

theorem alphaPrimeInvolutionBound_holds :
    ∀ (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
      (ρ : Representation (ZMod 2) G V) (q : ℕ) (P' T B : Subgroup G) (e : ℕ),
      BinaryActionRankCounterexample G q P' T B e ρ →
      ¬ IsPrimePow (2 ^ e - 1) →
      (∀ s ∈ twoCoreCommutator T B, s ∈ Subgroup.normalizer ((⁅B, P'⁆ : Subgroup G) : Set G) →
        ∀ E ∈ Delta q P' ρ, E.map (MulAut.conj s).toMonoidHom = E) →
      (∀ s ∈ twoCoreCommutator T B, ∀ s' ∈ twoCoreCommutator T B,
        s * s' * s⁻¹ * s'⁻¹ ∈ Subgroup.normalizer ((⁅B, P'⁆ : Subgroup G) : Set G) ∧
          s * s ∈ Subgroup.normalizer ((⁅B, P'⁆ : Subgroup G) : Set G)) →
      (2 ^ e ≤ Nat.card (Delta q P' ρ) ∧ (Odd e → 4 ^ e ≤ Nat.card (Delta q P' ρ))) →
      ∀ t : G, orderOf t = 2 → t ∈ Subgroup.centralizer (P' : Set G) →
        ⁅CFSG.Open.pCoreOf q (⊤ : Subgroup G), Subgroup.zpowers t⁆ ≠ ⊥ →
        e + 1 < Module.finrank (ZMod 2) (V ⧸ CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ
          (Subgroup.zpowers t)) := by
  intro G _ _ V _ _ ρ q P' T B e hc hpp hker _hcomm hcard t ht htP hOt
  classical
  by_contra hle
  push Not at hle
  have hS := hc.oddPrimeClassTwoAction.setting
  haveI : Fact q.Prime := ⟨hS.prime⟩
  have hq2 : q ≠ 2 := by
    intro h
    have hodd := hS.odd
    rw [h] at hodd
    exact absurd hodd (by decide)
  haveI : FiniteDimensional (ZMod 2) V :=
    hc.faithfulBinaryIrreducibleAction.irreducible.finiteDimensional
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  obtain ⟨Q, hQn, hPQ, hQP, hQexp, hQcb, hQQP, hcenter, y₀, hy₀Q, hy₀⟩ :=
    SymmetryReduction.exists_special hc ht htP hOt
  set Γ : Set (Subgroup G) :=
    {D | D ∈ Delta q P' ρ ∧ ∃ y ∈ Q, y * t * y⁻¹ * t⁻¹ ∉ SpecialBlocks.radical Q D} with hΓdef
  have hΓ : Γ ⊆ Delta q P' ρ := fun D hD => hD.1
  have hblock : ∀ D ∈ Γ,
      1 ≤ Module.finrank (ZMod 2) ((fixedSubmodule ρ D).map (ρ t - 1)) ∧
        (5 ≤ q → 2 ≤ Module.finrank (ZMod 2) ((fixedSubmodule ρ D).map (ρ t - 1))) := by
    rintro D ⟨hDΔ, y, hy, hyD⟩
    exact SpecialBlocks.finrank_block hc hQn hQP hQexp hQQP ht2 htP hDΔ hy hyD
  have hk : Nat.card ↥Γ ≤ e + 1 := by
    have h1 := SpecialBlocks.card_mul_le hc htP hΓ (m := 1) fun D hD => (hblock D hD).1
    omega
  have hk5 : 5 ≤ q → 2 * Nat.card ↥Γ ≤ e + 1 := fun h5 => by
    have h2 := SpecialBlocks.card_mul_le hc htP hΓ (m := 2) fun D hD => (hblock D hD).2 h5
    omega
  have hpe : ¬ q ∣ 2 ^ e - 1 := by
    intro h
    apply (three_lt_pRank_and_prime_not_dvd_card_actor hc).2
    rw [hc.oddPrimeClassTwoAction.pi_eq]
    exact ⟨hS.prime, h⟩
  obtain ⟨r, hr, hre, hcount⟩ := FreeTranslates.exists_prime_mul_sq_lt
    hc.oddPrimeClassTwoAction.two_lt hpp hS.prime hq2 hpe hk hk5 hcard.1 hcard.2
  haveI : Fact r.Prime := ⟨hr⟩
  have hrB : r ∣ Nat.card B := by
    have h3 : r ∈ piOf B := by
      rw [hc.oddPrimeClassTwoAction.pi_eq]
      exact ⟨hr, hre⟩
    exact h3.2
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) r hrB
  have hb₀ord : orderOf (b₀ : G) = r := by rw [Subgroup.orderOf_coe]; exact hb₀
  have hB₀card : Nat.card ↥(Subgroup.zpowers (b₀ : G)) = r := by rw [Nat.card_zpowers, hb₀ord]
  have hB₀B : Subgroup.zpowers (b₀ : G) ≤ B := Subgroup.zpowers_le.2 b₀.2
  have hB₀ : Subgroup.zpowers (b₀ : G) ≠ ⊥ := by
    intro h
    have h4 : Nat.card ↥(Subgroup.zpowers (b₀ : G)) = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hB₀card] at h4
    exact hr.one_lt.ne' h4
  have hB₀p : IsPGroup r ↥(Subgroup.zpowers (b₀ : G)) :=
    IsPGroup.of_card (n := 1) (by rw [hB₀card, pow_one])
  have hrq : r ≠ q := fun h => hpe (h ▸ hre)
  have hfix : ∀ b ∈ Subgroup.zpowers (b₀ : G), b ≠ 1 → ∀ y ∈ Q, b * y * b⁻¹ * y⁻¹ ∈ P' → y ∈ P' := by
    intro b hb hb1 y hy hby
    exact SpecialBlocks.mem_of_commutator_mem hc hPQ hQexp (hB₀B hb) hb1 (hQcb b (hB₀B hb) hb1) hr hrq
      (hB₀p.to_le (Subgroup.zpowers_le.2 hb)) hy hby
  have hx : y₀ * t * y₀⁻¹ * t⁻¹ ∈ Q := by
    simpa [mul_assoc] using Q.mul_mem hy₀Q (hQn.conj_mem y₀⁻¹ (Q.inv_mem hy₀Q) t)
  apply hy₀
  refine FreeTranslates.mem_of_support_card_lt hc hker hB₀B hB₀ hQn hPQ hQQP hfix
    (SpecialBlocks.radical Q) (fun D _ => ?_) (fun D _ => SpecialBlocks.radical_le Q D)
    (fun g D _ => SpecialBlocks.map_radical hQn g D)
    (fun x hx hxR => SpecialBlocks.mem_of_forall_mem_radical hc hQQP hQP hcenter hx hxR)
    hΓ (by rw [hB₀card]; exact hcount) hx (fun D hD hDΓ => ?_)
  · intro u hu
    refine SpecialBlocks.mem_radical_of (hPQ hu) fun y hy => ?_
    have huy : u * y = y * u := Subgroup.mem_centralizer_iff.1 (hQP hy) u hu
    have h5 : u * y * u⁻¹ * y⁻¹ = 1 := by rw [huy]; group
    rw [h5]
    exact Subgroup.one_mem _
  · by_contra hno
    exact hDΓ ⟨hD, y₀, hy₀Q, hno⟩

end CFSG.LocalAnalysis.RankThreeUC.Section5
