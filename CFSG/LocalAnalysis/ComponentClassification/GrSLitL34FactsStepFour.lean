module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitAction
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallS10
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.TBLitIntrinsicTypes

public section

namespace CFSG.ComponentClassification.TBLit.L34StepFour

open CFSG Subgroup
open scoped commutatorElement

theorem pPrimeCore_ne_top_of_isQuasisimple {N : Type*} [Group N]
    (h : IsQuasisimple (N ⧸ pPrimeCore 2 N)) : pPrimeCore 2 N ≠ ⊤ := by
  intro htop
  obtain ⟨u, v, huv⟩ := h.2.2
  apply huv
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center (N ⧸ pPrimeCore 2 N)) u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (center (N ⧸ pPrimeCore 2 N)) v
  have hsub : ∀ w : N ⧸ pPrimeCore 2 N, w = 1 := by
    intro w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 N) w
    exact (QuotientGroup.eq_one_iff w).mpr (htop ▸ mem_top w)
  rw [hsub u, hsub v]

theorem false_of_perfect_le_centralizer {X : Type} [Group X]
    [Finite X] {δ : X} {H N : Subgroup X}
    (htype : Blueprint.LieModel (H ⧸ Open.fusionZStar H) .PSL 3 2 2) (hδH : δ ∈ H)
    (hδ : δ * δ = 1) (hnt : ¬ ∀ h ∈ H, ⁅h, δ⁆ ∈ oddCoreIn H) (hNH : N ≤ H)
    (hNδ : N ≤ centralizer ({δ} : Set X)) (hNperf : ⁅N, N⁆ = N) (hN : pPrimeCore 2 ↥N ≠ ⊤) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel htype
  have hcent := (PSL3Four.facts_of_equiv_S.{0, 0} θ).2.1
  set π := QuotientGroup.mk' (Open.fusionZStar ↥H) with hπ
  set d : ↥H := ⟨δ, hδH⟩ with hd
  have hd1 : π d ≠ 1 := by
    intro h1
    apply hnt
    intro h hh
    have h2 := GSThmB.OddQuot.mem_fusionZStar_iff.mp ((QuotientGroup.eq_one_iff d).mp h1) ⟨h, hh⟩
    refine ⟨⁅d, ⟨h, hh⟩⁆⁻¹, inv_mem h2, ?_⟩
    rw [commutatorElement_inv, map_commutatorElement]
    rfl
  have hd2 : π d * π d = 1 := by
    rw [← map_mul, show d * d = 1 from Subtype.ext hδ, map_one]
  have hord : orderOf (π d) = 2 := orderOf_eq_prime (by rw [sq]; exact hd2) hd1
  set C := centralizer ({π d} : Set (↥H ⧸ Open.fusionZStar ↥H)) with hC
  have hC2 : IsPGroup 2 ↥C := IsPGroup.of_card (n := 6) (by rw [hcent _ hord]; norm_num)
  have hNperf' : ⁅N.subgroupOf H, N.subgroupOf H⁆ = N.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hNH, hNperf]
  set N' := (N.subgroupOf H).map π with hN'
  have hN'C : N' ≤ C := by
    rintro _ ⟨n, hn, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hNδ hn))
  have hN'perf : ⁅N', N'⁆ = N' := by rw [hN', ← map_commutator, hNperf']
  have hN'bot : N' = ⊥ := CatFactsSmall.eq_bot_of_perfect_of_isPGroup (hC2.to_le hN'C) hN'perf
  have hNZ : N.subgroupOf H ≤ Open.fusionZStar ↥H := by
    intro n hn
    have h1 : π n ∈ N' := mem_map_of_mem π hn
    rw [hN'bot, mem_bot] at h1
    exact (QuotientGroup.eq_one_iff n).mp h1
  have hNO : N.subgroupOf H ≤ pPrimeCore 2 ↥H := by
    rw [← hNperf', commutator_le]
    intro n₁ h₁ n₂ _
    exact GSThmB.OddQuot.mem_fusionZStar_iff.mp (hNZ h₁) n₂
  have hodd : Odd (Nat.card ↥N) := by
    have h1 : Nat.card ↥(N.subgroupOf H) ∣ Nat.card ↥(pPrimeCore 2 ↥H) :=
      Subgroup.card_dvd_of_le hNO
    rw [Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv] at h1
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h1
  exact hN (eq_top_iff.mpr (le_sSup ⟨inferInstance, by
    rw [card_top]
    exact Nat.coprime_two_left.mpr hodd⟩))

end CFSG.ComponentClassification.TBLit.L34StepFour
