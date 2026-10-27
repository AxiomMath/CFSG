module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.ThreeQuotient.Rank
public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofCensus194
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28.ThreeQuotient

open CFSG.Open Subgroup

theorem mem_normalizer_subgroupOf_iff {X : Type*} [Group X] {H K : Subgroup X} (hHK : H ≤ K)
    (s : K) : s ∈ Subgroup.normalizer ((H.subgroupOf K : Subgroup K) : Set K) ↔
      (s : X) ∈ Subgroup.normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    constructor
    · intro hx
      have := (h ⟨x, hHK hx⟩).1 (by simpa [Subgroup.mem_subgroupOf] using hx)
      simpa [Subgroup.mem_subgroupOf] using this
    · intro hx
      have hxK : x ∈ K := by
        have h1 : (s : X) * x * (s : X)⁻¹ ∈ K := hHK hx
        have h2 : (s : X)⁻¹ * ((s : X) * x * (s : X)⁻¹) * (s : X) ∈ K :=
          mul_mem (mul_mem (inv_mem s.2) h1) s.2
        simpa [mul_assoc] using h2
      have := (h ⟨x, hxK⟩).2 (by simpa [Subgroup.mem_subgroupOf] using hx)
      simpa [Subgroup.mem_subgroupOf] using this
  · intro h k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using h k

variable {X : Type} [Group X] [Finite X]

namespace ShapeData

variable {P Q₀ : Subgroup X}

theorem mem_normalizer (hD : ShapeData P Q₀) {g : X} (hg : g ∈ Subgroup.normalizer (P : Set X)) :
    g ∈ Subgroup.normalizer (Q₀ : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => hD.conj_mem hg ha, fun ha => ?_⟩
  have := hD.conj_mem (inv_mem hg) ha
  simpa [mul_assoc] using this

theorem not_dvd_card (S : Sylow 3 X) {Q₀ : Subgroup X} (hD : ShapeData (S : Subgroup X) Q₀) :
    ¬ 3 ^ 6 ∣ Nat.card X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := Sylow.card_eq_multiplicity S
  rw [hD.card] at h1
  have hfac : (Nat.card X).factorization 3 = 5 :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm
  intro h
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').1 h
  omega

end ShapeData

theorem false_of_le_alt (K : Subgroup X) {n : ℕ} (hn5 : 5 ≤ n)
    (e : K ≃* alternatingGroup (Fin n)) (S : Sylow 3 X) {Q₀ : Subgroup X}
    (hD : ShapeData (S : Subgroup X) Q₀) (hSK : (S : Subgroup X) ≤ K) : False := by
  by_cases h12 : 12 ≤ n
  · have h4 := CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof.four_le_pRank_alternatingGroup h12
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      CFSG.SectionRank.pRank_top_le_of_injective (by norm_num)
        (K.subtype.comp e.symm.toMonoidHom) (K.subtype_injective.comp e.symm.injective)
    have := hD.pRank_le_three S
    omega
  · haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hdvd : 3 ^ 5 ∣ Nat.card K := hD.card ▸ Subgroup.card_dvd_of_le hSK
    have hcard : Nat.card K = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
    have h2 : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
      have h2' := two_mul_nat_card_alternatingGroup (α := Fin n)
      rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm,
        Fintype.card_fin] at h2'
      exact h2'
    have h3 : 3 ^ 5 ∣ n.factorial := by
      rw [← h2, ← hcard]
      exact hdvd.mul_left 2
    have h11 : n.factorial ∣ (11 : ℕ).factorial := Nat.factorial_dvd_factorial (by omega)
    exact absurd (h3.trans h11) (by decide)

theorem sporOrd_eq_J3 (s : TauCeti.SporadicName) (h5 : 3 ^ 5 ∣ CFSG.AGLEmbedding.sporOrd s)
    (h6 : ¬ 3 ^ 6 ∣ CFSG.AGLEmbedding.sporOrd s) : s = .J3 := by
  revert h5 h6
  cases s <;> decide

section J3


theorem false_of_le_J3 (K : Subgroup X) (e : K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)
    (S : Sylow 3 X) {Q₀ : Subgroup X} (hD : ShapeData (S : Subgroup X) Q₀)
    (hSK : (S : Subgroup X) ≤ K) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF := CFSG.AGLEmbedding.kFactJ3Sylow K ⟨e⟩ (S.subtype hSK)
  obtain ⟨s, hsN, -, hs⟩ := hF.singer
  have hsX : (s : X) ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) :=
    (mem_normalizer_subgroupOf_iff hSK s).1 hsN
  have hs2X : ((s ^ 2 : K) : X) ∈ Subgroup.normalizer (Q₀ : Set X) := by
    rw [Subgroup.coe_pow]
    exact hD.mem_normalizer (pow_mem hsX 2)
  refine hs (Q₀.subgroupOf K) ?_ ?_ ((mem_normalizer_subgroupOf_iff (hD.le.trans hSK) _).2 hs2X)
  · intro x hx
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
    exact hD.le (Subgroup.mem_subgroupOf.1 hx)
  · rw [Sylow.coe_subtype, Subgroup.relIndex_subgroupOf hSK]
    exact hD.relIndex_eq

end J3

end CFSG.LocalAnalysis.RankThreeTheoremC.L28.ThreeQuotient
