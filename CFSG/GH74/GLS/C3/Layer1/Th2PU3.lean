module

public import CFSG.GH74.GLS.C3.Layer1.Th2CaseI
public import CFSG.GH74.GLS.C3.Layer1.Th2CaseISyl
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv

public section

namespace CFSG.GH74.GLS.Th2.PU3

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem cmap_eq_self_iff (L : Subgroup G) (m : G) :
    cmap m L = L ↔ m ∈ normalizer (L : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro l
    have : m * l * m⁻¹ ∈ cmap m L ↔ l ∈ L := by
      rw [mem_cmap, show m⁻¹ * (m * l * m⁻¹) * m = l by group]
    rw [h] at this
    exact this.symm
  · intro hm
    ext g
    rw [mem_cmap]
    have := Subgroup.mem_normalizer_iff.mp hm (m⁻¹ * g * m)
    rw [show m * (m⁻¹ * g * m) * m⁻¹ = g by group] at this
    exact this

theorem mem_normalizer_L_of_normalizes_K {K L M : Subgroup G} (hK : CFSG.IsQuasisimple ↥K)
    (hLM : IsPCompIn 2 M L) (hKL : K ≤ L) {m : G} (hm : m ∈ M)
    (hmK : m ∈ normalizer (K : Set G)) : m ∈ normalizer (L : Set G) := by
  by_contra hmL
  have hne : cmap m L ≠ L := fun h => hmL ((cmap_eq_self_iff L m).1 h)
  have hcM : cmap m M = M := (cmap_eq_self_iff M m).2 (Subgroup.le_normalizer hm)
  have hL' : IsPCompIn 2 M (cmap m L) := by
    have := isPCompIn_cmap hLM m
    rwa [hcM] at this
  have hcs : cmap m L ≤ cSec L := le_cSec_of_ne hL' hLM hne
  have hKL' : K ≤ cmap m L := by
    have h1 : cmap m K ≤ cmap m L := Subgroup.map_mono hKL
    rwa [(cmap_eq_self_iff K m).2 hmK] at h1
  have hKc : K ≤ cSec L := hKL'.trans hcs
  have hperf : ⁅K, K⁆ = K := Th2.commutator_self_of_perfect' K hK.1
  have hKK : ⁅K, K⁆ ≤ pPrimeCoreOf 2 K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ pPrimeCoreOf 2 L := (hKc hb).2.2 a (hKL ha)
    have h2 : ⁅a, b⁆ ∈ K := by
      have := Subgroup.commutator_mem_commutator ha hb
      rwa [hperf] at this
    exact Th2.inf_le_pPrimeCoreOf hKL ⟨h1, h2⟩
  have hab : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    have haK : a ∈ pPrimeCoreOf 2 K := hKK (by rw [hperf]; exact ha)
    exact Th2.commute_of_mem_pPrimeCoreOf hK haK hb
  obtain ⟨-, -, a, b, hne'⟩ := hK
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hne'
  have := hab a' a'.2 b' b'.2
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext this)

theorem pPrimeCoreOf_le_normalizer' {K L Q : Subgroup G}
    (hQL : ∀ q ∈ Q, q ∈ normalizer (L : Set G)) (hrk : 2 ≤ CFSG.pRank 2 ↥Q)
    (hgam : gammaK 2 Q 1 ≤ normalizer (K : Set G)) :
    pPrimeCoreOf 2 L ≤ normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEQ, hE, hEcard⟩ := Th2.CaseI.exists_elemAbelian_four hrk
  have hodd : ¬ 2 ∣ Nat.card ↥(pPrimeCoreOf 2 L) := by
    have h2 : Nat.card ↥(pPrimeCoreOf 2 L) = Nat.card ↥(pPrimeCore 2 ↥L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [h2]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 CFSG.pPrimeCore_coprime_card
  refine CFSG.Asc75.le_of_forall_inf_centralizer_le' hE hEcard hodd ?_ ?_
  · intro e he
    exact TwoThin.mem_normalizer_pPrimeCoreOf (hQL e (hEQ he))
  · intro b hb hb1
    have hb2 : orderOf b = 2 :=
      orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian b hb) hb1
    exact inf_le_right.trans ((C3.Layer1.U1a.centralizer_le_gammaK (hEQ hb) hb2).trans hgam)

theorem normal_of_caseI {x y : G} {K T S M : Subgroup G} (h : Th2M1 x y K T S M)
    (hQ84 : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K)) {L : Subgroup G} (hLM : IsPCompIn 2 M L)
    (hLeq : L = pPrimeCoreOf 2 L ⊔ K) (hKL : K ≤ L) (hrk : 2 ≤ pRank 2 ↥(T ⊓ CxK x K)) :
    ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := by
  have hstd : IsStandardSubgroup K := h.standard
  have hKq : CFSG.IsQuasisimple ↥K := hstd.1
  have hQC : IsSylowOf 2 (T ⊓ CxK x K) (centralizer (K : Set G)) := h.sylowQ
  have hgam : gammaK 2 (T ⊓ CxK x K) 1 ≤ normalizer (K : Set G) :=
    Th2.CaseI.gammaK_le_normalizer_of_standard hstd hQC
  have hQM : T ⊓ CxK x K ≤ M := hQ84.le.trans inf_le_left
  have hQK : ∀ q ∈ T ⊓ CxK x K, q ∈ normalizer (K : Set G) := fun q hq =>
    Subgroup.centralizer_le_normalizer (K : Set G) (hQC.le hq)
  have hQL : ∀ q ∈ T ⊓ CxK x K, q ∈ normalizer (L : Set G) := fun q hq =>
    mem_normalizer_L_of_normalizes_K hKq hLM hKL (hQM hq) (hQK q hq)
  have hN : pPrimeCoreOf 2 L ≤ normalizer (K : Set G) := pPrimeCoreOf_le_normalizer' hQL hrk hgam
  have hLN : L ≤ normalizer (K : Set G) := hLeq.le.trans (sup_le hN Subgroup.le_normalizer)
  have h2 : ∀ s ∈ L, ∀ k : ℕ, s ^ (2 ^ k) = 1 → s ∈ K := fun s hs k hk =>
    Th2.CaseI.mem_of_two_element hKL hLeq hLN hs hk
  intro m hm l hl
  by_contra hml
  have hne : cmap m L ≠ L := by
    intro hcm
    apply hml
    have : m * l * m⁻¹ ∈ cmap m L := by
      rw [mem_cmap, show m⁻¹ * (m * l * m⁻¹) * m = l by group]; exact hl
    rwa [hcm] at this
  have hcM : cmap m M = M := (cmap_eq_self_iff M m).2 (Subgroup.le_normalizer hm)
  have hL' : IsPCompIn 2 M (cmap m L) := by
    have := isPCompIn_cmap hLM m
    rwa [hcM] at this
  have hcs : cmap m L ≤ cSec L := le_cSec_of_ne hL' hLM hne
  have hXL : ∀ c ∈ cmap m L, ∀ l ∈ L, c * l * c⁻¹ ∈ L := fun c hc l hl =>
    (Subgroup.mem_normalizer_iff.1 (hcs hc).1 l).1 hl
  have hXK : cmap m L ≤ normalizer (K : Set G) :=
    Th2.CaseI.le_normalizer_of_two_elements hKq.1 hKL hXL h2
  have hXc : ∀ c ∈ cmap m L, c ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
    intro c hc
    refine ⟨hXK hc, TwoThin.mem_normalizer_pPrimeCoreOf (hXK hc), fun k hk => ?_⟩
    have h1 : ⁅k, c⁆ ∈ pPrimeCoreOf 2 L := (hcs hc).2.2 k (hKL hk)
    have h3 : ⁅k, c⁆ ∈ K := by
      have e : ⁅k, c⁆ = k * (c * k⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.1 (hXK hc) _).1 (K.inv_mem hk))
    exact Th2.inf_le_pPrimeCoreOf hKL ⟨h1, h3⟩
  have hcomm : ⁅K, conjugate K m⁻¹⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro k hk c hc
    have hcK : c ∈ cmap m K := by simpa [conjugate] using hc
    have hcL : c ∈ cmap m L := Subgroup.map_mono hKL hcK
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Th2.commute_of_mem_cSec hKq (hXc c hcL) k hk).symm
  exact hstd.2.2.2.2 m⁻¹ hcomm

end CFSG.GH74.GLS.Th2.PU3

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_thm2_PU3_II : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S M : Subgroup G) (ρ : Th2Row)
    (B : Subgroup G), Th2M2 x y K T S M ρ B → K ≤ M → IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K) →
      ∀ L : Subgroup G, IsMinSubnormalIn K M L → IsPCompIn 2 M L → L = pPrimeCoreOf 2 L ⊔ K →
        gammaK 2 (T ⊓ CxK x K) 1 ≤ M → 2 ≤ pRank 2 ↥(T ⊓ CxK x K) →
          ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L

theorem b_thm2_PU3_of_II (h : B_thm2_PU3_II) : B_thm2_PU3 := by
  intro G _ _ hG x y K T S M hchoice hKM hQ L hL hLcomp hLeq hgam hrk
  rcases hchoice with h1 | ⟨ρ, B, h2⟩
  · exact Th2.PU3.normal_of_caseI h1 hQ hLcomp hLeq hL.1 hrk
  · exact h G hG x y K T S M ρ B h2 hKM hQ L hL hLcomp hLeq hgam hrk

end CFSG.GH74.GLS
