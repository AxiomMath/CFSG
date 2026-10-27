module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedA
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L28AutThree
import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCoverAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem card_le_of_card_map_le {K : Subgroup X} [K.Normal] {Q : Subgroup X}
    (h27 : Nat.card (Q.map (MulAut.conjNormal (H := K))) ≤ 27) :
    Nat.card Q ≤ 27 * Nat.card (Subgroup.centralizer (K : Set X) ⊓ Q : Subgroup X) := by
  have h := Subgroup.relIndex_mul_card (H := (MulAut.conjNormal (H := K)).ker) (K := Q)
  rw [Subgroup.relIndex_ker, ker_conjNormal_eq_centralizer] at h
  rw [← h]
  exact Nat.mul_le_mul_right _ h27

theorem false_of_isCyclic_inf {Rb : Sylow 3 X} {X₀ : Subgroup X}
    (h : ReducedNongeneration 3 X Rb X₀) (hX : CatalogSimpleSections X) (hβ : KFactBeta)
    (hS : KFactSeitzCyc) (h3 : Open.pRank 3 (Rb : Subgroup X) = 3) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (huniq : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K)
    (hcyc : IsCyclic ((Rb : Subgroup X) ⊓ K : Subgroup X)) (hRb : 3 ^ 6 ≤ Nat.card Rb)
    {Q : Subgroup X} (hQ : IsPGroup 3 Q) (hQcard : 3 ^ 5 ≤ Nat.card Q) {a : X} (haQ : a ∈ Q)
    (ha3 : a ^ 3 = 1) (hC : ∀ r ∈ Q, r * a = a * r → r ^ 3 = 1) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hcyc' : ∀ L : Subgroup X, IsComponentOf L ⊤ →
      IsCyclic ((Rb : Subgroup X) ⊓ L : Subgroup X) := fun L hL => huniq L hL ▸ hcyc
  obtain ⟨L, hL, hLX₀⟩ := h.exists_not_le_of_caseTwo hX hβ hcyc' hK
  rw [huniq L hL] at hLX₀
  have hiso : IsCaseTwoGroup 3 K := h.isCaseTwoGroup_of_not_le hX hβ hS hcyc' h3 hK hLX₀
  have : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S Rb
  set c : X →* X := (MulAut.conj g).toMonoidHom with hc
  have hcS : (S : Subgroup X).map c = Rb := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def]
    rfl
  set Q' : Subgroup X := Q.map c with hQ'
  have hQ'R : Q' ≤ Rb := hcS ▸ Subgroup.map_mono hQS
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  have hQ'card : 3 ^ 5 ≤ Nat.card Q' := by rwa [hQ', Subgroup.card_map_of_injective hcinj]
  set a' : X := c a with ha'
  have ha'Q : a' ∈ Q' := Subgroup.mem_map_of_mem c haQ
  have ha'3 : a' ^ 3 = 1 := by rw [ha', ← map_pow, ha3, map_one]
  have hC' : ∀ r ∈ Q', r * a' = a' * r → r ^ 3 = 1 := by
    rintro _ ⟨r, hr, rfl⟩ hra
    have hra' : r * a = a * r := hcinj (by rw [map_mul, map_mul]; exact hra)
    rw [← map_pow, hC r hr hra', map_one]
  set TZ : Subgroup X := (Rb : Subgroup X) ⊓ Subgroup.centralizer (K : Set X) with hTZ
  have hTZ3 : IsPGroup 3 TZ := Rb.isPGroup'.to_le inf_le_left
  have hTZc : IsCyclic TZ := by
    by_contra hnc
    have h2 := two_le_pRank_of_isPGroup_not_isCyclic hp (by norm_num) hTZ3 hnc
    have h1 : Open.pRank 3 TZ ≤ 1 := h.pRank_inf_centralizer_le_one_of_not_le hK hLX₀
    omega
  have hbound : ∀ W : Subgroup X, IsPGroup 3 W →
      Nat.card W ≤ 27 * Nat.card (Subgroup.centralizer (K : Set X) ⊓ W : Subgroup X) :=
    fun W hW => card_le_of_card_map_le (kFactL28AutThree K hiso _ (hW.map _))
  have hTZ27 : 27 ≤ Nat.card TZ := by
    have h1 : Nat.card Rb ≤ 27 * Nat.card TZ := by
      have h0 := hbound Rb Rb.isPGroup'
      rw [inf_comm] at h0
      exact h0
    omega
  set N : Subgroup X := Subgroup.centralizer (K : Set X) ⊓ Q' with hN
  have hN9 : 9 ≤ Nat.card N := by
    have h1 : Nat.card Q' ≤ 27 * Nat.card N := hbound Q' (hQ.map c)
    omega
  have hNTZ : N ≤ TZ := fun x hx => ⟨hQ'R hx.2, hx.1⟩
  obtain ⟨g₀, hg₀N, hg₀⟩ := exists_orderOf_eq_nine_of_isCyclic (Subgroup.isCyclic_of_le hNTZ)
    (hTZ3.to_le hNTZ) hN9
  have ha'R : a' ∈ (Rb : Subgroup X) := hQ'R ha'Q
  have hconjTZ : ∀ y ∈ (Rb : Subgroup X), ∀ x ∈ TZ, y * x * y⁻¹ ∈ TZ := fun y hy x hx =>
    ⟨Rb.mul_mem (Rb.mul_mem hy hx.1) (Rb.inv_mem hy),
      (Subgroup.normal_centralizer (H := K)).conj_mem x hx.2 y⟩
  have ha'N : a' ∈ Subgroup.normalizer (TZ : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconjTZ a' ha'R x, fun hx => ?_⟩
    have := hconjTZ a'⁻¹ (Rb.inv_mem ha'R) _ hx
    rwa [show a'⁻¹ * (a' * x * a'⁻¹) * a'⁻¹⁻¹ = x by group] at this
  have hcomm := conj_eq_of_mem_normalizer_isCyclic hTZc hTZ3 hTZ27 ha'N ha'3 (hNTZ hg₀N)
    (by rw [← hg₀, pow_orderOf_eq_one])
  have h3' := hC' g₀ hg₀N.2 (by
    calc g₀ * a' = a' * g₀ * a'⁻¹ * a' := by rw [hcomm]
      _ = a' * g₀ := by group)
  have : orderOf g₀ ∣ 3 := orderOf_dvd_of_pow_eq_one h3'
  rw [hg₀] at this
  norm_num at this

end CFSG.AGLEmbedding
