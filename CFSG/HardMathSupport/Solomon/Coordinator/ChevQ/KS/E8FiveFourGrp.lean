module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace Four

open scoped Pointwise

theorem cube_le_of_index_five {P : Type*} [Group P] [Finite P] (A : Subgroup P) (hAn : A.Normal)
    (hidx : A.index = 5)
    (hfix : ∀ y : P, y ∉ A →
      Set.ncard {a : P | a ∈ A ∧ a ^ 5 = 1 ∧ a * y = y * a} ≤ 5)
    (E : Subgroup P) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 5 = 1)
    (hc : Nat.card E = 5 ^ 3) : E ≤ A := by
  by_contra hnot
  obtain ⟨y, hyE, hyA⟩ := SetLike.not_le_iff_exists.1 hnot
  have hrel : A.relIndex E = 5 := by
    have hdvd : A.relIndex E ∣ A.index := Subgroup.relIndex_dvd_index_of_normal A E
    rw [hidx] at hdvd
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h | h
    · exact absurd (Subgroup.relIndex_eq_one.1 h hyE) hyA
    · exact h
  have hcard : Nat.card (A ⊓ E : Subgroup P) = 25 := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := E)
    rw [hrel, hc] at h
    omega
  have hsub : ((A ⊓ E : Subgroup P) : Set P) ⊆
      {a : P | a ∈ A ∧ a ^ 5 = 1 ∧ a * y = y * a} := by
    intro a ha
    obtain ⟨haA, haE⟩ := ha
    exact ⟨haA, hexp a haE, hcomm a haE y hyE⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : Set.ncard ((A ⊓ E : Subgroup P) : Set P) = 25 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have h3 := hfix y hyA
  omega

theorem cube_le_ker {P Q : Type*} [Group P] [Finite P] [Group Q] (ρ : P →* Q)
    (hr : Nat.card ρ.range = 5)
    (hfix : ∀ y : P, ρ y ≠ 1 →
      Set.ncard {a : P | ρ a = 1 ∧ a ^ 5 = 1 ∧ a * y = y * a} ≤ 5)
    (E : Subgroup P) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 5 = 1)
    (hc : Nat.card E = 5 ^ 3) : E ≤ ρ.ker :=
  cube_le_of_index_five ρ.ker ρ.normal_ker (by rw [Subgroup.index_ker]; exact hr)
    (fun y hy => hfix y (fun h => hy (MonoidHom.mem_ker.2 h))) E hcomm hexp hc

theorem exists_conj_le_of_factorization_eq {G : Type*} [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] (H : Subgroup G)
    (hcard : (Nat.card H).factorization p = (Nat.card G).factorization p)
    {Q : Subgroup G} (hQ : IsPGroup p Q) : ∃ c : G, ∀ x ∈ Q, c * x * c⁻¹ ∈ H := by
  obtain ⟨P⟩ : Nonempty (Sylow p H) := inferInstance
  set P₁ : Subgroup G := (P : Subgroup H).map H.subtype with hP₁
  have hP₁card : Nat.card P₁ = p ^ (Nat.card G).factorization p := by
    rw [hP₁, Subgroup.card_map_of_injective (Subtype.val_injective), P.card_eq_multiplicity, hcard]
  set S₁ : Sylow p G := Sylow.ofCard P₁ hP₁card with hS₁
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S S₁
  refine ⟨c, fun x hx => ?_⟩
  have h1 : MulAut.conj c • x ∈ MulAut.conj c • (S : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hQS hx)
  rw [← Sylow.coe_subgroup_smul, hc, Sylow.coe_ofCard] at h1
  have h2 : c * x * c⁻¹ ∈ P₁ := by simpa [MulAut.smul_def] using h1
  obtain ⟨h, -, hh⟩ := Subgroup.mem_map.1 h2
  rw [← hh]
  exact h.2

theorem factorization_five_eq_of_ordProj {q : ℕ} (C N : ℕ)
    (hC : ordProj[5] C = 5 * ordProj[5] ((q * q + 1) ^ 4)) (hN : N = (q * q + 1) ^ 4 * 5) :
    N.factorization 5 = C.factorization 5 := by
  have h0 : (q * q + 1) ^ 4 ≠ 0 := by positivity
  have h2 : ordProj[5] N = ordProj[5] ((q * q + 1) ^ 4) * 5 := by
    rw [hN, Nat.ordProj_mul 5 h0 (by norm_num)]
    have : ordProj[5] 5 = 5 := by
      simpa using Nat.ordProj_self_pow (p := 5) (k := 1) Nat.prime_five
    rw [this]
  have h3 : 5 ^ N.factorization 5 = 5 ^ C.factorization 5 := by
    show ordProj[5] N = ordProj[5] C
    rw [h2, hC, mul_comm]
  exact Nat.pow_right_injective (by norm_num) h3

end Four

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
