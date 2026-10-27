module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NRm1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private lemma le_normalizer_of_commutator_le {H N C : Subgroup G} (h : ⁅H, N⁆ ≤ C)
    (hC : C ≤ N) : H ≤ Subgroup.normalizer N := by
  rw [Subgroup.le_normalizer_iff]
  intro h' hh n hn
  have h1 : ⁅h', n⁆ ∈ ⁅H, N⁆ := Subgroup.commutator_mem_commutator hh hn
  have h2 : ⁅h', n⁆ ∈ N := hC (h h1)
  have hmul : h' * n * h'⁻¹ = ⁅h', n⁆ * n := by
    rw [commutatorElement_def]; group
  rw [hmul]
  exact N.mul_mem h2 hn

private lemma commutator_mem_of_sup_inf {QM M A K : Subgroup G}
    (hKM : K ≤ Subgroup.normalizer QM) (hKA : K ≤ Subgroup.normalizer A)
    (hQMK : QM ≤ K) (hAK : A ≤ K) (hD : QM ⊓ A = M) {q a : G}
    (hq : q ∈ QM) (ha : a ∈ A) : ⁅q, a⁆ ∈ M := by
  have hnormM := Subgroup.le_normalizer_iff.mp hKM
  have hnormA := Subgroup.le_normalizer_iff.mp hKA
  have hqK : q ∈ K := hQMK hq
  have h1 : ⁅q, a⁆ ∈ QM := by
    have hx : a * q⁻¹ * a⁻¹ ∈ QM := hnormM a (hAK ha) q⁻¹ (inv_mem hq)
    have hm := QM.mul_mem hq hx
    simpa [commutatorElement_def, mul_assoc] using hm
  have h2 : ⁅q, a⁆ ∈ A := by
    have hc : q * a * q⁻¹ ∈ A := hnormA q hqK a ha
    have hm := A.mul_mem hc (A.inv_mem ha)
    simpa [commutatorElement_def, mul_assoc] using hm
  exact hD ▸ ⟨h1, h2⟩

theorem y7n_normal_two_le {K A B M Q : Subgroup G} (hA : SimpleSec A M) (hB : SimpleSec B M)
    (hsup : A ⊔ B = K) (hinf : A ⊓ B = M) (hcomm : ⁅A, B⁆ ≤ M) (hM2 : IsPGroup 2 M)
    (hQK : Q ≤ K) (hQn : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) (hQ2 : IsPGroup 2 Q) : Q ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let QM : Subgroup G := Q ⊔ M
  have hQ_le_QM : Q ≤ QM := le_sup_left
  have hM_le_QM : M ≤ QM := le_sup_right
  have hAK : A ≤ K := hsup ▸ le_sup_left
  have hBK : B ≤ K := hsup ▸ le_sup_right
  have hMA : M ≤ A := hA.le
  have hMB : M ≤ B := hB.le
  have hB_normA : B ≤ Subgroup.normalizer A :=
    le_normalizer_of_commutator_le (Subgroup.commutator_comm A B ▸ hcomm) hMA
  have hA_normB : A ≤ Subgroup.normalizer B := le_normalizer_of_commutator_le hcomm hMB
  have hK_normA : K ≤ Subgroup.normalizer A := hsup ▸ sup_le Subgroup.le_normalizer hB_normA
  have hK_normB : K ≤ Subgroup.normalizer B := hsup ▸ sup_le hA_normB Subgroup.le_normalizer
  have hK_normM : K ≤ Subgroup.normalizer M :=
    hsup ▸ sup_le (Subgroup.le_normalizer_iff.mpr hA.normal)
      (Subgroup.le_normalizer_iff.mpr hB.normal)
  have hK_normQ : K ≤ Subgroup.normalizer Q := Subgroup.le_normalizer_iff.mpr hQn
  have hK_normQM : K ≤ Subgroup.normalizer QM :=
    le_trans (le_inf hK_normQ hK_normM) (Subgroup.inf_normalizer_le_normalizer_sup Q M)
  have hQ_normM : Q ≤ Subgroup.normalizer M := hQK.trans hK_normM
  have hQM2 : IsPGroup 2 QM := hQ2.to_sup_of_normal_right' hM2 hQ_normM
  have hQM_le_K : QM ≤ K := sup_le hQK (hMA.trans hAK)
  have hAB := Subgroup.coe_mul_of_right_le_normalizer_left A B hB_normA
  have hAle_not : ¬ A ≤ QM := by
    intro hAle
    have hA2 : IsPGroup 2 A :=
      hQM2.of_injective (Subgroup.inclusion hAle) (Subgroup.inclusion_injective hAle)
    obtain ⟨n, hn⟩ := hA2.exists_card_eq
    have h3 : 3 ∣ 2 ^ n := by
      rw [← hn, hA.card]
      exact dvd_mul_of_dvd_left (by norm_num) _
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hBle_not : ¬ B ≤ QM := by
    intro hBle
    have hB2 : IsPGroup 2 B :=
      hQM2.of_injective (Subgroup.inclusion hBle) (Subgroup.inclusion_injective hBle)
    obtain ⟨n, hn⟩ := hB2.exists_card_eq
    have h3 : 3 ∣ 2 ^ n := by
      rw [← hn, hB.card]
      exact dvd_mul_of_dvd_left (by norm_num) _
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hDA : QM ⊓ A = M := by
    have hnorm : A ≤ Subgroup.normalizer (QM ⊓ A : Subgroup G) :=
      le_trans (le_inf (hAK.trans hK_normQM) Subgroup.le_normalizer)
        Subgroup.inf_normalizer_le_normalizer_inf
    rcases hA.simple (QM ⊓ A) (le_inf hM_le_QM hMA) inf_le_right
        (Subgroup.le_normalizer_iff.mp hnorm) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_left) hAle_not
  have hDB : QM ⊓ B = M := by
    have hnorm : B ≤ Subgroup.normalizer (QM ⊓ B : Subgroup G) :=
      le_trans (le_inf (hBK.trans hK_normQM) Subgroup.le_normalizer)
        Subgroup.inf_normalizer_le_normalizer_inf
    rcases hB.simple (QM ⊓ B) (le_inf hM_le_QM hMB) inf_le_right
        (Subgroup.le_normalizer_iff.mp hnorm) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_left) hBle_not
  have hQM_le_M : QM ≤ M := by
    intro q hq
    have hqK : q ∈ K := hQM_le_K hq
    have hqAB : q ∈ (A ⊔ B : Subgroup G) := by rw [hsup]; exact hqK
    have hqABmul : q ∈ (A : Set G) * (B : Set G) := by
      rw [← SetLike.mem_coe, hAB] at hqAB
      exact hqAB
    obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := Set.mem_mul.mp hqABmul
    have hqQM : a₀ * b₀ ∈ QM := by rw [hab]; exact hq
    have hqa : ∀ a ∈ A, ⁅a₀ * b₀, a⁆ ∈ M := fun a ha =>
      commutator_mem_of_sup_inf hK_normQM hK_normA hQM_le_K hAK hDA hqQM ha
    have hqb : ∀ b ∈ B, ⁅a₀ * b₀, b⁆ ∈ M := fun b hb =>
      commutator_mem_of_sup_inf hK_normQM hK_normB hQM_le_K hBK hDB hqQM hb
    rw [← hab]
    have ha₀M : a₀ ∈ M := by
      refine hA.central a₀ ha₀ (fun a ha => ?_)
      have h1 : ⁅a₀ * b₀, a⁆ ∈ M := hqa a ha
      have h2 : ⁅b₀, a⁆ ∈ M := by
        have hm : ⁅b₀, a⁆ ∈ ⁅B, A⁆ := Subgroup.commutator_mem_commutator hb₀ ha
        rw [← Subgroup.commutator_comm A B] at hm
        exact hcomm hm
      have h3 : a₀ * ⁅b₀, a⁆ * a₀⁻¹ ∈ M := hA.normal a₀ ha₀ _ h2
      have hid := commutatorElement_mul_left_eq_conj_mul a₀ b₀ a
      have heq : ⁅a₀, a⁆ = (a₀ * ⁅b₀, a⁆ * a₀⁻¹)⁻¹ * ⁅a₀ * b₀, a⁆ := by
        rw [hid]; group
      rw [heq]
      exact M.mul_mem (M.inv_mem h3) h1
    have hb₀M : b₀ ∈ M := by
      refine hB.central b₀ hb₀ (fun b hb => ?_)
      have h1 : ⁅a₀ * b₀, b⁆ ∈ M := hqb b hb
      have h2 : ⁅a₀, b⁆ ∈ M := hcomm (Subgroup.commutator_mem_commutator ha₀ hb)
      have hid := commutatorElement_mul_left_eq_conj_mul a₀ b₀ b
      have h3 : a₀ * ⁅b₀, b⁆ * a₀⁻¹ ∈ M := by
        have heq : a₀ * ⁅b₀, b⁆ * a₀⁻¹ = ⁅a₀ * b₀, b⁆ * ⁅a₀, b⁆⁻¹ := by
          rw [hid]; group
        rw [heq]
        exact M.mul_mem h1 (M.inv_mem h2)
      have heq2 : ⁅b₀, b⁆ = a₀⁻¹ * (a₀ * ⁅b₀, b⁆ * a₀⁻¹) * a₀ := by group
      rw [heq2]
      simpa using hA.normal a₀⁻¹ (A.inv_mem ha₀) _ h3
    exact M.mul_mem ha₀M hb₀M
  exact le_trans hQ_le_QM hQM_le_M

end CFSG.OddStandard.HigherRank.YamadaG23
