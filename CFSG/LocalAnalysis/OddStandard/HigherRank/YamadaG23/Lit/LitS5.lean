module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitClass2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitQuot0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitTrans

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X] {Z A : Subgroup X} [Z.Normal]

private lemma lit_s5_mem_left_of_mem_sup_of_pow_two_eq_one {H O : Subgroup X}
    [H.Normal] [O.Normal] (hO : Odd (Nat.card O)) {y : X} (hy : y ∈ H ⊔ O) (k : ℕ)
    (hyk : y ^ 2 ^ k = 1) : y ∈ H := by
  rw [Subgroup.mem_sup_of_normal_right] at hy
  obtain ⟨h0, hh0, o0, ho0, rfl⟩ := hy
  have hmk' : QuotientGroup.mk' H h0 = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff h0).mpr hh0
  have hmk : QuotientGroup.mk' H (h0 * o0) = QuotientGroup.mk' H o0 := by
    rw [map_mul, hmk', one_mul]
  have hdvd1 : orderOf (QuotientGroup.mk' H (h0 * o0)) ∣ 2 ^ k :=
    dvd_trans (orderOf_map_dvd (QuotientGroup.mk' H) (h0 * o0))
      (orderOf_dvd_iff_pow_eq_one.mpr hyk)
  have hdvd2 : orderOf (QuotientGroup.mk' H (h0 * o0)) ∣ Nat.card O := by
    rw [hmk]
    exact dvd_trans (orderOf_map_dvd (QuotientGroup.mk' H) o0)
      (Subgroup.orderOf_dvd_natCard O ho0)
  have hone : orderOf (QuotientGroup.mk' H (h0 * o0)) = 1 :=
    Nat.eq_one_of_dvd_coprimes ((hO.coprime_two_left).pow_left k) hdvd1 hdvd2
  have h1 : QuotientGroup.mk' H (h0 * o0) = 1 := orderOf_eq_one_iff.mp hone
  exact (QuotientGroup.eq_one_iff (h0 * o0)).mp (by simpa using h1)

theorem lit_s5 (h : LitCtx Z A) (hnab : ¬ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (φ : ↥(normalizer (A : Set X)) →* Equiv.Perm (Fin 6)) (hφs : Function.Surjective φ)
    (hφk : ∀ g : ↥(normalizer (A : Set X)), φ g = 1 ↔ ∀ a ∈ A, ⁅a, (g : X)⁆ ∈ Z)
    {H : Subgroup X} [H.Normal] (hAH : A ≤ H ⊔ litP Z) : Z ≤ H := by
  have step2 : ∀ a ∈ A, ∃ z ∈ Z, z⁻¹ * a ∈ H := by
    intro a ha
    have ha' : a ∈ Z ⊔ (H ⊔ CFSG.oddCore X) := by
      have h1 : a ∈ H ⊔ (Z ⊔ CFSG.oddCore X) := by
        simpa only [litP] using hAH ha
      rwa [sup_left_comm] at h1
    rw [Subgroup.mem_sup_of_normal_left] at ha'
    obtain ⟨z, hzZ, y, hyHO, hzy⟩ := ha'
    refine ⟨z, hzZ, ?_⟩
    have hy_eq : y = z⁻¹ * a := by rw [← hzy]; group
    rw [← hy_eq]
    have hyA : y ∈ A := by
      rw [hy_eq]
      exact A.mul_mem (A.inv_mem (h.Z_le_A hzZ)) ha
    obtain ⟨k, hk⟩ := h.isPGroup_A ⟨y, hyA⟩
    refine lit_s5_mem_left_of_mem_sup_of_pow_two_eq_one (lit_odd_card_oddCore X) hyHO k ?_
    have := congrArg Subtype.val hk
    simpa using this
  by_contra hZH
  obtain ⟨z0, hz0Z, hz0H⟩ := IsConcreteLE.not_le_iff_exists.mp hZH
  set B : Subgroup X := A ⊓ H with hB
  set Z1 : Subgroup X := Z ⊓ H with hZ1
  have hZ1_le_Z : Z1 ≤ Z := by rw [hZ1]; exact inf_le_left
  have hZ1_le_H : Z1 ≤ H := by rw [hZ1]; exact inf_le_right
  have hz0Z1 : z0 ∉ Z1 := fun hz => hz0H (by rw [hZ1] at hz; exact hz.2)
  have hZ1_ne_Z : Z1 ≠ Z := fun heq => hz0Z1 (by rw [heq]; exact hz0Z)
  have hZ1_dvd : Nat.card Z1 ∣ 4 := by
    have h1 := Subgroup.card_dvd_of_le hZ1_le_Z
    rwa [h.card_Z] at h1
  have hZ1_ne4 : Nat.card Z1 ≠ 4 := by
    intro h4
    exact hZ1_ne_Z (Subgroup.eq_of_le_of_card_ge hZ1_le_Z (by rw [h.card_Z, h4]))
  have hZ1_card_dvd2 : Nat.card Z1 ∣ 2 := by
    have hd : Nat.card Z1 ∣ 2 ^ 2 := by
      rwa [show (4 : ℕ) = 2 ^ 2 by norm_num] at hZ1_dvd
    obtain ⟨k, _hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    interval_cases k
    · rw [hk]; norm_num
    · rw [hk]; norm_num
    · exact absurd (by norm_num : (2 : ℕ) ^ 2 = 4) (by rw [← hk]; exact hZ1_ne4)
  have hsq1 : ∀ z ∈ Z1, z ^ 2 = 1 := by
    intro z hz
    exact orderOf_dvd_iff_pow_eq_one.mp
      (dvd_trans (Subgroup.orderOf_dvd_natCard Z1 hz) hZ1_card_dvd2)
  have hA_eq : Z ⊔ B = A := by
    refine le_antisymm ?_ ?_
    · rw [hB]; exact sup_le h.Z_le_A inf_le_left
    · intro a ha
      obtain ⟨z, hzZ, hza⟩ := step2 a ha
      have hzaB : z⁻¹ * a ∈ B := by
        rw [hB]
        exact ⟨A.mul_mem (A.inv_mem (h.Z_le_A hzZ)) ha, hza⟩
      have ha_eq : a = z * (z⁻¹ * a) := by group
      rw [ha_eq]
      exact mul_mem_sup hzZ hzaB
  have hZ_inf_B : (Z ⊓ B : Subgroup X) = Z1 := by
    rw [hB, ← inf_assoc, inf_eq_left.mpr h.Z_le_A, hZ1]
  have hcard_sup :
      Nat.card (Z ⊔ B : Subgroup X) * Nat.card (Z ⊓ B : Subgroup X)
        = Nat.card Z * Nat.card B := by
    have h1 : Z.relIndex (Z ⊔ B) * Nat.card Z = Nat.card (Z ⊔ B : Subgroup X) := by
      have hh := Subgroup.relIndex_mul_card (H := Z) (K := Z ⊔ B)
      rwa [inf_eq_left.mpr le_sup_left] at hh
    have h2 : (Z ⊓ B).relIndex B * Nat.card (Z ⊓ B : Subgroup X) = Nat.card B := by
      have hh := Subgroup.relIndex_mul_card (H := Z ⊓ B) (K := B)
      rwa [inf_eq_left.mpr inf_le_right] at hh
    have h3 : Z.relIndex (Z ⊔ B) = (Z ⊓ B).relIndex B := by
      rw [sup_comm, Subgroup.relIndex_sup_right, Subgroup.inf_relIndex_right]
    calc Nat.card (Z ⊔ B : Subgroup X) * Nat.card (Z ⊓ B : Subgroup X)
        = (Z.relIndex (Z ⊔ B) * Nat.card Z) * Nat.card (Z ⊓ B : Subgroup X) := by
          rw [← h1]
      _ = ((Z ⊓ B).relIndex B * Nat.card Z) * Nat.card (Z ⊓ B : Subgroup X) := by rw [h3]
      _ = Nat.card Z * ((Z ⊓ B).relIndex B * Nat.card (Z ⊓ B : Subgroup X)) := by ring
      _ = Nat.card Z * Nat.card B := by rw [h2]
  have hcardB : Nat.card B = 16 * Nat.card Z1 := by
    have hc := hcard_sup
    rw [hA_eq, hZ_inf_B, h.card_Z, h.card_A] at hc
    omega
  have hZB : Z1 ≤ B := by
    intro x hx
    rw [hZ1] at hx
    rw [hB]
    exact ⟨h.Z_le_A hx.1, hx.2⟩
  have hcent : ∀ z ∈ Z1, ∀ b ∈ B, z * b = b * z := by
    intro z hz b _
    rw [hZ1] at hz
    exact h.central z hz.1 b
  have hcommB : ∀ a ∈ B, ∀ b ∈ B, ⁅a, b⁆ ∈ Z1 := by
    intro a ha b hb
    rw [hB] at ha hb
    have hZ : ⁅a, b⁆ ∈ Z := h.comm_mem a ha.1 b hb.1
    have hH : ⁅a, b⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha.2 hb.2) (H.inv_mem ha.2)) (H.inv_mem hb.2)
    rw [hZ1]; exact ⟨hZ, hH⟩
  have hsqB : ∀ b ∈ B, b ^ 2 ∈ Z1 := by
    intro b hb
    rw [hB] at hb
    have hZ : b ^ 2 ∈ Z := h.sq_mem b hb.1
    have hH : b ^ 2 ∈ H := H.pow_mem hb.2 2
    rw [hZ1]; exact ⟨hZ, hH⟩
  have hconst : ∀ b ∈ B, ∀ c ∈ B, b ∉ Z1 → c ∉ Z1 → b ^ 2 = c ^ 2 := by
    intro b hb c hc hbZ1 hcZ1
    rw [hB] at hb hc
    have hbA : b ∈ A := hb.1
    have hbH : b ∈ H := hb.2
    have hcA : c ∈ A := hc.1
    have hcH : c ∈ H := hc.2
    have hbZ : b ∉ Z := fun hbz => hbZ1 (by rw [hZ1]; exact ⟨hbz, hbH⟩)
    have hcZ : c ∉ Z := fun hcz => hcZ1 (by rw [hZ1]; exact ⟨hcz, hcH⟩)
    obtain ⟨n, _hnN, z, hzZ, hnz⟩ := lit_transitive h φ hφs hφk hbA hcA hbZ hcZ
    have hzH : z ∈ H := by
      have hz_eq : z = c⁻¹ * (n * b * n⁻¹) := by rw [hnz]; group
      rw [hz_eq]
      exact H.mul_mem (H.inv_mem hcH) ((inferInstance : H.Normal).conj_mem b hbH n)
    have hzZ1 : z ∈ Z1 := by rw [hZ1]; exact ⟨hzZ, hzH⟩
    have hz2 : z ^ 2 = 1 := hsq1 z hzZ1
    have hsqn : (n * b * n⁻¹) ^ 2 = b ^ 2 := by
      have hb2Z : b ^ 2 ∈ Z := h.sq_mem b hbA
      have hconj : (n * b * n⁻¹) ^ 2 = n * b ^ 2 * n⁻¹ := by
        calc (n * b * n⁻¹) ^ 2 = (MulAut.conj n b) ^ 2 := by rw [MulAut.conj_apply]
          _ = MulAut.conj n (b ^ 2) := (map_pow (MulAut.conj n) b 2).symm
          _ = n * b ^ 2 * n⁻¹ := by rw [MulAut.conj_apply]
      rw [hconj, ← h.central (b ^ 2) hb2Z n]
      group
    have hsqc : (c * z) ^ 2 = c ^ 2 := by
      have hcz : Commute c z := (h.central z hzZ c).symm
      rw [Commute.mul_pow hcz 2, hz2, mul_one]
    rw [← hsqn, hnz, hsqc]
  have hBabel : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a :=
    lit_class2_abelian hZB hcent hsq1 hcommB hsqB hcardB hconst
  have hZcent : Z ≤ Subgroup.centralizer (A : Set X) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact (h.central z hz y).symm
  have hBcent : B ≤ Subgroup.centralizer (A : Set X) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨w, hwZ, hwy⟩ := step2 y hy
    have hwyB : w⁻¹ * y ∈ B := by
      rw [hB]
      exact ⟨A.mul_mem (A.inv_mem (h.Z_le_A hwZ)) hy, hwy⟩
    have hy_eq : y = w * (w⁻¹ * y) := by group
    rw [hy_eq]
    calc w * (w⁻¹ * y) * b = w * ((w⁻¹ * y) * b) := by group
      _ = w * (b * (w⁻¹ * y)) := by rw [hBabel (w⁻¹ * y) hwyB b hb]
      _ = b * (w * (w⁻¹ * y)) := by
          calc w * (b * (w⁻¹ * y)) = (w * b) * (w⁻¹ * y) := by group
            _ = (b * w) * (w⁻¹ * y) := by rw [h.central w hwZ b]
            _ = b * (w * (w⁻¹ * y)) := by group
  have hAcent : A ≤ Subgroup.centralizer (A : Set X) := by
    have hh := sup_le hZcent hBcent
    rwa [hA_eq] at hh
  exact hnab fun a ha a' ha' =>
    (Subgroup.mem_centralizer_iff.mp (hAcent ha) a' ha').symm

end CFSG.OddStandard.HigherRank.YamadaG23
