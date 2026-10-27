module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84EDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E4SylA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E4SylB
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem isSylow2Of_eq_of_le {G : Type} [Group G] [Finite G] {S K H : Subgroup G}
    (hS : IsSylow2Of S H) (hK : IsSylow2Of K H) (hle : S ≤ K) : S = K := by
  have hdvd : S.relIndex K ∣ S.relIndex H :=
    ⟨K.relIndex H, (Subgroup.relIndex_mul_relIndex S K H hle hK.1).symm⟩
  have hoddS : Odd (S.relIndex H) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hS.2.2
  have hoddSK : Odd (S.relIndex K) := hoddS.of_dvd_nat hdvd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK.2.1
  have hdvd2 : S.relIndex K ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.relIndex_dvd_card S K
  have hone : S.relIndex K = 1 := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
    have hk0 : k = 0 := by
      cases k with
      | zero => rfl
      | succ k =>
        exact absurd (even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.succ_ne_zero k)))
          (Nat.not_even_iff_odd.mpr (hk ▸ hoddSK))
    rw [hk0, pow_zero] at hk
    exact hk
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hone)

theorem sec8t84_tstruct {G : Type} [Group G] [Finite G] {t : G} {E Y1 Y2 T : Subgroup G}
    (ht : t * t = 1) (hE : IsElemAb2 E 8) (hc : Sec8T84XCore G t E Y1 Y2)
    (hT : IsSylow2Of T (normalizer (E : Set G))) (htT : t ∈ T) :
    IsSylow2Of (T ⊓ (Y1 ⊔ Y2)) (Y1 ⊔ Y2) ∧ Nat.card T = 2 * Nat.card ↥(T ⊓ (Y1 ⊔ Y2)) ∧
      T = zpowers t ⊔ (T ⊓ (Y1 ⊔ Y2)) ∧
      IsSylow2Of (T ⊓ Y1) Y1 ∧ IsSylow2Of (T ⊓ Y2) Y2 ∧
      T ⊓ (Y1 ⊔ Y2) = (T ⊓ Y1) ⊔ (T ⊓ Y2) ∧
      (∀ a ∈ T ⊓ Y1, ∀ b ∈ T ⊓ Y2, a * b = b * a) ∧ (T ⊓ Y1) ⊓ (T ⊓ Y2) = ⊥ ∧
      (∀ a ∈ T ⊓ Y1, t * a * t⁻¹ ∈ T ⊓ Y2) ∧ (∀ a ∈ T ⊓ Y2, t * a * t⁻¹ ∈ T ⊓ Y1) ∧
      E ≤ T ∧ E ⊓ Y1 ≤ T ⊓ Y1 ∧ E ⊓ Y2 ≤ T ⊓ Y2 ∧
      (∀ a ∈ T ⊓ Y1, ∀ e ∈ E ⊓ Y1, a * e * a⁻¹ ∈ E ⊓ Y1) ∧
      (∀ a ∈ T ⊓ Y2, ∀ e ∈ E ⊓ Y2, a * e * a⁻¹ ∈ E ⊓ Y2) := by
  have hOodd : Odd (Nat.card (oddCoreIn (normalizer (E : Set G)))) :=
    CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (normalizer (E : Set G))
  have h12 : ∀ a ∈ Y1, ∀ b ∈ Y2, a * b * a⁻¹ ∈ Y2 := by
    intro a ha b hb
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) :=
      hc.comm a ha b hb
    have heq : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
    rw [heq]
    exact mul_mem (hc.o_le2 hmem) hb
  have h21 : ∀ b ∈ Y2, ∀ a ∈ Y1, b * a * b⁻¹ ∈ Y1 := by
    intro b hb a ha
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) :=
      hc.comm a ha b hb
    have heq : b * a * b⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ * a := by group
    rw [heq]
    exact mul_mem (hc.o_le1 (inv_mem hmem)) ha
  have hY1norm : Y1 ≤ Subgroup.normalizer ((Y1 ⊔ Y2 : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer (Subgroup.le_normalizer_iff.mpr h12)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup Y1 Y2)
  have hY2norm : Y2 ≤ Subgroup.normalizer ((Y1 ⊔ Y2 : Subgroup G) : Set G) :=
    (le_inf (Subgroup.le_normalizer_iff.mpr h21) Subgroup.le_normalizer).trans
      (Subgroup.inf_normalizer_le_normalizer_sup Y1 Y2)
  have hmap1 : Y1.map (MulAut.conj t) ≤ Y2 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    simpa using hc.swap1 a ha
  have hmap2 : Y2.map (MulAut.conj t) ≤ Y1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    simpa using hc.swap2 a ha
  have hHmap : (Y1 ⊔ Y2).map (MulAut.conj t) ≤ Y1 ⊔ Y2 := by
    rw [Subgroup.map_sup]
    exact (sup_le (hmap1.trans le_sup_left) (hmap2.trans le_sup_right)).trans
      (le_of_eq (sup_comm Y2 Y1))
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hconj2 : ∀ a : G, t * (t * a * t⁻¹) * t⁻¹ = a := by
    intro a
    rw [htinv]
    calc
      t * (t * a * t) * t = (t * t) * a * (t * t) := by group
      _ = 1 * a * 1 := by rw [ht]
      _ = a := by simp
  have ht_norm : t ∈ Subgroup.normalizer ((Y1 ⊔ Y2 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      simpa using hHmap (Subgroup.mem_map.mpr ⟨h, hh, rfl⟩)
    · intro hh
      have heq : h = t * (t * h * t⁻¹) * t⁻¹ := (hconj2 h).symm
      rw [heq]
      simpa using hHmap (Subgroup.mem_map.mpr ⟨t * h * t⁻¹, hh, rfl⟩)
  have hzp : Subgroup.zpowers t ≤ Subgroup.normalizer ((Y1 ⊔ Y2 : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr ht_norm
  have hXleN : normalizer (E : Set G) ≤
      Subgroup.normalizer ((Y1 ⊔ Y2 : Subgroup G) : Set G) := by
    rw [← hc.sup]
    exact sup_le (sup_le hY1norm hY2norm) hzp
  have hXnorm : ∀ x ∈ normalizer (E : Set G), ∀ h ∈ Y1 ⊔ Y2, x * h * x⁻¹ ∈ Y1 ⊔ Y2 :=
    Subgroup.le_normalizer_iff.mp hXleN
  obtain ⟨hSylH, hcardT, hTsup⟩ :=
    sec8t84_index_two ht (sup_le hc.le1 hc.le2) hXnorm hc.sup hc.t_not hT htT
  have hHnormY1 : Y1 ⊔ Y2 ≤ Subgroup.normalizer (Y1 : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.le_normalizer_iff.mpr h21)
  have hHnormY1' : ∀ h ∈ Y1 ⊔ Y2, ∀ n ∈ Y1, h * n * h⁻¹ ∈ Y1 :=
    Subgroup.le_normalizer_iff.mp hHnormY1
  have hSyl1' : IsSylow2Of ((T ⊓ (Y1 ⊔ Y2)) ⊓ Y1) Y1 :=
    sec8t84_sylow_inf_normal hSylH le_sup_left hHnormY1'
  have hSyl1 : IsSylow2Of (T ⊓ Y1) Y1 := by
    have h := hSyl1'
    rw [inf_assoc] at h
    rwa [show (Y1 ⊔ Y2) ⊓ Y1 = Y1 from inf_eq_right.mpr le_sup_left] at h
  have hHnormY2 : Y1 ⊔ Y2 ≤ Subgroup.normalizer (Y2 : Set G) :=
    sup_le (Subgroup.le_normalizer_iff.mpr h12) Subgroup.le_normalizer
  have hHnormY2' : ∀ h ∈ Y1 ⊔ Y2, ∀ n ∈ Y2, h * n * h⁻¹ ∈ Y2 :=
    Subgroup.le_normalizer_iff.mp hHnormY2
  have hSyl2' : IsSylow2Of ((T ⊓ (Y1 ⊔ Y2)) ⊓ Y2) Y2 :=
    sec8t84_sylow_inf_normal hSylH le_sup_right hHnormY2'
  have hSyl2 : IsSylow2Of (T ⊓ Y2) Y2 := by
    have h := hSyl2'
    rw [inf_assoc] at h
    rwa [show (Y1 ⊔ Y2) ⊓ Y2 = Y2 from inf_eq_right.mpr le_sup_right] at h
  have hbotOT : oddCoreIn (normalizer (E : Set G)) ⊓ T = ⊥ := by
    have h2OT : IsPGroup 2 ↥(oddCoreIn (normalizer (E : Set G)) ⊓ T) :=
      hT.2.1.to_le inf_le_right
    have hoddOT : Odd (Nat.card ↥(oddCoreIn (normalizer (E : Set G)) ⊓ T)) :=
      hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2OT
    have hn0 : n = 0 := by
      by_contra hn0
      exact (Nat.not_even_iff_odd.mpr (hn ▸ hoddOT))
        (even_iff_two_dvd.mpr (dvd_pow_self 2 hn0))
    rw [hn0, pow_zero] at hn
    exact Subgroup.card_eq_one.mp hn
  have hcomm : ∀ a ∈ T ⊓ Y1, ∀ b ∈ T ⊓ Y2, a * b = b * a := by
    intro a ha b hb
    have hmemO : a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) :=
      hc.comm a ha.2 b hb.2
    have hmemT : a * b * a⁻¹ * b⁻¹ ∈ T :=
      mul_mem (mul_mem (mul_mem ha.1 hb.1) (inv_mem ha.1)) (inv_mem hb.1)
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) ⊓ T :=
      ⟨hmemO, hmemT⟩
    have hone : a * b * a⁻¹ * b⁻¹ = 1 := by
      rw [hbotOT] at hmem
      exact Subgroup.mem_bot.mp hmem
    calc
      a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = 1 * (b * a) := by rw [hone]
      _ = b * a := by simp
  have hinf12 : (T ⊓ Y1) ⊓ (T ⊓ Y2) = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxO : x ∈ oddCoreIn (normalizer (E : Set G)) := hc.inf ⟨hx.1.2, hx.2.2⟩
      have hxT : x ∈ T := hx.1.1
      have hmem : x ∈ oddCoreIn (normalizer (E : Set G)) ⊓ T := ⟨hxO, hxT⟩
      rw [hbotOT] at hmem
      exact hmem
    · exact bot_le
  have hswap1 : ∀ a ∈ T ⊓ Y1, t * a * t⁻¹ ∈ T ⊓ Y2 := by
    intro a ha
    have h1 : t * a * t⁻¹ ∈ T := mul_mem (mul_mem htT ha.1) (inv_mem htT)
    exact ⟨h1, hc.swap1 a ha.2⟩
  have hswap2 : ∀ a ∈ T ⊓ Y2, t * a * t⁻¹ ∈ T ⊓ Y1 := by
    intro a ha
    have h1 : t * a * t⁻¹ ∈ T := mul_mem (mul_mem htT ha.1) (inv_mem htT)
    exact ⟨h1, hc.swap2 a ha.2⟩
  have hY12odd : Odd (Nat.card ↥(Y1 ⊓ Y2)) :=
    hOodd.of_dvd_nat (Subgroup.card_dvd_of_le hc.inf)
  have hsupSyl : IsSylow2Of ((T ⊓ Y1) ⊔ (T ⊓ Y2)) (Y1 ⊔ Y2) ∧
      Nat.card ↥((T ⊓ Y1) ⊔ (T ⊓ Y2)) =
        Nat.card ↥(T ⊓ Y1) * Nat.card ↥(T ⊓ Y2) :=
    sec8t84_sylow_sup_commuting h12 h21 hY12odd hSyl1 hSyl2 hcomm hinf12
  have hleS : (T ⊓ Y1) ⊔ (T ⊓ Y2) ≤ T ⊓ (Y1 ⊔ Y2) :=
    sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_left))
      (le_inf inf_le_left (inf_le_right.trans le_sup_right))
  have hTinf_eq : T ⊓ (Y1 ⊔ Y2) = (T ⊓ Y1) ⊔ (T ⊓ Y2) :=
    (isSylow2Of_eq_of_le hsupSyl.1 hSylH hleS).symm
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hE.2
  have hEnorm : ∀ x ∈ normalizer (E : Set G), ∀ e ∈ E, x * e * x⁻¹ ∈ E :=
    fun x hx e he => (Subgroup.mem_normalizer_iff.mp hx e).mp he
  have hE_le_T : E ≤ T :=
    sec8t84_le_sylow_of_normal hT Subgroup.le_normalizer hEnorm hE2
  have hEY1 : E ⊓ Y1 ≤ T ⊓ Y1 := inf_le_inf hE_le_T le_rfl
  have hEY2 : E ⊓ Y2 ≤ T ⊓ Y2 := inf_le_inf hE_le_T le_rfl
  have hconjE1 : ∀ a ∈ T ⊓ Y1, ∀ e ∈ E ⊓ Y1, a * e * a⁻¹ ∈ E ⊓ Y1 := by
    intro a ha e he
    have h1 : a * e * a⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hT.1 ha.1) e).mp he.1
    have h2 : a * e * a⁻¹ ∈ Y1 := mul_mem (mul_mem ha.2 he.2) (inv_mem ha.2)
    exact ⟨h1, h2⟩
  have hconjE2 : ∀ a ∈ T ⊓ Y2, ∀ e ∈ E ⊓ Y2, a * e * a⁻¹ ∈ E ⊓ Y2 := by
    intro a ha e he
    have h1 : a * e * a⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hT.1 ha.1) e).mp he.1
    have h2 : a * e * a⁻¹ ∈ Y2 := mul_mem (mul_mem ha.2 he.2) (inv_mem ha.2)
    exact ⟨h1, h2⟩
  exact ⟨hSylH, hcardT, hTsup, hSyl1, hSyl2, hTinf_eq, hcomm, hinf12, hswap1, hswap2,
    hE_le_T, hEY1, hEY2, hconjE1, hconjE2⟩

end CFSG.OddStandard.SmallF3.Omega
