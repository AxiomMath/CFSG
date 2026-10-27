module

public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {Q : Type*} [Group Q]

@[expose] def Zc (R : Subgroup Q) : Subgroup Q := R ⊓ Subgroup.centralizer (R : Set Q)

theorem mem_Zc {R : Subgroup Q} {z : Q} : z ∈ Zc R ↔ z ∈ R ∧ ∀ r ∈ R, z * r = r * z := by
  unfold Zc
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun r hr => (h2 r hr).symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun r hr => (h2 r hr).symm⟩

theorem Zc_le (R : Subgroup Q) : Zc R ≤ R := inf_le_left

theorem finite_of_le' {A B : Subgroup Q} [Finite ↥B] (h : A ≤ B) : Finite ↥A :=
  Finite.of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

@[expose] def IsThreeOnePlusTwo (R : Subgroup Q) : Prop :=
  (∃ r ∈ R, ∃ s ∈ R, r * s ≠ s * r) ∧ Nat.card R = 27 ∧ ∀ g ∈ R, g ^ 3 = 1

theorem map_center_eq_Zc (R : Subgroup Q) :
    (Subgroup.center ↥R).map R.subtype = Zc R := by
  ext z
  rw [mem_Zc, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨z', hz'⟩, hc, rfl⟩
    refine ⟨hz', fun r hr => ?_⟩
    have := Subgroup.mem_center_iff.1 hc ⟨r, hr⟩
    exact congrArg Subtype.val this.symm
  · rintro ⟨hz, hc⟩
    refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact (hc g g.2).symm

theorem card_Zc_eq_card_center (R : Subgroup Q) :
    Nat.card (Zc R) = Nat.card (Subgroup.center ↥R) := by
  rw [← map_center_eq_Zc]
  exact (Subgroup.card_map_of_injective R.subtype_injective)

theorem IsThreeOnePlusTwo.card_Zc {R : Subgroup Q} (h : IsThreeOnePlusTwo R) :
    Nat.card (Zc R) = 3 := by
  obtain ⟨⟨r, hr, s, hs, hne⟩, hcard, hexp⟩ := h
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard' : Nat.card ↥R = 3 ^ 3 := by rw [hcard]; norm_num
  have hpg : IsPGroup 3 ↥R := IsPGroup.of_card hcard'
  have : Finite ↥R := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow hcard' (by norm_num)
  rw [card_Zc_eq_card_center, hk]
  have hkle : k ≤ 3 := by
    have hdvd : Nat.card (Subgroup.center ↥R) ∣ Nat.card ↥R := Subgroup.card_subgroup_dvd_card _
    rw [hk, hcard'] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hk1 : k = 1 := by
    by_contra hne1
    have hk23 : k = 2 ∨ k = 3 := by omega
    rcases hk23 with rfl | rfl
    ·
      have hZn : (Subgroup.center ↥R).Normal := inferInstance
      have hq : Nat.card (↥R ⧸ Subgroup.center ↥R) = 3 := by
        have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥R)
        rw [hcard, hk] at this
        omega
      have : Fact (Nat.Prime (Nat.card (↥R ⧸ Subgroup.center ↥R))) := ⟨hq ▸ Nat.prime_three⟩
      have : IsCyclic (↥R ⧸ Subgroup.center ↥R) := isCyclic_of_prime_card rfl
      have hcomm : IsMulCommutative ↥R :=
        MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' (Subgroup.center ↥R))
          (by rw [QuotientGroup.ker_mk']) 
      exact hne (congrArg Subtype.val (hcomm.is_comm.comm (⟨r, hr⟩ : ↥R) ⟨s, hs⟩))
    · have hZ : Subgroup.center ↥R = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hk, hcard]; norm_num
      have := Subgroup.mem_center_iff.1 (hZ ▸ Subgroup.mem_top (⟨r, hr⟩ : ↥R)) ⟨s, hs⟩
      exact hne (congrArg Subtype.val this.symm)
  rw [hk1]; norm_num


theorem IsThreeOnePlusTwo.comm_mem_Zc {R : Subgroup Q} (h : IsThreeOnePlusTwo R) {r s : Q}
    (hr : r ∈ R) (hs : s ∈ R) : ⁅r, s⁆ ∈ Zc R := by
  have hcard := h.card_Zc
  have hcard27 := h.2.1
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite ↥R := Nat.finite_of_card_ne_zero (by rw [hcard27]; norm_num)
  have hq : Nat.card (↥R ⧸ Subgroup.center ↥R) = 3 ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥R)
    rw [hcard27, ← card_Zc_eq_card_center, hcard] at h1
    omega
  have hcomm : IsMulCommutative (↥R ⧸ Subgroup.center ↥R) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  have h1 : (QuotientGroup.mk' (Subgroup.center ↥R)) ⁅(⟨r, hr⟩ : ↥R), ⟨s, hs⟩⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    have := hcomm.is_comm.comm (QuotientGroup.mk' (Subgroup.center ↥R) ⟨r, hr⟩)
      (QuotientGroup.mk' (Subgroup.center ↥R) ⟨s, hs⟩)
    generalize (QuotientGroup.mk' (Subgroup.center ↥R) ⟨r, hr⟩) = x at this ⊢
    generalize (QuotientGroup.mk' (Subgroup.center ↥R) ⟨s, hs⟩) = y at this ⊢
    rw [this]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  rw [← map_center_eq_Zc]
  exact ⟨_, h1, rfl⟩

theorem IsThreeOnePlusTwo.card_sup_zpowers {R : Subgroup Q} (h : IsThreeOnePlusTwo R) {a : Q}
    (ha : a ∈ R) (hna : a ∉ Zc R) : Nat.card ↥(Zc R ⊔ Subgroup.zpowers a) = 9 := by
  rw [card_sup_zpowers_of_pow_three_eq_one (h.2.2 a ha) hna
    (fun z hz => ((mem_Zc.1 hz).2 a ha)), h.card_Zc]

theorem IsThreeOnePlusTwo.Zc_eq_zpowers {R : Subgroup Q} (h : IsThreeOnePlusTwo R) {a b : Q}
    (ha : a ∈ R) (hb : b ∈ R) (hab : a * b ≠ b * a) : Zc R = Subgroup.zpowers ⁅a, b⁆ := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite ↥R := Nat.finite_of_card_ne_zero (by rw [h.2.1]; norm_num)
  have : Finite ↥(Zc R) := finite_of_le' (Zc_le R)
  have hz : ⁅a, b⁆ ∈ Zc R := h.comm_mem_Zc ha hb
  have hz1 : ⁅a, b⁆ ≠ 1 := by
    intro h1
    apply hab
    rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    simpa [mul_assoc] using h1
  have hz3 : ⁅a, b⁆ ^ 3 = 1 := h.2.2 _ (Zc_le R hz)
  have hord : orderOf ⁅a, b⁆ = 3 := orderOf_eq_prime hz3 hz1
  have hle : Subgroup.zpowers ⁅a, b⁆ ≤ Zc R := (Subgroup.zpowers_le).2 hz
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Nat.card_zpowers, hord, h.card_Zc]

theorem IsThreeOnePlusTwo.closure_eq {R : Subgroup Q} (h : IsThreeOnePlusTwo R) {a b : Q}
    (ha : a ∈ R) (hb : b ∈ R) (hab : a * b ≠ b * a) : Subgroup.closure {a, b} = R := by
  have hfin : Finite ↥R := Nat.finite_of_card_ne_zero (by rw [h.2.1]; norm_num)
  have hna : a ∉ Zc R := fun hz => hab ((mem_Zc.1 hz).2 b hb)
  set C : Subgroup Q := Subgroup.closure {a, b} with hC
  have haC : a ∈ C := Subgroup.subset_closure (by simp)
  have hbC : b ∈ C := Subgroup.subset_closure (by simp)
  have hCR : C ≤ R := (Subgroup.closure_le R).2 (by
    rintro x (rfl | rfl)
    · exact ha
    · exact hb)
  have hzC : ⁅a, b⁆ ∈ C := by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem haC hbC) (C.inv_mem haC)) (C.inv_mem hbC)
  have hZC : Zc R ≤ C := by
    rw [h.Zc_eq_zpowers ha hb hab]
    exact (Subgroup.zpowers_le).2 hzC
  have hDC : Zc R ⊔ Subgroup.zpowers a ≤ C := sup_le hZC ((Subgroup.zpowers_le).2 haC)
  have hD9 := h.card_sup_zpowers ha hna
  have hbD : b ∉ Zc R ⊔ Subgroup.zpowers a := by
    intro hbD
    have hle : Zc R ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({a} : Set Q) := by
      refine sup_le (fun z hz => ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((mem_Zc.1 hz).2 a ha)
      · rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hbD)
    exact hab this.symm
  have hne : Zc R ⊔ Subgroup.zpowers a ≠ C := fun heq => hbD (heq ▸ hbC)
  have : Finite ↥C := finite_of_le' hCR
  have hdvd1 : 9 ∣ Nat.card C := hD9 ▸ Subgroup.card_dvd_of_le hDC
  have hdvd2 : Nat.card C ∣ 27 := h.2.1 ▸ Subgroup.card_dvd_of_le hCR
  have hC27 : Nat.card C = 27 := by
    have : Nat.card C ∈ Nat.divisors 27 := by simp [hdvd2]
    have hd : Nat.divisors 27 = {1, 3, 9, 27} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h1 | h1 | h1 | h1
    · omega
    · omega
    · exfalso
      apply hne
      apply Subgroup.eq_of_le_of_card_ge hDC
      omega
    · exact h1
  exact Subgroup.eq_of_le_of_card_ge hCR (by rw [hC27, h.2.1])

@[expose] def HasElemSection3 (S : Subgroup Q) (n : ℕ) : Prop :=
  ∃ H N : Subgroup Q, N ≤ H ∧ H ≤ S ∧ (∀ h ∈ H, ∀ k ∈ N, h * k * h⁻¹ ∈ N) ∧
    (∀ g ∈ H, ∀ h ∈ H, g * h * g⁻¹ * h⁻¹ ∈ N) ∧ (∀ g ∈ H, g ^ 3 ∈ N) ∧
    3 ^ n ≤ (N.subgroupOf H).index

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
