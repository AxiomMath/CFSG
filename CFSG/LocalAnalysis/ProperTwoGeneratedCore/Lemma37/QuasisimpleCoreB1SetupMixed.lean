module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1SetupBasic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.BenderSuzuki.PFchapter1section1

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {u : J}

omit [Finite J] in
@[expose] def IsMixedInv (g : J ⧸ Subgroup.center J) : Prop :=
  orderOf g = 2 ∧ ∀ j : J, (j : J ⧸ Subgroup.center J) = g → orderOf j = 2

namespace IsMixedInv

variable {g : J ⧸ Subgroup.center J}

omit [Finite J] in
theorem orderOf_eq (ht : IsMixedInv g) : orderOf g = 2 :=
  ht.1

omit [Finite J] in
theorem orderOf_of_mk_eq (ht : IsMixedInv g) {j : J} (hj : (j : J ⧸ Subgroup.center J) = g) :
    orderOf j = 2 :=
  ht.2 j hj

omit [Finite J] in
theorem ne_one (ht : IsMixedInv g) : g ≠ 1 := by
  intro h1
  have h2 := ht.orderOf_eq
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by decide)

omit [Finite J] in
theorem conj (ht : IsMixedInv g) (x : J ⧸ Subgroup.center J) : IsMixedInv (x * g * x⁻¹) := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact ht.orderOf_eq
  · obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hj' : ((y⁻¹ * j * y : J) : J ⧸ Subgroup.center J) = g := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hj]
      group
    have h2 := ht.orderOf_of_mk_eq hj'
    rwa [show y⁻¹ * j * y = MulAut.conj y⁻¹ j by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq] at h2

end IsMixedInv

omit [Finite J] in
theorem isMixedInv_conj_iff (x g : J ⧸ Subgroup.center J) :
    IsMixedInv (x * g * x⁻¹) ↔ IsMixedInv g := by
  refine ⟨fun h => ?_, fun h => h.conj x⟩
  have h' := h.conj x⁻¹
  rwa [show x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g by group] at h'

omit [Finite J] in
theorem isMixedInv_inv_mul_mul_iff (x g : J ⧸ Subgroup.center J) :
    IsMixedInv (x⁻¹ * g * x) ↔ IsMixedInv g := by
  have h := isMixedInv_conj_iff x⁻¹ g
  rwa [inv_inv] at h

namespace Setting

theorem mul_mul_self_of_mem_center (h : Setting J Q B) {c : J} (hc : c ∈ Subgroup.center J)
    (j : J) : j * c * (j * c) = j * j := by
  have hcc : c * c = 1 := by
    rcases h.mem_center_iff.mp hc with rfl | rfl
    · exact mul_one 1
    · exact h.centralElt_mul_self
  calc j * c * (j * c) = j * (c * j) * c := by group
    _ = j * (j * c) * c := by rw [← Subgroup.mem_center_iff.mp hc j]
    _ = j * j * (c * c) := by group
    _ = j * j := by rw [hcc, mul_one]

theorem mul_self_eq_of_mk_eq (h : Setting J Q B) {j k : J}
    (hjk : (j : J ⧸ Subgroup.center J) = k) : k * k = j * j := by
  have hc : j⁻¹ * k ∈ Subgroup.center J := QuotientGroup.eq.mp hjk
  rw [show k = j * (j⁻¹ * k) by group, h.mul_mul_self_of_mem_center hc]

theorem isMixedInv_mk_iff (h : Setting J Q B) (j : J) :
    IsMixedInv (j : J ⧸ Subgroup.center J) ↔ orderOf j = 2 ∧ j ∉ Subgroup.center J := by
  constructor
  · intro ht
    refine ⟨ht.orderOf_of_mk_eq rfl, fun hj => ht.ne_one ?_⟩
    rwa [QuotientGroup.eq_one_iff]
  · rintro ⟨hj2, hjZ⟩
    have hjj : j * j = 1 := by rw [← pow_two, ← hj2, pow_orderOf_eq_one]
    have hj1 : (j : J ⧸ Subgroup.center J) ≠ 1 := by rwa [Ne, QuotientGroup.eq_one_iff]
    refine ⟨orderOf_eq_prime (by rw [pow_two, ← QuotientGroup.mk_mul, hjj, QuotientGroup.mk_one])
      hj1, fun k hk => orderOf_eq_prime (by rw [pow_two, h.mul_self_eq_of_mk_eq hk.symm, hjj]) ?_⟩
    rintro rfl
    exact hj1 (by rw [← hk, QuotientGroup.mk_one])

theorem isMixedInv_mk_iff_mul_self (h : Setting J Q B) (j : J) :
    IsMixedInv (j : J ⧸ Subgroup.center J) ↔ j * j = 1 ∧ j ∉ Subgroup.center J := by
  rw [h.isMixedInv_mk_iff]
  constructor
  · rintro ⟨hj2, hjZ⟩
    exact ⟨by rw [← pow_two, ← hj2, pow_orderOf_eq_one], hjZ⟩
  · rintro ⟨hjj, hjZ⟩
    exact ⟨orderOf_eq_prime (by rw [pow_two, hjj]) fun h1 => hjZ (h1 ▸ one_mem _), hjZ⟩

theorem mul_self_eq_centralElt_of_not_isMixedInv (h : Setting J Q B) {j : J}
    (hj : orderOf (j : J ⧸ Subgroup.center J) = 2)
    (hm : ¬ IsMixedInv (j : J ⧸ Subgroup.center J)) : j * j = centralElt J := by
  have hjj : j * j ∈ Subgroup.center J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hj, pow_orderOf_eq_one]
  rcases h.mem_center_iff.mp hjj with h1 | he
  · refine absurd ((h.isMixedInv_mk_iff_mul_self j).mpr ⟨h1, fun hjZ => ?_⟩) hm
    rw [(QuotientGroup.eq_one_iff j).mpr hjZ, orderOf_one] at hj
    exact absurd hj (by decide)
  · exact he

theorem centralizer_le_of_isMixedInv (h : Setting J Q B) {t : J ⧸ Subgroup.center J}
    (ht : IsMixedInv t) (htB : t ∈ b1Bar B) : Subgroup.centralizer {t} ≤ b1Bar B := by
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective t
  obtain ⟨hj2, hjZ⟩ := (h.isMixedInv_mk_iff j).mp ht
  exact h.centralizer_mk_le ((h.mk_mem_map_iff j).mp htB) hj2 hjZ

theorem mem_of_conj_mem_of_isMixedInv (h : Setting J Q B) {t g : J ⧸ Subgroup.center J}
    (ht : IsMixedInv t) (htB : t ∈ b1Bar B) (hg : g * t * g⁻¹ ∈ b1Bar B) : g ∈ b1Bar B := by
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective t
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨hj2, hjZ⟩ := (h.isMixedInv_mk_iff j).mp ht
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    h.mk_mem_map_iff] at hg
  exact (h.mk_mem_map_iff x).mpr (h.mem_of_conj_mem ((h.mk_mem_map_iff j).mp htB) hj2 hjZ hg)

end Setting

namespace CaseB1

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {M : ℕ}

theorem isMixedInv_mk_mul_iff (hb : CaseB1 Q B T L M) {q p : J} (hq : q ∈ partCLeft T L)
    (hp : p ∈ partCRight T L) (hs : orderOf ((q * p : J) : J ⧸ Subgroup.center J) = 2) :
    IsMixedInv ((q * p : J) : J ⧸ Subgroup.center J) ↔
      q ∉ Subgroup.center J ∧ p ∉ Subgroup.center J := by
  have h := hb.setting
  have hc := hb.partC
  have hqp : q * p * (q * p) = q * q * (p * p) := by
    calc q * p * (q * p) = q * (p * q) * p := by group
      _ = q * (q * p) * p := by rw [hc.commute q hq p hp]
      _ = q * q * (p * p) := by group
  have hsq : q * p * (q * p) ∈ Subgroup.center J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hs, pow_orderOf_eq_one]
  have hs1 : q * p ∉ Subgroup.center J := by
    rw [← QuotientGroup.eq_one_iff]
    intro h1
    rw [h1, orderOf_one] at hs
    exact absurd hs (by decide)
  have hqZ : q ∈ Subgroup.center J ↔ q * q = 1 := by
    rw [h.mem_center_iff]
    refine ⟨?_, quaternion_eq_of_mul_self hc.quaternion.some hc.mem_left hc.order hq⟩
    rintro (rfl | rfl)
    · exact mul_one 1
    · exact h.centralElt_mul_self
  have hpZ : p ∈ Subgroup.center J ↔ p * p = 1 := by
    rw [h.mem_center_iff]
    constructor
    · rintro (rfl | rfl)
      · exact mul_one 1
      · exact h.centralElt_mul_self
    · intro hpp
      by_cases hp1 : p = 1
      · exact Or.inl hp1
      · exact Or.inr (hc.unique p hp (orderOf_eq_prime (by rw [pow_two]; exact hpp) hp1))
  have hq2 := quaternion_mul_self hc.quaternion.some hc.mem_left hc.order hq
  have hp2 : p * p = 1 ∨ p * p = centralElt J := by
    refine h.mem_center_iff.mp ?_
    rw [hqp] at hsq
    rcases hq2 with hq2 | hq2
    · rwa [hq2, one_mul] at hsq
    · rw [hq2] at hsq
      have h' := (Subgroup.center J).mul_mem h.centralElt_mem_center hsq
      rwa [← mul_assoc, h.centralElt_mul_self, one_mul] at h'
  have he1 := h.centralElt_ne_one
  rw [h.isMixedInv_mk_iff_mul_self, hqp, hqZ, hpZ]
  rcases hq2 with hq2 | hq2 <;> rcases hp2 with hp2 | hp2 <;> rw [hq2, hp2]
  · exact absurd ((Subgroup.center J).mul_mem (hqZ.mpr hq2) (hpZ.mpr hp2)) hs1
  · simp [he1]
  · simp [he1]
  · simp [he1, h.centralElt_mul_self, hs1]

theorem isMixedInv_mul_iff (hb : CaseB1 Q B T L M) {x d : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hd : d ∈ b1D T L) (hs : orderOf (x * d) = 2) :
    IsMixedInv (x * d) ↔ x ≠ 1 ∧ d ≠ 1 := by
  obtain ⟨q, hq, rfl⟩ := hx
  obtain ⟨p, hp, rfl⟩ := hd
  rw [← map_mul, QuotientGroup.mk'_apply] at hs ⊢
  rw [hb.isMixedInv_mk_mul_iff hq hp hs, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, Ne,
    Ne, QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff]

theorem not_isMixedInv_of_mem_X (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) : ¬ IsMixedInv x := by
  obtain ⟨q, hq, rfl⟩ := hx
  intro ht
  rw [QuotientGroup.mk'_apply, hb.setting.isMixedInv_mk_iff_mul_self] at ht
  obtain ⟨hqq, hqZ⟩ := ht
  rcases quaternion_eq_of_mul_self hb.partC.quaternion.some hb.partC.mem_left hb.partC.order hq
    hqq with rfl | rfl
  · exact hqZ (one_mem _)
  · exact hqZ hb.setting.centralElt_mem_center

theorem not_isMixedInv_of_mem_D (hb : CaseB1 Q B T L M) {d : J ⧸ Subgroup.center J}
    (hd : d ∈ b1D T L) : ¬ IsMixedInv d := by
  obtain ⟨p, hp, rfl⟩ := hd
  intro ht
  rw [QuotientGroup.mk'_apply, hb.setting.isMixedInv_mk_iff] at ht
  exact ht.2 (hb.partC.unique p hp ht.1 ▸ hb.setting.centralElt_mem_center)

theorem isMixedInv_mul (hb : CaseB1 Q B T L M) {x d : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hd : d ∈ b1D T L) (hx1 : x ≠ 1) (hd2 : orderOf d = 2) :
    IsMixedInv (x * d) := by
  have hdd : d * d = 1 := by rw [← pow_two, ← hd2, pow_orderOf_eq_one]
  have hxd := (hb.commute_of_mem_X_of_mem_D hx hd).eq
  have hs : orderOf (x * d) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hx1 (hb.eq_one_of_mem_X_of_mem_D hx ?_)
    · rw [pow_two]
      calc x * d * (x * d) = x * (d * x) * d := by group
        _ = x * (x * d) * d := by rw [← hxd]
        _ = x * x * (d * d) := by group
        _ = 1 := by rw [hb.mul_self_of_mem_X hx, hdd, mul_one]
    · rw [eq_inv_of_mul_eq_one_left h1]
      exact (b1D T L).inv_mem hd
  refine (hb.isMixedInv_mul_iff hx hd hs).mpr ⟨hx1, fun h1 => ?_⟩
  rw [h1, orderOf_one] at hd2
  exact absurd hd2 (by decide)

theorem isMixedInv_iff_not_mem (hb : CaseB1 Q B T L M) {s : J ⧸ Subgroup.center J}
    (hs : s ∈ b1S T) (hs2 : orderOf s = 2) : IsMixedInv s ↔ s ∉ b1X T L ∧ s ∉ b1D T L := by
  obtain ⟨x, hx, d, hd, rfl⟩ := hb.exists_mul_of_mem_S hs
  rw [hb.isMixedInv_mul_iff hx hd hs2, Subgroup.mul_mem_cancel_left _ hx,
    Subgroup.mul_mem_cancel_right _ hd]
  have hdX : d ∈ b1X T L ↔ d = 1 :=
    ⟨fun h => hb.eq_one_of_mem_X_of_mem_D h hd, fun h => h ▸ one_mem _⟩
  have hxD : x ∈ b1D T L ↔ x = 1 :=
    ⟨fun h => hb.eq_one_of_mem_X_of_mem_D hx h, fun h => h ▸ one_mem _⟩
  rw [hdX, hxD]
  exact and_comm

theorem mem_X_or_mem_D_of_not_isMixedInv (hb : CaseB1 Q B T L M) {s : J ⧸ Subgroup.center J}
    (hs : s ∈ b1S T) (hs2 : orderOf s = 2) (hm : ¬ IsMixedInv s) : s ∈ b1X T L ∨ s ∈ b1D T L := by
  by_contra hno
  push Not at hno
  exact hm ((hb.isMixedInv_iff_not_mem hs hs2).mpr hno)

end CaseB1

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
