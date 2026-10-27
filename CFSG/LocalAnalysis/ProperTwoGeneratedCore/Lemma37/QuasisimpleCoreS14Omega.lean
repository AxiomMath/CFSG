module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreS14Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z : J}

namespace FourGen

theorem oddNormal_le (hz : FourGen Q z) (h : Setting J Q B) {w x : J} (hwB : w ∈ B)
    (hw : w * w = centralElt J) (hwz : w * z = z * w) {N : Subgroup J}
    (hNX : N ≤ quasiNormalizer w) (hXN : quasiNormalizer w ≤ Subgroup.normalizer (N : Set J))
    (hNodd : Odd (Nat.card N)) (hxB : x ∈ B) (hx : x * x = 1) (hxw : x * w = w * x)
    (hxz : x * z * x⁻¹ = centralElt J * z) : N ≤ B := by
  have hzz : z * z = 1 := hz.mul_self
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have he1 : centralElt J ≠ 1 := h.centralElt_ne_one
  have hxz' : x * z ≠ z * x := by
    intro h'
    apply he1
    have h2 : x * z * x⁻¹ = z := by rw [h', mul_inv_cancel_right]
    rw [hxz] at h2
    exact mul_eq_right.mp h2
  obtain ⟨s, hs⟩ : ∃ s, s = x * z := ⟨_, rfl⟩
  have hsz : s * z = x := by rw [hs, mul_assoc, hzz, mul_one]
  have hss : s * s = centralElt J := by
    calc s * s = (x * z * x⁻¹) * z := by rw [hs, hxinv]; group
      _ = centralElt J := by rw [hxz, mul_assoc, hzz, mul_one]
  have hsw : s * w = w * s := by rw [hs, mul_assoc, ← hwz, ← mul_assoc, hxw, mul_assoc]
  have hs_ne : s * z ≠ z * s := by
    intro h'
    apply hxz'
    have h2 : x = z * x * z := by
      calc x = s * z := hsz.symm
        _ = z * s := h'
        _ = z * x * z := by rw [hs, mul_assoc]
    calc x * z = z * x * z * z := by rw [← h2]
      _ = z * x := by rw [mul_assoc, hzz, mul_one]
  have hwz' : w⁻¹ * z = z * w⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hwz, mul_assoc, mul_inv_cancel, mul_one]
  have hcomm_of : ∀ c ∈ Subgroup.center J, s * w ≠ c := by
    intro c hc h'
    apply hs_ne
    have hs' : s = c * w⁻¹ := by rw [← h', mul_inv_cancel_right]
    rw [hs', mul_assoc, hwz', ← mul_assoc, (Subgroup.mem_center_iff.mp hc z).symm, mul_assoc]
  have hswsw : (s * w) * (s * w) = 1 := by
    calc (s * w) * (s * w) = (s * s) * (w * w) := by
          rw [mul_assoc, ← mul_assoc w, ← hsw]; group
      _ = 1 := by rw [hss, hw, h.centralElt_mul_self]
  have hsw1 : s * w ≠ 1 := hcomm_of 1 (Subgroup.center J).one_mem
  have hswe : s * w ≠ centralElt J := hcomm_of _ h.centralElt_mem_center
  have hsw2 : orderOf (s * w) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hswsw) hsw1
  have hzB : z ∈ B := hz.mem_of_setting h
  have hsB : s ∈ B := hs ▸ B.mul_mem hxB hzB
  have hswB : s * w ∈ B := B.mul_mem hsB hwB
  have hx1 : x ≠ 1 := fun h1 => hxz' (by rw [h1, one_mul, mul_one])
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  have hxe : x ≠ centralElt J := fun h1 => hxz' (by rw [h1]; exact (h.commute_centralElt z).eq.symm)
  set π := QuotientGroup.mk' (Subgroup.center J) with hπ
  have hπmem : ∀ c ∈ Subgroup.center J, π c = 1 := fun c hc =>
    (QuotientGroup.eq_one_iff c).mpr hc
  have hsbar : π s * π s = 1 := by rw [← map_mul, hss]; exact hπmem _ h.centralElt_mem_center
  have hzbar : π z * π z = 1 := by rw [← map_mul, hzz, map_one]
  have hszbar : Commute (π s) (π z) := by
    refine (commute_mk_iff s z).mpr ?_
    have : s * z * s⁻¹ * z⁻¹ = x * z * x⁻¹ * z⁻¹ := by rw [hs]; group
    rw [this, hxz, mul_inv_cancel_right]
    exact h.centralElt_mem_center
  have hs1 : π s ≠ 1 := by
    intro h1
    have hsZ : s ∈ Subgroup.center J := (QuotientGroup.eq_one_iff s).mp h1
    have := h.mul_self_of_mem_center hsZ
    rw [hss] at this
    exact he1 this
  have hz1 : π z ≠ 1 := hz.mk_ne_one
  have hsz1 : π s ≠ π z := by
    intro h1
    apply hxz'
    have hxZ : x ∈ Subgroup.center J := by
      rw [← QuotientGroup.eq_one_iff, ← hsz]
      change π (s * z) = 1
      rw [map_mul, h1, hzbar]
    exact Subgroup.mem_center_iff.mp hxZ z |>.symm
  set A := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions (π s) (π z) hsbar hzbar hszbar
    with hA
  have hAK : IsKleinFour A :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions _ _ hsbar hzbar hs1 hz1
      hsz1 hszbar
  have hAmem : ∀ a, a ∈ A ↔ a = π s * π z ∨ a = π s ∨ a = π z ∨ a = 1 := fun a => by
    change a ∈ ({π s * π z, π s, π z, 1} : Set (J ⧸ Subgroup.center J)) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  set Nbar := N.map π with hNbar
  have hsX : s ∈ quasiNormalizer w := h.mem_quasiNormalizer_of_mul_eq hw hsw
  have hzX : z ∈ quasiNormalizer w := h.mem_quasiNormalizer_of_mul_eq hw hwz.symm
  have hnorm : ∀ m ∈ quasiNormalizer w, π m ∈ Subgroup.normalizer (Nbar : Set _) := fun m hm =>
    Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π (hXN hm))
  have hAO : A ≤ Subgroup.normalizer (Nbar : Set _) := by
    intro a ha
    rcases (hAmem a).mp ha with rfl | rfl | rfl | rfl
    · rw [← map_mul]
      exact hnorm _ ((quasiNormalizer w).mul_mem hsX hzX)
    · exact hnorm _ hsX
    · exact hnorm _ hzX
    · exact Subgroup.one_mem _
  have hO : Odd (Nat.card Nbar) := Odd.of_dvd_nat hNodd (Subgroup.card_map_dvd N π)
  have hodd : ∀ n ∈ N, Odd (orderOf n) := fun n hn => by
    have hdvd : orderOf (⟨n, hn⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat hNodd hdvd
  have hcomm : ∀ n ∈ N, ∀ a : J, π n * π a = π a * π n → n * a = a * n := fun n hn a hna =>
    h.mul_comm_of_odd (hodd n hn) ((commute_mk_iff n a).mp hna)
  have hcent : ∀ a ∈ A, a ≠ 1 → Nbar ⊓ Subgroup.centralizer ({a} : Set _) ≤
      B.map π := by
    intro a ha ha1 y hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy.1
    have hyC : π n * a = a * π n := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    refine (h.mk_mem_map_iff n).mpr ?_
    rcases (hAmem a).mp ha with rfl | rfl | rfl | rfl
    · rw [← map_mul, hsz] at hyC
      exact h.centralizer_le_of_ne hxB hx2 hxe
        (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm n hn x hyC))
    · have hns := hcomm n hn s hyC
      have hnw := h.mul_comm_of_odd (hodd n hn) ((h.mem_normalizer_zpowers_iff hw).mp (hNX hn))
      refine h.centralizer_le_of_ne hswB hsw2 hswe
        (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
      rw [← mul_assoc, hns, mul_assoc, hnw, mul_assoc]
    · exact h.centralizer_le_of_ne hzB hz.order (hz.ne_centralElt h)
        (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm n hn z hyC))
    · exact absurd rfl ha1
  have hle := RankOnePair.le_of_kleinFour_centralizers_le hAO hO hcent
  intro n hn
  exact (h.mk_mem_map_iff n).mp (hle (Subgroup.mem_map_of_mem π hn))

theorem mem_fourGroup_of_commute (hz : FourGen Q z) (h : Setting J Q B) {w : J} (hwB : w ∈ B)
    (hw : w * w = centralElt J) (hwz : w * z = z * w)
    (hrank : CFSG.Open.pRank 2 (quasiNormalizer w) ≤ 2) {N : Subgroup J}
    (hNX : N ≤ quasiNormalizer w) (hXN : quasiNormalizer w ≤ Subgroup.normalizer (N : Set J))
    (hNodd : Odd (Nat.card N)) (hNB : ¬ N ≤ B) {x : J} (hxQ : x ∈ (Q : Subgroup J))
    (hxw : x * w = w * x) (hx : x * x = 1) : x ∈ fourGroup z := by
  by_contra hxV
  rcases hz.conj_eq h hxQ with h1 | h1
  · have hxz : x * z = z * x := by
      calc x * z = x * z * x⁻¹ * x := by group
        _ = z * x := by rw [h1]
    have h3 := hz.three_le_pRank h (h.centralElt_mem_quasiNormalizer w)
      (h.mem_quasiNormalizer_of_mul_eq hw hwz.symm) (h.mem_quasiNormalizer_of_mul_eq hw hxw) hx
      hxz hxV
    omega
  · exact hNB (hz.oddNormal_le h hwB hw hwz hNX hXN hNodd (h.sylow_le hxQ) hx hxw h1)

end FourGen

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
