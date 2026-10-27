module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step4

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Cat8

structure Q3Facts : Prop where
  simple : CFSec8Simple
  inner : CFSec8InnerCentralizer
  out : CFQ3Out
  l0 : CFQ3L0
  f2 : CFQ3F2
  conf : CFQ3Conf
  diag : CFA6Diag
  sylowCent : CFA6SylowCent
  noComm : CFA6NoComm
  innerInv : CFA6InnerInv
  noNilp : CFQ3NoNilp

end Cat8

namespace Eight

theorem card_conjOrbit_mul {G : Type*} [Group G] [Finite G] (N : Subgroup G) (w : G) :
    (Cat8.conjOrbit N w).ncard * Nat.card ↥(N ⊓ centralizer ({w} : Set G)) = Nat.card N := by
  let _ : MulAction ↥N G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp N.subtype)
  have hsmul : ∀ (n : ↥N) (y : G), n • y = (n : G) * y * (n : G)⁻¹ := fun _ _ => rfl
  have horb : MulAction.orbit ↥N w = Cat8.conjOrbit N w := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨(n : G)⁻¹, inv_mem n.2, ?_⟩
      change _ = n • w
      rw [hsmul, inv_inv]
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨n⁻¹, inv_mem hn⟩, ?_⟩
      change (⟨n⁻¹, inv_mem hn⟩ : ↥N) • w = _
      rw [hsmul]
      simp
  have hstab : MulAction.stabilizer ↥N w = (centralizer ({w} : Set G)).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc (n : G) * w = ((n : G) * w * (n : G)⁻¹) * n := by group
        _ = w * n := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  have h1 := card_mul_index (MulAction.stabilizer ↥N w)
  rw [MulAction.index_stabilizer, horb, hstab, ← card_map_of_injective N.subtype_injective,
    subgroupOf_map_subtype, inf_comm] at h1
  rw [mul_comm]
  exact h1

theorem conj_mem_of_generators {G : Type*} [Group G] {C : Subgroup G} {s u v w : G}
    (hu : s⁻¹ * u * s ∈ C) (hv : s⁻¹ * v * s ∈ C) (hw : s⁻¹ * w * s ∈ C) :
    ∀ c ∈ zpowers u ⊔ zpowers v ⊔ zpowers w, s⁻¹ * c * s ∈ C := by
  have key : ∀ t : G, s⁻¹ * t * s ∈ C → t ∈ C.comap (MulAut.conj s⁻¹).toMonoidHom := by
    intro t ht
    rw [mem_comap]
    simpa [MulAut.conj_apply] using ht
  have hle : zpowers u ⊔ zpowers v ⊔ zpowers w ≤ C.comap (MulAut.conj s⁻¹).toMonoidHom :=
    sup_le (sup_le (zpowers_le.mpr (key u hu)) (zpowers_le.mpr (key v hv)))
      (zpowers_le.mpr (key w hw))
  intro c hc
  have := hle hc
  rw [mem_comap] at this
  simpa [MulAut.conj_apply] using this

end Eight

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

namespace Q3Data

variable (d : Q3Data H)
include d

theorem Q_le_centralizer_tau (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    h.Q ≤ centralizer ({d.tau} : Set X) := by
  rw [d.Q_eq_sup]
  refine sup_le (fun q hq => mem_centralizer_singleton_iff.mpr (d.tau_comm_Q1 hCF1 hCF2 hq).symm)
    ?_
  rw [d.B_eq, zpowers_le, mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp d.b_mem_centralizer_M3 _ d.tau_mem.2).symm

theorem z_comm_a : d.z * h.a = h.a * d.z :=
  mem_centralizer_singleton_iff.mp (h.J_le (h.sec8_D_le_J d.z_D))

theorem Q_le_centralizer_z (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) : h.Q ≤ centralizer ({d.z} : Set X) := by
  rw [d.Q_eq_sup, d.Q1_eq hCF1 hCF2 hq hL0]
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · intro w hw
    exact mem_centralizer_singleton_iff.mpr (d.z_comm w hw).symm
  · rw [zpowers_le, mem_centralizer_singleton_iff]
    exact d.tau_comm_z hCF1 hCF2
  · rw [zpowers_le, mem_centralizer_singleton_iff]
    exact d.z_comm_a.symm
  · rw [d.B_eq, zpowers_le, mem_centralizer_singleton_iff]
    exact d.b_comm_z

abbrev N0 : Subgroup X := h.Q ⊔ zpowers h.x ⊔ zpowers d.g

abbrev Z3 : Subgroup X := zpowers h.a ⊔ zpowers d.tau ⊔ zpowers d.z

theorem N0_le_centralizer_z (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    d.N0 ≤ centralizer ({d.z} : Set X) := by
  refine sup_le (sup_le (d.Q_le_centralizer_z hq hF.simple hF.inner hF.l0) ?_) ?_
  · rw [zpowers_le, mem_centralizer_singleton_iff]
    have := d.z_x hq hF.simple hF.inner hF.l0 hF.sylowCent
    calc h.x * d.z = h.x * (h.x⁻¹ * d.z * h.x) := by rw [this]
      _ = d.z * h.x := by group
  · rw [zpowers_le, mem_centralizer_singleton_iff]
    have := d.z_g hF.simple hF.inner
    calc d.g * d.z = d.g * (d.g⁻¹ * d.z * d.g) := by rw [this]
      _ = d.z * d.g := by group

theorem mem_Z3 (hF : Cat8.Q3Facts) {y : X} (hy : y ∈ d.Z3) :
    y = 1 ∨ y = h.a ∨ y = d.tau ∨ y = h.a * d.tau ∨ y = d.z ∨ y = h.a * d.z ∨
      y = d.tau * d.z ∨ y = h.a * d.tau * d.z := by
  have hza : d.z ∈ normalizer ((zpowers h.a ⊔ zpowers d.tau : Subgroup X) : Set X) := by
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w hw => ?_)
    have hle : zpowers h.a ⊔ zpowers d.tau ≤ centralizer ({d.z} : Set X) := by
      refine sup_le ?_ ?_ <;> rw [zpowers_le, mem_centralizer_singleton_iff]
      · exact d.z_comm_a.symm
      · exact d.tau_comm_z hF.simple hF.inner
    exact mem_centralizer_singleton_iff.mp (hle hw)
  have hta : d.tau ∈ normalizer ((zpowers h.a : Subgroup X) : Set X) := by
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w hw => ?_)
    have hle : zpowers h.a ≤ centralizer ({d.tau} : Set X) := by
      rw [zpowers_le, mem_centralizer_singleton_iff]
      exact d.tau_comm_a.symm
    exact mem_centralizer_singleton_iff.mp (hle hw)
  obtain ⟨m, hm, hy⟩ := Eight.mem_sup_zpowers_cases hza d.z_sq hy
  obtain ⟨m', hm', hm⟩ := Eight.mem_sup_zpowers_cases hta d.tau_sq hm
  rcases mem_zpowers_two h.orderOf_a hm' with rfl | rfl <;> rcases hm with rfl | rfl <;>
    rcases hy with rfl | rfl <;> simp

theorem N0_le_normalizer_Z3 (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    d.N0 ≤ normalizer (d.Z3 : Set X) := by
  have haZ : h.a ∈ d.Z3 := mem_sup_left (mem_sup_left (mem_zpowers _))
  have htZ : d.tau ∈ d.Z3 := mem_sup_left (mem_sup_right (mem_zpowers _))
  have hzZ : d.z ∈ d.Z3 := mem_sup_right (mem_zpowers _)
  have hconj : ∀ s : X, s⁻¹ * h.a * s ∈ d.Z3 → s⁻¹ * d.tau * s ∈ d.Z3 →
      s⁻¹ * d.z * s ∈ d.Z3 → s ∈ normalizer (d.Z3 : Set X) := fun s h1 h2 h3 =>
    Eight.mem_normalizer_of_conj_mem (Eight.conj_mem_of_generators h1 h2 h3)
  have hfix : ∀ s : X, s * h.a = h.a * s → s * d.tau = d.tau * s → s * d.z = d.z * s →
      s ∈ normalizer (d.Z3 : Set X) := by
    intro s ha ht hz
    refine hconj s ?_ ?_ ?_
    · rwa [mul_assoc, ← ha, inv_mul_cancel_left]
    · rwa [mul_assoc, ← ht, inv_mul_cancel_left]
    · rwa [mul_assoc, ← hz, inv_mul_cancel_left]
  refine sup_le (sup_le ?_ ?_) ?_
  · intro q hq'
    exact hfix q (H.comm_a_of_mem_Q hq')
      (mem_centralizer_singleton_iff.mp (d.Q_le_centralizer_tau hF.simple hF.inner hq'))
      (mem_centralizer_singleton_iff.mp
        (d.Q_le_centralizer_z hq hF.simple hF.inner hF.l0 hq'))
  · rw [zpowers_le]
    refine hconj h.x ?_ ?_ ?_
    · rw [H.a_x]
      exact haZ
    · rw [d.tau_x_eq hq hF.simple hF.inner hF.out hF.l0 hF.diag hF.sylowCent hF.noComm
        hF.innerInv]
      exact mul_mem htZ hzZ
    · rw [d.z_x hq hF.simple hF.inner hF.l0 hF.sylowCent]
      exact hzZ
  · rw [zpowers_le]
    refine hconj d.g ?_ ?_ ?_
    · rw [d.a_g]
      exact mul_mem haZ htZ
    · rw [d.tau_g]
      exact htZ
    · rw [d.z_g hF.simple hF.inner]
      exact hzZ

theorem tz_eq_conj (hq : h.IsQ3) (hF : Cat8.Q3Facts) : h.x⁻¹ * d.tau * h.x = d.tau * d.z :=
  d.tau_x_eq hq hF.simple hF.inner hF.out hF.l0 hF.diag hF.sylowCent hF.noComm hF.innerInv

theorem exists_z_conj_tz (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    ∃ c : X, c⁻¹ * d.z * c = d.tau * d.z := by
  obtain ⟨k, -, hk⟩ := d.z_conj_tau hq hF.simple hF.inner hF.out
  refine ⟨k * h.x, ?_⟩
  rw [show (k * h.x)⁻¹ * d.z * (k * h.x) = h.x⁻¹ * (k⁻¹ * d.z * k) * h.x by group, hk,
    d.tz_eq_conj hq hF]

theorem a_not_conj_Z3 (hq : h.IsQ3) (hF : Cat8.Q3Facts) (w : X) :
    w⁻¹ * h.a * w ≠ 1 ∧ w⁻¹ * h.a * w ≠ d.tau ∧ w⁻¹ * h.a * w ≠ d.z ∧
      w⁻¹ * h.a * w ≠ d.tau * d.z := by
  have hntz := d.a_not_conj_tz hq hF.simple hF.inner hF.out
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_, hntz w⟩
  · have : h.a = 1 := by
      calc h.a = w * (w⁻¹ * h.a * w) * w⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have h2 := h.orderOf_a
    rw [this, orderOf_one] at h2
    norm_num at h2
  · apply hntz (w * h.x)
    rw [show (w * h.x)⁻¹ * h.a * (w * h.x) = h.x⁻¹ * (w⁻¹ * h.a * w) * h.x by group, h1,
      d.tz_eq_conj hq hF]
  · obtain ⟨c, hc⟩ := d.exists_z_conj_tz hq hF
    apply hntz (w * c)
    rw [show (w * c)⁻¹ * h.a * (w * c) = c⁻¹ * (w⁻¹ * h.a * w) * c by group, h1, hc]

theorem conjOrbit_N0_a (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    Cat8.conjOrbit d.N0 h.a = {h.a, h.a * d.tau, h.a * d.tau * d.z, h.a * d.z} := by
  have hNZ := d.N0_le_normalizer_Z3 hq hF
  have haZ : h.a ∈ d.Z3 := mem_sup_left (mem_sup_left (mem_zpowers _))
  have hgN : d.g ∈ d.N0 := mem_sup_right (mem_zpowers _)
  have hxN : h.x ∈ d.N0 := mem_sup_left (mem_sup_right (mem_zpowers _))
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hy : n⁻¹ * h.a * n ∈ d.Z3 := by
      have := (mem_normalizer_iff.mp (inv_mem (hNZ hn)) h.a).mp haZ
      rwa [inv_inv] at this
    obtain ⟨h1, h2, h3, h4⟩ := d.a_not_conj_Z3 hq hF n
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases d.mem_Z3 hF hy with h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5
    · exact absurd h5 h1
    · exact Or.inl h5
    · exact absurd h5 h2
    · exact Or.inr (Or.inl h5)
    · exact absurd h5 h3
    · exact Or.inr (Or.inr (Or.inr h5))
    · exact absurd h5 h4
    · exact Or.inr (Or.inr (Or.inl h5))
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hagx : (d.g * h.x)⁻¹ * h.a * (d.g * h.x) = h.a * d.tau * d.z := by
      rw [show (d.g * h.x)⁻¹ * h.a * (d.g * h.x) = h.x⁻¹ * (d.g⁻¹ * h.a * d.g) * h.x by group,
        d.a_g, show h.x⁻¹ * (h.a * d.tau) * h.x = (h.x⁻¹ * h.a * h.x) * (h.x⁻¹ * d.tau * h.x) by
          group, H.a_x, d.tz_eq_conj hq hF]
      exact (mul_assoc _ _ _).symm
    rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, one_mem _, by group⟩
    · exact ⟨d.g, hgN, d.a_g⟩
    · exact ⟨d.g * h.x, mul_mem hgN hxN, hagx⟩
    · refine ⟨d.g * h.x * d.g, mul_mem (mul_mem hgN hxN) hgN, ?_⟩
      rw [show (d.g * h.x * d.g)⁻¹ * h.a * (d.g * h.x * d.g) =
        d.g⁻¹ * ((d.g * h.x)⁻¹ * h.a * (d.g * h.x)) * d.g by group, hagx,
        show d.g⁻¹ * (h.a * d.tau * d.z) * d.g =
          (d.g⁻¹ * h.a * d.g) * (d.g⁻¹ * d.tau * d.g) * (d.g⁻¹ * d.z * d.g) by group,
        d.a_g, d.tau_g, d.z_g hF.simple hF.inner, mul_assoc h.a d.tau d.tau, d.tau_sq, mul_one]

theorem ncard_orbit (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    ({h.a, h.a * d.tau, h.a * d.tau * d.z, h.a * d.z} : Set X).ncard = 4 := by
  have ht1 := d.tau_ne_one
  have hz1 := d.z_ne
  have htz := d.tau_ne_z hq hF.simple hF.inner hF.l0
  have htz1 : d.tau * d.z ≠ 1 := by
    intro h1
    apply htz
    calc d.tau = d.tau * d.z * d.z := by rw [mul_assoc, d.z_sq, mul_one]
      _ = d.z := by rw [h1, one_mul]
  have e1 : h.a ≠ h.a * d.tau := fun h1 => ht1 (by simpa using h1.symm)
  have e2 : h.a ≠ h.a * d.tau * d.z := fun h1 => htz1 (by
    rw [mul_assoc] at h1
    simpa using h1.symm)
  have e3 : h.a ≠ h.a * d.z := fun h1 => hz1 (by simpa using h1.symm)
  have e4 : h.a * d.tau ≠ h.a * d.tau * d.z := fun h1 => hz1 (by simpa using h1.symm)
  have e5 : h.a * d.tau ≠ h.a * d.z := fun h1 => htz (mul_left_cancel h1)
  have e6 : h.a * d.tau * d.z ≠ h.a * d.z := fun h1 => ht1 (by
    rw [mul_assoc] at h1
    have h2 := mul_left_cancel h1
    simpa using h2)
  rw [Set.ncard_insert_of_notMem (by simp [e1, e2, e3]),
    Set.ncard_insert_of_notMem (by simp [e4, e5]), Set.ncard_pair e6]

theorem card_Q_sup_x (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    Nat.card ↥(h.Q ⊔ zpowers h.x) = 128 := by
  have hxS := h.x_mem
  have hxo : orderOf h.x = 2 := (gsUnbalancingTriple_iff.mp H.maximal.1).2.1
  have hQn : (h.Q.subgroupOf h.S).Normal := by
    have := Subgroup.normal_of_index_eq_two d.index_Q
    rwa [show (centralizer ({d.b} : Set X)).subgroupOf h.S = h.Q.subgroupOf h.S by
      rw [d.Q_eq, inf_subgroupOf_left]] at this
  have hxQ' : ∀ q ∈ h.Q, h.x * q * h.x⁻¹ ∈ h.Q := fun q hq =>
    hQn.conj_mem ⟨q, (inf_le_left : h.Q ≤ h.S) hq⟩ hq ⟨h.x, hxS⟩
  have hxN : zpowers h.x ≤ normalizer (h.Q : Set X) := by
    refine le_normalizer_of_conj fun y hy w hw => ?_
    rcases mem_zpowers_two hxo hy with rfl | rfl
    · simpa using hw
    · exact hxQ' w hw
  have hxQ : h.x ∉ h.Q := by
    intro hxQ
    rw [d.Q_eq] at hxQ
    have h1 := mem_centralizer_singleton_iff.mp hxQ.2
    have h2 : h.x⁻¹ * d.b * h.x = d.b := by rw [mul_assoc, ← h1, inv_mul_cancel_left]
    rw [d.xbx] at h2
    have h3 : h.a = 1 := by
      calc h.a = h.a * d.b * d.b⁻¹ := by group
        _ = 1 := by rw [h2, mul_inv_cancel]
    have h4 := h.orderOf_a
    rw [h3, orderOf_one] at h4
    norm_num at h4
  have hdisj : Disjoint h.Q (zpowers h.x) := by
    rw [disjoint_iff, eq_bot_iff]
    intro y hy
    rcases mem_zpowers_two hxo (mem_inf.mp hy).2 with rfl | rfl
    · exact one_mem _
    · exact absurd (mem_inf.mp hy).1 hxQ
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hxN hdisj,
    d.card_Q hCF1 hCF2, Nat.card_zpowers, hxo]

theorem dvd_card_N0 (hq : h.IsQ3) (hF : Cat8.Q3Facts) : 512 ∣ Nat.card d.N0 := by
  have h1 := Eight.card_conjOrbit_mul d.N0 h.a
  rw [d.conjOrbit_N0_a hq hF, d.ncard_orbit hq hF] at h1
  have hle : h.Q ⊔ zpowers h.x ≤ d.N0 ⊓ centralizer ({h.a} : Set X) := by
    refine le_inf le_sup_left (sup_le ?_ ?_)
    · intro q hq'
      exact mem_centralizer_singleton_iff.mpr (H.comm_a_of_mem_Q hq')
    · rw [zpowers_le, mem_centralizer_singleton_iff]
      calc h.x * h.a = h.x * (h.x⁻¹ * h.a * h.x) := by rw [H.a_x]
        _ = h.a * h.x := by group
  have h2 := card_dvd_of_le hle
  rw [d.card_Q_sup_x hF.simple hF.inner] at h2
  rw [← h1]
  obtain ⟨k, hk⟩ := h2
  rw [hk]
  exact ⟨k, by ring⟩

theorem exists_two_subgroup_centralizer_z (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    ∃ P : Subgroup X, P ≤ centralizer ({d.z} : Set X) ∧ IsPGroup 2 P ∧ Nat.card P = 512 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : 2 ^ 9 ∣ Nat.card ↥(centralizer ({d.z} : Set X)) :=
    (d.dvd_card_N0 hq hF).trans (card_dvd_of_le (d.N0_le_centralizer_z hq hF))
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 h1
  refine ⟨K.map (centralizer ({d.z} : Set X)).subtype, map_subtype_le _, ?_, ?_⟩
  · refine IsPGroup.of_card (n := 9) ?_
    rw [card_map_of_injective (subtype_injective _), hK]
  · rw [card_map_of_injective (subtype_injective _), hK]
    norm_num

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
