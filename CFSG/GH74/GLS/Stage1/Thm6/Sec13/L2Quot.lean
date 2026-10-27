module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.CenMod
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2Grp

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

structure NormIn (N M : Subgroup G) : Prop where
  le : N ≤ M
  norm : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N

theorem NormIn.normal {N M : Subgroup G} (h : NormIn N M) : (N.subgroupOf M).Normal :=
  (normal_subgroupOf_iff h.le).2 (fun n m hn hm => h.norm m hm n hn)

section Bridge

variable {M N : Subgroup G} [(N.subgroupOf M).Normal]

abbrev qm (M N : Subgroup G) [(N.subgroupOf M).Normal] : ↥M →* ↥M ⧸ N.subgroupOf M :=
  QuotientGroup.mk' _

theorem qm_eq_one {m : ↥M} : qm M N m = 1 ↔ (m : G) ∈ N := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem qm_eq_iff {a b : ↥M} : qm M N a = qm M N b ↔ (a : G)⁻¹ * b ∈ N := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
  rfl

omit [(N.subgroupOf M).Normal] in
theorem card_QR [Finite G] (hNM : N ≤ M) :
    Nat.card (↥M ⧸ N.subgroupOf M) * Nat.card N = Nat.card M := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf M)
  have e : Nat.card (N.subgroupOf M) = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe hNM).toEquiv
  rw [e] at h
  exact h.symm

end Bridge


section Bridge2

variable {M N : Subgroup G} [(N.subgroupOf M).Normal]

abbrev phiE (E : Subgroup G) (hEM : E ≤ M) : ↥E →* ↥M ⧸ N.subgroupOf M :=
  (qm M N).comp (Subgroup.inclusion hEM)

theorem mem_range_phiE {E : Subgroup G} (hEM : E ≤ M) {q : ↥M ⧸ N.subgroupOf M} :
    q ∈ (phiE (N := N) E hEM).range ↔ ∃ e ∈ E, ∃ he : e ∈ M, qm M N ⟨e, he⟩ = q := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.1, e.2, hEM e.2, rfl⟩
  · rintro ⟨e, he, heM, rfl⟩
    exact ⟨⟨e, he⟩, rfl⟩

theorem card_phiE [Finite G] {E : Subgroup G} (hNE : N ≤ E) (hEM : E ≤ M) :
    Nat.card E = Nat.card N * Nat.card (phiE (N := N) E hEM).range := by
  have hker : (phiE (N := N) E hEM).ker = N.subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      have := qm_eq_one.1 h
      exact this
    · intro h
      exact qm_eq_one.2 h
  have h1 := Subgroup.card_ker_mul_card_range (phiE (N := N) E hEM)
  rw [hker] at h1
  have e : Nat.card (N.subgroupOf E) = Nat.card N := Nat.card_congr (subgroupOfEquivOfLe hNE).toEquiv
  rw [e] at h1
  exact h1.symm

end Bridge2


section Bridge3

variable {M N : Subgroup G} [(N.subgroupOf M).Normal]

theorem card_cenMod_eq [Finite G] (hNM : N ≤ M) (hN : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) {z : G}
    (hz : z ∈ M) :
    Nat.card (cenMod M N z hN) = Nat.card N *
      Nat.card ↥(centralizer ({qm M N ⟨z, hz⟩} : Set (↥M ⧸ N.subgroupOf M))) := by
  classical
  let z' : ↥M := ⟨z, hz⟩
  let C : Subgroup (↥M ⧸ N.subgroupOf M) :=
    centralizer ({qm M N z'} : Set (↥M ⧸ N.subgroupOf M))
  let K' : Subgroup ↥M := C.comap (qm M N)
  have hK'card : Nat.card K' = Nat.card (N.subgroupOf M) * Nat.card C := by
    have h1 := Subgroup.card_mul_index K'
    have h2 : K'.index = C.index :=
      Subgroup.index_comap_of_surjective C (QuotientGroup.mk'_surjective _)
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf M)
    have h4 := Subgroup.card_mul_index C
    have hpos : 0 < C.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card K' * C.index = Nat.card K' * K'.index := by rw [h2]
      _ = Nat.card ↥M := h1
      _ = Nat.card (↥M ⧸ N.subgroupOf M) * Nat.card (N.subgroupOf M) := h3
      _ = (Nat.card C * C.index) * Nat.card (N.subgroupOf M) := by rw [h4]
      _ = Nat.card (N.subgroupOf M) * Nat.card C * C.index := by ring
  have hmem : ∀ g : ↥M, g ∈ K' ↔ (g : G) ∈ cenMod M N z hN := by
    intro g
    show qm M N g ∈ C ↔ _
    rw [mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [mem_cenMod]
    refine ⟨fun hc => ⟨g.2, ?_⟩, fun hc => ?_⟩
    · have h1 : ⁅qm M N z', qm M N g⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 hc
      rw [← map_commutatorElement, qm_eq_one] at h1
      simp only [commutatorElement_def] at h1
      exact h1
    · have h1 : (⁅z', g⁆ : ↥M) ∈ N.subgroupOf M := by
        rw [mem_subgroupOf]
        simp only [commutatorElement_def]
        exact hc.2
      have h2 : qm M N ⁅z', g⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h1
      rw [map_commutatorElement] at h2
      exact commutatorElement_eq_one_iff_mul_comm.1 h2
  have hcm : Nat.card (cenMod M N z hN) = Nat.card K' :=
    Nat.card_congr
      { toFun := fun g => ⟨⟨g.1, g.2.1⟩, (hmem _).2 g.2⟩
        invFun := fun k => ⟨k.1.1, (hmem k.1).1 k.2⟩
        left_inv := fun g => rfl
        right_inv := fun k => rfl }
  have hN'card : Nat.card (N.subgroupOf M) = Nat.card N :=
    Nat.card_congr (subgroupOfEquivOfLe hNM).toEquiv
  rw [hcm, hK'card, hN'card]

end Bridge3


section CyclicCentral

variable {R : Type} [Group R]

theorem cyclic_unique_invol {C : Type} [Group C] [Finite C] [IsCyclic C] {w w' : C} (hw : w * w = 1)
    (hw' : w' * w' = 1) (h1 : w ≠ 1) (h1' : w' ≠ 1) : w = w' := by
  classical
  have : Fintype C := Fintype.ofFinite C
  by_contra hne
  have hc := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, w, w'} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · rw [pow_two]; exact hw
    · rw [pow_two]; exact hw'
  have hcard : ({1, w, w'} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hne
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1.symm, h1'.symm⟩
  have := Finset.card_le_card hsub
  omega

theorem exists_cyclic_index_two_central [Finite R] (hR : IsPGroup 2 R) {z : R} (hzz : z * z = 1)
    (hz1 : z ≠ 1) (hC : Nat.card ↥(centralizer ({z} : Set R)) ≤ 4) (h8 : 8 ≤ Nat.card R) :
    ∃ a : R, orderOf a * 2 = Nat.card R ∧ z ∉ zpowers a ∧
      ∀ w ∈ zpowers a, w * w = 1 → ∀ r : R, r * w = w * r := by
  obtain ⟨a, ha, hza⟩ := exists_cyclic_index_two (Nat.card R) R rfl hR z hzz hz1 hC h8
  refine ⟨a, ha, hza, ?_⟩
  have hindex : (zpowers a).index = 2 := by
    have h := Subgroup.card_mul_index (zpowers a)
    rw [Nat.card_zpowers] at h
    have hpos : 0 < orderOf a := by
      have : 0 < Nat.card R := Nat.card_pos
      omega
    exact Nat.eq_of_mul_eq_mul_left hpos (by omega)
  have hnorm : (zpowers a).Normal := normal_of_index_eq_two hindex
  intro w hw hww r
  by_cases hw1 : w = 1
  · rw [hw1]; simp
  · have hw' : r * w * r⁻¹ ∈ zpowers a := hnorm.conj_mem w hw r
    have hw'2 : (r * w * r⁻¹) * (r * w * r⁻¹) = 1 := by
      calc (r * w * r⁻¹) * (r * w * r⁻¹) = r * (w * w) * r⁻¹ := by group
        _ = 1 := by rw [hww]; group
    have hw'1 : r * w * r⁻¹ ≠ 1 := by
      intro h
      apply hw1
      have : w = r⁻¹ * (r * w * r⁻¹) * r := by group
      rw [this, h]; group
    have := cyclic_unique_invol (C := ↥(zpowers a)) (w := ⟨w, hw⟩) (w' := ⟨r * w * r⁻¹, hw'⟩)
      (Subtype.ext (by simpa using hww)) (Subtype.ext (by simpa using hw'2))
      (fun h => hw1 (congrArg Subtype.val h)) (fun h => hw'1 (congrArg Subtype.val h))
    have h2 : w = r * w * r⁻¹ := congrArg Subtype.val this
    calc r * w = (r * w * r⁻¹) * r := by group
      _ = w * r := by rw [← h2]

end CyclicCentral


section AmbientM

variable {M N : Subgroup G}

theorem ambient_cyclic_index_two [Finite G] (hN : NormIn N M) (h2 : IsPGroup 2 ↥M) {z : G}
    (hzM : z ∈ M) (hzz : z * z ∈ N) (hzN : z ∉ N)
    (hC : Nat.card (cenMod M N z hN.norm) ≤ 4 * Nat.card N)
    (hbig : 8 * Nat.card N ≤ Nat.card M) :
    ∃ Q : Subgroup G, N ≤ Q ∧ Q ≤ M ∧ (∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) ∧
      Q.relIndex M = 2 ∧ z ∉ Q ∧ ∀ u ∈ Q, u * u ∈ N → ∀ s ∈ M, u * s * u⁻¹ * s⁻¹ ∈ N := by
  have := hN.normal
  have hR2 : IsPGroup 2 (↥M ⧸ N.subgroupOf M) := h2.to_quotient _
  let z' : ↥M := ⟨z, hzM⟩
  have hzb2 : qm M N z' * qm M N z' = 1 := by
    rw [← map_mul]
    exact qm_eq_one.2 (by simpa using hzz)
  have hzb1 : qm M N z' ≠ 1 := fun h => hzN (qm_eq_one.1 h)
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hCR : Nat.card ↥(centralizer ({qm M N z'} : Set (↥M ⧸ N.subgroupOf M))) ≤ 4 := by
    have h := card_cenMod_eq hN.le hN.norm hzM
    rw [h] at hC
    have : Nat.card N * Nat.card ↥(centralizer ({qm M N z'} : Set (↥M ⧸ N.subgroupOf M))) ≤
        Nat.card N * 4 := by linarith
    exact Nat.le_of_mul_le_mul_left this hNpos
  have hRcard : 8 ≤ Nat.card (↥M ⧸ N.subgroupOf M) := by
    have h := card_QR (M := M) hN.le
    by_contra hlt
    push Not at hlt
    have : Nat.card (↥M ⧸ N.subgroupOf M) * Nat.card N ≤ 7 * Nat.card N :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨a, ha, hza, hcent⟩ := exists_cyclic_index_two_central hR2 hzb2 hzb1 hCR hRcard
  have hindex : (zpowers a).index = 2 := by
    have h := Subgroup.card_mul_index (zpowers a)
    rw [Nat.card_zpowers] at h
    have hpos : 0 < orderOf a := by
      have : 0 < Nat.card (↥M ⧸ N.subgroupOf M) := Nat.card_pos
      omega
    exact Nat.eq_of_mul_eq_mul_left hpos (by omega)
  have hnorm : (zpowers a).Normal := normal_of_index_eq_two hindex
  let X : Subgroup ↥M := (zpowers a).comap (qm M N)
  let Q : Subgroup G := X.map M.subtype
  have hmemQ : ∀ m : G, m ∈ Q ↔ ∃ hm : m ∈ M, qm M N ⟨m, hm⟩ ∈ zpowers a := by
    intro m
    constructor
    · rintro ⟨m', hm', rfl⟩
      exact ⟨m'.2, hm'⟩
    · rintro ⟨hm, h⟩
      exact ⟨⟨m, hm⟩, h, rfl⟩
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [hmemQ]
    refine ⟨hN.le hn, ?_⟩
    have h1 : qm M N ⟨n, hN.le hn⟩ = 1 := (qm_eq_one (M := M) (N := N) (m := ⟨n, hN.le hn⟩)).2 hn
    rw [h1]
    exact one_mem _
  · rintro _ ⟨m', -, rfl⟩
    exact m'.2
  · intro g hg q hq
    obtain ⟨hqM, hq'⟩ := (hmemQ q).1 hq
    rw [hmemQ]
    refine ⟨M.mul_mem (M.mul_mem hg hqM) (M.inv_mem hg), ?_⟩
    have h := hnorm.conj_mem _ hq' (qm M N ⟨g, hg⟩)
    have e : qm M N ⟨g * q * g⁻¹, M.mul_mem (M.mul_mem hg hqM) (M.inv_mem hg)⟩ =
        qm M N ⟨g, hg⟩ * qm M N ⟨q, hqM⟩ * (qm M N ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [e]
    exact h
  · have hX : Q.subgroupOf M = X := by
      ext m
      rw [mem_subgroupOf, hmemQ]
      constructor
      · rintro ⟨hm, h⟩
        exact h
      · intro h
        exact ⟨m.2, h⟩
    show (Q.subgroupOf M).index = 2
    rw [hX]
    exact (Subgroup.index_comap_of_surjective (zpowers a) (QuotientGroup.mk'_surjective _)).trans hindex
  · intro hz
    obtain ⟨hzM', h⟩ := (hmemQ z).1 hz
    exact hza h
  · intro u hu huu s hs
    obtain ⟨huM, hu'⟩ := (hmemQ u).1 hu
    have hw2 : qm M N ⟨u, huM⟩ * qm M N ⟨u, huM⟩ = 1 := by
      rw [← map_mul]
      exact qm_eq_one.2 (by simpa using huu)
    have h1 := hcent _ hu' hw2 (qm M N ⟨s, hs⟩)
    have h2 : ⁅qm M N ⟨u, huM⟩, qm M N ⟨s, hs⟩⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 h1.symm
    rw [← map_commutatorElement, qm_eq_one] at h2
    exact h2

end AmbientM


section AmbientD

variable {M N : Subgroup G}

theorem ambient_klein [Finite G] {K : Subgroup G} (hN : NormIn N M) (h2 : IsPGroup 2 ↥M) {z : G}
    (hzM : z ∈ M) (hzz : z * z ∈ N) (hzN : z ∉ N)
    (hC : Nat.card (cenMod M N z hN.norm) ≤ 4 * Nat.card N)
    (hKM : K ≤ M) (hNK : N ≤ K) (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hKsq : ∀ k ∈ K, k * k ∈ N) (hKc : ∀ k ∈ K, ∀ l ∈ K, k * l * k⁻¹ * l⁻¹ ∈ N)
    (hKz : ∃ k ∈ K, z * k * z⁻¹ * k⁻¹ ∉ N) :
    z ∉ K ∧ Nat.card K = 4 * Nat.card N ∧ (∀ r ∈ M, r ∈ K ∨ r * z ∈ K) ∧
      Nat.card (cenMod K N z (fun k hk n hn => hN.norm k (hKM hk) n hn)) = 2 * Nat.card N := by
  have := hN.normal
  have hR2 : IsPGroup 2 (↥M ⧸ N.subgroupOf M) := h2.to_quotient _
  let z' : ↥M := ⟨z, hzM⟩
  have hzb2 : qm M N z' * qm M N z' = 1 := by
    rw [← map_mul]
    exact qm_eq_one.2 (by simpa using hzz)
  have hzb1 : qm M N z' ≠ 1 := fun h => hzN (qm_eq_one.1 h)
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hCR : Nat.card ↥(centralizer ({qm M N z'} : Set (↥M ⧸ N.subgroupOf M))) ≤ 4 := by
    have h := card_cenMod_eq hN.le hN.norm hzM
    rw [h] at hC
    have : Nat.card N * Nat.card ↥(centralizer ({qm M N z'} : Set (↥M ⧸ N.subgroupOf M))) ≤
        Nat.card N * 4 := by linarith
    exact Nat.le_of_mul_le_mul_left this hNpos
  let Kb : Subgroup (↥M ⧸ N.subgroupOf M) := (phiE (N := N) K hKM).range
  have hKb : ∀ k : G, ∀ hk : k ∈ K, qm M N ⟨k, hKM hk⟩ ∈ Kb := fun k hk => ⟨⟨k, hk⟩, rfl⟩
  have hKbmem : ∀ q, q ∈ Kb ↔ ∃ k : ↥K, qm M N ⟨k.1, hKM k.2⟩ = q := fun q => Iff.rfl
  have hconjK : ∀ (m : ↥M) (k : G) (hk : k ∈ K),
      qm M N m * qm M N ⟨k, hKM hk⟩ * (qm M N m)⁻¹ ∈ Kb := by
    intro m k hk
    have hkk : (m : G) * k * (m : G)⁻¹ ∈ K := hKn m m.2 k hk
    have e : qm M N m * qm M N ⟨k, hKM hk⟩ * (qm M N m)⁻¹ =
        qm M N ⟨(m : G) * k * (m : G)⁻¹, hKM hkk⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [e]
    exact hKb _ hkk
  have hKbn : Kb.Normal := by
    refine ⟨fun q hq r => ?_⟩
    obtain ⟨⟨k, hk⟩, rfl⟩ := hq
    obtain ⟨m, rfl⟩ := (QuotientGroup.mk'_surjective (N.subgroupOf M)) r
    exact hconjK m k hk
  have hKbsq : ∀ q ∈ Kb, q * q = 1 := by
    intro q hq
    obtain ⟨⟨k, hk⟩, rfl⟩ := hq
    rw [← map_mul]
    exact qm_eq_one.2 (hKsq k hk)
  have hKbc : ∀ q ∈ Kb, ∀ q' ∈ Kb, q * q' = q' * q := by
    intro q hq q' hq'
    obtain ⟨⟨k, hk⟩, rfl⟩ := hq
    obtain ⟨⟨l, hl⟩, rfl⟩ := hq'
    have h : ⁅qm M N ⟨k, hKM hk⟩, qm M N ⟨l, hKM hl⟩⁆ = 1 := by
      rw [← map_commutatorElement, qm_eq_one]
      exact hKc k hk l hl
    exact commutatorElement_eq_one_iff_mul_comm.1 h
  have hKbz : ∃ q ∈ Kb, qm M N z' * q ≠ q * qm M N z' := by
    obtain ⟨k, hk, hkz⟩ := hKz
    refine ⟨qm M N ⟨k, hKM hk⟩, hKb k hk, fun h => hkz ?_⟩
    have h' : ⁅qm M N z', qm M N ⟨k, hKM hk⟩⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h
    rw [← map_commutatorElement, qm_eq_one] at h'
    exact h'
  obtain ⟨hzKb, hKbcard, hRK, hKbC⟩ := two_group_klein hR2 hzb2 hzb1 hCR Kb hKbsq hKbc hKbz
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzK
    exact hzKb (hKb z hzK)
  · rw [card_phiE hNK hKM, hKbcard]
    ring
  · intro r hr
    rcases hRK (qm M N ⟨r, hr⟩) with h | h
    · obtain ⟨⟨k, hk⟩, hkr⟩ := h
      left
      have h1 := qm_eq_iff.1 hkr
      have h2' : (⟨k, hKM hk⟩ : ↥M).1⁻¹ * (⟨r, hr⟩ : ↥M).1 = k⁻¹ * r := rfl
      have h3 : k⁻¹ * r ∈ N := h1
      have : r = k * (k⁻¹ * r) := by group
      rw [this]
      exact K.mul_mem hk (hNK h3)
    · obtain ⟨⟨k, hk⟩, hkr⟩ := h
      right
      have hrz : qm M N ⟨r, hr⟩ * qm M N z' = qm M N ⟨r * z, M.mul_mem hr hzM⟩ := by
        rw [← map_mul]; rfl
      rw [hrz] at hkr
      have h1 := qm_eq_iff.1 hkr
      have h3 : k⁻¹ * (r * z) ∈ N := h1
      have : r * z = k * (k⁻¹ * (r * z)) := by group
      rw [this]
      exact K.mul_mem hk (hNK h3)
  ·
    have hF : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N := fun k hk n hn => hN.norm k (hKM hk) n hn
    have hFK : cenMod K N z hF ≤ K := fun g hg => hg.1
    have hNF : N ≤ cenMod K N z hF := by
      intro n hn
      refine ⟨hNK hn, ?_⟩
      have := hN.norm z hzM n hn
      have e : z * n * z⁻¹ * n⁻¹ = (z * n * z⁻¹) * n⁻¹ := rfl
      rw [e]
      exact N.mul_mem this (N.inv_mem hn)
    have hrange : (phiE (N := N) (cenMod K N z hF) (hFK.trans hKM)).range =
        Kb ⊓ centralizer ({qm M N z'} : Set (↥M ⧸ N.subgroupOf M)) := by
      ext q
      constructor
      · rintro ⟨⟨f, hf⟩, rfl⟩
        refine ⟨hKb f (hFK hf), ?_⟩
        show qm M N ⟨f, _⟩ ∈ centralizer ({qm M N z'} : Set (↥M ⧸ N.subgroupOf M))
        rw [mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        have h1 : (⁅z', (⟨f, hKM (hFK hf)⟩ : ↥M)⁆ : ↥M) ∈ N.subgroupOf M := by
          rw [mem_subgroupOf]
          exact hf.2
        have h2 : qm M N ⁅z', (⟨f, hKM (hFK hf)⟩ : ↥M)⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h1
        rw [map_commutatorElement] at h2
        exact commutatorElement_eq_one_iff_mul_comm.1 h2
      · rintro ⟨hq, hqc⟩
        obtain ⟨⟨k, hk⟩, rfl⟩ := hq
        have h1 := mem_centralizer_iff.1 hqc (qm M N z') rfl
        have h2 : ⁅qm M N z', qm M N ⟨k, hKM hk⟩⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h1
        rw [← map_commutatorElement, qm_eq_one] at h2
        refine ⟨⟨k, ⟨hk, h2⟩⟩, rfl⟩
    have hcard := card_phiE hNF (hFK.trans hKM)
    rw [hrange, hKbC] at hcard
    rw [hcard]
    ring

end AmbientD

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
