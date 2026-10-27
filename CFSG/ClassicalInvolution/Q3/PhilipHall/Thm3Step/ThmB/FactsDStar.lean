module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.Facts

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {Q : Subgroup Y}

theorem inv_mem_eta_of_two_lt (hΦ : HypOmegaGen Φ) {S : Sylow 2 Y} {η : Set (Subgroup Y)}
    (hη : η ∈ etaG Φ) (hηS : ∀ V ∈ η, V ≤ (S : Subgroup Y)) {K : Subgroup Y} (hK : K ∈ Φ)
    {z : Y} (hz : IsUniqueInvolution K z) (h2 : 2 < Nat.card ↥(K ⊓ (S : Subgroup Y))) :
    K ⊓ (⨆ U ∈ η, U) ∈ η ∧ z ∈ ⨆ U ∈ η, U := by
  have hmem := Sec6Gen.l6_11Gen Y Φ hΦ S η hη hηS K hK h2
  refine ⟨hmem, ?_⟩
  obtain ⟨S', hη', -⟩ := hη
  have hU := (hη'.1 hmem).1
  obtain ⟨R, hR, J₁, -, hRJ, hUR, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΦ hU
  have hne : K ⊓ (⨆ U ∈ η, U) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h4
    omega
  exact (TL4.mem_of_isPGroup_of_ne_bot hz inf_le_left (hRJ.2.1.to_le hUR) hne).2

namespace QFam

variable (h : QFam Φ Q)
include h

theorem commute_conj_conj {K : Subgroup Y} (hK : K ∈ Φ) {z : Y} (hz : IsUniqueInvolution K z)
    (g : Y) : Commute ((g * z * g⁻¹) * z * (g * z * g⁻¹)⁻¹) z := by
  have hΦ := h.hypGen
  haveI := h.normal
  obtain ⟨S, hS⟩ := (IsPGroup.to_sup_of_normal_left h.two (h.isPGroup K hK)).exists_le_sylow
  obtain ⟨η, hη, hηS, hWab, hSW⟩ := TL4.exists_eta hΦ S
  have h2 : 2 < Nat.card ↥(K ⊓ (S : Subgroup Y)) := by
    rw [inf_eq_left.mpr (le_sup_right.trans hS), h.natCard_eq_eight hK]
    norm_num
  obtain ⟨-, hzW⟩ := inv_mem_eta_of_two_lt hΦ hη hηS hK hz h2
  have hgz : g * z * g⁻¹ ∈ (S : Subgroup Y) :=
    le_sup_left.trans hS (h.normal.conj_mem z (h.inv_mem K hK z hz) g)
  exact hWab _ (hSW _ hgz z hzW) z hzW

theorem exists_le_centralizer {J L : Subgroup Y} (hJ : J ∈ Φ) (hL : L ∈ Φ) {u v : Y}
    (hu : IsUniqueInvolution J u) (hv : IsUniqueInvolution L v)
    (hvJ : v ∈ Subgroup.normalizer (J : Set Y)) :
    ∃ X : Subgroup Y, X ≤ J ⊓ Subgroup.centralizer ({v} : Set Y) ∧ IsPGroup 2 X ∧
      4 ≤ Nat.card X := by
  have hΦ := h.hypGen
  have hJ2 := h.isPGroup J hJ
  have hL2 := h.isPGroup L hL
  have hvQ := h.inv_mem L hL v hv
  have hQn := h.normal
  by_cases h2 : 2 < Nat.card ↥(J ⊓ Q)
  · haveI := hQn
    obtain ⟨S, hS⟩ := (IsPGroup.to_sup_of_normal_right hL2 h.two).exists_le_sylow
    obtain ⟨η, hη, hηS, hWab, -⟩ := TL4.exists_eta hΦ S
    have hJS2 : 2 < Nat.card ↥(J ⊓ (S : Subgroup Y)) :=
      lt_of_lt_of_le h2 (Subgroup.card_le_of_le (inf_le_inf_left J (le_sup_right.trans hS)))
    have hLS2 : 2 < Nat.card ↥(L ⊓ (S : Subgroup Y)) := by
      rw [inf_eq_left.mpr (le_sup_left.trans hS), h.natCard_eq_eight hL]
      norm_num
    obtain ⟨hJW, -⟩ := inv_mem_eta_of_two_lt hΦ hη hηS hJ hu hJS2
    obtain ⟨-, hvW⟩ := inv_mem_eta_of_two_lt hΦ hη hηS hL hv hLS2
    obtain ⟨S', hη', -⟩ := hη
    obtain ⟨R, -, J₁, -, hRJ, hUR, -, -, h4⟩ :=
      Sec6Gen.exists_data_of_mem_USet hΦ (hη'.1 hJW).1
    refine ⟨J ⊓ ⨆ U ∈ η, U, fun x hx => ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr
      (hWab x hx.2 v hvW)⟩, hRJ.2.1.to_le hUR, h4⟩
  ·
    have hcomm : ∀ j ∈ J, v * j * v⁻¹ * j⁻¹ = 1 ∨ v * j * v⁻¹ * j⁻¹ = u := by
      intro j hj
      have hcJ : v * j * v⁻¹ * j⁻¹ ∈ J :=
        J.mul_mem ((Subgroup.mem_normalizer_iff.mp hvJ j).mp hj) (J.inv_mem hj)
      have hcQ : v * j * v⁻¹ * j⁻¹ ∈ Q := by
        have := Q.mul_mem hvQ (hQn.conj_mem v⁻¹ (Q.inv_mem hvQ) j)
        rwa [show v * (j * v⁻¹ * j⁻¹) = v * j * v⁻¹ * j⁻¹ by group] at this
      have hc2 : (v * j * v⁻¹ * j⁻¹) * (v * j * v⁻¹ * j⁻¹) = 1 := by
        have hpow : (⟨_, hcJ, hcQ⟩ : ↥(J ⊓ Q)) ^ Nat.card ↥(J ⊓ Q) = 1 := pow_card_eq_one'
        have hpos : 0 < Nat.card ↥(J ⊓ Q) := Nat.card_pos
        have hle : Nat.card ↥(J ⊓ Q) ≤ 2 := not_lt.mp h2
        have hcp : (v * j * v⁻¹ * j⁻¹) ^ Nat.card ↥(J ⊓ Q) = 1 := by
          have := congrArg Subtype.val hpow
          simpa using this
        interval_cases hn : Nat.card ↥(J ⊓ Q)
        · rw [pow_one] at hcp
          rw [hcp, one_mul]
        · rw [← pow_two]
          exact hcp
      exact hu.unique _ hcJ hc2
    have : NeZero (2 : ℕ) := ⟨by norm_num⟩
    obtain ⟨e⟩ := h.hyp.sylow J hJ J (h.isSylow2In_self hJ)
    set x : Y := ((e.symm (QuaternionGroup.a 1) : ↥J) : Y) with hx
    set y : Y := ((e.symm (QuaternionGroup.xa 0) : ↥J) : Y) with hy
    have hxJ : x ∈ J := (e.symm _).2
    have hyJ : y ∈ J := (e.symm _).2
    have hord : ∀ q : QuaternionGroup 2, orderOf ((e.symm q : ↥J) : Y) = orderOf q := by
      intro q
      rw [Subgroup.orderOf_coe]
      have := orderOf_injective e.symm.toMonoidHom e.symm.injective q
      simpa only [MulEquiv.coe_toMonoidHom] using this
    have hxo : orderOf x = 4 := by rw [hx, hord, QuaternionGroup.orderOf_a_one]
    have hyo : orderOf y = 4 := by rw [hy, hord, QuaternionGroup.orderOf_xa]
    have hxyo : orderOf (x * y) = 4 := by
      have : x * y = ((e.symm (QuaternionGroup.a 1 * QuaternionGroup.xa 0) : ↥J) : Y) := by
        rw [map_mul]
        rfl
      rw [this, hord, QuaternionGroup.a_mul_xa, QuaternionGroup.orderOf_xa]
    have huc : ∀ j ∈ J, j * u = u * j := fun j hj => (hu.commute_of_mem hj).symm
    obtain ⟨w, hwJ, hwv, hwo⟩ : ∃ w ∈ J, v * w * v⁻¹ * w⁻¹ = 1 ∧ orderOf w = 4 := by
      rcases hcomm x hxJ with hcx | hcx
      · exact ⟨x, hxJ, hcx, hxo⟩
      rcases hcomm y hyJ with hcy | hcy
      · exact ⟨y, hyJ, hcy, hyo⟩
      refine ⟨x * y, J.mul_mem hxJ hyJ, ?_, hxyo⟩
      calc v * (x * y) * v⁻¹ * (x * y)⁻¹
          = (v * x * v⁻¹ * x⁻¹) * (x * (v * y * v⁻¹ * y⁻¹) * x⁻¹) := by group
        _ = u * (x * u * x⁻¹) := by rw [hcx, hcy]
        _ = u * u := by rw [huc x hxJ]; group
        _ = 1 := hu.sq
    refine ⟨Subgroup.zpowers w, Subgroup.zpowers_le.mpr ⟨hwJ,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, hJ2.to_le (Subgroup.zpowers_le.mpr hwJ),
      by rw [Nat.card_zpowers, hwo]⟩
    calc w * v = (v * w * v⁻¹ * w⁻¹)⁻¹ * (v * w) := by group
      _ = v * w := by rw [hwv, inv_one, one_mul]

theorem mem_dstarComp_of_four_le {K J : Subgroup Y} (hK : K ∈ Φ) (hJ : J ∈ Φ) {z : Y}
    (hz : IsUniqueInvolution K z) {X : Subgroup Y}
    (hXJ : X ≤ J ⊓ Subgroup.centralizer ({z} : Set Y)) (hX2 : IsPGroup 2 X)
    (hX4 : 4 ≤ Nat.card X) : J ∈ dstarComp Φ K := by
  have hΦ := h.hypGen
  by_cases hJK : J = K
  · subst hJK
    exact Relation.ReflTransGen.refl
  by_cases htw : J ∈ twinSet Φ K
  · obtain ⟨-, z', hz'K, hz'J⟩ := htw
    exact Relation.ReflTransGen.single ⟨hJ, Or.inl (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΦ K
      (Q3CL.T3.twin_mem_omegaNbr hΦ hK hJ hJK hz'K hz'J))⟩
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΦ hJ
  obtain ⟨V, hV, hXV⟩ := IsSylow2In.exists_ge hX2 hXJ
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  have hV4 : 4 ≤ Nat.card V := hX4.trans (Subgroup.card_le_of_le hXV)
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
  rcases Sec6Gen.l6_2Gen Y Φ hΦ K hK z hz J hJ htw t ht V hV
      (ht.mem_of_le hVJ hV.2.1 (by omega)) with
    ⟨hVt, -⟩ | ⟨hVt, -⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, hVK⟩
  · rw [hVt, Nat.card_zpowers, ht2] at hV4
    omega
  · rw [hVt, Nat.card_zpowers, ht2] at hV4
    omega
  · exact Relation.ReflTransGen.single ⟨hJ, Or.inl ⟨hJ, hJK, V, hVU, hVJ, hVN⟩⟩
  ·
    have hVJ' : V = J := ((Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΦ hJ hVR hVJ).eq_of_le
      (h.isPGroup J hJ) le_rfl hVJ).symm
    rw [hVJ', h.oddCoreOf_eq_bot hK] at hVK
    refine Relation.ReflTransGen.single ⟨hJ, Or.inl (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΦ K
      (h.mem_omegaNbr_of_commutes hJ hJK fun x hx y hy => ?_))⟩
    have hc := hVK (Subgroup.commutator_mem_commutator hx hy)
    rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc

theorem mem_dstarComp_of_normalizes {L M : Subgroup Y} (hL : L ∈ Φ) (hM : M ∈ Φ) {v : Y}
    (hv : IsUniqueInvolution M v) (hvL : v ∈ Subgroup.normalizer (L : Set Y)) :
    L ∈ dstarComp Φ M := by
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution h.hypGen hL
  obtain ⟨X, hXC, hX2, hX4⟩ := h.exists_le_centralizer hL hM hu hv hvL
  exact h.mem_dstarComp_of_four_le hM hL hv hXC hX2 hX4

end QFam

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
