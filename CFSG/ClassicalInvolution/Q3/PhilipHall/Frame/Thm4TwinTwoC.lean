module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinTwoB
public import CFSG.ClassicalInvolution.Q3.TL4SepTwoD

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace Thm4Twin

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

theorem TwinT4Hyp.exists_le_centralizer (h : TwinT4Hyp r G Δ) {J L : Subgroup G} (hJ : J ∈ Δ)
    (hL : L ∈ Δ) {u v : G} (hu : IsUniqueInvolution J u) (hv : IsUniqueInvolution L v)
    {Q : Subgroup G} (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q) (huQ : u ∈ Q) (hvQ : v ∈ Q)
    (hvJ : v ∈ Subgroup.normalizer (J : Set G)) :
    ∃ X : Subgroup G, X ≤ J ⊓ Subgroup.centralizer ({v} : Set G) ∧ IsPGroup 2 X ∧
      4 ≤ Nat.card X := by
  have hJ2 := h.isPGroup_of_inO2 hJ hu ⟨Q, hQn, hQ2, huQ⟩
  have hL2 := h.isPGroup_of_inO2 hL hv ⟨Q, hQn, hQ2, hvQ⟩
  have hr := h.three_le hJ
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hJS : IsSylow2In J J := ⟨le_rfl, hJ2, fun V' hV'J _ hJV' => le_antisymm hV'J hJV'⟩
  have hLS : IsSylow2In L L := ⟨le_rfl, hL2, fun V' hV'L _ hLV' => le_antisymm hV'L hLV'⟩
  by_cases h2 : 2 < Nat.card ↥(J ⊓ Q)
  · have : Q.Normal := hQn
    obtain ⟨S, hS⟩ := (IsPGroup.to_sup_of_normal_right hL2 hQ2).exists_le_sylow
    obtain ⟨η, hη, hηS, hWab, -⟩ := TL4.exists_eta h.hyp S
    have hJS2 : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) :=
      lt_of_lt_of_le h2 (Subgroup.card_le_of_le (inf_le_inf_left J (le_sup_right.trans hS)))
    have hLS2 : 2 < Nat.card ↥(L ⊓ (S : Subgroup G)) := by
      obtain ⟨e⟩ := h.quat L hL L hLS
      have hLc : Nat.card ↥L = 4 * 2 ^ (r - 2) := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      rw [inf_eq_left.mpr (le_sup_left.trans hS), hLc]
      have : 0 < 2 ^ (r - 2) := pow_pos (by norm_num) _
      omega
    obtain ⟨hJW, -⟩ := h.mem_eta_of_two_lt hη hηS hJ hu hJS2
    obtain ⟨-, hvW⟩ := h.mem_eta_of_two_lt hη hηS hL hv hLS2
    obtain ⟨S', hη', -⟩ := hη
    obtain ⟨R, -, J₁, -, hRJ, hUR, -, -, h4⟩ :=
      Sec6Gen.exists_data_of_mem_USet h.hyp (hη'.1 hJW).1
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
    obtain ⟨e⟩ := h.quat J hJ J hJS
    set x : G := ((e.symm (QuaternionGroup.a 1) : ↥J) : G) with hx
    set y : G := ((e.symm (QuaternionGroup.xa 0) : ↥J) : G) with hy
    have hxJ : x ∈ J := (e.symm _).2
    have hyJ : y ∈ J := (e.symm _).2
    have hord : ∀ q : QuaternionGroup (2 ^ (r - 2)), orderOf ((e.symm q : ↥J) : G) = orderOf q := by
      intro q
      rw [Subgroup.orderOf_coe]
      have := orderOf_injective e.symm.toMonoidHom e.symm.injective q
      simpa only [MulEquiv.coe_toMonoidHom] using this
    have hxo : 4 ≤ orderOf x := by
      rw [hx, hord, QuaternionGroup.orderOf_a_one]
      have : 2 ≤ 2 ^ (r - 2) :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hyo : orderOf y = 4 := by rw [hy, hord, QuaternionGroup.orderOf_xa]
    have hxyo : orderOf (x * y) = 4 := by
      have : x * y = ((e.symm (QuaternionGroup.a 1 * QuaternionGroup.xa 0) : ↥J) : G) := by
        rw [map_mul]
        rfl
      rw [this, hord, QuaternionGroup.a_mul_xa, QuaternionGroup.orderOf_xa]
    have huc : ∀ j ∈ J, j * u = u * j := fun j hj => (hu.commute_of_mem hj).symm
    obtain ⟨w, hwJ, hwv, hwo⟩ : ∃ w ∈ J, v * w * v⁻¹ * w⁻¹ = 1 ∧ 4 ≤ orderOf w := by
      rcases hcomm x hxJ with hcx | hcx
      · exact ⟨x, hxJ, hcx, hxo⟩
      rcases hcomm y hyJ with hcy | hcy
      · exact ⟨y, hyJ, hcy, hyo.ge⟩
      refine ⟨x * y, J.mul_mem hxJ hyJ, ?_, hxyo.ge⟩
      calc v * (x * y) * v⁻¹ * (x * y)⁻¹
          = (v * x * v⁻¹ * x⁻¹) * (x * (v * y * v⁻¹ * y⁻¹) * x⁻¹) := by group
        _ = u * (x * u * x⁻¹) := by rw [hcx, hcy]
        _ = u * u := by rw [huc x hxJ]; group
        _ = 1 := hu.sq
    refine ⟨Subgroup.zpowers w, Subgroup.zpowers_le.mpr ⟨hwJ,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, hJ2.to_le (Subgroup.zpowers_le.mpr hwJ),
      by rw [Nat.card_zpowers]; exact hwo⟩
    calc w * v = (v * w * v⁻¹ * w⁻¹)⁻¹ * (v * w) := by group
      _ = v * w := by rw [hwv, inv_one, one_mul]

variable {J L : Subgroup G}

theorem TwinT4Min.false_of_mem_normalizer (hm : TwinT4Min r G Δ J L) {u v : G}
    (hu : IsUniqueInvolution J u) (hv : IsUniqueInvolution L v) (hinu : TightInO2 u)
    (hinv : TightInO2 v) (hvJ : v ∈ Subgroup.normalizer (J : Set G)) : False := by
  have h := hm.hyp
  obtain ⟨Pu, hPun, hPu2, huP⟩ := hinu
  obtain ⟨Pv, hPvn, hPv2, hvP⟩ := hinv
  have : Pv.Normal := hPvn
  have : Pu.Normal := hPun
  have hQn : (Pu ⊔ Pv).Normal := Subgroup.sup_normal Pu Pv
  have hQ2 : IsPGroup 2 ↥(Pu ⊔ Pv) := IsPGroup.to_sup_of_normal_right hPu2 hPv2
  have huQ : u ∈ Pu ⊔ Pv := Subgroup.mem_sup_left huP
  have hvQ : v ∈ Pu ⊔ Pv := Subgroup.mem_sup_right hvP
  have hJ2 := h.isPGroup_of_inO2 hm.memJ hu ⟨_, hQn, hQ2, huQ⟩
  have hL2 := h.isPGroup_of_inO2 hm.memL hv ⟨_, hQn, hQ2, hvQ⟩
  have hJR := TL4.mem_RSet_self hm.memJ hJ2
  have hLR := TL4.mem_RSet_self hm.memL hL2
  have hJL : J ≠ L := fun e => hm.notConj ⟨1, by rw [conjSub_one, e]⟩
  by_cases huv : u = v
  ·
    subst huv
    have hLu : L ≤ Subgroup.centralizer ({u} : Set G) := isUniqueInvolution_le_centralizer hv
    have hLN : L ≤ Subgroup.normalizer (J : Set G) :=
      h.le_normalizer_of_le_centralizer hm.memJ hm.memL hJL hu hLu
    exact hm.notComm (TL4.commutes_of_le_normalizer h.hyp hJR hLR hJ2 hL2 hJL hLN)
  obtain ⟨X, hXC, hX2, hX4⟩ :=
    h.exists_le_centralizer hm.memJ hm.memL hu hv hQn hQ2 huQ hvQ hvJ
  obtain ⟨V, hV, hXV⟩ := IsSylow2In.exists_ge hX2 hXC
  have hV4 : 4 ≤ Nat.card V := hX4.trans (Subgroup.card_le_of_le hXV)
  have hVne : V ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hV4
    omega
  have huV : u ∈ V := TL4.mem_of_isPGroup_of_ne_bot hu (hV.1.trans inf_le_left) hV.2.1 hVne
  have hJtw : J ∉ twinSet Δ L := by
    rintro ⟨-, z, hzL, hzJ⟩
    exact huv ((hzJ.eq hu).symm.trans (hzL.eq hv))
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu.sq) hu.ne_one
  have hRJ : ∀ R ∈ RSet Δ, R ≤ J → R = J := fun R hR hRJ =>
    ((Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hm.memJ hR hRJ).eq_of_le hJ2 le_rfl hRJ).symm
  rcases Sec6Gen.l6_2Gen G Δ h.hyp L hm.memL v hv J hm.memJ hJtw u hu V hV huV with
    ⟨hVu, -⟩ | ⟨hVu, -⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, hVL⟩
  · rw [hVu, Nat.card_zpowers, hu2] at hV4
    omega
  · rw [hVu, Nat.card_zpowers, hu2] at hV4
    omega
  · have hJstar : J ∈ omegaStarNbr Δ L :=
      ⟨hm.memJ, hJL, V, hVU, hV.1.trans inf_le_left, hVN⟩
    by_cases hJn : J ∈ omegaNbr Δ L
    · obtain ⟨-, -, R, hR, hRJ', hRN⟩ := hJn
      rw [hRJ R hR hRJ'] at hRN
      exact hm.notComm
        (TL4.commutes_of_le_normalizer h.hyp hLR hJR hL2 hJ2 hJL.symm hRN).symm
    · obtain ⟨g, -, hg⟩ := h.aEmpty L hm.memL J hJstar hJn v u hv hu
      exact hm.notConj ⟨g⁻¹, by rw [← hg, conjSub_inv_conjSub]⟩
  · rw [hRJ V hVR (hV.1.trans inf_le_left), TL4.oddCoreOf_eq_bot_of_isPGroup hL2] at hVL
    refine hm.notComm fun x hx y hy => ?_
    have hc := hVL (Subgroup.commutator_mem_commutator hx hy)
    rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc

end Thm4Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
