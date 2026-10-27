module

public import CFSG.ClassicalInvolution.Q3.TL4SepTwoA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

theorem exists_eta (hΩ : HypOmegaGen Δ) (S : Sylow 2 G) :
    ∃ η : Set (Subgroup G), η ∈ etaG Δ ∧ (∀ V ∈ η, V ≤ (S : Subgroup G)) ∧
      (∀ x ∈ ⨆ U ∈ η, U, ∀ y ∈ ⨆ U ∈ η, U, x * y = y * x) ∧
      (∀ s ∈ (S : Subgroup G), ∀ w ∈ ⨆ U ∈ η, U, s * w * s⁻¹ ∈ ⨆ U ∈ η, U) := by
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  refine ⟨η, ⟨S, hη, hinv⟩, fun V hV => (hη.1 hV).2,
    (Sec6Gen.eta_abelian_of_cyc66 hΩ (Sec6Gen.cyc66 hΩ) hη hinv).1, fun s hs w hw => ?_⟩
  have hle : conjSub s (⨆ U ∈ η, U) ≤ ⨆ U ∈ η, U := by
    unfold conjSub
    rw [Subgroup.map_iSup]
    refine iSup_le fun U => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hU => ?_
    exact le_iSup₂_of_le (conjSub s U) (hinv s hs U hU) le_rfl
  exact hle (conj_mem_conjSub hw)

theorem T4Hyp.mem_eta_of_two_lt (h : T4Hyp r G Δ) {S : Sylow 2 G} {η : Set (Subgroup G)}
    (hη : η ∈ etaG Δ) (hηS : ∀ V ∈ η, V ≤ (S : Subgroup G)) {K : Subgroup G} (hK : K ∈ Δ)
    {z : G} (hz : IsUniqueInvolution K z) (h2 : 2 < Nat.card ↥(K ⊓ (S : Subgroup G))) :
    K ⊓ (⨆ U ∈ η, U) ∈ η ∧ z ∈ ⨆ U ∈ η, U := by
  have hmem := Sec6Gen.l6_11Gen G Δ h.hyp S η hη hηS K hK h2
  refine ⟨hmem, ?_⟩
  obtain ⟨S', hη', -⟩ := hη
  have hU := (hη'.1 hmem).1
  obtain ⟨R, hR, J₁, -, hRJ, hUR, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet h.hyp hU
  have hne : K ⊓ (⨆ U ∈ η, U) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h4
    omega
  exact (mem_of_isPGroup_of_ne_bot hz inf_le_left (hRJ.2.1.to_le hUR) hne).2

theorem T4Hyp.commute_comm_conj (h : T4Hyp r G Δ) {K : Subgroup G} (hK : K ∈ Δ) {z : G}
    (hz : IsUniqueInvolution K z) {P : Subgroup G} (hPn : P.Normal) (hP2 : IsPGroup 2 P)
    (hzP : z ∈ P) (g : G) :
    Commute (g * z * g⁻¹ * z * (g * z * g⁻¹)⁻¹ * z⁻¹) z := by
  obtain ⟨R, -, hRK, -⟩ := exists_mem_RSet_ge (Ω := Δ) hK IsPGroup.of_bot bot_le
  have : P.Normal := hPn
  obtain ⟨S, hS⟩ := (IsPGroup.to_sup_of_normal_left hP2 hRK.2.1).exists_le_sylow
  obtain ⟨η, hη, hηS, hWab, hSW⟩ := exists_eta h.hyp S
  have h2 : 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) := by
    obtain ⟨e⟩ := h.quat K hK R hRK
    have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
    have hR : Nat.card ↥R = 4 * 2 ^ (r - 2) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hle : Nat.card ↥R ≤ Nat.card ↥(K ⊓ (S : Subgroup G)) :=
      Subgroup.card_le_of_le (le_inf hRK.1 (le_sup_right.trans hS))
    have : 0 < 2 ^ (r - 2) := pow_pos (by norm_num) _
    omega
  obtain ⟨-, hzW⟩ := h.mem_eta_of_two_lt hη hηS hK hz h2
  have hgz : g * z * g⁻¹ ∈ (S : Subgroup G) := le_sup_left.trans hS (hPn.conj_mem z hzP g)
  have hc : g * z * g⁻¹ * z * (g * z * g⁻¹)⁻¹ * z⁻¹ ∈ ⨆ U ∈ η, U :=
    Subgroup.mul_mem _ (hSW _ hgz z hzW) (Subgroup.inv_mem _ hzW)
  exact hWab _ hc z hzW

theorem T4Hyp.le_three_of_not_mem_normalizer (h : T4Hyp r G Δ) {J L : Subgroup G} (hJ : J ∈ Δ)
    (hL : L ∈ Δ) {u v : G} (hu : IsUniqueInvolution J u) (hv : IsUniqueInvolution L v)
    (hinu : TightInO2 u) (hinv : TightInO2 v) (hvJ : v ∉ Subgroup.normalizer (J : Set G)) :
    r ≤ 3 := by
  have hJ2 := h.isPGroup_of_inO2 hJ hu hinu
  have hJR := mem_RSet_self hJ hJ2
  obtain ⟨Pu, hPun, hPu2, -⟩ := hinu
  obtain ⟨Pv, hPvn, hPv2, hvP⟩ := hinv
  have : Pv.Normal := hPvn
  have : Pu.Normal := hPun
  have hQn : (Pu ⊔ Pv).Normal := Subgroup.sup_normal Pu Pv
  have hQ2 : IsPGroup 2 ↥(Pu ⊔ Pv) := IsPGroup.to_sup_of_normal_right hPu2 hPv2
  have hvQ : v ∈ Pu ⊔ Pv := Subgroup.mem_sup_right hvP
  have hJv : conjSub v J ∈ Δ := h.hyp.conjInvariant v J hJ
  have hne : J ≠ conjSub v J := fun e => hvJ (mem_normalizer_of_conjSub_eq e.symm)
  have hJv2 : IsPGroup 2 ↥(conjSub v J) := hJ2.map _
  have hJvR := mem_RSet_self hJv hJv2
  have : (Pu ⊔ Pv).Normal := hQn
  obtain ⟨S, hS⟩ := (IsPGroup.to_sup_of_normal_right hJ2 hQ2).exists_le_sylow
  have hJvS : conjSub v J ≤ (S : Subgroup G) := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have e1 : y = v * ((v⁻¹ * y * v) * v⁻¹ * (v⁻¹ * y * v)⁻¹) * (v⁻¹ * y * v) := by group
    rw [e1]
    exact hS (Subgroup.mul_mem _ (Subgroup.mem_sup_right ((Pu ⊔ Pv).mul_mem hvQ
      (hQn.conj_mem _ ((Pu ⊔ Pv).inv_mem hvQ) _))) (Subgroup.mem_sup_left hy))
  have hcomm := Q3CP.l67Gen G Δ h.hyp S J hJR _ hJvR (le_sup_left.trans hS) hJvS hne
  have hbot : J ⊓ conjSub v J = ⊥ := by
    by_contra hnb
    have huJv : u ∈ conjSub v J :=
      (mem_of_isPGroup_of_ne_bot hu inf_le_left (hJ2.to_le inf_le_left) hnb).2
    have huv : u = v * u * v⁻¹ := ((hu.conj v).unique u huJv hu.sq).resolve_left hu.ne_one
    have hu' : IsUniqueInvolution (conjSub v J) u := huv ▸ hu.conj v
    exact hne (h.noTwins J hJ _ hJv u hu hu')
  have hvv : v * v = 1 := hv.sq
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hx4 : ∀ x ∈ J, x ^ 4 = 1 := by
    intro x hx
    have hyJv : v * x * v⁻¹ ∈ conjSub v J := conj_mem_conjSub hx
    have hxy : Commute x⁻¹ (v * x * v⁻¹) := hcomm _ (J.inv_mem hx) _ hyJv
    have h3 := h.commute_comm_conj hL hv hPvn hPv2 hvP x⁻¹
    have e1 : x⁻¹ * v * x⁻¹⁻¹ * v * (x⁻¹ * v * x⁻¹⁻¹)⁻¹ * v⁻¹ =
        x⁻¹ * (v * x * v⁻¹) * (x⁻¹ * (v * x * v⁻¹)) := by
      simp only [mul_inv_rev, inv_inv, hvinv]
      group
    rw [e1] at h3
    set d := x⁻¹ * (v * x * v⁻¹) with hd
    have e2 : v * d * v⁻¹ = d⁻¹ := by
      rw [hd, hvinv]
      calc v * (x⁻¹ * (v * x * v)) * v = v * x⁻¹ * v * x * (v * v) := by group
        _ = v * x⁻¹ * v * x := by rw [hvv, mul_one]
        _ = (x⁻¹ * (v * x * v))⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hvinv, inv_inv]
          group
    have e3 : d * d = d⁻¹ * d⁻¹ := by
      calc d * d = v * (d * d) * v⁻¹ := by rw [← h3.eq]; group
        _ = (v * d * v⁻¹) * (v * d * v⁻¹) := by group
        _ = d⁻¹ * d⁻¹ := by rw [e2]
    have hd4 : d ^ 4 = 1 := by
      calc d ^ 4 = (d * d) * (d * d) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        _ = (d⁻¹ * d⁻¹) * (d * d) := by rw [← e3]
        _ = 1 := by group
    rw [hd, hxy.mul_pow, inv_pow] at hd4
    have hy4 : (v * x * v⁻¹) ^ 4 = x ^ 4 := (inv_mul_eq_one.mp hd4).symm
    have hmem : x ^ 4 ∈ J ⊓ conjSub v J :=
      ⟨J.pow_mem hx 4, hy4 ▸ (conjSub v J).pow_mem hyJv 4⟩
    rw [hbot] at hmem
    exact hmem
  have hJS : IsSylow2In J J := ⟨le_rfl, hJ2, fun V' hV'J _ hJV' => le_antisymm hV'J hJV'⟩
  obtain ⟨e⟩ := h.quat J hJ J hJS
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hx := hx4 _ (e.symm (QuaternionGroup.a 1)).2
  have hord : orderOf (((e.symm (QuaternionGroup.a 1) : ↥J) : G)) = 2 * 2 ^ (r - 2) := by
    rw [Subgroup.orderOf_coe]
    have := orderOf_injective e.symm.toMonoidHom e.symm.injective (QuaternionGroup.a 1)
    simp only [MulEquiv.coe_toMonoidHom] at this
    rw [this, QuaternionGroup.orderOf_a_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hx
  rw [hord, show (4 : ℕ) = 2 * 2 by norm_num] at hdvd
  have h2 : 2 ^ (r - 2) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd)
  by_contra hr
  have h4 : 2 ^ 2 ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.ClassicalInvolution.Q3.TL4
