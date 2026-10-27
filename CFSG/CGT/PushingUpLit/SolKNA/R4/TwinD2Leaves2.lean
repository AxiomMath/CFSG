module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinD2Vac
public import CFSG.ClassicalInvolution.Q3.TL3T29

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Quaternion

theorem quaternion_commutator_sq_ne_one (k : ℕ) (hk : 2 ≤ k) :
    ((QuaternionGroup.a 1 * QuaternionGroup.xa 0 * (QuaternionGroup.a 1)⁻¹ *
        (QuaternionGroup.xa 0)⁻¹ : QuaternionGroup (2 ^ k)) *
      (QuaternionGroup.a 1 * QuaternionGroup.xa 0 * (QuaternionGroup.a 1)⁻¹ *
        (QuaternionGroup.xa 0)⁻¹ : QuaternionGroup (2 ^ k))) ≠ 1 := by
  have hinv_a : ∀ i : ZMod (2 * 2 ^ k), (QuaternionGroup.a i : QuaternionGroup (2 ^ k))⁻¹ =
      QuaternionGroup.a (-i) := fun i =>
    inv_eq_of_mul_eq_one_right (by rw [QuaternionGroup.a_mul_a, add_neg_cancel,
      QuaternionGroup.one_def])
  have hn : (((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) + (2 ^ k : ℕ)) = 0 := by
    rw [← two_mul]
    exact_mod_cast ZMod.natCast_self (2 * 2 ^ k)
  have hinv_xa : ∀ i : ZMod (2 * 2 ^ k), (QuaternionGroup.xa i : QuaternionGroup (2 ^ k))⁻¹ =
      QuaternionGroup.xa (((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) + i) := fun i =>
    inv_eq_of_mul_eq_one_right (by
      rw [QuaternionGroup.xa_mul_xa, QuaternionGroup.one_def]
      congr 1
      linear_combination hn)
  have hc : (QuaternionGroup.a 1 * QuaternionGroup.xa 0 * (QuaternionGroup.a 1)⁻¹ *
      (QuaternionGroup.xa 0)⁻¹ : QuaternionGroup (2 ^ k)) = QuaternionGroup.a 2 := by
    rw [hinv_a, hinv_xa, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a,
      QuaternionGroup.xa_mul_xa]
    congr 1
    linear_combination hn
  rw [hc, QuaternionGroup.a_mul_a, QuaternionGroup.one_def]
  intro h
  have h4 : ((2 + 2 : ZMod (2 * 2 ^ k))) = 0 := by injection h
  have h5 : ((4 : ℕ) : ZMod (2 * 2 ^ k)) = 0 := by push_cast; linear_combination h4
  rw [ZMod.natCast_eq_zero_iff] at h5
  have h6 : 2 * 2 ^ k ≤ 4 := Nat.le_of_dvd (by norm_num) h5
  have h7 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

variable {G : Type} [Group G]

theorem exists_commutator_sq_ne_one_of_isQuatSub {J : Subgroup G} (hq : IsQuatSub J)
    (h16 : 16 ≤ Nat.card J) :
    ∃ x ∈ J, ∃ y ∈ J, (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) ≠ 1 := by
  obtain ⟨k, hk1, ⟨e⟩⟩ := hq
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  have hcard : Nat.card J = 2 ^ (k + 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    ring
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk : k = 1 := by omega
    rw [hcard, hk] at h16
    norm_num at h16
  refine ⟨((e.symm (QuaternionGroup.a 1) : ↥J) : G), (e.symm (QuaternionGroup.a 1)).2,
    ((e.symm (QuaternionGroup.xa 0) : ↥J) : G), (e.symm (QuaternionGroup.xa 0)).2, fun h => ?_⟩
  apply quaternion_commutator_sq_ne_one k hk2
  have h' : (e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) *
      (e.symm (QuaternionGroup.a 1))⁻¹ * (e.symm (QuaternionGroup.xa 0))⁻¹) *
      (e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) *
      (e.symm (QuaternionGroup.a 1))⁻¹ * (e.symm (QuaternionGroup.xa 0))⁻¹) = 1 :=
    Subtype.ext (by push_cast; exact h)
  have := congrArg e h'
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, map_one] at this
  exact this

end Quaternion

section Involutions

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem card_inf_le_two_of_not_mem_normalizer (hΩ : HypOmegaGen Ω) {J L : Subgroup G}
    (hJ : J ∈ Ω) (hL : L ∈ Ω) (hJ2 : IsPGroup 2 J) (hL2 : IsPGroup 2 L) {v : G}
    (hv : IsUniqueInvolution L v) (hvJ : v ∉ Subgroup.normalizer (J : Set G)) {Q : Subgroup G}
    (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q) (hvQ : v ∈ Q) : Nat.card ↥(J ⊓ Q) ≤ 2 := by
  by_contra hlt
  push Not at hlt
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (IsPGroup.to_sup_of_normal_right hL2 hQ2).exists_le_sylow
  obtain ⟨η, hηS, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hη : η ∈ etaG Ω := ⟨S, hηS, hinv⟩
  have hηle : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hηS.1 hV).2
  set W := TC.etaSpan η with hW
  have hW2 : IsPGroup 2 W := TC.etaSpan_isPGroup hη
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := TC.etaSpan_comm hΩ hη
  have hLS : L ≤ (S : Subgroup G) := le_sup_left.trans hS
  have hL8 := (Sec6Gen.isQuatSub_of_mem_RSet hΩ (TC.mem_RSet_of_isPGroup hL hL2)).eight_le
  have hLW : L ⊓ W ∈ η := Sec6Gen.l6_11Gen G Ω hΩ S η hη hηle L hL
    (by rw [inf_eq_left.mpr hLS]; omega)
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ (hηS.1 hLW).1
  have hvW : v ∈ W := (hv.mem_of_le inf_le_left (hW2.to_le inf_le_right) (by omega)).2
  have hJS : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) :=
    lt_of_lt_of_le hlt (Subgroup.card_le_of_le (inf_le_inf_left J (le_sup_right.trans hS)))
  have hJW : J ⊓ W ∈ η := Sec6Gen.l6_11Gen G Ω hΩ S η hη hηle J hJ hJS
  obtain ⟨-, -, -, -, -, -, -, -, h4J⟩ := Sec6Gen.exists_data_of_mem_USet hΩ (hηS.1 hJW).1
  have hJv : conjSub v J ≠ J := fun h => hvJ (mem_normalizer_iff_conjSub_eq.mpr h)
  have hle : J ⊓ W ≤ J ⊓ conjSub v J := by
    intro y hy
    refine ⟨hy.1, mem_conjSub_iff.mpr ?_⟩
    have hyv : y * v = v * y := hWcomm y hy.2 v hvW
    have : v⁻¹ * y * v = y := by rw [mul_assoc, hyv, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact hy.1
  have h1 := (hΩ.omega4 J hJ (conjSub v J) (hΩ.conjInvariant v J hJ) hJv.symm).1
  have hJJ2 : IsPGroup 2 ↥(J ⊓ conjSub v J) := hJ2.to_le inf_le_left
  obtain ⟨k, hk⟩ := hJJ2.exists_card_eq
  rw [hk, padicValNat.prime_pow] at h1
  have hc := Subgroup.card_le_of_le hle
  rw [hk] at hc
  have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
  omega

theorem mem_normalizer_of_sixteen_le (hΩ : HypOmegaGen Ω) {J L : Subgroup G} (hJ : J ∈ Ω)
    (hL : L ∈ Ω) (hJ2 : IsPGroup 2 J) (hL2 : IsPGroup 2 L) (h16 : 16 ≤ Nat.card J) {v : G}
    (hv : IsUniqueInvolution L v) {Q : Subgroup G} (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q)
    (hvQ : v ∈ Q) : v ∈ Subgroup.normalizer (J : Set G) := by
  by_contra hvJ
  have hQle := card_inf_le_two_of_not_mem_normalizer hΩ hJ hL hJ2 hL2 hv hvJ hQn hQ2 hvQ
  have hJv : conjSub v J ≠ J := fun h => hvJ (mem_normalizer_iff_conjSub_eq.mpr h)
  have hJv' : conjSub v J ∈ Ω := hΩ.conjInvariant v J hJ
  obtain ⟨S, hS⟩ := (IsPGroup.to_sup_of_normal_right hJ2 hQ2).exists_le_sylow
  have hJvS : conjSub v J ≤ (S : Subgroup G) := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have e1 : y = v * ((v⁻¹ * y * v) * v⁻¹ * (v⁻¹ * y * v)⁻¹) * (v⁻¹ * y * v) := by group
    rw [e1]
    exact hS (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Q.mul_mem hvQ
      (hQn.conj_mem _ (Q.inv_mem hvQ) _))) (Subgroup.mem_sup_left hy))
  have hcomm : ∀ x ∈ J, ∀ y ∈ conjSub v J, x * y = y * x :=
    Q3CP.l67Gen G Ω hΩ S J (TC.mem_RSet_of_isPGroup hJ hJ2) (conjSub v J)
      (TC.mem_RSet_of_isPGroup hJv' (isPGroup_conjSub v hJ2)) (le_sup_left.trans hS) hJvS
      hJv.symm
  have hcommQ : ∀ x ∈ J, ∀ y ∈ J, x * y * x⁻¹ * y⁻¹ ∈ Q := by
    intro x hx y hy
    have hy' : v * y * v⁻¹ ∈ conjSub v J := conj_mem_conjSub hy
    have hxy' : x * (v * y * v⁻¹) = (v * y * v⁻¹) * x := hcomm x hx _ hy'
    have hmk : QuotientGroup.mk' Q y = QuotientGroup.mk' Q (v * y * v⁻¹) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have h1 : y⁻¹ * (v * y * v⁻¹) = (y⁻¹ * v * y) * v⁻¹ := by group
      rw [h1]
      exact Q.mul_mem (by simpa using hQn.conj_mem v hvQ y⁻¹) (Q.inv_mem hvQ)
    have h1 : QuotientGroup.mk' Q (x * y * x⁻¹ * y⁻¹) = 1 := by
      have h2' : QuotientGroup.mk' Q x * QuotientGroup.mk' Q (v * y * v⁻¹) =
          QuotientGroup.mk' Q (v * y * v⁻¹) * QuotientGroup.mk' Q x := by
        rw [← map_mul, ← map_mul, hxy']
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hmk, h2']
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hcomm_sq : ∀ x ∈ J, ∀ y ∈ J, (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) = 1 := by
    intro x hx y hy
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ J ⊓ Q :=
      ⟨J.mul_mem (J.mul_mem (J.mul_mem hx hy) (J.inv_mem hx)) (J.inv_mem hy), hcommQ x hx y hy⟩
    have hdvd := Subgroup.orderOf_dvd_natCard (J ⊓ Q) hmem
    have hpos : 0 < Nat.card ↥(J ⊓ Q) := Nat.card_pos
    have hord : orderOf (x * y * x⁻¹ * y⁻¹) ∣ 2 := by
      rcases (show Nat.card ↥(J ⊓ Q) = 1 ∨ Nat.card ↥(J ⊓ Q) = 2 by omega) with h | h
      · rw [h] at hdvd
        exact hdvd.trans (one_dvd 2)
      · rwa [h] at hdvd
    have := orderOf_dvd_iff_pow_eq_one.mp hord
    rwa [pow_two] at this
  obtain ⟨x, hx, y, hy, hne⟩ := exists_commutator_sq_ne_one_of_isQuatSub
    (Sec6Gen.isQuatSub_of_mem_RSet hΩ (TC.mem_RSet_of_isPGroup hJ hJ2)) h16
  exact hne (hcomm_sq x hx y hy)

theorem mem_normalizer_of_four_le {r : ℕ} (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r)
    (hinO2 : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
      ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q)
    {J L : Subgroup G} (hJ : J ∈ Ω) (hL : L ∈ Ω) {v : G} (hv : IsUniqueInvolution L v) :
    v ∈ Subgroup.normalizer (J : Set G) := by
  obtain ⟨Q, hQn, hQ2, hvQ⟩ := hinO2 L hL v hv
  refine mem_normalizer_of_sixteen_le hΩ hJ hL (h2 J hJ) (h2 L hL) ?_ hv hQn hQ2 hvQ
  rw [h8 J hJ]
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin in
theorem _root_.CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin.TwinT4Hyp.le_three_of_not_mem_normalizer
    {r : ℕ} {Δ : Set (Subgroup G)} (h : TwinT4Hyp r G Δ) {J L : Subgroup G} (hJ : J ∈ Δ)
    (hL : L ∈ Δ) {u v : G} (hu : IsUniqueInvolution J u) (hv : IsUniqueInvolution L v)
    (hinu : TightInO2 u) (hinv : TightInO2 v) (hvJ : v ∉ Subgroup.normalizer (J : Set G)) :
    r ≤ 3 := by
  by_contra hr
  push Not at hr
  have hJ2 := h.isPGroup_of_inO2 hJ hu hinu
  have hL2 := h.isPGroup_of_inO2 hL hv hinv
  obtain ⟨Q, hQn, hQ2, hvQ⟩ := hinv
  obtain ⟨e⟩ := h.quat J hJ J ⟨le_rfl, hJ2, fun V' hV'J _ hJV' => le_antisymm hV'J hJV'⟩
  have hcard : Nat.card J = 2 ^ r := by
    haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card,
      show 4 * 2 ^ (r - 2) = 2 ^ r by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega]
  exact hvJ (mem_normalizer_of_sixteen_le h.hyp hJ hL hJ2 hL2 (by
    rw [hcard]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)) hv hQn hQ2 hvQ)

end Involutions

section Adjacency

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_omegaStarNbr_of_normalizes {r : ℕ} (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r) (hA : ∀ J ∈ Ω, AEmpty Ω J)
    (hodd : classicalInvolutionOddCore G = ⊥)
    (hinO2 : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
      ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hJK : J ≠ K) {z : G}
    (hz : IsUniqueInvolution K z) (hzJ : z ∈ Subgroup.normalizer (J : Set G)) :
    J ∈ omegaStarNbr Ω K := by
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  obtain ⟨Pu, hPun, hPu2, huP⟩ := hinO2 J hJ u hu
  obtain ⟨Pz, hPzn, hPz2, hzP⟩ := hinO2 K hK z hz
  have : Pu.Normal := hPun
  have : Pz.Normal := hPzn
  have hQn : (Pu ⊔ Pz).Normal := Subgroup.sup_normal Pu Pz
  have hQ2 : IsPGroup 2 ↥(Pu ⊔ Pz) := IsPGroup.to_sup_of_normal_right hPu2 hPz2
  obtain ⟨X, hXJ, hX2, hX4⟩ := (twinT4Hyp_of hΩ h2 h8 hA hodd).exists_le_centralizer hJ hK hu hz
    hQn hQ2 (Subgroup.mem_sup_left huP) (Subgroup.mem_sup_right hzP) hzJ
  by_cases htw : J ∈ twinSet Ω K
  · obtain ⟨-, z', hz'K, hz'J⟩ := htw
    exact Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΩ K
      (Q3CL.T3.twin_mem_omegaNbr hΩ hK hJ hJK hz'K hz'J)
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  obtain ⟨V, hV, hXV⟩ := IsSylow2In.exists_ge hX2 hXJ
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  have hV4 : 4 ≤ Nat.card V := hX4.trans (Subgroup.card_le_of_le hXV)
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
  rcases Sec6Gen.l6_2Gen G Ω hΩ K hK z hz J hJ htw t ht V hV
      (ht.mem_of_le hVJ hV.2.1 (by omega)) with
    ⟨hVt, -⟩ | ⟨hVt, -⟩ | ⟨hVU, hVN, -⟩ | ⟨hVR, hVK⟩
  · rw [hVt, Nat.card_zpowers, ht2] at hV4
    omega
  · rw [hVt, Nat.card_zpowers, ht2] at hV4
    omega
  · exact ⟨hJ, hJK, V, hVU, hVJ, hVN⟩
  ·
    have hVJ' : V = J := ((Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJ hVR hVJ).eq_of_le
      (h2 J hJ) le_rfl hVJ).symm
    rw [hVJ', TL4.oddCoreOf_eq_bot_of_isPGroup (h2 K hK)] at hVK
    have hc : Commutes J K := fun x hx y hy => by
      have hc := hVK (Subgroup.commutator_mem_commutator hx hy)
      rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΩ K
      ((TC.mem_omegaNbr_iff hΩ h2).mpr ⟨hJ, hJK, Asc77.AscL62.le_normalizer_of_commutes hc⟩)

end Adjacency

section USetStructure

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_of_mem_USet_of_le {r : ℕ} (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r) {K U V : Subgroup G}
    (hK : K ∈ Ω) (hU : U ∈ USet Ω) (hV : V ∈ USet Ω) (hUK : U ≤ K) (hVK : V ≤ K) : U = V := by
  have hq : IsQuatSub K :=
    Sec6Gen.isQuatSub_of_mem_RSet hΩ (TC.mem_RSet_of_isPGroup hK (h2 K hK))
  have h16 : 16 ≤ Nat.card K := by
    rw [h8 K hK]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have key : ∀ W : Subgroup G, W ∈ USet Ω → W ≤ K →
      IsCyclic ↥W ∧ Nat.card K = 2 * Nat.card W := by
    intro W hW hWK
    obtain ⟨R, -, J, hJ, hRJ, hWR, hcW, hRW, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hW
    have hJK : J = K := Sec6Gen.eq_of_mem_USet hΩ hW hJ hK (hWR.trans hRJ.1) hWK
    rw [hJK] at hRJ
    have hRK : R = K := (hRJ.2.2 K le_rfl (h2 K hK) hRJ.1).symm
    exact ⟨hcW, hRK ▸ hRW⟩
  obtain ⟨hcU, hcardU⟩ := key U hU hUK
  obtain ⟨hcV, hcardV⟩ := key V hV hVK
  exact hq.eq_of_cyclic hUK hVK hcU hcV hcardU hcardV h16

theorem mem_normalizer_of_mem_USet {r : ℕ} (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r) {K U : Subgroup G}
    (hK : K ∈ Ω) (hU : U ∈ USet Ω) (hUK : U ≤ K) {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) : n ∈ Subgroup.normalizer (U : Set G) := by
  have hnK : conjSub n K = K := mem_normalizer_iff_conjSub_eq.mp hn
  have hUn : conjSub n U ∈ USet Ω := USet.conj hΩ.conjInvariant hU n
  have hle : conjSub n U ≤ K := by
    have := conjSub_mono (n := n) hUK
    rwa [hnK] at this
  exact mem_normalizer_iff_conjSub_eq.mpr
    (eq_of_mem_USet_of_le hr hΩ h2 h8 hK hUn hU hle hUK)

theorem le_normalizer_of_four_le {r : ℕ} (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r)
    (hA : ∀ J ∈ Ω, AEmpty Ω J) (hodd : classicalInvolutionOddCore G = ⊥)
    (hinO2 : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
      ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q)
    {U U' : Subgroup G} (hU : U ∈ USet Ω) (hU' : U' ∈ USet Ω) :
    U' ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨K, hK, hUK⟩ := Sec6Gen.exists_member_of_mem_USet hΩ hU
  obtain ⟨J, hJ, hU'J⟩ := Sec6Gen.exists_member_of_mem_USet hΩ hU'
  by_cases hJK : J = K
  · subst hJK
    have := eq_of_mem_USet_of_le hr hΩ h2 h8 hJ hU' hU hU'J hUK
    rw [this]
    exact Subgroup.le_normalizer
  · obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
    have hstar := mem_omegaStarNbr_of_normalizes hΩ h2 h8 hA hodd hinO2 hK hJ hJK hz
      (mem_normalizer_of_four_le hr hΩ h2 h8 hinO2 hJ hK hz)
    obtain ⟨-, -, U'', hU'', hU''J, hU''N⟩ := hstar
    have hUeq : U'' = U' := eq_of_mem_USet_of_le hr hΩ h2 h8 hJ hU'' hU' hU''J hU'J
    intro n hn
    have hnU'' : n ∈ U'' := by rw [hUeq]; exact hn
    exact mem_normalizer_of_mem_USet hr hΩ h2 h8 hK hU hUK (hU''N hnU'')

end USetStructure

section WSetStructure

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem isPGroup_iSup_uSet (hΩ : HypOmegaGen Ω)
    (hnorm : ∀ U ∈ USet Ω, ∀ U' ∈ USet Ω, U' ≤ Subgroup.normalizer (U : Set G)) :
    IsPGroup 2 ↥(⨆ U ∈ USet Ω, U) := by
  set Y : Subgroup G := ⨆ U ∈ USet Ω, U with hY
  have hUY : ∀ U ∈ USet Ω, U ≤ Y := fun U hU =>
    le_iSup₂ (f := fun U (_ : U ∈ USet Ω) => U) U hU
  have hYN : ∀ U ∈ USet Ω, Y ≤ Subgroup.normalizer (U : Set G) := fun U hU =>
    iSup₂_le fun U' hU' => hnorm U hU U' hU'
  have hP : IsPGroup 2 ↥((pCore 2 ↥Y).map Y.subtype) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map Y.subtype
  refine hP.to_le (iSup₂_le fun U hU => ?_)
  have hn : (U.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hUY U hU)).mpr (hYN U hU)
  have h2 : IsPGroup 2 ↥(U.subgroupOf Y) := (Sec6Gen.isPGroup_of_mem_USet hΩ hU).comap_subtype
  have hle : U.subgroupOf Y ≤ pCore 2 ↥Y := le_sSup ⟨hn, h2⟩
  calc U = (U.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le (hUY U hU)).symm
    _ ≤ (pCore 2 ↥Y).map Y.subtype := Subgroup.map_mono hle

theorem normal_iSup_uSet (hΩ : HypOmegaGen Ω) : (⨆ U ∈ USet Ω, U : Subgroup G).Normal := by
  refine ⟨fun y hy g => ?_⟩
  have hle : conjSub g (⨆ U ∈ USet Ω, U) ≤ ⨆ U ∈ USet Ω, U := by
    simp only [conjSub, Subgroup.map_iSup]
    exact iSup₂_le fun U hU => le_iSup₂_of_le (conjSub g U)
      (USet.conj hΩ.conjInvariant hU g) le_rfl
  exact hle (conj_mem_conjSub hy)

theorem iSup_uSet_le_pCore (hΩ : HypOmegaGen Ω)
    (hnorm : ∀ U ∈ USet Ω, ∀ U' ∈ USet Ω, U' ≤ Subgroup.normalizer (U : Set G)) :
    (⨆ U ∈ USet Ω, U : Subgroup G) ≤ pCore 2 G :=
  le_sSup ⟨normal_iSup_uSet hΩ, isPGroup_iSup_uSet hΩ hnorm⟩

theorem etaSet_eq_of_forall_le {r : ℕ} (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r) {S : Subgroup G}
    (hS : ∀ U ∈ USet Ω, U ≤ S) : etaSet Ω S = {USet Ω} := by
  have hmem : USet Ω ∈ etaSet Ω S := by
    refine Sec6Gen.mem_etaSet_of_cover hΩ (fun U hU => ⟨hU, hS U hU⟩) ?_ ?_
    · intro U hU U' hU' hne J hJ hUJ
      exact hne (eq_of_mem_USet_of_le hr hΩ h2 h8 hJ hU hU' hUJ.1 hUJ.2)
    · rintro K hK ⟨U, hU, hUK⟩
      exact ⟨U, hU.1, hUK⟩
  ext η
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hη
    refine Set.Subset.antisymm (fun U hU => (hη.1 hU).1) fun U hU => ?_
    obtain ⟨K, hK, hUK⟩ := Sec6Gen.exists_member_of_mem_USet hΩ hU
    obtain ⟨V, hV, hVK⟩ := Sec6Gen.exists_mem_of_mem_etaSet hΩ hη hK ⟨hU, hS U hU⟩ hUK
    have := eq_of_mem_USet_of_le hr hΩ h2 h8 hK (hη.1 hV).1 hU hVK hUK
    rwa [← this]
  · rintro rfl
    exact hmem

theorem etaG_eq_of_forall_le {r : ℕ} (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r)
    (hS : ∀ S : Sylow 2 G, ∀ U ∈ USet Ω, U ≤ (S : Subgroup G)) : etaG Ω = {USet Ω} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext η
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨S, hη, -⟩
    rwa [etaSet_eq_of_forall_le hr hΩ h2 h8 (hS S), Set.mem_singleton_iff] at hη
  · rintro rfl
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
    exact ⟨S, by rw [etaSet_eq_of_forall_le hr hΩ h2 h8 (hS S)]; rfl,
      fun s _ U hU => USet.conj hΩ.conjInvariant hU s⟩

theorem wSet_eq_of_forall_le {r : ℕ} (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r)
    (hS : ∀ S : Sylow 2 G, ∀ U ∈ USet Ω, U ≤ (S : Subgroup G)) :
    WSet Ω = {⨆ U ∈ USet Ω, U} := by
  ext W
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨η, hη, rfl⟩
    rw [etaG_eq_of_forall_le hr hΩ h2 h8 hS, Set.mem_singleton_iff] at hη
    rw [hη]
  · rintro rfl
    exact ⟨USet Ω, by rw [etaG_eq_of_forall_le hr hΩ h2 h8 hS]; rfl, rfl⟩

theorem wSet_eq_singleton_of_four_le {r : ℕ} (hr : 4 ≤ r) (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r)
    (hA : ∀ J ∈ Ω, AEmpty Ω J) (hodd : classicalInvolutionOddCore G = ⊥)
    (hinO2 : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
      ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q) :
    ∃ W : Subgroup G, WSet Ω = {W} := by
  have hnorm : ∀ U ∈ USet Ω, ∀ U' ∈ USet Ω, U' ≤ Subgroup.normalizer (U : Set G) :=
    fun U hU U' hU' => le_normalizer_of_four_le hr hΩ h2 h8 hA hodd hinO2 hU hU'
  have hS : ∀ S : Sylow 2 G, ∀ U ∈ USet Ω, U ≤ (S : Subgroup G) := fun S U hU =>
    (le_iSup₂ (f := fun U (_ : U ∈ USet Ω) => U) U hU).trans
      ((iSup_uSet_le_pCore hΩ hnorm).trans (IsPGroup.le_sylow_of_normal pCore_isPGroup S))
  exact ⟨_, wSet_eq_of_forall_le hr hΩ h2 h8 hS⟩

end WSetStructure

section Packaging

theorem thmDAbsCollapsedAt_of_four_le {r : ℕ} (hr : 4 ≤ r) (G : Type) [Group G] [Finite G] :
    ThmDAbsCollapsedAt r G :=
  fun _ hΩ h2 h8 hA _ _ hodd hinO2 =>
    Or.inr (wSet_eq_singleton_of_four_le hr hΩ h2 h8 hA hodd hinO2)

theorem thmDAbs_of_four_le {r : ℕ} (hr : 4 ≤ r) : ThmDAbs r :=
  thmDAbs_of_collapsed fun G _ _ => thmDAbsCollapsedAt_of_four_le hr G

end Packaging

end CFSG.CGT.PushingUpLit.SolKNA.R4
