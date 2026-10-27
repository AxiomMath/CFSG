module

public import CFSG.LargeExtraspecial.AS35LPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZM

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary AS35L
open CFSG.Blueprint.Fischer (K)

variable {L : Type} [Group L] {D : Set L} (hD : IsTClass D) {k : ℕ} (hk : 2 ≤ k)
include hD hk

theorem exists_normalized (ψ : L ⧸ center L ≃* PG (k + 2)) {r t : L} (hr : r ∈ D) (ht : t ∈ D)
    (hrt : r * t ≠ t * r) :
    ∃ ψ' : L ⧸ center L ≃* PG (k + 2), ψ' (QuotientGroup.mk r) = tq (v₀ k) ∧
      ψ' (QuotientGroup.mk t) = tq (u₀ k) := by
  obtain ⟨a, ha0, ha, hra⟩ := hD.mem_DG hk ψ hr
  obtain ⟨b, hb0, hb, htb⟩ := hD.mem_DG hk ψ ht
  have hab : herm frob a b ≠ 0 := by
    intro h0
    apply hrt
    rw [hD.commute_iff hk ψ hr ht, ← hra, ← htb]
    exact (tq_commute_iff (by omega) ha0 ha hb0 hb).2 h0
  set c : K := (herm frob a b)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hab
  have hb' : herm frob (c • b) (c • b) = 0 := herm_smul_smul_self hb c
  have hab' : herm frob a (c • b) = 1 := by rw [herm_smul_right, hc, inv_mul_cancel₀ hab]
  obtain ⟨g, hga, hgb⟩ := exists_smul_eq_hyp (by omega : 1 ≤ k) ha0 ha hb' hab'
  refine ⟨ψ.trans (MulAut.conj (QuotientGroup.mk g : PG (k + 2))), ?_, ?_⟩
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, ← hra, conj_tq g ha, hga]
  · have htq : tq b = tq (c • b) := by
      change (QuotientGroup.mk (tvU b) : PG (k + 2)) = QuotientGroup.mk (tvU (c • b))
      rw [tvU_smul_vec hb hc0]
    rw [MulEquiv.trans_apply, MulAut.conj_apply, ← htb, htq, conj_tq g hb', hgb]

omit hD hk in
theorem exists_sep_vec {m : ℕ} {z z' : Fin m → K} (hz0 : z ≠ 0) (hz : herm frob z z = 0)
    (hzz' : herm frob z z' = 0) (hind : ∀ c : K, z' ≠ c • z) :
    ∃ w : Fin m → K, w ≠ 0 ∧ herm frob w w = 0 ∧ herm frob z' w = 0 ∧ herm frob z w ≠ 0 := by
  obtain ⟨c₀, hc₀', hc₀⟩ : ∃ c₀ : Fin m → K, herm frob z' c₀ = 0 ∧ herm frob z c₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    by_cases hz'0 : z' = 0
    · exact hz0 (eq_zero_of_herm frob fun v => hcon v (by rw [hz'0, herm_zero_left]))
    obtain ⟨y, hy⟩ := exists_herm_eq_one frob hz'0
    have key : ∀ v, herm frob (z - frob (herm frob z y) • z') v = 0 := by
      intro v
      have h := hcon (v - herm frob z' v • y)
        (by rw [herm_sub_right, herm_smul_right, hy, mul_one, sub_self])
      rw [herm_sub_right, herm_smul_right, sub_eq_zero] at h
      rw [herm_sub_left, herm_smul_left, frob_frob, h, mul_comm, sub_self]
    obtain ⟨μ₀, hzz⟩ : ∃ μ₀ : K, z = μ₀ • z' :=
      ⟨_, sub_eq_zero.1 (eq_zero_of_herm frob key)⟩
    have hc : μ₀ ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hzz
      exact hz0 hzz
    apply hind μ₀⁻¹
    rw [hzz, smul_smul, inv_mul_cancel₀ hc, one_smul]
  set β := herm frob z c₀ with hβ
  obtain ⟨a, ha⟩ := AS35L.exists_add_frob_eq (herm_self_eq_zero_or_one c₀)
  set μ : K := frob (a * β⁻¹) with hμ
  have hfμ : frob μ * β = a := by rw [hμ, frob_frob, mul_assoc, inv_mul_cancel₀ hc₀, mul_one]
  have hz'z : herm frob z' z = 0 := herm_eq_zero_comm frob frob_frob hzz'
  have hc₀z : herm frob c₀ z = frob β := herm_conj frob frob_frob z c₀
  have hw : herm frob (c₀ + μ • z) (c₀ + μ • z) = 0 := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hz, mul_zero,
      add_zero, hc₀z, ← hβ]
    have e : μ * frob β = frob a := by rw [← hfμ, map_mul, frob_frob, mul_comm]
    rw [e, hfμ, add_assoc, ha]
    exact add_self_K _
  have hzw : herm frob z (c₀ + μ • z) = β := by
    rw [herm_add_right, herm_smul_right, hz, mul_zero, add_zero]
  refine ⟨c₀ + μ • z, fun h0 => hc₀ ?_, hw, ?_, by rw [hzw]; exact hc₀⟩
  · rw [← hzw, h0, herm_zero_right]
  · rw [herm_add_right, herm_smul_right, hz'z, mul_zero, add_zero, hc₀']

omit hD hk in
theorem two_mul_lt {k : ℕ} (i : Fin (k / 2)) : 2 * (i : ℕ) < k := by
  have := i.2
  omega

omit hD hk in
theorem two_mul_add_one_lt {k : ℕ} (i : Fin (k / 2)) : 2 * (i : ℕ) + 1 < k := by
  have := i.2
  omega

@[expose] noncomputable def frameVec {k : ℕ} (i : Fin (k / 2)) (c : K) : Fin k → K :=
  Pi.single ⟨2 * i, two_mul_lt i⟩ 1 + Pi.single ⟨2 * i + 1, two_mul_add_one_lt i⟩ c

omit hD hk in
theorem frameVec_isotropic {k : ℕ} (i : Fin (k / 2)) {c : K} (hc : c ≠ 0) :
    herm frob (frameVec i c) (frameVec i c) = 0 :=
  isotropic_single_add_single (by simp [Fin.ext_iff]) hc

omit hD hk in
theorem frameVec_ne_zero {k : ℕ} (i : Fin (k / 2)) (c : K) : frameVec i c ≠ 0 := by
  intro h
  have := congrFun h ⟨2 * i, two_mul_lt i⟩
  simp [frameVec, Fin.ext_iff] at this

omit hD hk in
theorem herm_frameVec' {k : ℕ} (i j : Fin (k / 2)) (c c' : K) :
    herm frob (frameVec i c) (frameVec j c') =
      frameVec j c' ⟨2 * i, two_mul_lt i⟩ +
        frob c * frameVec j c' ⟨2 * i + 1, two_mul_add_one_lt i⟩ := by
  rw [frameVec, herm_single_add_single_left]

omit hD hk in
theorem frameVec_apply_ne {k : ℕ} {i j : Fin (k / 2)} (hij : i ≠ j) (c : K) :
    frameVec j c ⟨2 * i, two_mul_lt i⟩ = 0 ∧
      frameVec j c ⟨2 * i + 1, two_mul_add_one_lt i⟩ = 0 := by
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  simp only [frameVec, Pi.add_apply]
  have hne : ∀ a b : ℕ, ∀ (ha : a < k) (hb : b < k), a ≠ b →
      (⟨a, ha⟩ : Fin k) ≠ ⟨b, hb⟩ := fun a b _ _ h e => h (Fin.mk.inj e)
  rw [Pi.single_eq_of_ne (hne _ _ _ _ (by omega)), Pi.single_eq_of_ne (hne _ _ _ _ (by omega)),
    Pi.single_eq_of_ne (hne _ _ _ _ (by omega)), Pi.single_eq_of_ne (hne _ _ _ _ (by omega))]
  simp

omit hD hk in
theorem herm_frameVec_ne {k : ℕ} {i j : Fin (k / 2)} (hij : i ≠ j) (c c' : K) :
    herm frob (frameVec i c) (frameVec j c') = 0 := by
  rw [herm_frameVec', (frameVec_apply_ne hij c').1, (frameVec_apply_ne hij c').2, mul_zero,
    add_zero]

omit hD hk in
theorem herm_frameVec_one_omega {k : ℕ} (i : Fin (k / 2)) :
    herm frob (frameVec i 1) (frameVec i ω) ≠ 0 := by
  rw [herm_frameVec' i i 1 ω, map_one, one_mul]
  simp only [frameVec, Pi.add_apply, Pi.single_apply, Fin.mk.injEq]
  simp only [show 2 * (i : ℕ) ≠ 2 * i + 1 by omega, show 2 * (i : ℕ) + 1 ≠ 2 * i by omega,
    ite_true, ite_false, add_zero, zero_add]
  rw [add_comm, ← frob_omega]
  exact frob_ne_zero omega_ne_zero

section Normal

variable (ψ : L ⧸ center L ≃* PG (k + 2)) {r t : L} (hr : r ∈ D) (ht : t ∈ D)
  (hψr : ψ (QuotientGroup.mk r) = tq (v₀ k)) (hψt : ψ (QuotientGroup.mk t) = tq (u₀ k))
include hr ht hψr hψt

theorem exists_vec_of_commute {d : L} (hd : d ∈ D) (hdr : d * r = r * d) (hdt : d * t = t * d) :
    ∃ z : Fin k → K, z ≠ 0 ∧ herm frob z z = 0 ∧ ψ (QuotientGroup.mk d) = tq (ι k z) := by
  obtain ⟨w, hw0, hw, hdw⟩ := hD.mem_DG hk ψ hd
  have h1 : herm frob w (v₀ k) = 0 := by
    have := (hD.commute_iff hk ψ hd hr).1 hdr
    rw [← hdw, hψr] at this
    exact (tq_commute_iff (by omega) hw0 hw v₀_ne_zero herm_v₀_v₀).1 this
  have h2 : herm frob w (u₀ k) = 0 := by
    have := (hD.commute_iff hk ψ hd ht).1 hdt
    rw [← hdw, hψt] at this
    exact (tq_commute_iff (by omega) hw0 hw u₀_ne_zero herm_u₀_u₀).1 this
  have hw' : w = ι k (π k w) := by
    conv_lhs => rw [decomp w]
    rw [herm_eq_zero_comm frob frob_frob h1, herm_eq_zero_comm frob frob_frob h2, zero_smul,
      zero_smul, zero_add, zero_add]
  refine ⟨π k w, fun h0 => hw0 (by rw [hw', h0, map_zero]), ?_, ?_⟩
  · rw [← herm_ι_ι, ← hw']
    exact hw
  · rw [← hdw, ← hw']

omit hr ht hψr hψt in
theorem commute_iff_vec {d e : L} (hd : d ∈ D) (he : e ∈ D) {z z' : Fin k → K} (hz0 : z ≠ 0)
    (hz : herm frob z z = 0) (hz0' : z' ≠ 0) (hz' : herm frob z' z' = 0)
    (hdz : ψ (QuotientGroup.mk d) = tq (ι k z)) (hez : ψ (QuotientGroup.mk e) = tq (ι k z')) :
    d * e = e * d ↔ herm frob z z' = 0 := by
  rw [hD.commute_iff hk ψ hd he, hdz, hez, tq_commute_iff (by omega) (ι_ne_zero hz0)
    (by rw [herm_ι_ι]; exact hz) (ι_ne_zero hz0') (by rw [herm_ι_ι]; exact hz'), herm_ι_ι]

theorem exists_mem_of_vec {z : Fin k → K} (hz0 : z ≠ 0) (hz : herm frob z z = 0) :
    ∃ d ∈ D, ψ (QuotientGroup.mk d) = tq (ι k z) ∧ d * r = r * d ∧ d * t = t * d := by
  have hι : herm frob (ι k z) (ι k z) = 0 := by rw [herm_ι_ι]; exact hz
  obtain ⟨d, hd, hdz⟩ := hD.exists_eq hk ψ (tq_mem_DG (ι_ne_zero hz0) hι)
  refine ⟨d, hd, hdz, ?_, ?_⟩
  · rw [hD.commute_iff hk ψ hd hr, hdz, hψr]
    exact (tq_commute_iff (by omega) (ι_ne_zero hz0) hι v₀_ne_zero herm_v₀_v₀).2
      (herm_ι_v₀ z)
  · rw [hD.commute_iff hk ψ hd ht, hdz, hψt]
    exact (tq_commute_iff (by omega) (ι_ne_zero hz0) hι u₀_ne_zero herm_u₀_u₀).2
      (herm_ι_u₀ z)

omit hr ht hψr hψt in
theorem ne_smul_of_ne {d e : L} (hd : d ∈ D) (he : e ∈ D) (hde : d ≠ e) {z z' : Fin k → K}
    (hz0 : z ≠ 0) (hz : herm frob z z = 0) (hz0' : z' ≠ 0) (hz' : herm frob z' z' = 0)
    (hdz : ψ (QuotientGroup.mk d) = tq (ι k z)) (hez : ψ (QuotientGroup.mk e) = tq (ι k z'))
    (c : K) : z' ≠ c • z := by
  intro hc
  apply hde
  refine hD.mk_injOn hk ψ hd he (ψ.injective ?_)
  rw [hdz, hez, tq_eq_tq_iff (by omega) (ι_ne_zero hz0) (by rw [herm_ι_ι]; exact hz)
    (ι_ne_zero hz0') (by rw [herm_ι_ι]; exact hz')]
  exact ⟨c, by rw [hc, map_smul]⟩

theorem exists_sep {f f' : L} (hf : f ∈ D) (hf' : f' ∈ D) (hfr : f * r = r * f)
    (hft : f * t = t * f) (hf'r : f' * r = r * f') (hf't : f' * t = t * f')
    (hff' : f * f' = f' * f) (hne : f ≠ f') :
    ∃ c ∈ D, c * r = r * c ∧ c * t = t * c ∧ c * f' = f' * c ∧ c * f ≠ f * c := by
  obtain ⟨z, hz0, hz, hfz⟩ := exists_vec_of_commute hD hk ψ hr ht hψr hψt hf hfr hft
  obtain ⟨z', hz0', hz', hfz'⟩ := exists_vec_of_commute hD hk ψ hr ht hψr hψt hf' hf'r hf't
  have hzz' : herm frob z z' = 0 :=
    (commute_iff_vec hD hk ψ hf hf' hz0 hz hz0' hz' hfz hfz').1 hff'
  obtain ⟨w, hw0, hw, hz'w, hzw⟩ :=
    exists_sep_vec hz0 hz hzz' (ne_smul_of_ne hD hk ψ hf hf' hne hz0 hz hz0' hz' hfz hfz')
  obtain ⟨c, hc, hcw, hcr, hct⟩ := exists_mem_of_vec hD hk ψ hr ht hψr hψt hw0 hw
  refine ⟨c, hc, hcr, hct, ?_, ?_⟩
  · exact (commute_iff_vec hD hk ψ hc hf' hw0 hw hz0' hz' hcw hfz').2
      (herm_eq_zero_comm frob frob_frob hz'w)
  · intro h
    exact hzw (herm_eq_zero_comm frob frob_frob
      ((commute_iff_vec hD hk ψ hc hf hw0 hw hz0 hz hcw hfz).1 h))

theorem exists_frame :
    ∃ F G : Fin (k / 2) → L, (∀ i, F i ∈ D ∧ G i ∈ D) ∧
      (∀ i, F i * r = r * F i ∧ F i * t = t * F i ∧ G i * r = r * G i ∧ G i * t = t * G i) ∧
      (∀ i, F i * G i ≠ G i * F i) ∧
      ∀ i j, i ≠ j → F i * F j = F j * F i ∧ F i * G j = G j * F i ∧
        G i * F j = F j * G i ∧ G i * G j = G j * G i := by
  have hF := fun i : Fin (k / 2) => exists_mem_of_vec hD hk ψ hr ht hψr hψt
    (frameVec_ne_zero i 1) (frameVec_isotropic i one_ne_zero)
  have hG := fun i : Fin (k / 2) => exists_mem_of_vec hD hk ψ hr ht hψr hψt
    (frameVec_ne_zero i ω) (frameVec_isotropic i omega_ne_zero)
  choose F hFD hFv hFr hFt using hF
  choose G hGD hGv hGr hGt using hG
  have hc : ∀ {d e : L} (hd : d ∈ D) (he : e ∈ D) {i j : Fin (k / 2)} {c c' : K} (hc : c ≠ 0)
      (hc' : c' ≠ 0), ψ (QuotientGroup.mk d) = tq (ι k (frameVec i c)) →
      ψ (QuotientGroup.mk e) = tq (ι k (frameVec j c')) →
      (d * e = e * d ↔ herm frob (frameVec i c) (frameVec j c') = 0) :=
    fun hd he _ _ _ _ hc hc' hdv hev => commute_iff_vec hD hk ψ hd he (frameVec_ne_zero _ _)
      (frameVec_isotropic _ hc) (frameVec_ne_zero _ _) (frameVec_isotropic _ hc') hdv hev
  refine ⟨F, G, fun i => ⟨hFD i, hGD i⟩, fun i => ⟨hFr i, hFt i, hGr i, hGt i⟩, fun i h => ?_,
    fun i j hij => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact herm_frameVec_one_omega i
      ((hc (hFD i) (hGD i) one_ne_zero omega_ne_zero (hFv i) (hGv i)).1 h)
  · exact (hc (hFD i) (hFD j) one_ne_zero one_ne_zero (hFv i) (hFv j)).2
      (herm_frameVec_ne hij _ _)
  · exact (hc (hFD i) (hGD j) one_ne_zero omega_ne_zero (hFv i) (hGv j)).2
      (herm_frameVec_ne hij _ _)
  · exact (hc (hGD i) (hFD j) omega_ne_zero one_ne_zero (hGv i) (hFv j)).2
      (herm_frameVec_ne hij _ _)
  · exact (hc (hGD i) (hGD j) omega_ne_zero omega_ne_zero (hGv i) (hGv j)).2
      (herm_frameVec_ne hij _ _)

end Normal

end CFSG.LargeExtraspecial.AS35ZM
