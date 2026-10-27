module

public import CFSG.ClassicalInvolution.Asc77.AscT3Z2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section Arith

theorem r_int_identity {k : ℕ} (hk : 2 ≤ k) (c' : ℤ) :
    (2 : ℤ) ^ (k + 1) ∣ ((2 : ℤ) ^ k - 2) * (c' * ((2 : ℤ) ^ (k - 1) + 1) - (2 : ℤ) ^ (k - 1)) +
      2 * c' + (2 : ℤ) ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have h1 : (2 : ℤ) ^ (m + 2 - 1) = 2 ^ (m + 1) := by
    rw [show m + 2 - 1 = m + 1 by omega]
  rw [h1]
  refine ⟨(c' - 1) * 2 ^ m + 1, ?_⟩
  ring

end Arith

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.r_inverted_elt [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) {b : G}
    (hb : FieldInv20 S K K' W z t b) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k - 1)) :
    ∃ r ∈ R, r ∉ W ∧ b * r * b⁻¹ = r⁻¹ := by
  obtain ⟨hbN, -⟩ := d.x_fieldData c9 h8 hb
  have hbK : conjSub b K = K := mem_normalizer_iff_conjSub_eq.mp hbN
  have hbS := hb.mem
  have hb2 := hb.sq
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hbb : b⁻¹ * b⁻¹ = 1 := by rw [← mul_inv_rev, hb2, inv_one]
  have hcR : Nat.card ↥R = 2 * Nat.card ↥(K ⊓ W) :=
    Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp d.late_KW d.late_mem_K d.hR
  obtain ⟨r₀, hr₀R, hr₀W⟩ : ∃ r ∈ R, r ∉ W := by
    by_contra hcon
    push Not at hcon
    have hle : R ≤ K ⊓ W := le_inf d.hR.1 fun x hx => hcon x hx
    have h1 := Subgroup.card_le_of_le hle
    have hpos : 0 < Nat.card ↥(K ⊓ W) := Nat.card_pos
    omega
  obtain ⟨hinv, hr₀sq⟩ := d.w_conj_facts hr₀R hr₀W
  obtain ⟨u₀, -, hd⟩ := d.w_dData hr₀R hr₀W
  have hr₀K : r₀ ∈ K := d.hR.1 hr₀R
  have hKWR : K ⊓ W ≤ R := by
    rw [d.late_R_eq]
    exact inf_le_inf_left K d.hWS
  have hI := d.viol.hzK
  have hzW := d.late_z_mem_W
  have hzu : z = u ^ ((2 : ℤ) ^ k) := by
    have h := (w_isUniqueInvolution_zpowers huo).unique z (hu ▸ ⟨hI.mem, hzW⟩) hI.sq
    have h' : z = u ^ 2 ^ k := h.resolve_left hI.ne_one
    rw [h', show ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hmem : ∀ n : ℤ, u ^ n ∈ K ⊓ W := fun n => by
    rw [← hu]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) n
  have hconj : ∀ n : ℤ, b * u ^ n * b⁻¹ = u ^ (n * ((2 : ℤ) ^ k - 1)) := fun n => by
    rw [hact _ (hmem n), ← zpow_mul]
  have hr₀u : ∀ m : ℤ, r₀ * u ^ m = u ^ (-m) * r₀ := fun m => by
    have h := hinv _ (hmem m)
    calc r₀ * u ^ m = (r₀ * u ^ m * r₀⁻¹) * r₀ := by group
      _ = (u ^ m)⁻¹ * r₀ := by rw [h]
      _ = u ^ (-m) * r₀ := by rw [zpow_neg]
  have hord : ∀ n : ℤ, (2 : ℤ) ^ (k + 1) ∣ n → u ^ n = 1 := fun n hn => by
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [huo]
    simpa using hn
  have hbr₀R : b * r₀ * b⁻¹ ∈ R := by
    rw [d.late_R_eq]
    refine ⟨?_, S.mul_mem (S.mul_mem hbS (d.hRS hr₀R)) (S.inv_mem hbS)⟩
    have := conj_mem_conjSub (n := b) hr₀K
    rwa [hbK] at this
  have hbr₀W : b * r₀ * b⁻¹ ∉ W := by
    intro hW
    apply hr₀W
    have h1 := (Subgroup.mem_normalizer_iff.mp (d.hWN (S.inv_mem hbS)) _).mp hW
    have e : b⁻¹ * (b * r₀ * b⁻¹) * b⁻¹⁻¹ = r₀ := by group
    rwa [e] at h1
  obtain ⟨y, hyW, hy⟩ := late_dData_cover hd hbr₀R hbr₀W
  have hyK : y ∈ K := by
    have h1 : y = (b * r₀ * b⁻¹) * r₀⁻¹ := by rw [hy]; group
    rw [h1]
    exact K.mul_mem (d.hR.1 hbr₀R) (K.inv_mem hr₀K)
  have hyKW : y ∈ K ⊓ W := ⟨hyK, hyW⟩
  rw [← hu] at hyKW
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp hyKW
  have hbr₀ : b * r₀ * b⁻¹ = u ^ c * r₀ := by rw [hc]; exact hy
  have hord' : ∀ n : ℤ, u ^ n = 1 → (2 : ℤ) ^ (k + 1) ∣ n := fun n hn => by
    have := orderOf_dvd_iff_zpow_eq_one.mpr hn
    rw [huo] at this
    simpa using this
  have hc2 : (2 : ℤ) ∣ c := by
    have e1 : b * (b * r₀ * b⁻¹) * b⁻¹ = (b * b) * r₀ * (b⁻¹ * b⁻¹) := by group
    rw [hb2, hbb, one_mul, mul_one] at e1
    have e2 : r₀ = (b * u ^ c * b⁻¹) * (b * r₀ * b⁻¹) := by
      calc r₀ = b * (b * r₀ * b⁻¹) * b⁻¹ := e1.symm
        _ = b * (u ^ c * r₀) * b⁻¹ := by rw [hbr₀]
        _ = (b * u ^ c * b⁻¹) * (b * r₀ * b⁻¹) := by group
    rw [hconj c, hbr₀, ← mul_assoc, ← zpow_add] at e2
    have e3 : u ^ (c * ((2 : ℤ) ^ k - 1) + c) = 1 :=
      mul_right_cancel (b := r₀) (by rw [one_mul]; exact e2.symm)
    have h1 : (2 : ℤ) ^ (k + 1) ∣ c * ((2 : ℤ) ^ k - 1) + c := hord' _ e3
    have h3 : c * ((2 : ℤ) ^ k - 1) + c = 2 ^ k * c := by ring
    rw [h3, pow_succ] at h1
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).mp h1
  obtain ⟨c', rfl⟩ := hc2
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = c' * ((2 : ℤ) ^ (k - 1) + 1) - (2 : ℤ) ^ (k - 1) := ⟨_, rfl⟩
  refine ⟨u ^ j * r₀, R.mul_mem (hKWR (hmem j)) hr₀R, ?_, ?_⟩
  · intro hrW
    apply hr₀W
    have := W.mul_mem (W.inv_mem (hmem j).2) hrW
    simpa using this
  · have hr₀inv : r₀⁻¹ = r₀ * z⁻¹ := by rw [← hr₀sq]; group
    have hrinv : (u ^ j * r₀)⁻¹ = u ^ (j + (2 : ℤ) ^ k) * r₀ := by
      have e1 : (u ^ j * r₀)⁻¹ = r₀ * u ^ (-((2 : ℤ) ^ k) + -j) := by
        rw [mul_inv_rev, hr₀inv, hzu, zpow_add, zpow_neg, zpow_neg, mul_assoc]
      rw [e1, hr₀u]
      congr 2
      ring
    have hbr : b * (u ^ j * r₀) * b⁻¹ = u ^ (j * ((2 : ℤ) ^ k - 1) + 2 * c') * r₀ := by
      calc b * (u ^ j * r₀) * b⁻¹ = (b * u ^ j * b⁻¹) * (b * r₀ * b⁻¹) := by group
        _ = u ^ (j * ((2 : ℤ) ^ k - 1)) * (u ^ (2 * c') * r₀) := by rw [hconj j, hbr₀]
        _ = u ^ (j * ((2 : ℤ) ^ k - 1) + 2 * c') * r₀ := by rw [← mul_assoc, ← zpow_add]
    rw [hbr, hrinv]
    congr 1
    have e : u ^ (j * ((2 : ℤ) ^ k - 1) + 2 * c' - (j + (2 : ℤ) ^ k)) = 1 := by
      apply hord
      have h0 := r_int_identity hk c'
      rw [← hj] at h0
      have h2 : j * ((2 : ℤ) ^ k - 1) + 2 * c' - (j + (2 : ℤ) ^ k) =
          ((2 : ℤ) ^ k - 2) * j + 2 * c' + 2 ^ k - 2 ^ (k + 1) := by ring
      rw [h2]
      exact dvd_sub h0 (dvd_refl _)
    rwa [zpow_sub, mul_inv_eq_one] at e

theorem Std20.r_swap_elt [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t) {r s : G}
    (hrR : r ∈ R) (hrW : r ∉ W) (hsS : s ∈ (S : Subgroup G)) (hsK : conjSub s K = K') :
    s * r * s⁻¹ ∈ R' ∧ (s * r * s⁻¹) * t * (s * r * s⁻¹)⁻¹ = z * t := by
  have hI := d.viol.hzK
  obtain ⟨-, hr2⟩ := d.w_conj_facts hrR hrW
  have hrt := d.w_conj_t hrR hrW
  have hrz : r * z = z * r := by rw [← hr2, ← mul_assoc]
  have hsz : s * z * s⁻¹ = z := d.late_S_act_z hsS
  refine ⟨?_, ?_⟩
  · rw [d.late_R'_eq]
    refine ⟨?_, (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hsS (d.hRS hrR))
      ((S : Subgroup G).inv_mem hsS)⟩
    have := conj_mem_conjSub (n := s) (d.hR.1 hrR)
    rwa [hsK] at this
  · have hrzr : r * z * r⁻¹ = z := by rw [hrz]; group
    have hzzt : z * (z * t) = t := by rw [← mul_assoc, hI.sq, one_mul]
    have key : (s * r * s⁻¹) * t * (s * r * s⁻¹)⁻¹ = s * (r * (s⁻¹ * t * s) * r⁻¹) * s⁻¹ := by
      group
    have e0 : t = s * (s⁻¹ * t * s) * s⁻¹ := by group
    rw [key]
    rcases d.late_S_act_t ((S : Subgroup G).inv_mem hsS) with hst | hst
    · rw [inv_inv] at hst
      rw [hst] at e0 ⊢
      rw [hrt]
      calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
        _ = z * t := by rw [hsz, ← e0]
    · rw [inv_inv] at hst
      rw [hst] at e0 ⊢
      have e1 : s * (z * t) * s⁻¹ = z * (s * t * s⁻¹) := by
        calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
          _ = z * (s * t * s⁻¹) := by rw [hsz]
      rw [e1] at e0
      have e2 : s * t * s⁻¹ = z * t := by
        calc s * t * s⁻¹ = z * (z * (s * t * s⁻¹)) := by rw [← mul_assoc, hI.sq, one_mul]
          _ = z * t := by rw [← e0]
      calc s * (r * (z * t) * r⁻¹) * s⁻¹ = s * ((r * z * r⁻¹) * (r * t * r⁻¹)) * s⁻¹ := by group
        _ = s * t * s⁻¹ := by rw [hrzr, hrt, hzzt]
        _ = z * t := e2

theorem Std20.r_exists_plus [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) {b : G}
    (hb : FieldInv20 S K K' W z t b) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k - 1)) :
    ∃ b' : G, FieldInv20 S K K' W z t b' ∧
      ∀ x ∈ K ⊓ W, b' * x * b'⁻¹ = x ^ ((2 : ℤ) ^ k + 1) := by
  obtain ⟨r, hrR, hrW, hbr⟩ := d.r_inverted_elt c9 h8 hb hk hu huo hact
  obtain ⟨s, hsS, hsK, hsb⟩ := d.z_exists_swap c7 c9 h8 hb
  have hbS := hb.mem
  have hb2 := hb.sq
  have hI := d.viol.hzK
  obtain ⟨hr'R', hr't⟩ := d.r_swap_elt hrR hrW hsS hsK
  obtain ⟨hrinv, hr2⟩ := d.w_conj_facts hrR hrW
  have hrt := d.w_conj_t hrR hrW
  have hrz : r * z = z * r := by rw [← hr2, ← mul_assoc]
  have hrK : r ∈ K := d.hR.1 hrR
  have hrS : r ∈ (S : Subgroup G) := d.hRS hrR
  have hKWR : K ⊓ W ≤ R := by
    rw [d.late_R_eq]
    exact inf_le_inf_left K d.hWS
  have hbs : b * s * b⁻¹ = s := by rw [← hsb]; group
  have hbsi : b * s⁻¹ * b⁻¹ = s⁻¹ := by
    have : b * s⁻¹ * b⁻¹ = (b * s * b⁻¹)⁻¹ := by group
    rw [this, hbs]
  have hbr' : b * (s * r * s⁻¹) * b⁻¹ = (s * r * s⁻¹)⁻¹ := by
    calc b * (s * r * s⁻¹) * b⁻¹ = (b * s * b⁻¹) * (b * r * b⁻¹) * (b * s⁻¹ * b⁻¹) := by group
      _ = s * r⁻¹ * s⁻¹ := by rw [hbs, hbr, hbsi]
      _ = (s * r * s⁻¹)⁻¹ := by group
  generalize s * r * s⁻¹ = r' at hr'R' hr't hbr'
  have hcomm : r * r' = r' * r := d.late_R_R'_comm hrR hr'R'
  have hr'K' : r' ∈ K' := d.hR'.1 hr'R'
  have hρX : r * r' ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
    (sec20X (CoreAssembly.conjClass K) z K K').mul_mem (le_sec20X_left hrK) (le_sec20X_right hr'K')
  have hρinv : (r * r')⁻¹ = r⁻¹ * r'⁻¹ := by rw [hcomm, mul_inv_rev]
  have hρb : b * (r * r') * b⁻¹ = (r * r')⁻¹ := by
    calc b * (r * r') * b⁻¹ = (b * r * b⁻¹) * (b * r' * b⁻¹) := by group
      _ = (r * r')⁻¹ := by rw [hbr, hbr', hρinv]
  have hρt : (r * r') * t * (r * r')⁻¹ = t := by
    have hzzt : z * (z * t) = t := by rw [← mul_assoc, hI.sq, one_mul]
    calc (r * r') * t * (r * r')⁻¹ = r * (r' * t * r'⁻¹) * r⁻¹ := by group
      _ = r * (z * t) * r⁻¹ := by rw [hr't]
      _ = (r * z * r⁻¹) * (r * t * r⁻¹) := by group
      _ = z * (z * t) := by rw [hrt, show r * z * r⁻¹ = z by rw [hrz]; group]
      _ = t := hzzt
  have hbt : b * t * b⁻¹ = t := by rw [hb.comm_t]; group
  have hb't : b * (r * r') * t * (b * (r * r'))⁻¹ = t := by
    calc b * (r * r') * t * (b * (r * r'))⁻¹ = b * ((r * r') * t * (r * r')⁻¹) * b⁻¹ := by group
      _ = b * t * b⁻¹ := by rw [hρt]
      _ = t := hbt
  have hplus : ∀ x ∈ K ⊓ W, b * (r * r') * x * (b * (r * r'))⁻¹ = x ^ ((2 : ℤ) ^ k + 1) := by
    intro x hx
    have hxr' : x * r' = r' * x := d.late_R_R'_comm (hKWR hx) hr'R'
    have hρx : (r * r') * x * (r * r')⁻¹ = x⁻¹ := by
      calc (r * r') * x * (r * r')⁻¹ = r * (r' * x * r'⁻¹) * r⁻¹ := by group
        _ = r * x * r⁻¹ := by rw [← hxr']; group
        _ = x⁻¹ := hrinv x hx
    have hxo : x ^ ((2 : ℤ) ^ (k + 1)) = 1 := by
      rw [← hu] at hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_mul, mul_comm, zpow_mul, show ((2 : ℤ) ^ (k + 1)) = ((2 ^ (k + 1) : ℕ) : ℤ) by
        push_cast; ring, zpow_natCast, ← huo, pow_orderOf_eq_one, one_zpow]
    calc b * (r * r') * x * (b * (r * r'))⁻¹ = b * ((r * r') * x * (r * r')⁻¹) * b⁻¹ := by group
      _ = (b * x * b⁻¹)⁻¹ := by rw [hρx]; group
      _ = (x ^ ((2 : ℤ) ^ k - 1))⁻¹ := by rw [hact x hx]
      _ = x ^ ((2 : ℤ) ^ k + 1) * (x ^ ((2 : ℤ) ^ (k + 1)))⁻¹ := by
          rw [← zpow_neg, ← zpow_neg, ← zpow_add]
          congr 1
          ring
      _ = x ^ ((2 : ℤ) ^ k + 1) := by rw [hxo, inv_one, mul_one]
  have hmem : b * (r * r') ∈ (S : Subgroup G) :=
    (S : Subgroup G).mul_mem hbS ((S : Subgroup G).mul_mem hrS (d.hR'S hr'R'))
  have hsq : b * (r * r') * (b * (r * r')) = 1 := by
    calc b * (r * r') * (b * (r * r')) = (b * (r * r') * b⁻¹) * (b * b) * (r * r') := by group
      _ = 1 := by rw [hρb, hb2, mul_one, inv_mul_cancel]
  have hat : b * (r * r') * t * (b * (r * r'))⁻¹ = t := hb't
  refine ⟨b * (r * r'), ⟨hmem, hsq, ?_, ?_, ?_, u, k, hk, hu, huo, Or.inl hplus⟩, hplus⟩
  · intro h
    apply hb.not_mem_X
    have := (sec20X (CoreAssembly.conjClass K) z K K').mul_mem h
      ((sec20X (CoreAssembly.conjClass K) z K K').inv_mem hρX)
    rwa [mul_inv_cancel_right] at this
  · calc b * (r * r') * t = b * (r * r') * t * (b * (r * r'))⁻¹ * (b * (r * r')) := by group
      _ = t * (b * (r * r')) := by rw [hb't]
  · exact d.v_conj_t hmem hsq hat hk hu huo (Or.inl hplus)

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
