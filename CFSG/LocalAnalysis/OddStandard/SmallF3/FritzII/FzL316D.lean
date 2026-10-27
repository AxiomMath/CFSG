module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316B

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem fzl_norm_mem {Q Φ : Subgroup G} {rho : G} (hrho3 : rho ^ 3 = 1)
    (hQ : ∀ q ∈ Q, rho * q * rho⁻¹ ∈ Q) (hc : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Φ)
    (hΦQ : Φ ≤ Q) {p : G} (hp : p ∈ ⁅Q, zpowers rho⁆) :
    p * (rho * p * rho⁻¹) * (rho ^ 2 * p * (rho ^ 2)⁻¹) ∈ Φ := by
  classical
  let Nrm : G → G := fun x => x * (rho * x * rho⁻¹) * (rho ^ 2 * x * (rho ^ 2)⁻¹)
  have hNrm_conj : ∀ x : G, Nrm (rho * x * rho⁻¹) = rho * Nrm x * rho⁻¹ := by
    intro x; simp only [Nrm]; group
  have hr3 : rho * rho * rho = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using hrho3
  have hNQ : (Φ.subgroupOf Q).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hΦQ]
    intro h k hh hk; rw [show k * h * k⁻¹ = ⁅k, h⁆ * h from by group]
    exact Φ.mul_mem (hc k hk h (hΦQ hh)) hh
  let Nq : Subgroup Q := Φ.subgroupOf Q
  haveI : Nq.Normal := hNQ
  let π : Q →* Q ⧸ Nq := QuotientGroup.mk' Nq
  have hcomm : _root_.commutator Q ≤ Nq :=
    Subgroup.commutator_le.mpr fun a _ b _ => hc a a.2 b b.2
  haveI : IsMulCommutative (Q ⧸ Nq) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let cQ : Q →* Q :=
    { toFun := fun x => ⟨rho * (x : G) * rho⁻¹, hQ x x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp [mul_assoc] }
  let nrm : Q → Q := fun x => x * cQ x * cQ (cQ x)
  have hNrm_eq : ∀ (x : G) (hx : x ∈ Q), (nrm ⟨x, hx⟩ : G) = Nrm x := by
    intro x hx
    show x * (rho * x * rho⁻¹) * (rho * (rho * x * rho⁻¹) * rho⁻¹)
        = x * (rho * x * rho⁻¹) * (rho ^ 2 * x * (rho ^ 2)⁻¹)
    group
  let K : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ Nrm x ∈ Φ}
      one_mem' := ⟨Q.one_mem, by simp [Nrm]⟩
      mul_mem' := by
        rintro x y ⟨hxQ, hnx⟩ ⟨hyQ, hny⟩
        refine ⟨Q.mul_mem hxQ hyQ, ?_⟩
        let a : Q := ⟨x, hxQ⟩
        let b : Q := ⟨y, hyQ⟩
        have hnqx : nrm a ∈ Nq := by
          show (nrm a : G) ∈ Φ
          rw [hNrm_eq x hxQ]; exact hnx
        have hnqy : nrm b ∈ Nq := by
          show (nrm b : G) ∈ Φ
          rw [hNrm_eq y hyQ]; exact hny
        have hπa : π (nrm a) = 1 := (QuotientGroup.eq_one_iff (nrm a)).mpr hnqx
        have hπb : π (nrm b) = 1 := (QuotientGroup.eq_one_iff (nrm b)).mpr hnqy
        have hkey : π (nrm (a * b)) = π (nrm a) * π (nrm b) := by
          simp only [nrm, map_mul]
          ac_rfl
        have h1 : π (nrm (a * b)) = 1 := by rw [hkey, hπa, hπb, mul_one]
        have hmem : nrm (a * b) ∈ Nq := (QuotientGroup.eq_one_iff (nrm (a * b))).mp h1
        show Nrm (x * y) ∈ Φ
        rw [← hNrm_eq (x * y) (Q.mul_mem hxQ hyQ)]
        exact hmem
      inv_mem' := by
        rintro x ⟨hxQ, hnx⟩
        refine ⟨Q.inv_mem hxQ, ?_⟩
        let a : Q := ⟨x, hxQ⟩
        have hnqx : nrm a ∈ Nq := by
          show (nrm a : G) ∈ Φ
          rw [hNrm_eq x hxQ]; exact hnx
        have hπa : π (nrm a) = 1 := (QuotientGroup.eq_one_iff (nrm a)).mpr hnqx
        have hkey : π (nrm a⁻¹) = (π (nrm a))⁻¹ := by
          simp only [nrm, map_mul, map_inv, mul_inv_rev]
          ac_rfl
        have h1 : π (nrm a⁻¹) = 1 := by rw [hkey, hπa, inv_one]
        have hmem : nrm a⁻¹ ∈ Nq := (QuotientGroup.eq_one_iff (nrm a⁻¹)).mp h1
        show Nrm x⁻¹ ∈ Φ
        rw [← hNrm_eq x⁻¹ (Q.inv_mem hxQ)]
        exact hmem }
  have hx0Q : ∀ q ∈ Q, ⁅q, rho⁆ ∈ Q := by
    intro q hq
    have h1 : rho * q * rho⁻¹ ∈ Q := hQ q hq
    rw [commutatorElement_def,
      show q * rho * q⁻¹ * rho⁻¹ = q * (rho * q * rho⁻¹)⁻¹ from by group]
    exact Q.mul_mem hq (Q.inv_mem h1)
  have hx0Nrm : ∀ q ∈ Q, Nrm ⁅q, rho⁆ = 1 := by
    intro q _
    have hqy : Nrm (q * (rho * q * rho⁻¹)⁻¹) = 1 := by
      let y : G := rho * q * rho⁻¹
      let z : G := rho ^ 2 * q * (rho ^ 2)⁻¹
      have hzq : rho * z * rho⁻¹ = q := by
        show rho * (rho ^ 2 * q * (rho ^ 2)⁻¹) * rho⁻¹ = q
        calc rho * (rho ^ 2 * q * (rho ^ 2)⁻¹) * rho⁻¹
            = rho ^ 3 * q * (rho ^ 3)⁻¹ := by group
          _ = q := by rw [hrho3]; group
      have h1 : rho * (q * y⁻¹) * rho⁻¹ = y * z⁻¹ := by
        show rho * (q * (rho * q * rho⁻¹)⁻¹) * rho⁻¹
            = (rho * q * rho⁻¹) * (rho ^ 2 * q * (rho ^ 2)⁻¹)⁻¹
        group
      have hy2 : rho ^ 2 * y * (rho ^ 2)⁻¹ = q := by
        show rho ^ 2 * (rho * q * rho⁻¹) * (rho ^ 2)⁻¹ = q
        rw [show rho ^ 2 * (rho * q * rho⁻¹) * (rho ^ 2)⁻¹ = rho * z * rho⁻¹ from by
          show rho ^ 2 * (rho * q * rho⁻¹) * (rho ^ 2)⁻¹
              = rho * (rho ^ 2 * q * (rho ^ 2)⁻¹) * rho⁻¹
          group]
        exact hzq
      have h2 : rho ^ 2 * (q * y⁻¹) * (rho ^ 2)⁻¹ = z * q⁻¹ := by
        show rho ^ 2 * (q * (rho * q * rho⁻¹)⁻¹) * (rho ^ 2)⁻¹
            = (rho ^ 2 * q * (rho ^ 2)⁻¹) * q⁻¹
        rw [show rho ^ 2 * (q * (rho * q * rho⁻¹)⁻¹) * (rho ^ 2)⁻¹
              = (rho ^ 2 * q * (rho ^ 2)⁻¹)
                * (rho ^ 2 * (rho * q * rho⁻¹) * (rho ^ 2)⁻¹)⁻¹ from by group,
            hy2]
      show Nrm (q * y⁻¹) = 1
      simp only [Nrm]
      rw [h1, h2]
      group
    rw [show ⁅q, rho⁆ = q * (rho * q * rho⁻¹)⁻¹ from by
      rw [commutatorElement_def]; group]
    exact hqy
  have hK : ⁅Q, zpowers rho⁆ ≤ K := by
    refine Subgroup.commutator_le.mpr (fun q hq k hk => ?_)
    have hord : orderOf rho ≤ 3 := by
      have hd : orderOf rho ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hrho3
      exact Nat.le_of_dvd (by norm_num) hd
    rw [mem_zpowers_iff_mem_range_orderOf] at hk
    obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_range] at hi
    rw [← hiy]
    have hi3 : i < 3 := lt_of_lt_of_le hi hord
    have hx0K : ⁅q, rho⁆ ∈ K :=
      ⟨hx0Q q hq, by rw [hx0Nrm q hq]; exact Φ.one_mem⟩
    have hx1K : rho * ⁅q, rho⁆ * rho⁻¹ ∈ K := by
      refine ⟨hQ _ (hx0Q q hq), ?_⟩
      rw [hNrm_conj, hx0Nrm q hq]
      simpa using Φ.one_mem
    interval_cases i
    · simp [commutatorElement_def]
    · simpa using hx0K
    · rw [show ⁅q, rho ^ 2⁆ = ⁅q, rho⁆ * (rho * ⁅q, rho⁆ * rho⁻¹) from by
        rw [commutatorElement_def, pow_two]; group]
      exact K.mul_mem hx0K hx1K
  exact (hK hp).2

theorem fzl_card_mod3_of_fpf {Y : Subgroup G} {rho : G} (hrho3 : rho ^ 3 = 1)
    (hY : ∀ y ∈ Y, rho * y * rho⁻¹ ∈ Y) (hfix : ∀ y ∈ Y, rho * y * rho⁻¹ = y → y = 1) :
    Nat.card Y % 3 = 1 := by
  classical
  haveI : Fintype Y := Fintype.ofFinite Y
  let f : Function.End Y := fun y => ⟨rho * (y : G) * rho⁻¹, hY y y.2⟩
  have hr3 : rho * rho * rho = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using hrho3
  have hf3 : f ^ 3 = 1 := by
    funext y; apply Subtype.ext
    change rho * (rho * (rho * (y : G) * rho⁻¹) * rho⁻¹) * rho⁻¹ = (y : G)
    calc rho * (rho * (rho * (y : G) * rho⁻¹) * rho⁻¹) * rho⁻¹
        = rho * rho * rho * (y : G) * (rho * rho * rho)⁻¹ := by group
      _ = (y : G) := by rw [hr3]; group
  have hcardfix : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, ?_⟩, ?_⟩
    · rw [Function.mem_fixedPoints_iff]; apply Subtype.ext; simp [f]
    · intro b; apply Subtype.ext; apply Subtype.ext
      have hb : f b.1 = b.1 := b.2
      have hb' : rho * ((b.1 : Y) : G) * rho⁻¹ = ((b.1 : Y) : G) := by
        have h := congrArg Subtype.val hb
        simpa [f] using h
      exact hfix b.1 b.1.2 hb'
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf3
  rw [hcardfix] at hmod
  rw [Nat.card_eq_fintype_card]
  rw [Nat.ModEq] at hmod
  simpa using hmod

theorem fzl_phiQ_eq_W {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (hP : t ∈ ⁅Q, zpowers rho⁆) :
    fzlPhi Q = W := by
  have hΦW : fzlPhi Q ≤ W :=
    fzl_phi_le_of_elem (fun a ha b hb => h.R_comm a (h.QR ha) b (h.QR hb))
      (fun a ha => h.R_sq a (h.QR ha))
  have hZΦ : Z ≤ fzlPhi Q := by
    intro z hz
    obtain ⟨e, he, hez⟩ := h.Z_sqrt z hz
    rw [← hez]
    exact fzl_sq_mem_phi (h.WQ (h.EW he))
  have htΦ : t ∈ fzlPhi Q := by
    have h1 := fzl_norm_mem h.rho_ord h.rho_nrm_Q
      (fun a ha b hb => fzl_comm_mem_phi ha hb) (hΦW.trans h.WQ) hP
    have h3 : rho ^ 2 * t * (rho ^ 2)⁻¹ = t := by
      calc rho ^ 2 * t * (rho ^ 2)⁻¹
          = rho * (rho * t * rho⁻¹) * rho⁻¹ := by
            rw [pow_two, mul_inv_rev]; group
        _ = t := by simp only [h.rho_t]
    rw [h.rho_t, h3] at h1
    have htt : t * t * t = t := by rw [← pow_two, h.t_sq, one_mul]
    rw [htt] at h1
    exact h1
  have hmapQ : Q.map (MulAut.conj rho : G →* G) ≤ Q := by
    rintro _ ⟨q, hq, rfl⟩
    exact h.rho_nrm_Q q hq
  have hΦrho : ∀ x ∈ fzlPhi Q, rho * x * rho⁻¹ ∈ fzlPhi Q := by
    intro x hx
    have hmem : (MulAut.conj rho : G →* G) x ∈
        (fzlPhi Q).map (MulAut.conj rho : G →* G) := Subgroup.mem_map_of_mem _ hx
    rw [fzl_phi_map (MulAut.conj rho : G →* G) Q] at hmem
    exact fzl_phi_mono hmapQ hmem
  let Y : Subgroup G := fzlPhi Q ⊓ E
  have hZY : Z ≤ Y := fun z hz => ⟨hZΦ hz, h.ZE hz⟩
  have hYE : Y ≤ E := inf_le_right
  have hYrho : ∀ y ∈ Y, rho * y * rho⁻¹ ∈ Y := by
    rintro y ⟨hyΦ, hyE⟩
    exact ⟨hΦrho y hyΦ, h.rho_nrm_E y hyE⟩
  have hYfix : ∀ y ∈ Y, rho * y * rho⁻¹ = y → y = 1 := by
    rintro y ⟨hyΦ, hyE⟩ hy
    have hyQ : y ∈ Q := hΦW.trans h.WQ hyΦ
    rcases h.rho_Q y hyQ hy with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hyE) h.t_notin_E
  have hYmod : Nat.card Y % 3 = 1 :=
    fzl_card_mod3_of_fpf h.rho_ord hYrho hYfix
  have hcard16 : Nat.card Y ∣ 16 := by
    rw [← h.card_E]; exact Subgroup.card_dvd_of_le hYE
  have hcard4 : 4 ∣ Nat.card Y := by
    rw [← h.card_Z]; exact Subgroup.card_dvd_of_le hZY
  have hYZE : Y = Z ∨ Y = E := by
    obtain ⟨k, hk⟩ := hcard4
    have hk4 : k ∣ 4 := by
      obtain ⟨m, hm⟩ := hcard16
      refine ⟨m, ?_⟩
      have hm' : 16 = 4 * (k * m) := by
        rw [hk] at hm; exact hm.trans (by ring)
      have h44 : 4 * 4 = 4 * (k * m) := by rw [← hm']
      exact Nat.mul_left_cancel (by norm_num) h44
    have hk_le : k ≤ 4 := Nat.le_of_dvd (by norm_num) hk4
    have hkpos : 0 < k := by
      have hge : 4 ≤ Nat.card Y := h.card_Z.symm.trans_le (Subgroup.card_le_of_le hZY)
      rw [hk] at hge; omega
    have hYcard : Nat.card Y = 4 ∨ Nat.card Y = 16 := by
      interval_cases k
      · left; rw [hk]
      · exfalso; rw [hk] at hYmod; omega
      · exfalso; exact absurd hk4 (by norm_num)
      · right; rw [hk]
    rcases hYcard with hc | hc
    · left
      exact (Subgroup.eq_of_le_of_card_ge hZY (by rw [h.card_Z, hc])).symm
    · right
      exact Subgroup.eq_of_le_of_card_ge hYE (by rw [h.card_E, hc])
  rcases hYZE with hYZ | hYE_eq
  · exfalso
    have hΦ_subset : ∀ w ∈ fzlPhi Q, w ∈ Z ∨ ∃ z ∈ Z, w = t * z := by
      intro w hw
      have hwW : w ∈ W := hΦW hw
      rcases h.W_split w hwW with hwE | htwE
      · left
        have hmem : w ∈ Y := ⟨hw, hwE⟩
        rwa [hYZ] at hmem
      · right
        have htwΦ : t * w ∈ fzlPhi Q := mul_mem htΦ hw
        have hmem : t * w ∈ Y := ⟨htwΦ, htwE⟩
        rw [hYZ] at hmem
        exact ⟨t * w, hmem, by rw [← mul_assoc, ← pow_two, h.t_sq, one_mul]⟩
    have hsq_general : ∀ e ∈ W, (t * e) ^ 2 = e ^ 2 := by
      intro e he
      rw [pow_two, pow_two]
      calc (t * e) * (t * e) = t * (e * t) * e := by group
        _ = t * (t * e) * e := by rw [h.W_comm e he t h.t_mem]
        _ = (t * t) * (e * e) := by group
        _ = e * e := by rw [← pow_two, h.t_sq, one_mul]
    have hQsq : ∀ q ∈ Q, q ^ 2 ∈ Z := by
      intro q hq
      by_cases hqW : q ∈ W
      · rcases h.W_split q hqW with hqE | htqE
        · exact h.E_sq q hqE
        · have hqe : q = t * (t * q) := by rw [← mul_assoc, ← pow_two, h.t_sq, one_mul]
          rw [hqe, hsq_general (t * q) (h.EW htqE)]
          exact h.E_sq (t * q) htqE
      · have hq2Φ : q ^ 2 ∈ fzlPhi Q := fzl_sq_mem_phi hq
        rcases hΦ_subset (q ^ 2) hq2Φ with hZ | ⟨z, hzZ, hz_eq⟩
        · exact hZ
        · exfalso
          have hzQ : z ∈ Q := h.WQ (h.EW (h.ZE hzZ))
          have hqz : q * z * q⁻¹ = z := h.R_Z q (h.QR hq) z hzZ
          have hcomm2 : q * q ^ 2 * q⁻¹ = q ^ 2 := by rw [pow_two]; group
          have ht_eq : q * t * q⁻¹ = t := by
            have h1 : q * (t * z) * q⁻¹ = t * z := by
              rw [← hz_eq]; exact hcomm2
            calc q * t * q⁻¹
                = (q * (t * z) * q⁻¹) * (q * z * q⁻¹)⁻¹ := by group
              _ = (t * z) * z⁻¹ := by rw [h1, hqz]
              _ = t := by group
          exact h.Q_t q hq hqW ht_eq
    have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z := by
      intro a ha b hb
      refine fzl_comm_mem_of_sq (N := Z) (hQsq a ha) (hQsq b hb)
        (hQsq (a * b) (mul_mem ha hb)) ?_
      intro n hn
      have hbn : b⁻¹ * n * b = n := by
        have h' : b * n * b⁻¹ = n := h.R_Z b (h.QR hb) n hn
        calc b⁻¹ * n * b = b⁻¹ * (b * n * b⁻¹) * b := by rw [h']
          _ = n := by group
      rw [hbn]; exact hn
    exact h.t_notin_E (h.ZE (fzl_phi_le_of_elem hQcomm hQsq htΦ))
  · have hEΦ : E ≤ fzlPhi Q := by
      rw [← hYE_eq]
      exact inf_le_left
    have hWΦ : W ≤ fzlPhi Q := by
      intro w hw
      rcases h.W_split w hw with hwE | htwE
      · exact hEΦ hwE
      · have htwΦ : t * w ∈ fzlPhi Q := hEΦ htwE
        have hw_eq : w = t * (t * w) := by rw [← mul_assoc, ← pow_two, h.t_sq, one_mul]
        rw [hw_eq]
        exact mul_mem htΦ htwΦ
    exact le_antisymm hΦW hWΦ

end CFSG.OddStandard.SmallF3.FritzII
