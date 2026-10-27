module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Prop46d
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Quat

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q F : Subgroup G} {FA : G → Prop}

omit [Finite G] in
theorem exists_pow_sq_eq {Y : Subgroup G} (hY2 : IsPGroup 2 ↥Y)
    (hinv : ∀ p ∈ Y, p * p = 1 → p = 1 ∨ p = z) {q : G} (hq : q ∈ Y) (hq2 : q * q ≠ 1) :
    ∃ k : ℕ, (q ^ k) * (q ^ k) = z := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hY2) ⟨q, hq⟩
  have hm' : orderOf q = 2 ^ m := by simpa using hm
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push Not at hlt
    apply hq2
    have : q ^ 2 = 1 := by
      have h1 : orderOf q ∣ 2 := by
        rw [hm']
        calc 2 ^ m ∣ 2 ^ 1 := pow_dvd_pow 2 (by omega)
          _ = 2 := by norm_num
      exact orderOf_dvd_iff_pow_eq_one.1 h1
    simpa [sq] using this
  refine ⟨2 ^ (m - 2), ?_⟩
  have hsq : (q ^ (2 ^ (m - 2))) * (q ^ (2 ^ (m - 2))) = q ^ (2 ^ (m - 1)) := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    congr 2
    omega
  have hmem : q ^ (2 ^ (m - 2)) ∈ Y := Y.pow_mem hq _
  have hone : (q ^ (2 ^ (m - 2))) * (q ^ (2 ^ (m - 2))) ≠ 1 := by
    rw [hsq]
    apply pow_ne_one_of_lt_orderOf (by positivity)
    rw [hm']
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hsq1 : ((q ^ (2 ^ (m - 2))) * (q ^ (2 ^ (m - 2)))) * ((q ^ (2 ^ (m - 2))) * (q ^ (2 ^ (m - 2)))) = 1 := by
    rw [hsq, ← pow_add, ← two_mul, ← pow_succ']
    have : 2 ^ (m - 1 + 1) = 2 ^ m := by congr 1; omega
    rw [this, ← hm']
    exact pow_orderOf_eq_one q
  have hmem2 : (q ^ (2 ^ (m - 2))) * (q ^ (2 ^ (m - 2))) ∈ Y := Y.mul_mem hmem hmem
  rcases hinv _ hmem2 hsq1 with h1 | h1
  · exact absurd h1 hone
  · exact h1

namespace Cfg1

theorem decomp_four' (h : Cfg1 G z S P Q F FA) (hQinv : ∀ q ∈ Q, q * q = 1 → q = 1 ∨ q = z) {u : G}
    (huR : u ∈ P ⊔ Q) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z) :
    ∃ u₁ ∈ P, ∃ u₂ ∈ Q, u = u₁ * u₂ ∧ u₁ * u₁ = z ∧ u₂ * u₂ = z := by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute (fun a ha b hb => h.PQ_comm a ha b hb) huR
  have hcomm : q * p = p * q := (h.PQ_comm p hp q hq).symm
  have hpq : (p * p) * (q * q) = 1 := by
    calc (p * p) * (q * q) = p * (p * q) * q := by group
      _ = p * (q * p) * q := by rw [← hcomm]
      _ = (p * q) * (p * q) := by group
      _ = 1 := hu2
  have hqq : q * q = (p * p)⁻¹ := eq_inv_of_mul_eq_one_right hpq
  have hppP : p * p ∈ P := mul_mem hp hp
  have hppQ : p * p ∈ Q := by
    have : (q * q)⁻¹ ∈ Q := inv_mem (mul_mem hq hq)
    have e : p * p = (q * q)⁻¹ := by rw [hqq, inv_inv]
    rw [e]; exact this
  rcases h.PQ_inf _ hppP hppQ with e | e
  · exfalso
    have hq2 : q * q = 1 := by rw [hqq, e]; group
    rcases h.P_inv p hp e with h1 | h1 <;> rcases hQinv q hq hq2 with h2 | h2
    · exact hu1 (by rw [h1, h2]; group)
    · exact huz (by rw [h1, h2]; group)
    · exact huz (by rw [h1, h2]; group)
    · exact hu1 (by rw [h1, h2]; exact h.z_sq)
  · refine ⟨p, hp, q, hq, rfl, e, ?_⟩
    rw [hqq, e]
    exact inv_eq_of_mul_eq_one_right h.z_sq

end Cfg1

namespace Cfg1K

theorem inverts_both (h : Cfg1K G z S P Q F FA) {y : G} (hyS : y ∈ S) {U : Subgroup G}
    (hUR : U ≤ P ⊔ Q) (hU4 : Four U) (hUn : ∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U)
    {u u₁ u₂ : G} (huU : u ∈ U) (hu1 : u ≠ 1) (huz : u ≠ z) (hu₁P : u₁ ∈ P) (hu₂Q : u₂ ∈ Q)
    (hu : u = u₁ * u₂) (hu₁sq : u₁ * u₁ = z) (hu₂sq : u₂ * u₂ = z)
    (hCP : ∀ p ∈ P, y * p = p * y → p = 1 ∨ p = z)
    (hZsq : ∀ w : G, w * y = y * w → w * w ≠ z) :
    y * u₁ * y⁻¹ = u₁⁻¹ ∧ y * u₂ * y⁻¹ = u₂⁻¹ ∧ y * u = u * y := by
  have hzU : z ∈ U := h.toCfg1.z_mem_four hU4 (hUR.trans (sup_le h.P_le h.Q_le)) hUn
  have hz1 := h.z_ne
  have hz2 := h.z_sq
  have hyuU : y * u * y⁻¹ ∈ U := hUn y hyS u huU
  have hyu1 : y * u * y⁻¹ ≠ 1 := by
    intro e
    apply hu1
    calc u = y⁻¹ * (y * u * y⁻¹) * y := by group
      _ = 1 := by rw [e]; group
  have hyuz : y * u * y⁻¹ ≠ z := by
    intro e
    apply huz
    have hzc : y * z = z * y := (h.z_cent y hyS).symm
    calc u = y⁻¹ * (y * u * y⁻¹) * y := by group
      _ = y⁻¹ * z * y := by rw [e]
      _ = z := by
        calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
          _ = y⁻¹ * (y * z) := by rw [hzc]
          _ = z := by group
  have hcases := Four.mem_cases hU4 hzU huU hz1 hu1 huz hyuU
  have hab : y * u * y⁻¹ = u ∨ y * u * y⁻¹ = z * u := by
    rcases hcases with e | e | e | e
    · exact absurd e hyu1
    · exact absurd e hyuz
    · exact Or.inl e
    · exact Or.inr e
  set a := u₁⁻¹ * (y * u₁ * y⁻¹) with ha
  set b := u₂⁻¹ * (y * u₂ * y⁻¹) with hb
  have haP : a ∈ P := mul_mem (inv_mem hu₁P) (h.P_norm y hyS u₁ hu₁P)
  have hbQ : b ∈ Q := mul_mem (inv_mem hu₂Q) (h.Q_norm y hyS u₂ hu₂Q)
  have hcomm' : ∀ p ∈ P, ∀ q ∈ Q, q * p = p * q := fun p hp q hq => (h.PQ_comm p hp q hq).symm
  have hyu_eq : y * u * y⁻¹ = u * (a * b) := by
    have e1 : y * u * y⁻¹ = (y * u₁ * y⁻¹) * (y * u₂ * y⁻¹) := by rw [hu]; group
    have e2 : y * u₁ * y⁻¹ = u₁ * a := by rw [ha]; group
    have e3 : y * u₂ * y⁻¹ = u₂ * b := by rw [hb]; group
    rw [e1, e2, e3, hu]
    calc u₁ * a * (u₂ * b) = u₁ * (a * u₂) * b := by group
      _ = u₁ * (u₂ * a) * b := by rw [hcomm' a haP u₂ hu₂Q]
      _ = u₁ * u₂ * (a * b) := by group
  have huS : u ∈ S := (sup_le h.P_le h.Q_le) (hUR huU)
  have hab' : a * b = 1 ∨ a * b = z := by
    rcases hab with e | e
    · left
      have : u * (a * b) = u * 1 := by rw [← hyu_eq, e]; group
      exact mul_left_cancel this
    · right
      have : u * (a * b) = u * z := by rw [← hyu_eq, e, h.z_cent u huS]
      exact mul_left_cancel this
  have hya : y * u₁ * y⁻¹ = u₁ * a := by rw [ha]; group
  have hyb : y * u₂ * y⁻¹ = u₂ * b := by rw [hb]; group
  have hP1 : a = 1 → False := by
    intro e
    rw [e, mul_one] at hya
    have hc : y * u₁ = u₁ * y := by
      calc y * u₁ = y * u₁ * y⁻¹ * y := by group
        _ = u₁ * y := by rw [hya]
    rcases hCP u₁ hu₁P hc with h1 | h1
    · rw [h1, one_mul] at hu₁sq; exact hz1 hu₁sq.symm
    · rw [h1, hz2] at hu₁sq; exact hz1 hu₁sq.symm
  have hQ1 : b = 1 → False := by
    intro e
    rw [e, mul_one] at hyb
    have hc : u₂ * y = y * u₂ := by
      calc u₂ * y = y * u₂ * y⁻¹ * y := by rw [hyb]
        _ = y * u₂ := by group
    exact hZsq u₂ hc hu₂sq
  have haz : a = z ∧ b = z := by
    have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    rcases hab' with e | e
    · have haQ : a ∈ Q := by
        rw [eq_inv_of_mul_eq_one_left e]; exact inv_mem hbQ
      rcases h.PQ_inf a haP haQ with h1 | h1
      · exact absurd h1 (fun h1 => hP1 h1)
      · refine ⟨h1, ?_⟩
        rw [h1] at e
        have : b = z⁻¹ := eq_inv_of_mul_eq_one_right e
        rw [this, hz']
    · exfalso
      have haQ : a ∈ Q := by
        have e' : a = z * b⁻¹ := by
          calc a = (a * b) * b⁻¹ := by group
            _ = z * b⁻¹ := by rw [e]
        rw [e']
        exact mul_mem h.z_Q (inv_mem hbQ)
      rcases h.PQ_inf a haP haQ with h1 | h1
      · exact hP1 h1
      · rw [h1] at e
        have : b = 1 := mul_left_cancel (a := z) (by rw [mul_one]; exact e)
        exact hQ1 this
  refine ⟨?_, ?_, ?_⟩
  · rw [hya, haz.1, h.toCfg1.inv_eq_mul_z hu₁sq]
  · rw [hyb, haz.2, h.toCfg1.inv_eq_mul_z hu₂sq]
  · have : y * u * y⁻¹ = u := by rw [hyu_eq, haz.1, haz.2, hz2, mul_one]
    calc y * u = y * u * y⁻¹ * y := by group
      _ = u * y := by rw [this]

theorem conj_yu9 (h : Cfg1 G z S P Q F FA) {y u u₁ u₂ : G} (hy2 : y * y = 1)
    (hP : ∀ v ∈ P, (v * y) * (v * y) = 1 → ∃ p ∈ P, p⁻¹ * y * p = v * y)
    (hQ : ∀ v ∈ Q, (v * y) * (v * y) = 1 → ∃ q ∈ Q, q⁻¹ * y * q = v * y)
    (hu₁P : u₁ ∈ P) (hu₂Q : u₂ ∈ Q) (hu : u = u₁ * u₂) (hi₁ : y * u₁ * y⁻¹ = u₁⁻¹)
    (hi₂ : y * u₂ * y⁻¹ = u₂⁻¹) (hyu : y * u = u * y) :
    ∃ r ∈ P ⊔ Q, r⁻¹ * y * r = y * u := by
  have h1 : (u₁ * y) * (u₁ * y) = 1 := by
    calc (u₁ * y) * (u₁ * y) = u₁ * (y * u₁ * y⁻¹) * (y * y) := by group
      _ = 1 := by rw [hi₁, hy2]; group
  have h2 : (u₂ * y) * (u₂ * y) = 1 := by
    calc (u₂ * y) * (u₂ * y) = u₂ * (y * u₂ * y⁻¹) * (y * y) := by group
      _ = 1 := by rw [hi₂, hy2]; group
  obtain ⟨p, hp, hpy⟩ := hP u₁ hu₁P h1
  obtain ⟨q, hq, hqy⟩ := hQ u₂ hu₂Q h2
  refine ⟨p * q, mul_mem (mem_sup_left hp) (mem_sup_right hq), ?_⟩
  have hcomm : q⁻¹ * u₁ * q = u₁ := by
    have := h.PQ_comm u₁ hu₁P q hq
    calc q⁻¹ * u₁ * q = q⁻¹ * (u₁ * q) := by group
      _ = q⁻¹ * (q * u₁) := by rw [this]
      _ = u₁ := by group
  calc (p * q)⁻¹ * y * (p * q) = q⁻¹ * (p⁻¹ * y * p) * q := by group
    _ = q⁻¹ * (u₁ * y) * q := by rw [hpy]
    _ = (q⁻¹ * u₁ * q) * (q⁻¹ * y * q) := by group
    _ = u₁ * (u₂ * y) := by rw [hcomm, hqy]
    _ = u * y := by rw [hu]; group
    _ = y * u := hyu.symm

theorem caseA (h : Cfg1K G z S P Q Q FA) {nQ : ℕ} (hQq : IVK.IsQuaternionTwoGroup ↥Q nQ)
    (hZsq : ∀ y ∈ S, y * y = 1 → y ∉ P ⊔ Q → IsConj z y → ∀ w : G, w * y = y * w → w * w ≠ z)
    (hsdQ : ∀ y : G, y * y = 1 → y ∉ Q → (∀ q ∈ Q, y * q * y⁻¹ ∈ Q) →
      (∃ n, IVK.IsSemidihedralTwoGroup ↥(Q ⊔ zpowers y) n) →
      ∀ v ∈ Q, (v * y) * (v * y) = 1 → ∃ q ∈ Q, q⁻¹ * y * q = v * y)
    (h1024 : Bg.B_maximalClass_of_small_centralizer) (hshape : Bg.B_two_maximalClass_shape)
    (hZ : ∃ t ∈ S, t ≠ z ∧ IsConj z t)
    (hR : ∀ w ∈ P ⊔ Q, w * w = 1 → w ≠ 1 → w ≠ z → ¬ IsConj z w) : False := by
  obtain ⟨y, hyS, hyz, hzy⟩ := hZ
  have hy2 : y * y = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hzy
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [h.z_sq]; group
  have hy1 : y ≠ 1 := by
    intro e
    obtain ⟨c, hc⟩ := isConj_iff.1 hzy
    apply h.z_ne
    calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
      _ = 1 := by rw [hc, e]; group
  have hQinv := quat_invol_sub hQq h.z_Q h.z_sq h.z_ne
  have hyR : y ∉ P ⊔ Q := fun hm => hR y hm hy2 hy1 hyz hzy
  have hy : Is47b S P Q y := h.toCfg1.is47b_of hyS hy2 hyR
  have hyQ : y ∉ Q := fun hm => hyR (mem_sup_right hm)
  obtain ⟨hCP, hPconj, -⟩ := h.sdf_of_Y hy
  have hZy := hZsq y hyS hy2 hyR hzy
  have hcent : ∀ q ∈ Q, y * q = q * y → q = 1 ∨ q = z := by
    intro q hq hqc
    by_cases hq2 : q * q = 1
    · exact hQinv q hq hq2
    · exfalso
      obtain ⟨k, hk⟩ := exists_pow_sq_eq (isPGroup_of_quat hQq) hQinv hq hq2
      apply hZy (q ^ k) ?_ hk
      exact (((show Commute y q from hqc).pow_right k).eq).symm
  have hyn : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := fun q hq => h.Q_norm y hyS q hq
  obtain ⟨m, hSDQ⟩ := sd_of_centralizer hQq h.z_Q h.z_sq h.z_ne hy2 hyQ hyn hcent h1024 hshape
  have hQconj := hsdQ y hy2 hyQ hyn ⟨m, hSDQ⟩
  have hQne : Q ≠ zpowers z := by
    intro hQz
    have h8 := card_ge_of_quat hQq
    have : Nat.card ↥Q = 2 := by
      rw [hQz, Nat.card_zpowers]
      exact orderOf_two_of_sq_one h.z_sq h.z_ne
    omega
  obtain ⟨U, hUR, hU4, hUn⟩ := h.rn4 hQne
  obtain ⟨u, huU, hu1, huz⟩ : ∃ u ∈ U, u ≠ 1 ∧ u ≠ z := by
    classical
    by_contra hcon
    push Not at hcon
    have hsub : ∀ e ∈ U, e ∈ ({1, z} : Finset G) := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases he1 : e = 1
      · exact Or.inl he1
      · exact Or.inr (hcon e he he1)
    have h1 := B.card_subgroup_le_finset U _ hsub
    have h2 : ({1, z} : Finset G).card ≤ 2 := Finset.card_le_two
    have h3 := hU4.2
    omega
  obtain ⟨u₁, hu₁P, u₂, hu₂Q, hu, hu₁sq, hu₂sq⟩ :=
    h.toCfg1.decomp_four' hQinv (hUR huU) (hU4.1 u huU) hu1 huz
  obtain ⟨hi₁, hi₂, hyu⟩ := h.inverts_both hyS hUR hU4 hUn huU hu1 huz hu₁P hu₂Q hu hu₁sq hu₂sq hCP hZy
  obtain ⟨r, hr, hry⟩ := conj_yu9 h.toCfg1 hy2 hPconj hQconj hu₁P hu₂Q hu hi₁ hi₂ hyu
  have hzyu : IsConj z (y * u) := hzy.trans (isConj_iff.2 ⟨r⁻¹, by rw [inv_inv]; exact hry⟩)
  exact h.final_block hy hzy hR (fun e he' _ => by rw [← hy.2.2.2]; exact he') (hUR huU) hu1 huz
    (hU4.1 u huU) hyu hzyu

end Cfg1K

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
