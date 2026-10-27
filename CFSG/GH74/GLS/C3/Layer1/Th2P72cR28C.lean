module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR28B

public section

namespace CFSG.GH74.GLS.Th2.R714

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2

variable {G : Type} [Group G] [Finite G]

theorem klein_facts {a b : G} (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab' : a ≠ b) :
    Nat.card ↥(zpowers a ⊔ zpowers b) = 4 ∧
      ∀ v ∈ zpowers a ⊔ zpowers b, v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by
  have ha2' : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have hb2' : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  have hcd : CommDisj (zpowers a) (zpowers b) := by
    refine ⟨fun p hp q hq => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hp
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hq
      exact ((Commute.zpow_zpow (show Commute a b from hab) m n)).eq
    · refine eq_bot_iff.2 fun z hz => ?_
      rcases mem_zpowers_two ha2' hz.1 with h0 | h0
      · simp [h0]
      · rcases mem_zpowers_two hb2' hz.2 with h1 | h1
        · simp [h1]
        · exact absurd (h0.symm.trans h1) hab'
  refine ⟨?_, fun v hv => ?_⟩
  · rw [hcd.card_sup le_rfl le_rfl, Nat.card_zpowers, Nat.card_zpowers, ha2', hb2']
  · obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hcd.comm hv
    rcases mem_zpowers_two ha2' hp with h0 | h0 <;> rcases mem_zpowers_two hb2' hq with h1 | h1
    · left; rw [h0, h1]; simp
    · right; right; left; rw [h0, h1]; simp
    · right; left; rw [h0, h1]; simp
    · right; right; right; rw [h0, h1]

namespace Setup714

variable {x t y : G} {T Q P : Subgroup G} {Good : G → Prop} (S : Setup714 x t y T Q P Good)

include S in
theorem case_c (hQ8 : Nat.card Q = 8) : False := by
  obtain ⟨u, huQ, hu2, hu1, hux, huy, hGu, hGxu, htu⟩ := S.exists_u
  have hxu : x * u = u * x := (S.xc u (S.QT huQ)).symm
  have hy1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right S.y2
  have ht1' : t⁻¹ = t := inv_eq_of_mul_eq_one_right S.t2
  have hyx : y * x = x * y := S.xc y S.yT
  obtain ⟨hVcard, hVel⟩ := klein_facts S.x2 hu2 hxu S.x1 hu1 (fun h => hux h.symm)
  set V : Subgroup G := zpowers x ⊔ zpowers u with hV
  have hVQ : V ≤ Q := sup_le (zpowers_le.2 S.xQ) (zpowers_le.2 huQ)
  have hxV : x ∈ V := mem_sup_left (mem_zpowers x)
  have huV : u ∈ V := mem_sup_right (mem_zpowers u)
  have hVidx : V.relIndex Q ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card V Q
    rw [inf_eq_left.2 hVQ, hVcard, hQ8] at h1
    omega
  have htV : t ∉ V := by
    intro h
    rcases hVel t h with h1 | h1 | h1 | h1
    · exact S.t1 h1
    · exact S.tx h1
    · exact S.t_bad (h1 ▸ hGu)
    · exact S.t_bad (h1 ▸ hGxu)
  have hVsq : ∀ v ∈ V, v * v = 1 := by
    intro v hv
    rcases hVel v hv with h | h | h | h
    · rw [h]; simp
    · rw [h]; exact S.x2
    · rw [h]; exact hu2
    · rw [h]
      calc x * u * (x * u) = x * (u * x) * u := by group
        _ = x * (x * u) * u := by rw [hxu]
        _ = (x * x) * (u * u) := by group
        _ = 1 := by rw [S.x2, hu2, one_mul]
  have twist : ∀ e : G, e * e = 1 → e * t⁻¹ ∈ V → e = t ∨ e = x * t := by
    intro e he hq
    set q := e * t⁻¹ with hqdef
    have hqe : e = q * t := by rw [hqdef, ht1', mul_assoc, S.t2, mul_one]
    have hq2 : q * q = 1 := hVsq q hq
    have hqt : q * t = t * q := by
      have h1 : (q * t) * (q * t) = 1 := by rw [← hqe]; exact he
      have hq' : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq2
      have : q * t = (q * t)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      rw [this, mul_inv_rev, ht1', hq']
    rcases hVel q hq with h | h | h | h
    · left; rw [hqe, h, one_mul]
    · right; rw [hqe, h]
    · exfalso
      apply htu
      rw [h] at hqt
      exact hqt.symm
    · exfalso
      apply htu
      rw [h] at hqt
      have hxt : x * t = t * x := (S.xc t (S.QT S.tQ)).symm
      have : u * t = t * u := by
        calc u * t = x * (x * u) * t := by rw [← mul_assoc, S.x2, one_mul]
          _ = x * ((x * u) * t) := by group
          _ = x * (t * (x * u)) := by rw [hqt]
          _ = (x * t) * (x * u) := by group
          _ = (t * x) * (x * u) := by rw [hxt]
          _ = t * (x * x) * u := by group
          _ = t * u := by rw [S.x2]; group
      exact this.symm
  have hyv : ∀ v ∈ V, y * v * y⁻¹ = v := by
    intro v hv
    rcases hVel v hv with h | h | h | h
    · rw [h]; group
    · rw [h, hy1, hyx]
      calc x * y * y = x * (y * y) := by group
        _ = x := by rw [S.y2, mul_one]
    · rw [h, hy1, huy]
      calc u * y * y = u * (y * y) := by group
        _ = u := by rw [S.y2, mul_one]
    · rw [h, hy1]
      calc y * (x * u) * y = (y * x) * u * y := by group
        _ = (x * y) * u * y := by rw [hyx]
        _ = x * (y * u) * y := by group
        _ = x * (u * y) * y := by rw [huy]
        _ = x * u * (y * y) := by group
        _ = x * u := by rw [S.y2, mul_one]
  have hyt : y * t * y⁻¹ = t ∨ y * t * y⁻¹ = x * t := by
    have htQ' : y * t * y⁻¹ ∈ Q := S.Qn y S.yT t S.tQ
    have hinv : y * t * y⁻¹ * (y * t * y⁻¹) = 1 := by
      calc y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
        _ = 1 := by rw [S.t2]; group
    have hnot : y * t * y⁻¹ ∉ V := by
      intro h
      apply htV
      have h1 := hyv _ h
      have : y * (y * t * y⁻¹) * y⁻¹ = t := by
        calc y * (y * t * y⁻¹) * y⁻¹ = (y * y) * t * (y⁻¹ * y⁻¹) := by group
          _ = t := by rw [S.y2, hy1, S.y2]; group
      rw [this] at h1
      exact h1.symm ▸ h
    have hmem := Stage1.Thm3.Sec6.B.mem_or_mul_inv_mem hVidx S.tQ htV htQ'
    exact twist _ hinv (hmem.resolve_left hnot)
  have hu1' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hutu : u * t * u⁻¹ = x * t := by
    have htQ' : u * t * u⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem huQ S.tQ) (Q.inv_mem huQ)
    have hinv : u * t * u⁻¹ * (u * t * u⁻¹) = 1 := by
      calc u * t * u⁻¹ * (u * t * u⁻¹) = u * (t * t) * u⁻¹ := by group
        _ = 1 := by rw [S.t2]; group
    have hnot : u * t * u⁻¹ ∉ V := by
      intro h
      apply htV
      have := V.mul_mem (V.mul_mem (V.inv_mem huV) h) huV
      have e : u⁻¹ * (u * t * u⁻¹) * u = t := by group
      rwa [e] at this
    have hmem := Stage1.Thm3.Sec6.B.mem_or_mul_inv_mem hVidx S.tQ htV htQ'
    rcases twist _ hinv (hmem.resolve_left hnot) with h | h
    · exfalso
      apply htu
      calc t * u = (u * t * u⁻¹) * u := by rw [h]
        _ = u * t := by group
    · exact h
  rcases hyt with h | h
  · have hyt' : y * t = t * y := by
      calc y * t = (y * t * y⁻¹) * y := by group
        _ = t * y := by rw [h]
    exact S.t_bad (S.good_outer t S.tQ S.t2 S.t1 S.tx y S.yT S.yR S.y2 hyt')
  ·
    have hyu_t : (y * u) * t = t * (y * u) := by
      have e1 : y * u * t * (y * u)⁻¹ = t := by
        calc y * u * t * (y * u)⁻¹ = y * (u * t * u⁻¹) * y⁻¹ := by group
          _ = y * (x * t) * y⁻¹ := by rw [hutu]
          _ = (y * x * y⁻¹) * (y * t * y⁻¹) := by group
          _ = x * (x * t) := by
            rw [h, hy1, hyx]
            congr 1
            calc x * y * y = x * (y * y) := by group
              _ = x := by rw [S.y2, mul_one]
          _ = t := by rw [← mul_assoc, S.x2, one_mul]
      calc y * u * t = (y * u * t * (y * u)⁻¹) * (y * u) := by group
        _ = t * (y * u) := by rw [e1]
    have hyu2 : (y * u) * (y * u) = 1 := by
      calc (y * u) * (y * u) = y * (u * y) * u := by group
        _ = y * (y * u) * u := by rw [huy]
        _ = (y * y) * (u * u) := by group
        _ = 1 := by rw [S.y2, hu2, one_mul]
    have hyuT : y * u ∈ T := T.mul_mem S.yT (S.QT huQ)
    have hyuR : y * u ∉ P ⊔ Q := by
      intro hR
      apply S.yR
      have hu' : u ∈ P ⊔ Q := mem_sup_right huQ
      have := (P ⊔ Q).mul_mem hR ((P ⊔ Q).inv_mem hu')
      have e : y * u * u⁻¹ = y := by group
      rwa [e] at this
    exact S.t_bad (S.good_outer t S.tQ S.t2 S.t1 S.tx (y * u) hyuT hyuR hyu2 hyu_t)

end Setup714

end CFSG.GH74.GLS.Th2.R714
