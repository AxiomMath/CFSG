module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.Th2.R714

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2

section Def

variable {G : Type} [Group G]

structure Setup714 (x t y : G) (T Q P : Subgroup G) (Good : G → Prop) : Prop where
  T2 : IsPGroup 2 ↥T
  QT : Q ≤ T
  Qn : ∀ s ∈ T, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q
  PT : P ≤ T
  Pn : ∀ s ∈ T, ∀ p ∈ P, s * p * s⁻¹ ∈ P
  PQc : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p
  PQ : P ⊓ Q = ⊥
  Pc : ∀ p ∈ P, ∀ p' ∈ P, p * p' = p' * p
  Ps : ∀ p ∈ P, p * p = 1
  P4 : Nat.card P = 4
  Tcard : Nat.card T = 8 * Nat.card Q
  Qrank : ∀ E : Subgroup G, E ≤ Q → (∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) → (∀ e ∈ E, e * e = 1) →
    Nat.card E ≤ 4
  xQ : x ∈ Q
  x2 : x * x = 1
  x1 : x ≠ 1
  xc : ∀ s ∈ T, s * x = x * s
  yT : y ∈ T
  y2 : y * y = 1
  yR : y ∉ P ⊔ Q
  yP : ¬ ∀ p ∈ P, y * p = p * y
  tQ : t ∈ Q
  t2 : t * t = 1
  t1 : t ≠ 1
  tx : t ≠ x
  Klein : ∃ a b : G, a ∈ Q ∧ b ∈ Q ∧ a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
    y * a = a * y ∧ y * b = b * y
  good_conj : ∀ s ∈ T, ∀ u : G, Good u → Good (s * u * s⁻¹)
  good_outer : ∀ u ∈ Q, u * u = 1 → u ≠ 1 → u ≠ x → ∀ w ∈ T, w ∉ P ⊔ Q → w * w = 1 →
    w * u = u * w → Good u
  good_x : Good x
  t_bad : ¬ Good t

end Def

section NoFin

variable {G : Type} [Group G] {x t y : G} {T Q P : Subgroup G} {Good : G → Prop}

namespace Setup714

variable (S : Setup714 x t y T Q P Good)

include S in
theorem commDisj : CommDisj P Q := ⟨S.PQc, S.PQ⟩

include S in
theorem exists_pq {r : G} (hr : r ∈ P ⊔ Q) : ∃ p ∈ P, ∃ q ∈ Q, r = p * q :=
  exists_mul_of_mem_sup_of_commute S.PQc hr

include S in
theorem R_le_T : P ⊔ Q ≤ T := sup_le S.PT S.QT

end Setup714

end NoFin

section Basic

variable {G : Type} [Group G] [Finite G] {x t y : G} {T Q P : Subgroup G} {Good : G → Prop}

namespace Setup714

variable (S : Setup714 x t y T Q P Good)

include S in
theorem card_R : Nat.card ↥(P ⊔ Q) = 4 * Nat.card Q := by
  rw [S.commDisj.card_sup le_rfl le_rfl, S.P4]

include S in
theorem relIndex_R : (P ⊔ Q).relIndex T ≤ 2 := by
  have h1 := Subgroup.relIndex_mul_card (P ⊔ Q) T
  rw [inf_eq_left.2 S.R_le_T, S.Tcard, S.card_R] at h1
  have hQ : 0 < Nat.card Q := Nat.card_pos
  have : (P ⊔ Q).relIndex T * (4 * Nat.card Q) = 2 * (4 * Nat.card Q) := by rw [h1]; ring
  have h2 := Nat.eq_of_mul_eq_mul_right (by omega) this
  omega

include S in
theorem T_dec {s : G} (hs : s ∈ T) : s ∈ P ⊔ Q ∨ s * y⁻¹ ∈ P ⊔ Q :=
  Stage1.Thm3.Sec6.B.mem_or_mul_inv_mem S.relIndex_R S.yT S.yR hs


include S in
theorem rank3 {a b c : G} (ha : a ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q) (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hc2 : c * c = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab' : a ≠ b) :
    c = 1 ∨ c = a ∨ c = b ∨ c = a * b := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hca, hcb, hcab⟩ := hcon
  have ha2' : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have hb2' : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  have hc2' : orderOf c = 2 := orderOf_eq_prime (by rw [sq]; exact hc2) hc1
  have hel : ∀ {z : G}, orderOf z = 2 → CFSG.IsElementaryAbelian 2 ↥(zpowers z) := fun h =>
    Th2.isElementaryAbelian_zpowers_of_orderOf_two h
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
  set V : Subgroup G := zpowers a ⊔ zpowers b with hV
  have hVel : CFSG.IsElementaryAbelian 2 ↥V :=
    hcd.isElementaryAbelian_sup' (hel ha2') (hel hb2') le_rfl le_rfl
  have hVcard : Nat.card V = 4 := by
    rw [hV, hcd.card_sup le_rfl le_rfl, Nat.card_zpowers, Nat.card_zpowers, ha2', hb2']
  have hVQ : V ≤ Q := sup_le (zpowers_le.2 ha) (zpowers_le.2 hb)
  have hcV : c ∉ V := by
    intro hcv
    obtain ⟨p, hp, q, hq, hpq⟩ := exists_mul_of_mem_sup_of_commute hcd.comm hcv
    rcases mem_zpowers_two ha2' hp with h0 | h0 <;> rcases mem_zpowers_two hb2' hq with h1 | h1
    · exact hc1 (by rw [hpq, h0, h1]; simp)
    · exact hcb (by rw [hpq, h0, h1]; simp)
    · exact hca (by rw [hpq, h0, h1]; simp)
    · exact hcab (by rw [hpq, h0, h1])
  set W : Subgroup G := V ⊔ zpowers c with hW
  have hVW : V ≤ W := le_sup_left
  have hVc : V ≤ centralizer ({c} : Set G) := by
    refine sup_le ?_ ?_
    · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 hac)
    · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 hbc)
  have hWel : CFSG.IsElementaryAbelian 2 ↥W :=
    isElementaryAbelian_sup hVel (hel hc2') fun k hk l hl => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hl
      exact (Commute.zpow_right (show Commute k c from mem_centralizer_singleton_iff.1 (hVc hk)) m).eq
  obtain ⟨hWc, hWs⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hWel
  have hWQ : W ≤ Q := sup_le hVQ (zpowers_le.2 hc)
  have hW4 := S.Qrank W hWQ (fun e he e' he' => hWc e he e' he') (fun e he => hWs e he)
  have hne : W ≠ V := fun h => hcV (h ▸ (le_sup_right : zpowers c ≤ W) (mem_zpowers c))
  have hlt : Nat.card V < Nat.card W := by
    by_contra hge
    push Not at hge
    exact hne (Subgroup.eq_of_le_of_card_ge hVW hge).symm
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hVW
  rw [hVcard] at hm hlt
  have : 2 ≤ m := by
    by_contra h2
    push Not at h2
    interval_cases m <;> omega
  omega


include S in
theorem x_mem_klein {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab' : a ≠ b) :
    x = a ∨ x = b ∨ x = a * b := by
  rcases S.rank3 ha hb S.xQ hab (S.xc a (S.QT ha)) (S.xc b (S.QT hb)) ha2 hb2 S.x2 ha1 hb1 hab' with
    h | h | h | h
  · exact absurd h S.x1
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

include S in
theorem good_of_klein {u : G} (huQ : u ∈ Q) (hu2 : u * u = 1) (hu1 : u ≠ 1) (hux : u ≠ x)
    (huy : y * u = u * y) : Good u ∧ Good (x * u) ∧ t * u ≠ u * t := by
  have hux' : u * x = x * u := S.xc u (S.QT huQ)
  have hyx : y * x = x * y := S.xc y S.yT
  have hGu : Good u := S.good_outer u huQ hu2 hu1 hux y S.yT S.yR S.y2 huy
  have hxuQ : x * u ∈ Q := Q.mul_mem S.xQ huQ
  have hxu2 : x * u * (x * u) = 1 := by
    calc x * u * (x * u) = x * (u * x) * u := by group
      _ = x * (x * u) * u := by rw [hux']
      _ = (x * x) * (u * u) := by group
      _ = 1 := by rw [S.x2, hu2, one_mul]
  have hxu1 : x * u ≠ 1 := by
    intro h
    apply hux
    calc u = x⁻¹ * (x * u) := by group
      _ = x⁻¹ := by rw [h, mul_one]
      _ = x := inv_eq_of_mul_eq_one_right S.x2
  have hxux : x * u ≠ x := by
    intro h
    apply hu1
    calc u = x⁻¹ * (x * u) := by group
      _ = x⁻¹ * x := by rw [h]
      _ = 1 := inv_mul_cancel x
  have hGxu : Good (x * u) := by
    refine S.good_outer (x * u) hxuQ hxu2 hxu1 hxux y S.yT S.yR S.y2 ?_
    calc y * (x * u) = (y * x) * u := by group
      _ = (x * y) * u := by rw [hyx]
      _ = x * (y * u) := by group
      _ = x * (u * y) := by rw [huy]
      _ = x * u * y := by group
  refine ⟨hGu, hGxu, fun h => ?_⟩
  rcases S.rank3 S.xQ huQ S.tQ hux'.symm (S.xc t (S.QT S.tQ)).symm h.symm S.x2 hu2 S.t2 S.x1 hu1
    (fun h' => hux h'.symm) with h1 | h1 | h1 | h1
  · exact S.t1 h1
  · exact S.tx h1
  · exact S.t_bad (h1 ▸ hGu)
  · exact S.t_bad (h1 ▸ hGxu)

include S in
theorem exists_u : ∃ u : G, u ∈ Q ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ x ∧ y * u = u * y ∧ Good u ∧
    Good (x * u) ∧ t * u ≠ u * t := by
  obtain ⟨a, b, haQ, hbQ, ha2, hb2, hab, ha1, hb1, hab', hya, hyb⟩ := S.Klein
  rcases S.x_mem_klein haQ hbQ ha2 hb2 hab ha1 hb1 hab' with h | h | h
  · refine ⟨b, hbQ, hb2, hb1, fun h' => hab' (h.symm.trans h'.symm), hyb, ?_⟩
    exact S.good_of_klein hbQ hb2 hb1 (fun h' => hab' (h.symm.trans h'.symm)) hyb
  · refine ⟨a, haQ, ha2, ha1, fun h' => hab' (h'.trans h), hya, ?_⟩
    exact S.good_of_klein haQ ha2 ha1 (fun h' => hab' (h'.trans h)) hya
  · have hxa : a ≠ x := by
      intro h'
      apply hb1
      have : a * b = a * 1 := by rw [← h, h', mul_one]
      exact mul_left_cancel this
    refine ⟨a, haQ, ha2, ha1, hxa, hya, ?_⟩
    exact S.good_of_klein haQ ha2 ha1 hxa hya

include S in
theorem central_involution_eq {z : G} (hz : z ∈ Q) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hzc : ∀ q ∈ Q, z * q = q * z) : z = x := by
  by_contra hzx
  obtain ⟨u, huQ, hu2, hu1, hux, huy, hGu, hGxu, htu⟩ := S.exists_u
  have hxz : x * z = z * x := (S.xc z (S.QT hz)).symm
  rcases S.rank3 S.xQ hz S.tQ hxz (S.xc t (S.QT S.tQ)).symm (hzc t S.tQ) S.x2 hz2 S.t2 S.x1 hz1
    (fun h => hzx h.symm) with h | h | h | h
  · exact S.t1 h
  · exact S.tx h
  · apply htu
    rw [h]
    exact hzc u huQ
  · apply htu
    rw [h]
    calc x * z * u = x * (z * u) := by group
      _ = x * (u * z) := by rw [hzc u huQ]
      _ = (x * u) * z := by group
      _ = (u * x) * z := by rw [(S.xc u (S.QT huQ)).symm]
      _ = u * (x * z) := by group

omit [Finite G] in
include S in
theorem exists_p_not_comm : ∃ p ∈ P, y * p ≠ p * y := by
  by_contra h
  push Not at h
  exact S.yP h

omit [Finite G] in
include S in
theorem T_nonab : ∃ a ∈ T, ∃ b ∈ T, a * b * a⁻¹ * b⁻¹ ∉ Q := by
  obtain ⟨p, hp, hyp⟩ := S.exists_p_not_comm
  refine ⟨y, S.yT, p, S.PT hp, fun hQ => hyp ?_⟩
  have hP' : y * p * y⁻¹ * p⁻¹ ∈ P := P.mul_mem (S.Pn y S.yT p hp) (P.inv_mem hp)
  have h1 : y * p * y⁻¹ * p⁻¹ ∈ P ⊓ Q := ⟨hP', hQ⟩
  rw [S.PQ, Subgroup.mem_bot] at h1
  calc y * p = (y * p * y⁻¹ * p⁻¹) * (p * y) := by group
    _ = p * y := by rw [h1, one_mul]


include S in
theorem exists_zP : ∃ z ∈ P, z ≠ 1 ∧ z * z = 1 ∧ (∀ s ∈ T, s * z = z * s) ∧
    (∀ p ∈ P, p * (y * p * y⁻¹) = 1 ∨ p * (y * p * y⁻¹) = z) ∧
    ∀ s ∈ T, (∃ q ∈ Q, s * s = q * q) ∨
      ∃ q ∈ Q, (s * s = q * (y * q * y⁻¹) ∨ s * s = z * (q * (y * q * y⁻¹))) := by
  classical
  obtain ⟨p₀, hp₀, hyp₀⟩ := S.exists_p_not_comm
  have hy1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right S.y2
  set p₁ := y * p₀ * y⁻¹ with hp₁
  have hp₁P : p₁ ∈ P := S.Pn y S.yT p₀ hp₀
  have hyp₁ : y * p₁ * y⁻¹ = p₀ := by
    rw [hp₁, hy1]
    calc y * (y * p₀ * y) * y = (y * y) * p₀ * (y * y) := by group
      _ = p₀ := by rw [S.y2]; group
  have hp₁ne : p₁ ≠ p₀ := by
    intro h
    apply hyp₀
    have : y * p₀ * y⁻¹ = p₀ := h
    calc y * p₀ = (y * p₀ * y⁻¹) * y := by group
      _ = p₀ * y := by rw [this]
  have hp₀1 : p₀ ≠ 1 := by
    rintro rfl
    exact hyp₀ (by simp)
  have hp₁1 : p₁ ≠ 1 := by
    intro h
    apply hp₀1
    have : y * p₀ * y⁻¹ = 1 := h
    calc p₀ = y⁻¹ * (y * p₀ * y⁻¹) * y := by group
      _ = 1 := by rw [this]; group
  set z := p₀ * p₁ with hz
  have hzP : z ∈ P := P.mul_mem hp₀ hp₁P
  have hzz : z * z = 1 := by
    calc z * z = p₀ * (p₁ * p₀) * p₁ := by rw [hz]; group
      _ = p₀ * (p₀ * p₁) * p₁ := by rw [S.Pc p₁ hp₁P p₀ hp₀]
      _ = (p₀ * p₀) * (p₁ * p₁) := by group
      _ = 1 := by rw [S.Ps p₀ hp₀, S.Ps p₁ hp₁P, one_mul]
  have hz1 : z ≠ 1 := by
    intro h
    apply hp₁ne
    have h1 : p₀⁻¹ = p₀ := inv_eq_of_mul_eq_one_right (S.Ps p₀ hp₀)
    calc p₁ = p₀⁻¹ * (p₀ * p₁) := by group
      _ = p₀⁻¹ := by rw [← hz, h, mul_one]
      _ = p₀ := h1
  have hyz : y * z * y⁻¹ = z := by
    calc y * z * y⁻¹ = (y * p₀ * y⁻¹) * (y * p₁ * y⁻¹) := by rw [hz]; group
      _ = p₁ * p₀ := by rw [← hp₁, hyp₁]
      _ = p₀ * p₁ := S.Pc p₁ hp₁P p₀ hp₀
  have hyzc : y * z = z * y := by
    calc y * z = (y * z * y⁻¹) * y := by group
      _ = z * y := by rw [hyz]
  have hzc : ∀ r ∈ P ⊔ Q, r * z = z * r := by
    intro r hr
    obtain ⟨p, hp, q, hq, rfl⟩ := S.exists_pq hr
    calc p * q * z = p * (q * z) := by group
      _ = p * (z * q) := by rw [(S.PQc z hzP q hq).symm]
      _ = (p * z) * q := by group
      _ = (z * p) * q := by rw [S.Pc p hp z hzP]
      _ = z * (p * q) := by group
  have hzT : ∀ s ∈ T, s * z = z * s := by
    intro s hs
    rcases S.T_dec hs with h | h
    · exact hzc s h
    · have e : s = (s * y⁻¹) * y := by group
      rw [e]
      calc s * y⁻¹ * y * z = (s * y⁻¹) * (y * z) := by group
        _ = (s * y⁻¹) * (z * y) := by rw [hyzc]
        _ = ((s * y⁻¹) * z) * y := by group
        _ = (z * (s * y⁻¹)) * y := by rw [hzc _ h]
        _ = z * (s * y⁻¹ * y) := by group
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  set Cy : Subgroup G := P ⊓ centralizer ({y} : Set G) with hCy
  have hzCy : z ∈ Cy := ⟨hzP, mem_centralizer_singleton_iff.2 hyzc.symm⟩
  have hZCy : zpowers z ≤ Cy := zpowers_le.2 hzCy
  have hCyP : Cy ≤ P := inf_le_left
  have hCyne : Nat.card Cy < Nat.card P := by
    by_contra hge
    push Not at hge
    have hCyeq : Cy = P := Subgroup.eq_of_le_of_card_ge hCyP hge
    apply hyp₀
    have : p₀ ∈ Cy := hCyeq ▸ hp₀
    exact (mem_centralizer_singleton_iff.1 this.2).symm
  have hCydvd : Nat.card Cy ∣ 4 := S.P4 ▸ Subgroup.card_dvd_of_le hCyP
  have hCyle : Nat.card Cy ≤ 2 := by
    rw [S.P4] at hCyne
    by_contra hgt
    push Not at hgt
    have h3 : Nat.card Cy = 3 := by omega
    rw [h3] at hCydvd
    exact absurd hCydvd (by norm_num)
  have hZc : Nat.card ↥(zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
  have hCyeq : Cy = zpowers z := (Subgroup.eq_of_le_of_card_ge hZCy (by omega)).symm
  have hPyz : ∀ p ∈ P, p * (y * p * y⁻¹) = 1 ∨ p * (y * p * y⁻¹) = z := by
    intro p hp
    have hw : p * (y * p * y⁻¹) ∈ Cy := by
      refine ⟨P.mul_mem hp (S.Pn y S.yT p hp), mem_centralizer_singleton_iff.2 ?_⟩
      have e : y * (p * (y * p * y⁻¹)) * y⁻¹ = (y * p * y⁻¹) * p := by
        calc y * (p * (y * p * y⁻¹)) * y⁻¹ = (y * p * y⁻¹) * ((y * y) * p * (y⁻¹ * y⁻¹)) := by group
          _ = (y * p * y⁻¹) * p := by rw [S.y2, hy1, S.y2]; group
      have e2 : (y * p * y⁻¹) * p = p * (y * p * y⁻¹) := S.Pc _ (S.Pn y S.yT p hp) p hp
      have : y * (p * (y * p * y⁻¹)) = (p * (y * p * y⁻¹)) * y := by
        calc y * (p * (y * p * y⁻¹)) = (y * (p * (y * p * y⁻¹)) * y⁻¹) * y := by group
          _ = (p * (y * p * y⁻¹)) * y := by rw [e, e2]
      exact this.symm
    rw [hCyeq] at hw
    rcases mem_zpowers_two hz2 hw with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨z, hzP, hz1, hzz, hzT, hPyz, ?_⟩
  intro s hs
  rcases S.T_dec hs with h | h
  · left
    obtain ⟨p, hp, q, hq, rfl⟩ := S.exists_pq h
    refine ⟨q, hq, ?_⟩
    calc p * q * (p * q) = p * (q * p) * q := by group
      _ = p * (p * q) * q := by rw [(S.PQc p hp q hq).symm]
      _ = (p * p) * (q * q) := by group
      _ = q * q := by rw [S.Ps p hp, one_mul]
  · right
    obtain ⟨p, hp, q, hq, hr⟩ := S.exists_pq h
    refine ⟨q, hq, ?_⟩
    have hs' : s * s = (p * q) * (y * (p * q) * y⁻¹) := by
      calc s * s = (s * y⁻¹) * (y * (s * y⁻¹) * y⁻¹) * (y * y) := by group
        _ = (s * y⁻¹) * (y * (s * y⁻¹) * y⁻¹) := by rw [S.y2, mul_one]
        _ = (p * q) * (y * (p * q) * y⁻¹) := by rw [hr]
    have hp' : y * p * y⁻¹ ∈ P := S.Pn y S.yT p hp
    have hq' : y * q * y⁻¹ ∈ Q := S.Qn y S.yT q hq
    have hexp : (p * q) * (y * (p * q) * y⁻¹) = (p * (y * p * y⁻¹)) * (q * (y * q * y⁻¹)) := by
      calc (p * q) * (y * (p * q) * y⁻¹) = p * q * ((y * p * y⁻¹) * (y * q * y⁻¹)) := by group
        _ = p * (q * (y * p * y⁻¹)) * (y * q * y⁻¹) := by group
        _ = p * ((y * p * y⁻¹) * q) * (y * q * y⁻¹) := by rw [(S.PQc _ hp' q hq).symm]
        _ = (p * (y * p * y⁻¹)) * (q * (y * q * y⁻¹)) := by group
    rw [hs', hexp]
    rcases hPyz p hp with h1 | h1
    · left; rw [h1, one_mul]
    · right; rw [h1]

end Setup714

end Basic

end CFSG.GH74.GLS.Th2.R714
