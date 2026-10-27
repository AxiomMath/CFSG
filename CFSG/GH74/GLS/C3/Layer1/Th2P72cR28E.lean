module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR28A
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR28C
public import CFSG.GH74.GLS.IVK.Lifted.DSDGroup

public section

namespace CFSG.GH74.GLS.Th2.R714

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2

section Klein

variable {G : Type} [Group G] [Finite G]

theorem klein_gens {U : Subgroup G} (hU4 : Nat.card U = 4) (hUc : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u)
    (hUs : ∀ u ∈ U, u * u = 1) :
    ∃ a b : G, a ∈ U ∧ b ∈ U ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ ∀ v ∈ U, v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by
  have hne : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hU4
    omega
  obtain ⟨⟨a, haU⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hUs a haU) ha1'
  obtain ⟨b, hbU, hbA⟩ : ∃ b ∈ U, b ∉ zpowers a := by
    by_contra hno
    push Not at hno
    have hle : U ≤ zpowers a := fun b hb => hno b hb
    have := Subgroup.card_le_of_le hle
    rw [hU4, Nat.card_zpowers, ha2] at this
    omega
  have hb1 : b ≠ 1 := fun h => hbA (h ▸ one_mem _)
  have hab : a ≠ b := fun h => hbA (h ▸ mem_zpowers a)
  obtain ⟨hVcard, hVel⟩ := klein_facts (hUs a haU) (hUs b hbU) (hUc a haU b hbU) ha1' hb1 hab
  have hVU : zpowers a ⊔ zpowers b ≤ U := sup_le (zpowers_le.2 haU) (zpowers_le.2 hbU)
  have hUV : U = zpowers a ⊔ zpowers b :=
    (Subgroup.eq_of_le_of_card_ge hVU (by rw [hVcard, hU4])).symm
  refine ⟨a, b, haU, hbU, ha1', hb1, hab, fun v hv => hVel v (hUV ▸ hv)⟩

end Klein


section CaseE

variable {G : Type} [Group G] [Finite G] {x t y : G} {T Q P : Subgroup G} {Good : G → Prop}

namespace Setup714

variable (S : Setup714 x t y T Q P Good)

omit [Finite G] in
include S in
theorem good_of_outer {u w : G} (huQ : u ∈ Q) (hu2 : u * u = 1) (hu1 : u ≠ 1) (hux : u ≠ x)
    (hwT : w ∈ T) (hwR : w ∉ P ⊔ Q) (hw2 : w * w = 1) (hwu : w * u = u * w) :
    Good u ∧ Good (x * u) := by
  have hux' : u * x = x * u := S.xc u (S.QT huQ)
  have hwx : w * x = x * w := S.xc w hwT
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
  refine ⟨S.good_outer u huQ hu2 hu1 hux w hwT hwR hw2 hwu,
    S.good_outer (x * u) hxuQ hxu2 hxu1 hxux w hwT hwR hw2 ?_⟩
  calc w * (x * u) = (w * x) * u := by group
    _ = (x * w) * u := by rw [hwx]
    _ = x * (w * u) := by group
    _ = x * (u * w) := by rw [hwu]
    _ = x * u * w := by group

include S in
theorem case_e (hIG : Stage1.Thm3.Sec5.IG_15_16_ext)
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) {Syl : Subgroup G}
    (hSyl : IsSylowOf 2 Syl ⊤) (hTSyl : T ≤ Syl) (hTx : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hv : ∃ v ∈ Q, orderOf v = 4 ∧ v * t = t * v)
    (hU : ∃ U : Subgroup G, U ≤ Q ∧ Nat.card U = 4 ∧ (∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u) ∧
      (∀ u ∈ U, u * u = 1) ∧ (∀ s ∈ T, ∀ u ∈ U, s * u * s⁻¹ ∈ U))
    (fus : ∀ g : G, g⁻¹ * x * g ∈ Q → Good (g⁻¹ * x * g) → g⁻¹ * t * g ∈ T →
      g⁻¹ * t * g ∈ Q ∧ ¬ Good (g⁻¹ * t * g)) : False := by
  classical
  obtain ⟨v, hvQ, hv4, hvt⟩ := hv
  obtain ⟨U, hUQ, hU4, hUc, hUs, hUn⟩ := hU
  have hy1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right S.y2
  obtain ⟨a, b, haU, hbU, ha1, hb1, hab, hUel⟩ := klein_gens hU4 hUc hUs
  have hxU : x ∈ U := by
    rcases S.x_mem_klein (hUQ haU) (hUQ hbU) (hUs a haU) (hUs b hbU) (hUc a haU b hbU) ha1 hb1 hab
      with h | h | h
    · rw [h]; exact haU
    · rw [h]; exact hbU
    · rw [h]; exact U.mul_mem haU hbU
  obtain ⟨c, hcU, hc1, hcx⟩ : ∃ c ∈ U, c ≠ 1 ∧ c ≠ x := by
    by_cases hax : a = x
    · exact ⟨b, hbU, hb1, fun h => hab (hax.trans h.symm)⟩
    · exact ⟨a, haU, ha1, hax⟩
  have hcQ : c ∈ Q := hUQ hcU
  have hc2 : c * c = 1 := hUs c hcU
  have hxc : x * c = c * x := (S.xc c (S.QT hcQ)).symm
  obtain ⟨hVcard, hVel⟩ := klein_facts S.x2 hc2 hxc S.x1 hc1 (fun h => hcx h.symm)
  have hVU : zpowers x ⊔ zpowers c ≤ U := sup_le (zpowers_le.2 hxU) (zpowers_le.2 hcU)
  have hUV : U = zpowers x ⊔ zpowers c :=
    (Subgroup.eq_of_le_of_card_ge hVU (by rw [hVcard, hU4])).symm
  have hUel' : ∀ w ∈ U, w = 1 ∨ w = x ∨ w = c ∨ w = x * c := fun w hw => hVel w (hUV ▸ hw)
  have hxcU : x * c ∈ U := U.mul_mem hxU hcU
  have hTc : ∀ s ∈ T, s * c * s⁻¹ = c ∨ s * c * s⁻¹ = x * c := by
    intro s hs
    have hU' := hUn s hs c hcU
    have hne1 : s * c * s⁻¹ ≠ 1 := by
      intro h
      apply hc1
      calc c = s⁻¹ * (s * c * s⁻¹) * s := by group
        _ = 1 := by rw [h]; group
    have hnex : s * c * s⁻¹ ≠ x := by
      intro h
      apply hcx
      have hsx : s⁻¹ * x * s = x := by
        have := S.xc s⁻¹ (T.inv_mem hs)
        calc s⁻¹ * x * s = (x * s⁻¹) * s := by rw [this]
          _ = x := by group
      calc c = s⁻¹ * (s * c * s⁻¹) * s := by group
        _ = s⁻¹ * x * s := by rw [h]
        _ = x := hsx
    rcases hUel' _ hU' with h | h | h | h
    · exact absurd h hne1
    · exact absurd h hnex
    · exact Or.inl h
    · exact Or.inr h
  have hy' : ∃ y' ∈ T, y' ∉ P ⊔ Q ∧ y' * y' = 1 ∧ y' * c = c * y' := by
    rcases hTc y S.yT with h | h
    · refine ⟨y, S.yT, S.yR, S.y2, ?_⟩
      calc y * c = (y * c * y⁻¹) * y := by group
        _ = c * y := by rw [h]
    · obtain ⟨u, huQ, hu2, hu1, hux, huy, -, -, -⟩ := S.exists_u
      have hyx : y * x = x * y := S.xc y S.yT
      rcases hTc u (S.QT huQ) with h2 | h2
      · exfalso
        have hucomm : u * c = c * u := by
          calc u * c = (u * c * u⁻¹) * u := by group
            _ = c * u := by rw [h2]
        have hycomm : y * c = c * y := by
          rcases S.rank3 S.xQ hcQ huQ hxc (S.xc u (S.QT huQ)).symm hucomm.symm S.x2 hc2 hu2 S.x1 hc1
            (fun h' => hcx h'.symm) with h3 | h3 | h3 | h3
          · exact absurd h3 hu1
          · exact absurd h3 hux
          · rw [h3] at huy; exact huy
          · rw [h3] at huy
            calc y * c = x * (x * (y * c)) := by rw [← mul_assoc, S.x2, one_mul]
              _ = x * ((x * y) * c) := by group
              _ = x * ((y * x) * c) := by rw [hyx]
              _ = x * (y * (x * c)) := by group
              _ = x * ((x * c) * y) := by rw [huy]
              _ = (x * x) * (c * y) := by group
              _ = c * y := by rw [S.x2, one_mul]
        apply S.x1
        have : y * c * y⁻¹ = c := by
          calc y * c * y⁻¹ = (c * y) * y⁻¹ := by rw [hycomm]
            _ = c := by group
        rw [this] at h
        calc x = (x * c) * c⁻¹ := by group
          _ = c * c⁻¹ := by rw [← h]
          _ = 1 := mul_inv_cancel c
      · refine ⟨y * u, T.mul_mem S.yT (S.QT huQ), ?_, ?_, ?_⟩
        · intro hR
          apply S.yR
          have hu' : u ∈ P ⊔ Q := mem_sup_right huQ
          have := (P ⊔ Q).mul_mem hR ((P ⊔ Q).inv_mem hu')
          have e : y * u * u⁻¹ = y := by group
          rwa [e] at this
        · calc (y * u) * (y * u) = y * (u * y) * u := by group
            _ = y * (y * u) * u := by rw [huy]
            _ = (y * y) * (u * u) := by group
            _ = 1 := by rw [S.y2, hu2, one_mul]
        · have e1 : y * u * c * (y * u)⁻¹ = c := by
            calc y * u * c * (y * u)⁻¹ = y * (u * c * u⁻¹) * y⁻¹ := by group
              _ = y * (x * c) * y⁻¹ := by rw [h2]
              _ = (y * x * y⁻¹) * (y * c * y⁻¹) := by group
              _ = x * (x * c) := by
                rw [h, hy1, hyx]
                congr 1
                calc x * y * y = x * (y * y) := by group
                  _ = x := by rw [S.y2, mul_one]
              _ = c := by rw [← mul_assoc, S.x2, one_mul]
          calc y * u * c = (y * u * c * (y * u)⁻¹) * (y * u) := by group
            _ = c * (y * u) := by rw [e1]
  obtain ⟨y', hy'T, hy'R, hy'2, hy'c⟩ := hy'
  have hGc := S.good_of_outer hcQ hc2 hc1 hcx hy'T hy'R hy'2 hy'c
  have hGU : ∀ w ∈ U, w ≠ 1 → Good w := by
    intro w hw hw1
    rcases hUel' w hw with h | h | h | h
    · exact absurd h hw1
    · rw [h]; exact S.good_x
    · rw [h]; exact hGc.1
    · rw [h]; exact hGc.2
  have htU : t ∉ U := fun h => S.t_bad (hGU t h S.t1)
  have hxt : x * t = t * x := (S.xc t (S.QT S.tQ)).symm
  have hconjx : ∀ s ∈ T, s * x * s⁻¹ = x := by
    intro s hs
    calc s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [S.xc s hs]
      _ = x := by group
  have hv4' := IVK.Lifted.pow_four_aux hv4
  have hww2 : v * v * (v * v) = 1 := by
    calc v * v * (v * v) = v * (v * (v * v)) := by group
      _ = 1 := hv4'
  have hww1 : v * v ≠ 1 := by
    intro h
    have : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hv4] at this
    omega
  have hwQ : v * v ∈ Q := Q.mul_mem hvQ hvQ
  have hvvx : v * v = x := by
    have hvT : v ∈ T := S.QT hvQ
    have hwc : v * v * c = c * (v * v) := by
      have e : v * (v * c * v⁻¹) * v⁻¹ = c := by
        rcases hTc v hvT with h | h
        · rw [h, h]
        · rw [h]
          calc v * (x * c) * v⁻¹ = (v * x * v⁻¹) * (v * c * v⁻¹) := by group
            _ = x * (x * c) := by rw [hconjx v hvT, h]
            _ = c := by rw [← mul_assoc, S.x2, one_mul]
      calc v * v * c = (v * (v * c * v⁻¹) * v⁻¹) * (v * v) := by group
        _ = c * (v * v) := by rw [e]
    have hwU : v * v ∈ U := by
      rcases S.rank3 S.xQ hcQ hwQ hxc (S.xc _ (S.QT hwQ)).symm hwc.symm S.x2 hc2 hww2 S.x1 hc1
        (fun h => hcx h.symm) with h | h | h | h
      · exact absurd h hww1
      · rw [h]; exact hxU
      · rw [h]; exact hcU
      · rw [h]; exact hxcU
    have hwt : t * (v * v) = (v * v) * t := by
      calc t * (v * v) = (t * v) * v := by group
        _ = (v * t) * v := by rw [hvt]
        _ = v * (t * v) := by group
        _ = v * (v * t) := by rw [hvt]
        _ = (v * v) * t := by group
    rcases S.rank3 S.tQ S.xQ hwQ hxt.symm hwt (S.xc _ (S.QT hwQ)).symm S.t2 S.x2 hww2 S.t1 S.x1 S.tx with
      h | h | h | h
    · exact absurd h hww1
    · exact absurd (h ▸ hwU) htU
    · exact h
    · exfalso
      apply htU
      have := U.mul_mem hwU hxU
      have e : v * v * x = t := by
        rw [h]
        calc t * x * x = t * (x * x) := by group
          _ = t := by rw [S.x2, mul_one]
      rwa [e] at this
  have hxel : ∀ {z : G}, orderOf z = 2 → CFSG.IsElementaryAbelian 2 ↥(zpowers z) := fun h =>
    Th2.isElementaryAbelian_zpowers_of_orderOf_two h
  have hx2' : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact S.x2) S.x1
  have ht2' : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact S.t2) S.t1
  obtain ⟨hVtcard, hVtel⟩ := klein_facts S.x2 S.t2 hxt S.x1 S.t1 (fun h => S.tx h.symm)
  set Vt : Subgroup G := zpowers x ⊔ zpowers t with hVt
  have hVtQ : Vt ≤ Q := sup_le (zpowers_le.2 S.xQ) (zpowers_le.2 S.tQ)
  have hVtEA : CFSG.IsElementaryAbelian 2 ↥Vt :=
    isElementaryAbelian_sup (hxel hx2') (hxel ht2') fun k hk l hl => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hk
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hl
      exact (Commute.zpow_zpow (show Commute x t from hxt) m n).eq
  have hPEA : CFSG.IsElementaryAbelian 2 ↥P :=
    C3.Layer1.Back.isElementaryAbelian_of_forall (fun u hu v hv => S.Pc u hu v hv) (fun u hu => S.Ps u hu)
  have hcd : CommDisj P Vt := ⟨fun p hp q hq => S.PQc p hp q (hVtQ hq), by
    refine eq_bot_iff.2 fun z hz => ?_
    have : z ∈ P ⊓ Q := ⟨hz.1, hVtQ hz.2⟩
    rw [S.PQ] at this
    exact this⟩
  set E : Subgroup G := P ⊔ Vt with hE
  have hEcard : Nat.card E = 16 := by rw [hE, hcd.card_sup le_rfl le_rfl, S.P4, hVtcard]
  have hEEA : CFSG.IsElementaryAbelian 2 ↥E := hcd.isElementaryAbelian_sup' hPEA hVtEA le_rfl le_rfl
  have hET : E ≤ T := sup_le S.PT (hVtQ.trans S.QT)
  have hEt : ∀ e ∈ E, e * t = t * e := by
    have : E ≤ centralizer ({t} : Set G) := by
      refine sup_le (fun p hp => mem_centralizer_singleton_iff.2 (S.PQc p hp t S.tQ)) ?_
      refine sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 (S.xc t (S.QT S.tQ)).symm)) ?_
      exact zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
    exact fun e he => mem_centralizer_singleton_iff.1 (this he)
  have hEv : ∀ e ∈ E, e * v = v * e := by
    have : E ≤ centralizer ({v} : Set G) := by
      refine sup_le (fun p hp => mem_centralizer_singleton_iff.2 (S.PQc p hp v hvQ)) ?_
      refine sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 (S.xc v (S.QT hvQ)).symm)) ?_
      exact zpowers_le.2 (mem_centralizer_singleton_iff.2 hvt.symm)
    exact fun e he => mem_centralizer_singleton_iff.1 (this he)
  have hTc2 : (T ⊓ centralizer ({c} : Set G)).relIndex T ≤ 2 := relIndex_centralizer_le_two hTc
  have hE4 : ∀ g : G, (∀ d ∈ T ⊓ centralizer ({t} : Set G), g⁻¹ * d * g ∈ T) → g⁻¹ * x * g ∈ U := by
    intro g hg
    set E' : Subgroup G := cj g⁻¹ E with hE'
    have hmemE' : ∀ z, z ∈ E' ↔ g * z * g⁻¹ ∈ E := by
      intro z
      rw [hE', mem_cj_iff, inv_inv]
    have hE'T : E' ≤ T := by
      intro z hz
      have hzE := (hmemE' z).1 hz
      have := hg (g * z * g⁻¹) ⟨hET hzE, mem_centralizer_singleton_iff.2 (hEt _ hzE)⟩
      have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
      rwa [e] at this
    have hE'card : Nat.card E' = 16 := by
      rw [hE', ← hEcard]
      exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have hE'EA : CFSG.IsElementaryAbelian 2 ↥E' := isElementaryAbelian_cj g⁻¹ hEEA
    obtain ⟨hE'c, hE's⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hE'EA
    have hE'Q : Nat.card ↥(E' ⊓ Q) ≤ 4 :=
      S.Qrank (E' ⊓ Q) inf_le_right (fun e he e' he' => hE'c e he.1 e' he'.1) (fun e he => hE's e he.1)
    have hv'T : g⁻¹ * v * g ∈ T := hg v ⟨S.QT hvQ, mem_centralizer_singleton_iff.2 hvt⟩
    have hv'E : ∀ e ∈ E', (g⁻¹ * v * g) * e = e * (g⁻¹ * v * g) := by
      intro e he
      have h1 := hEv _ ((hmemE' e).1 he)
      calc (g⁻¹ * v * g) * e = g⁻¹ * (v * (g * e * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * e * g⁻¹) * v) * g := by rw [h1]
        _ = e * (g⁻¹ * v * g) := by group
    have hsq := sq_mem_of_centralizes S.QT S.Qn S.Tcard S.T_nonab hE'T hE'c hE's
      (by rw [hE'card]; omega) hv'T hv'E
    have hx' : g⁻¹ * x * g = (g⁻¹ * v * g) * (g⁻¹ * v * g) := by rw [← hvvx]; group
    have hx'Q : g⁻¹ * x * g ∈ Q := hx' ▸ hsq
    have hx'T : g⁻¹ * x * g ∈ T := S.QT hx'Q
    have hx'C : g⁻¹ * x * g ∈ T ⊓ centralizer ({c} : Set G) := hx' ▸ sq_mem_of_relIndex_le_two hTc2 hv'T
    have hx'c : g⁻¹ * x * g * c = c * (g⁻¹ * x * g) := mem_centralizer_singleton_iff.1 hx'C.2
    have hx'2 : g⁻¹ * x * g * (g⁻¹ * x * g) = 1 := by
      calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
        _ = 1 := by rw [S.x2]; group
    rcases S.rank3 S.xQ hcQ hx'Q hxc (S.xc _ hx'T).symm hx'c.symm S.x2 hc2 hx'2 S.x1 hc1
      (fun h => hcx h.symm) with h | h | h | h
    · exfalso
      apply S.x1
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · rw [h]; exact hxU
    · rw [h]; exact hcU
    · rw [h]; exact hxcU
  have hcentral_c : ¬ (∀ s ∈ T, s * c = c * s) := by
    intro h
    exact hcx (S.central_involution_eq hcQ hc2 hc1 (fun q hq => (h q (S.QT hq)).symm))
  have hN : ∀ n ∈ normalizer (T : Set G), n * x = x * n := by
    intro n hn
    have hn' : n⁻¹ ∈ normalizer (T : Set G) := (normalizer (T : Set G)).inv_mem hn
    have hTn : ∀ d ∈ T ⊓ centralizer ({t} : Set G), n⁻¹ * d * n ∈ T := by
      intro d hd
      have := (Subgroup.mem_normalizer_iff.1 hn' d).1 hd.1
      simpa using this
    have hxU' := hE4 n hTn
    have hcen : ∀ s ∈ T, s * (n⁻¹ * x * n) = (n⁻¹ * x * n) * s := by
      intro s hs
      have hs' : n * s * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hn s).1 hs
      have h1 := S.xc _ hs'
      calc s * (n⁻¹ * x * n) = n⁻¹ * ((n * s * n⁻¹) * x) * n := by group
        _ = n⁻¹ * (x * (n * s * n⁻¹)) * n := by rw [h1]
        _ = (n⁻¹ * x * n) * s := by group
    have hx'1 : n⁻¹ * x * n ≠ 1 := by
      intro h
      apply S.x1
      calc x = n * (n⁻¹ * x * n) * n⁻¹ := by group
        _ = 1 := by rw [h]; group
    rcases hUel' _ hxU' with h | h | h | h
    · exact absurd h hx'1
    · calc n * x = n * (n⁻¹ * x * n) := by rw [h]
        _ = x * n := by group
    · exfalso
      apply hcentral_c
      intro s hs
      have hh := hcen s hs
      rw [h] at hh
      exact hh
    · exfalso
      apply hcentral_c
      intro s hs
      have hh := hcen s hs
      rw [h] at hh
      have h1 : x * (s * c) = x * (c * s) := by
        calc x * (s * c) = (x * s) * c := by group
          _ = (s * x) * c := by rw [← S.xc s hs]
          _ = s * (x * c) := by group
          _ = (x * c) * s := hh
          _ = x * (c * s) := by group
      exact mul_left_cancel h1
  have hTeq : T = Syl := eq_of_normalizer_le_centralizer hSyl hTSyl hTx (fun n _ hnN => hN n hnN)
  have hSylT : IsSylowOf 2 T ⊤ := hTeq ▸ hSyl
  have ht2 : orderOf t = 2 := ht2'
  obtain ⟨g, hg1, hg2⟩ := transfer_finish hIG hperf hSylT inf_le_left hTc2 (S.QT S.tQ) ht2
  have hx'U := hE4 g hg2
  have hx'1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply S.x1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨ht₁Q, ht₁bad⟩ := fus g (hUQ hx'U) (hGU _ hx'U hx'1) hg1.1
  have ht₁c : g⁻¹ * t * g * c = c * (g⁻¹ * t * g) := mem_centralizer_singleton_iff.1 hg1.2
  have ht₁1 : g⁻¹ * t * g ≠ 1 := by
    intro h
    apply S.t1
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have ht₁2 : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [S.t2]; group
  have ht₁U : g⁻¹ * t * g ∈ U := by
    rcases S.rank3 S.xQ hcQ ht₁Q hxc (S.xc _ hg1.1).symm ht₁c.symm S.x2 hc2 ht₁2 S.x1 hc1
      (fun h => hcx h.symm) with h | h | h | h
    · exact absurd h ht₁1
    · rw [h]; exact hxU
    · rw [h]; exact hcU
    · rw [h]; exact hxcU
  exact ht₁bad (hGU _ ht₁U ht₁1)

end Setup714

end CaseE

end CFSG.GH74.GLS.Th2.R714
