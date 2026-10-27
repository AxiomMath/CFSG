module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR28A
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR28B
public import CFSG.GH74.GLS.IVK.Lifted.DSDGroup

public section

namespace CFSG.GH74.GLS.Th2.R714

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2

section Def

variable {G : Type} [Group G]

structure DSDShape (Q A : Subgroup G) (ρ x : G) : Prop where
  AQ : A ≤ Q
  A2 : IsPGroup 2 ↥A
  cyc : IsCyclic ↥A
  ρA : ρ ∈ A
  ρ4 : orderOf ρ = 4
  card : Nat.card Q = 2 * Nat.card A
  A8 : 8 ≤ Nat.card A
  inv : ∀ s ∈ Q, s ∉ A → s * ρ * s⁻¹ = ρ⁻¹
  out : ∀ s ∈ Q, s ∉ A → orderOf s < Nat.card A
  xQ : x ∈ Q
  x2 : x * x = 1
  x1 : x ≠ 1
  xc : ∀ q ∈ Q, q * x = x * q

theorem orderOf_conj' (s a : G) : orderOf (s * a * s⁻¹) = orderOf a := by
  have := orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective a
  simpa [MulAut.conj_apply] using this

@[expose] def Cl3G (Q : Subgroup G) (x : G) : Prop :=
  ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, a * a = 1 → b * b = 1 → c * c = 1 → a ≠ 1 → b ≠ 1 → c ≠ 1 →
    a ≠ x → b ≠ x → c ≠ x →
    (∃ q ∈ Q, q * a * q⁻¹ = b) ∨ (∃ q ∈ Q, q * a * q⁻¹ = c) ∨ (∃ q ∈ Q, q * b * q⁻¹ = c)

end Def

section Shape

variable {G : Type} [Group G] [Finite G] {Q A : Subgroup G} {ρ x : G}

namespace DSDShape

variable (D : DSDShape Q A ρ x)

omit [Finite G] in
include D in
theorem ρ_sq_ne : ρ * ρ ≠ 1 := by
  intro h
  have : orderOf ρ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  rw [D.ρ4] at this
  omega

omit [Finite G] in
include D in
theorem ρ_inv_ne : ρ⁻¹ ≠ ρ := fun h => D.ρ_sq_ne (by
  calc ρ * ρ = ρ⁻¹ * ρ := by rw [h]
    _ = 1 := inv_mul_cancel ρ)

omit [Finite G] in
include D in
theorem x_mem_A : x ∈ A := by
  by_contra hx
  have h1 := D.inv x D.xQ hx
  have h2 : x * ρ * x⁻¹ = ρ := by
    calc x * ρ * x⁻¹ = (ρ * x) * x⁻¹ := by rw [D.xc ρ (D.AQ D.ρA)]
      _ = ρ := by group
  rw [h2] at h1
  apply D.ρ_sq_ne
  calc ρ * ρ = ρ⁻¹ * ρ := by rw [← h1]
    _ = 1 := inv_mul_cancel ρ

include D in
theorem A_inv {a : G} (ha : a ∈ A) (ha2 : a * a = 1) : a = 1 ∨ a = x := by
  by_cases h : a = 1
  · exact Or.inl h
  · exact Or.inr (Stage1.Thm3.Sec6.B.cyclic_invol_unique D.cyc ha D.x_mem_A ha2 D.x2 h D.x1)

include D in
theorem relIndex_le : A.relIndex Q ≤ 2 := by
  have h1 := Subgroup.relIndex_mul_card A Q
  rw [inf_eq_left.2 D.AQ, D.card] at h1
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h2 := Nat.eq_of_mul_eq_mul_right hpos h1
  omega

include D in
theorem prod_mem {q q' : G} (hq : q ∈ Q) (hq' : q' ∈ Q) (hqA : q ∉ A) (hq'A : q' ∉ A) :
    q * q' ∈ A := by
  have := Stage1.Thm3.Sec6.B.mem_or_mul_inv_mem D.relIndex_le (Q.inv_mem hq')
    (fun h => hq'A (by simpa using A.inv_mem h)) hq
  rcases this with h | h
  · exact absurd h hqA
  · simpa using h

include D in
theorem sq_mem {q : G} (hq : q ∈ Q) : q * q ∈ A := by
  by_cases h : q ∈ A
  · exact A.mul_mem h h
  · exact D.prod_mem hq hq h h

omit [Finite G] in
include D in
theorem A_T {T : Subgroup G} (hQn : ∀ s ∈ T, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q) {s a : G} (hs : s ∈ T)
    (ha : a ∈ A) : s * a * s⁻¹ ∈ A := by
  obtain ⟨g, hg⟩ := D.cyc.exists_generator
  have hgord : orderOf (g : G) = Nat.card A := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hsgQ : s * (g : G) * s⁻¹ ∈ Q := hQn s hs g (D.AQ g.2)
  have hsgA : s * (g : G) * s⁻¹ ∈ A := by
    by_contra hn
    have h1 := D.out _ hsgQ hn
    rw [orderOf_conj', hgord] at h1
    exact lt_irrefl _ h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨a, ha⟩)
  have hak : a = (g : G) ^ k := by simpa using (congrArg Subtype.val hk).symm
  rw [hak]
  have : s * (g : G) ^ k * s⁻¹ = (s * g * s⁻¹) ^ k := conj_zpow.symm
  rw [this]
  exact A.zpow_mem hsgA k

include D in
theorem exists_fourth : ∃ a ∈ A, a * a * a * a = x := by
  obtain ⟨g, hg⟩ := D.cyc.exists_generator
  have hgord : orderOf (g : G) = Nat.card A := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 D.A2
  have hj3 : 3 ≤ j := by
    by_contra h
    push Not at h
    have h1 : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := D.A8
    rw [hj] at h2
    omega
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 3 := ⟨j - 3, by omega⟩
  have hord : orderOf (g : G) = 2 ^ (i + 3) := by rw [hgord, hj]
  set b : G := (g : G) ^ (2 ^ (i + 2)) with hb
  have hbord : orderOf b = 2 := by
    rw [hb, orderOf_pow_of_dvd (by positivity) (by rw [hord]; exact pow_dvd_pow 2 (by omega)), hord]
    rw [show 2 ^ (i + 3) = 2 * 2 ^ (i + 2) by ring]
    exact Nat.mul_div_cancel _ (by positivity)
  have hbA : b ∈ A := A.pow_mem g.2 _
  have hb2 : b * b = 1 := by
    have h := pow_orderOf_eq_one b
    rw [hbord] at h
    simpa [pow_two] using h
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hbord
    omega
  have hbx : b = x := by
    rcases D.A_inv hbA hb2 with h | h
    · exact absurd h hb1
    · exact h
  refine ⟨(g : G) ^ (2 ^ i), A.pow_mem g.2 _, ?_⟩
  rw [← hbx, hb]
  calc (g : G) ^ 2 ^ i * (g : G) ^ 2 ^ i * (g : G) ^ 2 ^ i * (g : G) ^ 2 ^ i
      = (g : G) ^ (2 ^ i * 4) := by
        rw [pow_mul]; group
    _ = (g : G) ^ 2 ^ (i + 2) := by
        congr 1; ring

include D in
theorem sq_of_comm {b a : G} (hbQ : b ∈ Q) (hbA : b ∉ A) (haA : a ∈ A) (hab : a * b = b * a) :
    a * a = 1 := by
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, orderOf a = 2 ^ k := by
    have := IsPGroup.iff_orderOf.1 D.A2 ⟨a, haA⟩
    simpa [Subgroup.orderOf_mk] using this
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    apply hne
    have hd : orderOf a ∣ 2 := by
      rw [hk]
      simpa using pow_dvd_pow 2 (show k ≤ 1 by omega)
    have h2 : a ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hd
    simpa [pow_two] using h2
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
  set a' : G := a ^ (2 ^ i) with ha'
  have ha'4 : orderOf a' = 4 := by
    rw [ha', orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk]
    rw [show 2 ^ (i + 2) = 4 * 2 ^ i by ring]
    exact Nat.mul_div_cancel _ (by positivity)
  have ha'A : a' ∈ A := A.pow_mem haA _
  have hcomm : a' * b = b * a' := (Commute.pow_left (show Commute a b from hab) _).eq
  have hρb : b * ρ = ρ * b := by
    rcases IVK.Lifted.eq_or_inv_of_orderOf_four D.cyc D.ρA ha'A D.ρ4 ha'4 with h | h
    · rw [h] at hcomm
      exact hcomm.symm
    · rw [h] at hcomm
      have h1 : ρ⁻¹ * b = b * ρ⁻¹ := hcomm
      calc b * ρ = ρ * (ρ⁻¹ * (b * ρ)) := by group
        _ = ρ * ((ρ⁻¹ * b) * ρ) := by group
        _ = ρ * ((b * ρ⁻¹) * ρ) := by rw [h1]
        _ = ρ * b := by group
  have h2 : b * ρ * b⁻¹ = ρ := by
    calc b * ρ * b⁻¹ = (ρ * b) * b⁻¹ := by rw [hρb]
      _ = ρ := by group
  rw [D.inv b hbQ hbA] at h2
  exact D.ρ_inv_ne h2

include D in
theorem conj_ρ {T : Subgroup G} (hQn : ∀ s ∈ T, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q) {s : G} (hs : s ∈ T) :
    s * ρ * s⁻¹ = ρ ∨ s * ρ * s⁻¹ = ρ⁻¹ := by
  have hA := D.A_T hQn hs D.ρA
  have h4 : orderOf (s * ρ * s⁻¹) = 4 := by rw [orderOf_conj', D.ρ4]
  exact IVK.Lifted.eq_or_inv_of_orderOf_four D.cyc D.ρA hA D.ρ4 h4

omit [Finite G] in
include D in
theorem mem_A_of_comm_ρ {q : G} (hq : q ∈ Q) (h : q * ρ = ρ * q) : q ∈ A := by
  by_contra hqA
  have h1 := D.inv q hq hqA
  have h2 : q * ρ * q⁻¹ = ρ := by
    calc q * ρ * q⁻¹ = (ρ * q) * q⁻¹ := by rw [h]
      _ = ρ := by group
  rw [h2] at h1
  exact D.ρ_inv_ne h1.symm

end DSDShape

end Shape

section CaseF

variable {G : Type} [Group G] [Finite G] {x t y : G} {T Q P A : Subgroup G} {ρ : G}
  {Good : G → Prop}

namespace Setup714

variable (S : Setup714 x t y T Q P Good) (D : DSDShape Q A ρ x)

include S D in
theorem exists_zP_A : ∃ z ∈ P, z ≠ 1 ∧ z * z = 1 ∧ (∀ s ∈ T, s * z = z * s) ∧
    ∀ s ∈ T, ∃ c ∈ A, s * s = c ∨ s * s = z * c := by
  obtain ⟨z, hzP, hz1, hzz, hzT, -, hsq⟩ := S.exists_zP
  have hy1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right S.y2
  have hαA : ∀ q ∈ Q, q * (y * q * y⁻¹) ∈ A := by
    intro q hq
    by_cases hqA : q ∈ A
    · exact A.mul_mem hqA (D.A_T S.Qn S.yT hqA)
    · have hαQ : y * q * y⁻¹ ∈ Q := S.Qn y S.yT q hq
      have hαA' : y * q * y⁻¹ ∉ A := by
        intro h
        apply hqA
        have := D.A_T S.Qn S.yT h
        have e : y * (y * q * y⁻¹) * y⁻¹ = q := by
          calc y * (y * q * y⁻¹) * y⁻¹ = (y * y) * q * (y⁻¹ * y⁻¹) := by group
            _ = q := by rw [S.y2, hy1, S.y2]; group
        rwa [e] at this
      exact D.prod_mem hq hαQ hqA hαA'
  refine ⟨z, hzP, hz1, hzz, hzT, fun s hs => ?_⟩
  rcases hsq s hs with ⟨q, hq, h⟩ | ⟨q, hq, h | h⟩
  · exact ⟨q * q, D.sq_mem hq, Or.inl h⟩
  · exact ⟨_, hαA q hq, Or.inl h⟩
  · exact ⟨_, hαA q hq, Or.inr h⟩

include S D in
theorem normalizer_le_centralizer {n : G} (hn : n ∈ normalizer (T : Set G)) : n * x = x * n := by
  obtain ⟨z, hzP, hz1, hzz, hzT, hsq⟩ := S.exists_zP_A D
  obtain ⟨a, haA, ha4⟩ := D.exists_fourth
  have haT : a ∈ T := S.QT (D.AQ haA)
  have hn' : n⁻¹ ∈ normalizer (T : Set G) := (normalizer (T : Set G)).inv_mem hn
  have hsT : n⁻¹ * a * n ∈ T := by
    have := (Subgroup.mem_normalizer_iff.1 hn' a).1 haT
    simpa using this
  obtain ⟨c, hcA, hc⟩ := hsq _ hsT
  set s := n⁻¹ * a * n with hs
  have hx' : n⁻¹ * x * n = (s * s) * (s * s) := by
    rw [← ha4, hs]; group
  have hcQ : c ∈ Q := D.AQ hcA
  have hzc : z * c = c * z := S.PQc z hzP c hcQ
  have hxc : n⁻¹ * x * n = c * c := by
    rw [hx']
    rcases hc with h | h
    · rw [h]
    · rw [h]
      calc z * c * (z * c) = z * (c * z) * c := by group
        _ = z * (z * c) * c := by rw [← hzc]
        _ = (z * z) * (c * c) := by group
        _ = c * c := by rw [hzz, one_mul]
  have hxA : n⁻¹ * x * n ∈ A := by rw [hxc]; exact A.mul_mem hcA hcA
  have hx2 : n⁻¹ * x * n * (n⁻¹ * x * n) = 1 := by
    calc n⁻¹ * x * n * (n⁻¹ * x * n) = n⁻¹ * (x * x) * n := by group
      _ = 1 := by rw [S.x2]; group
  have hx1 : n⁻¹ * x * n ≠ 1 := by
    intro h
    apply S.x1
    calc x = n * (n⁻¹ * x * n) * n⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hxx : n⁻¹ * x * n = x := by
    rcases D.A_inv hxA hx2 with h | h
    · exact absurd h hx1
    · exact h
  calc n * x = n * (n⁻¹ * x * n) := by rw [hxx]
    _ = x * n := by group

include S D in
theorem case_f (hIG : Stage1.Thm3.Sec5.IG_15_16_ext)
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) {Syl : Subgroup G}
    (hSyl : IsSylowOf 2 Syl ⊤) (hTSyl : T ≤ Syl) (hTx : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hCl3 : Cl3G Q x)
    (fusC : ∀ g : G, g * x = x * g → g⁻¹ * t * g ∈ T → g⁻¹ * t * g ∈ Q) : False := by
  classical
  have hy1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right S.y2
  obtain ⟨z, hzP, hz1, hzz, hzT, hsq⟩ := S.exists_zP_A D
  have hTeq : T = Syl := eq_of_normalizer_le_centralizer hSyl hTSyl hTx
    (fun n _ hnN => S.normalizer_le_centralizer D hnN)
  have hSylT : IsSylowOf 2 T ⊤ := hTeq ▸ hSyl
  have htT : t ∈ T := S.QT S.tQ
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact S.t2) S.t1
  have htA : t ∉ A := by
    intro h
    rcases D.A_inv h S.t2 with h1 | h1
    · exact S.t1 h1
    · exact S.tx h1
  have hrho : ∀ s ∈ T, s * ρ * s⁻¹ = ρ ∨ s * ρ * s⁻¹ = ρ⁻¹ := fun s hs => D.conj_ρ S.Qn hs
  have hidx : (T ⊓ centralizer ({ρ} : Set G)).relIndex T ≤ 2 := relIndex_centralizer_le_two hrho
  obtain ⟨g, hg1, hg2⟩ := transfer_finish hIG hperf hSylT inf_le_left hidx htT ht2
  obtain ⟨u, huQ, hu2, hu1, hux, huy, hGu, hGxu, htu⟩ := S.exists_u
  have ht'Q : y * t * y⁻¹ ∈ Q := S.Qn y S.yT t S.tQ
  have ht'2 : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
    calc (y * t * y⁻¹) * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
      _ = 1 := by rw [S.t2]; group
  have ht'1 : y * t * y⁻¹ ≠ 1 := by
    intro h
    apply S.t1
    calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  have hyxc : y * x = x * y := S.xc y S.yT
  have ht'x : y * t * y⁻¹ ≠ x := by
    intro h
    apply S.tx
    calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
      _ = y⁻¹ * x * y := by rw [h]
      _ = x := by
        rw [hy1]
        calc y * x * y = (x * y) * y := by rw [hyxc]
          _ = x * (y * y) := by group
          _ = x := by rw [S.y2, mul_one]
  have hy₁ : ∃ y₁ ∈ T, y₁ ∉ P ⊔ Q ∧ y₁ * t = t * y₁ ∧ y₁ * y₁ = x := by
    rcases hCl3 u huQ t S.tQ (y * t * y⁻¹) ht'Q hu2 S.t2 ht'2 hu1 S.t1 ht'1 hux S.tx ht'x with
      ⟨q, hq, hqe⟩ | ⟨q, hq, hqe⟩ | ⟨q, hq, hqe⟩
    · exact absurd (hqe ▸ S.good_conj q (S.QT hq) u hGu) S.t_bad
    · exfalso
      apply S.t_bad
      have e : t = (y⁻¹ * q) * u * (y⁻¹ * q)⁻¹ := by
        calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
          _ = y⁻¹ * (q * u * q⁻¹) * y := by rw [hqe]
          _ = (y⁻¹ * q) * u * (y⁻¹ * q)⁻¹ := by group
      rw [e]
      exact S.good_conj (y⁻¹ * q) (T.mul_mem (T.inv_mem S.yT) (S.QT hq)) u hGu
    ·
      have hyqT : y * q ∈ T := T.mul_mem S.yT (S.QT hq)
      have hyqR : y * q ∉ P ⊔ Q := by
        intro hR
        apply S.yR
        have := (P ⊔ Q).mul_mem hR ((P ⊔ Q).inv_mem (mem_sup_right hq : q ∈ P ⊔ Q))
        have e : y * q * q⁻¹ = y := by group
        rwa [e] at this
      have hyqt : y * q * t = t * (y * q) := by
        have e1 : y * q * t * (y * q)⁻¹ = t := by
          calc y * q * t * (y * q)⁻¹ = y * (q * t * q⁻¹) * y⁻¹ := by group
            _ = y * (y * t * y⁻¹) * y⁻¹ := by rw [hqe]
            _ = (y * y) * t * (y⁻¹ * y⁻¹) := by group
            _ = t := by rw [S.y2, hy1, S.y2]; group
        calc y * q * t = (y * q * t * (y * q)⁻¹) * (y * q) := by group
          _ = t * (y * q) := by rw [e1]
      have hαQ : y * q * y⁻¹ ∈ Q := S.Qn y S.yT q hq
      have hy₁sq : (y * q) * (y * q) = (y * q * y⁻¹) * q := by
        calc (y * q) * (y * q) = (y * q * y⁻¹) * (y * y) * q := by group
          _ = (y * q * y⁻¹) * q := by rw [S.y2, mul_one]
      have hy₁A : (y * q) * (y * q) ∈ A := by
        rw [hy₁sq]
        by_cases hqA : q ∈ A
        · exact A.mul_mem (D.A_T S.Qn S.yT hqA) hqA
        · have hαA : y * q * y⁻¹ ∉ A := by
            intro h
            apply hqA
            have := D.A_T S.Qn S.yT h
            have e : y * (y * q * y⁻¹) * y⁻¹ = q := by
              calc y * (y * q * y⁻¹) * y⁻¹ = (y * y) * q * (y⁻¹ * y⁻¹) := by group
                _ = q := by rw [S.y2, hy1, S.y2]; group
            rwa [e] at this
          exact D.prod_mem hαQ hq hαA hqA
      have hy₁c : (y * q) * (y * q) * t = t * ((y * q) * (y * q)) := by
        calc (y * q) * (y * q) * t = (y * q) * ((y * q) * t) := by group
          _ = (y * q) * (t * (y * q)) := by rw [hyqt]
          _ = ((y * q) * t) * (y * q) := by group
          _ = (t * (y * q)) * (y * q) := by rw [hyqt]
          _ = t * ((y * q) * (y * q)) := by group
      have hy₁2 := D.sq_of_comm S.tQ htA hy₁A hy₁c
      rcases D.A_inv hy₁A hy₁2 with h | h
      · exfalso
        exact S.t_bad (S.good_outer t S.tQ S.t2 S.t1 S.tx (y * q) hyqT hyqR h hyqt)
      · exact ⟨y * q, hyqT, hyqR, hyqt, h⟩
  obtain ⟨y₁, hy₁T, hy₁R, hy₁t, hy₁x⟩ := hy₁
  have hwT : g⁻¹ * y₁ * g ∈ T := hg2 y₁ ⟨hy₁T, mem_centralizer_singleton_iff.2 hy₁t⟩
  have hx'w : g⁻¹ * x * g = (g⁻¹ * y₁ * g) * (g⁻¹ * y₁ * g) := by
    rw [← hy₁x]; group
  have hx'2 : g⁻¹ * x * g * (g⁻¹ * x * g) = 1 := by
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [S.x2]; group
  have hx'1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply S.x1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hx'cen : ∀ s ∈ T, s * (g⁻¹ * x * g) = (g⁻¹ * x * g) * s := by
    obtain ⟨c, hcA, hc⟩ := hsq _ hwT
    have hcQ : c ∈ Q := D.AQ hcA
    rcases hc with h | h
    · have hxc : g⁻¹ * x * g = c := hx'w.trans h
      have hcc : c * c = 1 := by rw [← hxc]; exact hx'2
      rcases D.A_inv hcA hcc with h1 | h1
      · exact absurd (hxc.trans h1) hx'1
      · intro s hs
        rw [hxc, h1]
        exact S.xc s hs
    · have hxc : g⁻¹ * x * g = z * c := hx'w.trans h
      have hzc : z * c = c * z := S.PQc z hzP c hcQ
      have hcc : c * c = 1 := by
        have h2 : z * c * (z * c) = 1 := by rw [← hxc]; exact hx'2
        calc c * c = (z * z) * (c * c) := by rw [hzz, one_mul]
          _ = z * (z * c) * c := by group
          _ = z * (c * z) * c := by rw [hzc]
          _ = z * c * (z * c) := by group
          _ = 1 := h2
      rcases D.A_inv hcA hcc with h1 | h1
      · intro s hs
        rw [hxc, h1, mul_one]
        exact hzT s hs
      · intro s hs
        rw [hxc, h1]
        calc s * (z * x) = (s * z) * x := by group
          _ = (z * s) * x := by rw [hzT s hs]
          _ = z * (s * x) := by group
          _ = z * (x * s) := by rw [S.xc s hs]
          _ = z * x * s := by group
  obtain ⟨n, hnN, hn⟩ := burnside_central hSylT (a := x) (g := g) (fun s hs => S.xc s hs) hx'cen
  have hnx := S.normalizer_le_centralizer D hnN
  have hgx' : g⁻¹ * x * g = x := by
    rw [← hn]
    calc n⁻¹ * x * n = n⁻¹ * (x * n) := by group
      _ = n⁻¹ * (n * x) := by rw [hnx]
      _ = x := by group
  have hgx : g * x = x * g := by
    calc g * x = g * (g⁻¹ * x * g) := by rw [hgx']
      _ = x * g := by group
  have ht₁T : g⁻¹ * t * g ∈ T := hg1.1
  have ht₁Q : g⁻¹ * t * g ∈ Q := fusC g hgx ht₁T
  have ht₁ρ : g⁻¹ * t * g * ρ = ρ * (g⁻¹ * t * g) := mem_centralizer_singleton_iff.1 hg1.2
  have ht₁A : g⁻¹ * t * g ∈ A := D.mem_A_of_comm_ρ ht₁Q ht₁ρ
  have ht₁2 : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [S.t2]; group
  have ht₁1 : g⁻¹ * t * g ≠ 1 := by
    intro h
    apply S.t1
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have ht₁x : g⁻¹ * t * g = x := by
    rcases D.A_inv ht₁A ht₁2 with h | h
    · exact absurd h ht₁1
    · exact h
  apply S.tx
  calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    _ = g * x * g⁻¹ := by rw [ht₁x]
    _ = x := by rw [hgx]; group

end Setup714

end CaseF

end CFSG.GH74.GLS.Th2.R714
