module

public import CFSG.ClassicalInvolution.Asc77.AscS24BCyc1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24

section General

variable {G : Type} [Group G]

theorem eq_or_eq_inv_of_conj_mem {x y : G} (hx : orderOf x = 4)
    (h : y * x * y⁻¹ ∈ Subgroup.zpowers x) : y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hmod : x ^ (k % 4) = x ^ k := by
    have h1 := zpow_mod_orderOf x k
    rw [hx] at h1
    exact_mod_cast h1
  have h4 : x ^ (4 : ℤ) = 1 := by
    have h1 := pow_orderOf_eq_one x
    rw [hx] at h1
    exact_mod_cast h1
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    omega
  have hx2 : x ^ 2 ≠ 1 := by
    intro h2
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hx] at this
    omega
  have hr : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rw [← hmod] at hk
  rcases hr with h0 | h0 | h0 | h0 <;> rw [h0] at hk
  · exfalso
    apply hx1
    have e : y * x * y⁻¹ = 1 := by rw [← hk, zpow_zero]
    calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
      _ = 1 := by rw [e]; group
  · left
    rw [← hk, zpow_one]
  · exfalso
    apply hx2
    have e : (y * x * y⁻¹) ^ 2 = 1 := by
      rw [← hk, ← zpow_natCast, ← zpow_mul]
      exact h4
    rw [conj_pow] at e
    calc x ^ 2 = y⁻¹ * (y * x ^ 2 * y⁻¹) * y := by group
      _ = 1 := by rw [e]; group
  · right
    rw [← hk, eq_inv_iff_mul_eq_one, ← zpow_add_one]
    exact h4

theorem sq_le_centralizer [Finite G] {Q : Subgroup G} {x s₀ y : G}
    (hU : Subgroup.zpowers x ≤ Q) (hcard : Nat.card ↥Q = 2 * Nat.card ↥(Subgroup.zpowers x))
    (hs₀ : s₀ ∈ Q) (hs₀U : s₀ ∉ Subgroup.zpowers x) (hyQ : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q)
    (hyx : y * x * y⁻¹ = x⁻¹) : Q ≤ Subgroup.centralizer ({y * y} : Set G) := by
  have hyxk : ∀ k : ℤ, y * x ^ k * y⁻¹ = x ^ (-k) := fun k => by
    rw [← conj_zpow, hyx, inv_zpow, zpow_neg]
  have hyinv : ∀ k : ℤ, y⁻¹ * x ^ k * y = x ^ (-k) := fun k => by
    have h1 := hyxk (-k)
    rw [neg_neg] at h1
    calc y⁻¹ * x ^ k * y = y⁻¹ * (y * x ^ (-k) * y⁻¹) * y := by rw [h1]
      _ = x ^ (-k) := by group
  have hys : y * s₀ * y⁻¹ ∈ Q := hyQ s₀ hs₀
  have hysU : y * s₀ * y⁻¹ ∉ Subgroup.zpowers x := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hs₀U
    have e : s₀ = y⁻¹ * (y * s₀ * y⁻¹) * y := by group
    rw [e, ← hk, hyinv]
    exact Subgroup.zpow_mem_zpowers _ _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (Thompson.inv_mul_mem_of_card_eq_two_mul hU hcard hs₀ hys hs₀U hysU)
  have hk' : y * s₀ * y⁻¹ = s₀ * x ^ k := by rw [hk]; group
  have hx : (y * y) * x = x * (y * y) := by
    have e : (y * y) * x * (y * y)⁻¹ = x := by
      calc (y * y) * x * (y * y)⁻¹ = y * (y * x * y⁻¹) * y⁻¹ := by group
        _ = x := by
          rw [hyx]
          have := hyxk (-1)
          rw [zpow_neg_one, neg_neg, zpow_one] at this
          exact this
    calc (y * y) * x = (y * y) * x * (y * y)⁻¹ * (y * y) := by group
      _ = x * (y * y) := by rw [e]
  have hs : (y * y) * s₀ = s₀ * (y * y) := by
    have e : (y * y) * s₀ * (y * y)⁻¹ = s₀ := by
      calc (y * y) * s₀ * (y * y)⁻¹ = y * (y * s₀ * y⁻¹) * y⁻¹ := by group
        _ = y * (s₀ * x ^ k) * y⁻¹ := by rw [hk']
        _ = (y * s₀ * y⁻¹) * (y * x ^ k * y⁻¹) := by group
        _ = s₀ * x ^ k * x ^ (-k) := by rw [hk', hyxk]
        _ = s₀ := by rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
    calc (y * y) * s₀ = (y * y) * s₀ * (y * y)⁻¹ * (y * y) := by group
      _ = s₀ * (y * y) := by rw [e]
  exact S24B.commute_of_index_two hU hcard hs₀ hs₀U hx hs

end General

section Sub

variable {G : Type} [Group G]

@[expose] def sZero (Ω : Set (Subgroup G)) (W S : Subgroup G) : Subgroup G where
  carrier := {s | s ∈ S ∧ ∃ m ∈ MGrp Ω W, ∀ w ∈ W, s * w * s⁻¹ = m * w * m⁻¹}
  one_mem' := ⟨S.one_mem, 1, (MGrp Ω W).one_mem, fun w _ => by group⟩
  mul_mem' := by
    rintro a b ⟨haS, m₁, hm₁, h₁⟩ ⟨hbS, m₂, hm₂, h₂⟩
    refine ⟨S.mul_mem haS hbS, m₁ * m₂, (MGrp Ω W).mul_mem hm₁ hm₂, fun w hw => ?_⟩
    have hm₂N := Thompson.MGrp_le_normalizer Ω W hm₂
    have hw' : m₂ * w * m₂⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hm₂N w).mp hw
    calc a * b * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
      _ = a * (m₂ * w * m₂⁻¹) * a⁻¹ := by rw [h₂ w hw]
      _ = m₁ * (m₂ * w * m₂⁻¹) * m₁⁻¹ := h₁ _ hw'
      _ = m₁ * m₂ * w * (m₁ * m₂)⁻¹ := by group
  inv_mem' := by
    rintro a ⟨haS, m, hm, h⟩
    refine ⟨S.inv_mem haS, m⁻¹, (MGrp Ω W).inv_mem hm, fun w hw => ?_⟩
    have hmN := Thompson.MGrp_le_normalizer Ω W hm
    have hw' : m⁻¹ * w * m⁻¹⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmN) w).mp hw
    have e := h _ hw'
    have e2 : m * (m⁻¹ * w * m⁻¹⁻¹) * m⁻¹ = w := by group
    rw [e2] at e
    calc a⁻¹ * w * a⁻¹⁻¹ = a⁻¹ * (a * (m⁻¹ * w * m⁻¹⁻¹) * a⁻¹) * a := by rw [e]; group
      _ = m⁻¹ * w * m⁻¹⁻¹ := by group

theorem inf_le_sZero {Ω : Set (Subgroup G)} {W S : Subgroup G} : S ⊓ MGrp Ω W ≤ sZero Ω W S :=
  fun s hs => ⟨hs.1, s, hs.2, fun _ _ => rfl⟩

end Sub

section TrivMu

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem trivMu_mul {y₁ y₂ : G} (hy₁ : y₁ ∈ Subgroup.normalizer (W : Set G))
    (h₁ : S24B.TrivMu Ω W y₁) (h₂ : S24B.TrivMu Ω W y₂) : S24B.TrivMu Ω W (y₁ * y₂) := by
  intro m hm
  have hN : y₁ ∈ Subgroup.normalizer ((W ⊔ OCW W : Subgroup G) : Set G) :=
    Thompson.normalizer_le_normalizer_sup W hy₁
  have e1 : y₁ * (y₂ * m * y₂⁻¹ * m⁻¹) * y₁⁻¹ ∈ W ⊔ OCW W :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp (h₂ m hm)
  have e : y₁ * y₂ * m * (y₁ * y₂)⁻¹ * m⁻¹ =
      (y₁ * (y₂ * m * y₂⁻¹ * m⁻¹) * y₁⁻¹) * (y₁ * m * y₁⁻¹ * m⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ e1 (h₁ m hm)

theorem trivMu_of_mem_W {w : G} (hw : w ∈ W) : S24B.TrivMu Ω W w := by
  intro m hm
  have hmN := Thompson.MGrp_le_normalizer Ω W hm
  have h1 : m * w⁻¹ * m⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hmN _).mp (W.inv_mem hw)
  have e : w * m * w⁻¹ * m⁻¹ = w * (m * w⁻¹ * m⁻¹) := by group
  rw [e]
  exact Subgroup.mem_sup_left (W.mul_mem hw h1)

theorem inv_conj_of_inv {y : G} (hinv : ∀ w ∈ W, y * w * y⁻¹ = w⁻¹) :
    ∀ w ∈ W, y⁻¹ * w * y = w⁻¹ := fun w hw => by
  have e := hinv _ (W.inv_mem hw)
  rw [inv_inv] at e
  calc y⁻¹ * w * y = y⁻¹ * (y * w⁻¹ * y⁻¹) * y := by rw [e]
    _ = w⁻¹ := by group

theorem conj_eq_of_mem_centralizer {n : G} (hn : n ∈ Subgroup.centralizer (W : Set G)) {v : G}
    (hv : v ∈ W) : n * v * n⁻¹ = v := by
  have h := Subgroup.mem_centralizer_iff.mp hn v hv
  rw [← h]
  group

end TrivMu

section Ctx

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : S24B.Ctx8 p f Ω K K' W S R R' z u)

include C in
theorem sup_OCW_le_centralizer : W ⊔ OCW W ≤ Subgroup.centralizer (W : Set G) := by
  refine sup_le (fun x hx => ?_) (Thompson.OCW_le_centralizer W)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Thompson.commutes_of_mem_WSet C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW y hy x hx

theorem inf_W_eq_x₁ : K ⊓ W = Subgroup.zpowers C.D.x₁ := by
  rw [C.D.h₁, C.hR]
  apply le_antisymm
  · intro x hx
    refine ⟨?_, hx.2⟩
    rw [← C.inf_S_eq_R]
    exact ⟨hx.1, C.hd.hWS hx.2⟩
  · exact inf_le_inf_right W C.hd.hR.2.1

theorem inf_W_eq_x₂ : K' ⊓ W = Subgroup.zpowers C.D.x₂ := by
  rw [C.D.h₂, C.hR']
  apply le_antisymm
  · intro x hx
    refine ⟨?_, hx.2⟩
    rw [← C.inf_S_eq_R']
    exact ⟨hx.1, C.hd.hWS hx.2⟩
  · exact inf_le_inf_right W C.hd.hR'.2.1

theorem conj_x₁_cases {y : G} (hyN : y ∈ Subgroup.normalizer (W : Set G))
    (hyK : conjSub y K = K) :
    y * C.D.x₁ * y⁻¹ = C.D.x₁ ∨ y * C.D.x₁ * y⁻¹ = C.D.x₁⁻¹ := by
  refine eq_or_eq_inv_of_conj_mem C.orderOf_x₁ ?_
  rw [← inf_W_eq_x₁ C]
  refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hyN _).mp C.D.x₁_mem⟩
  have h := conj_mem_conjSub (n := y) C.x₁_mem_K
  rwa [hyK] at h

include C in
theorem acts_pm {y : G} (hyS : y ∈ (S : Subgroup G)) (hT : S24B.TrivMu Ω W y) :
    (∀ w ∈ W, y * w * y⁻¹ = w) ∨ (∀ w ∈ W, y * w * y⁻¹ = w⁻¹) := by
  have hyN : y ∈ Subgroup.normalizer (W : Set G) := C.le_normalizer_W hyS
  have hK : conjSub y K = K := by
    have h := C.fix_of_trivMu hyN hT C.D.F.ρ
    rwa [C.hK] at h
  have h1 := conj_x₁_cases C hyN hK
  have hsM : C.D.F.ρ₃.r ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D C.D.F.ρ₃.hR C.D.F.ρ₃.hr
  obtain ⟨n, hnd⟩ : ∃ n, y * C.D.F.ρ₃.r * y⁻¹ * C.D.F.ρ₃.r⁻¹ = n := ⟨_, rfl⟩
  have hn : n ∈ W ⊔ OCW W := hnd ▸ hT _ hsM
  have hnc := sup_OCW_le_centralizer C hn
  have hys : y * C.D.F.ρ₃.r * y⁻¹ = n * C.D.F.ρ₃.r := by rw [← hnd]; group
  have hx13 : C.D.x₁ * C.D.x₃ ∈ W := W.mul_mem C.D.x₁_mem C.D.x₃_mem
  have key : (y * C.D.x₁ * y⁻¹) * (y * C.D.x₃ * y⁻¹) =
      n * (C.D.F.ρ₃.r * (y * C.D.x₁ * y⁻¹) * C.D.F.ρ₃.r⁻¹) * n⁻¹ := by
    calc (y * C.D.x₁ * y⁻¹) * (y * C.D.x₃ * y⁻¹) = y * (C.D.x₁ * C.D.x₃) * y⁻¹ := by group
      _ = y * (C.D.F.ρ₃.r * C.D.x₁ * C.D.F.ρ₃.r⁻¹) * y⁻¹ := by rw [C.D.s₁]
      _ = (y * C.D.F.ρ₃.r * y⁻¹) * (y * C.D.x₁ * y⁻¹) * (y * C.D.F.ρ₃.r * y⁻¹)⁻¹ := by group
      _ = (n * C.D.F.ρ₃.r) * (y * C.D.x₁ * y⁻¹) * (n * C.D.F.ρ₃.r)⁻¹ := by rw [hys]
      _ = n * (C.D.F.ρ₃.r * (y * C.D.x₁ * y⁻¹) * C.D.F.ρ₃.r⁻¹) * n⁻¹ := by group
  have hconj : ∀ a b : ℤ, y * (C.D.x₁ ^ a * C.D.x₃ ^ b) * y⁻¹ =
      (y * C.D.x₁ * y⁻¹) ^ a * (y * C.D.x₃ * y⁻¹) ^ b := fun a b => by
    rw [conj_zpow, conj_zpow]
    group
  rcases h1 with h1 | h1
  · left
    have e := key
    rw [h1, C.D.s₁, conj_eq_of_mem_centralizer hnc hx13] at e
    have h3 : y * C.D.x₃ * y⁻¹ = C.D.x₃ := mul_left_cancel e
    intro w hw
    obtain ⟨a, b, rfl⟩ := C.exists_nf hw
    rw [hconj, h1, h3]
  · right
    have e := key
    have e' : C.D.F.ρ₃.r * C.D.x₁⁻¹ * C.D.F.ρ₃.r⁻¹ = (C.D.x₁ * C.D.x₃)⁻¹ := by
      rw [← C.D.s₁]
      group
    rw [h1, e', conj_eq_of_mem_centralizer hnc (W.inv_mem hx13)] at e
    have h3 : y * C.D.x₃ * y⁻¹ = C.D.x₃⁻¹ := by
      calc y * C.D.x₃ * y⁻¹ = C.D.x₁ * (C.D.x₁⁻¹ * (y * C.D.x₃ * y⁻¹)) := by group
        _ = C.D.x₁ * (C.D.x₁ * C.D.x₃)⁻¹ := by rw [e]
        _ = C.D.x₃⁻¹ := by rw [C.D.comm13.eq]; group
    intro w hw
    obtain ⟨a, b, rfl⟩ := C.exists_nf hw
    rw [hconj, h1, h3, inv_zpow', inv_zpow', mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact (C.D.comm13.zpow_zpow (-a) (-b)).eq

include C in
theorem exists_centralizes_r {y : G} (hyS : y ∈ (S : Subgroup G)) (hT : S24B.TrivMu Ω W y)
    (hinv : ∀ w ∈ W, y * w * y⁻¹ = w⁻¹) :
    ∃ k : ℤ, (y * C.D.x₃ ^ k) * C.D.F.ρ.r = C.D.F.ρ.r * (y * C.D.x₃ ^ k) := by
  have hyN := C.le_normalizer_W hyS
  have hK : conjSub y K = K := by
    have h := C.fix_of_trivMu hyN hT C.D.F.ρ
    rwa [C.hK] at h
  have hyr : y * C.D.F.ρ.r * y⁻¹ ∈ R := by
    refine (le_of_eq C.inf_S_eq_R) ⟨?_, S.mul_mem (S.mul_mem hyS (C.hd.hR.2.2 C.r_mem_R))
      (S.inv_mem hyS)⟩
    have h := conj_mem_conjSub (n := y) C.r_mem_K
    rwa [hK] at h
  have hU : Subgroup.zpowers C.D.x₁ ≤ R := Subgroup.zpowers_le.mpr C.x₁_mem_R
  have hinv' := inv_conj_of_inv hinv
  have hyrU : y * C.D.F.ρ.r * y⁻¹ ∉ Subgroup.zpowers C.D.x₁ := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply C.r_not_mem_zpowers
    have e : C.D.F.ρ.r = y⁻¹ * (y * C.D.F.ρ.r * y⁻¹) * y := by group
    rw [e, ← hk, hinv' _ (W.zpow_mem C.D.x₁_mem k)]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers _ _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (Thompson.inv_mul_mem_of_card_eq_two_mul hU C.card_R C.r_mem_R hyr C.r_not_mem_zpowers hyrU)
  refine ⟨k, ?_⟩
  have hyrk : y * C.D.F.ρ.r * y⁻¹ = C.D.F.ρ.r * C.D.x₁ ^ k := by rw [hk]; group
  have h1 := C.conj_x₃_zpow_r k
  have h2 : y * C.D.x₁ ^ (-k) * y⁻¹ = C.D.x₁ ^ k := by
    rw [hinv _ (W.zpow_mem C.D.x₁_mem _), zpow_neg, inv_inv]
  have h4 : C.D.x₁ ^ k * C.D.F.ρ.r = C.D.F.ρ.r * C.D.x₁ ^ (-k) := by
    have h3 := C.r_mul_x₁_zpow (-k)
    rw [neg_neg] at h3
    exact h3.symm
  have e : (y * C.D.x₃ ^ k) * C.D.F.ρ.r * (y * C.D.x₃ ^ k)⁻¹ = C.D.F.ρ.r := by
    calc (y * C.D.x₃ ^ k) * C.D.F.ρ.r * (y * C.D.x₃ ^ k)⁻¹
        = y * (C.D.x₃ ^ k * C.D.F.ρ.r * (C.D.x₃ ^ k)⁻¹) * y⁻¹ := by group
      _ = y * (C.D.x₁ ^ (-k) * C.D.F.ρ.r) * y⁻¹ := by rw [h1]
      _ = (y * C.D.x₁ ^ (-k) * y⁻¹) * (y * C.D.F.ρ.r * y⁻¹) := by group
      _ = C.D.x₁ ^ k * C.D.F.ρ.r * C.D.x₁ ^ k := by rw [h2, hyrk]; group
      _ = C.D.F.ρ.r * C.D.x₁ ^ (-k) * C.D.x₁ ^ k := by rw [h4]
      _ = C.D.F.ρ.r := by rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  calc (y * C.D.x₃ ^ k) * C.D.F.ρ.r
      = (y * C.D.x₃ ^ k) * C.D.F.ρ.r * (y * C.D.x₃ ^ k)⁻¹ * (y * C.D.x₃ ^ k) := by group
    _ = C.D.F.ρ.r * (y * C.D.x₃ ^ k) := by rw [e]

include C in
theorem graph_sq [IsSimpleGroup G] (h3 : S24B.H3 p f) {c : G} (hcS : c ∈ (S : Subgroup G))
    (hT : S24B.TrivMu Ω W c) (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) : c * c = 1 := by
  have hcN := C.le_normalizer_W hcS
  have hK : conjSub c K = K := by
    have h := C.fix_of_trivMu hcN hT C.D.F.ρ
    rwa [C.hK] at h
  have hK' : conjSub c K' = K' := by
    have h := C.fix_of_trivMu hcN hT C.D.F.ρ'
    rwa [C.hK'] at h
  have hJ : conjSub c C.D.F.ρ₃.K = C.D.F.ρ₃.K := C.fix_of_trivMu hcN hT C.D.F.ρ₃
  have hRQ : ∀ q ∈ R, c * q * c⁻¹ ∈ R := fun q hq => by
    refine (le_of_eq C.inf_S_eq_R) ⟨?_, S.mul_mem (S.mul_mem hcS (C.hd.hR.2.2 hq))
      (S.inv_mem hcS)⟩
    have h := conj_mem_conjSub (n := c) (C.hd.hR.2.1 hq)
    rwa [hK] at h
  have hR'Q : ∀ q ∈ R', c * q * c⁻¹ ∈ R' := fun q hq => by
    refine (le_of_eq C.inf_S_eq_R') ⟨?_, S.mul_mem (S.mul_mem hcS (C.hd.hR'.2.2 hq))
      (S.inv_mem hcS)⟩
    have h := conj_mem_conjSub (n := c) (C.hd.hR'.2.1 hq)
    rwa [hK'] at h
  have hR : R ≤ Subgroup.centralizer ({c * c} : Set G) :=
    sq_le_centralizer (Subgroup.zpowers_le.mpr C.x₁_mem_R) C.card_R C.r_mem_R
      C.r_not_mem_zpowers hRQ (hinv _ C.D.x₁_mem)
  have hR' : R' ≤ Subgroup.centralizer ({c * c} : Set G) :=
    sq_le_centralizer (Subgroup.zpowers_le.mpr C.x₂_mem_R') C.card_R' C.t_mem_R'
      C.t_not_mem_zpowers hR'Q (hinv _ C.D.x₂_mem)
  have hQS : W ⊔ Subgroup.zpowers c ≤ (S : Subgroup G) :=
    sup_le C.hd.hWS (Subgroup.zpowers_le.mpr hcS)
  have hQ2 : IsPGroup 2 ↥(W ⊔ Subgroup.zpowers c) := S.isPGroup'.to_le hQS
  have hQJ : W ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (C.D.F.ρ₃.K : Set G) :=
    sup_le (C.W_le_normalizer C.D.F.ρ₃.K C.D.F.ρ₃.hK ⟨C.x₃_mem_J, C.D.x₃_mem⟩ C.orderOf_x₃)
      (Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hJ))
  obtain ⟨T₃, hT₃, hT₃n⟩ := T3.exists_sylow_normalized hQ2 hQJ
  have hT₃N : W ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (T₃ : Set G) := fun q hq =>
    mem_normalizer_iff_conjSub_eq.mpr (hT₃n q hq)
  have hx₃T : C.D.x₃ ∈ T₃ := by
    have h2 : IsPGroup 2 ↥(Subgroup.zpowers C.D.x₃) :=
      T7A.isPGroup_zpowers_of_orderOf_four C.orderOf_x₃
    have hle : Subgroup.zpowers C.D.x₃ ≤ Subgroup.normalizer (T₃ : Set G) :=
      Subgroup.zpowers_le.mpr (hT₃N (Subgroup.mem_sup_left C.D.x₃_mem))
    have hsup := h2.to_sup_of_normal_right' hT₃.2.1 hle
    have heq := hT₃.eq_of_le hsup
      (sup_le (Subgroup.zpowers_le.mpr C.x₃_mem_J) hT₃.1) le_sup_right
    rw [← heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hT₃W : T₃ ≤ Subgroup.normalizer (W : Set G) := by
    have hsup := hQ2.to_sup_of_normal_right' hT₃.2.1 hT₃N
    obtain ⟨S'', hS''⟩ := hsup.exists_le_sylow
    have hWS'' : W ≤ (S'' : Subgroup G) := le_sup_left.trans (le_sup_left.trans hS'')
    have hT₃S'' : T₃ ≤ (S'' : Subgroup G) := le_sup_right.trans hS''
    exact (Thompson.mem_DSet_of_le_sylow C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW hWS''
      (mem_RSet_of_isSylow2In C.D.F.ρ₃.hK hT₃) hT₃S'').2
  have hcard : Nat.card ↥T₃ = 2 * Nat.card ↥(Subgroup.zpowers C.D.x₃) := by
    rw [IsSylow2In.natCard_eq hT₃ C.D.F.ρ₃.hRK]
    have h := Thompson.D_card C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW C.D.F.ρ₃.hR
    rw [← C.D.h₃] at h
    exact h
  have hU₃ : Subgroup.zpowers C.D.x₃ ≤ T₃ := Subgroup.zpowers_le.mpr hx₃T
  obtain ⟨s₃, hs₃, hs₃U⟩ : ∃ s₃ ∈ T₃, s₃ ∉ Subgroup.zpowers C.D.x₃ := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (fun y hy => hcon y hy : T₃ ≤ Subgroup.zpowers C.D.x₃)
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers C.D.x₃) := Nat.card_pos
    omega
  have hT₃Q : ∀ q ∈ T₃, c * q * c⁻¹ ∈ T₃ := fun q hq => by
    have h := hT₃n c (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
    rw [← h]
    exact conj_mem_conjSub hq
  have hT₃c : T₃ ≤ Subgroup.centralizer ({c * c} : Set G) :=
    sq_le_centralizer hU₃ hcard hs₃ hs₃U hT₃Q (hinv _ C.D.x₃_mem)
  refine S24B.eq_one_of_forall_pow
    (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (S.mul_mem hcS hcS))) fun k hk => ?_
  exact h3 G Ω K K' W S R R' z u C.hs C.hd C.h8 C.D C.hK C.hK' C.hR C.hR' _ hk
    (S24B.le_centralizer_pow hR k) (S24B.le_centralizer_pow hR' k) T₃ hT₃ hT₃W
    (S24B.le_centralizer_pow hT₃c k)

include C in
theorem conj_mem_sZero {s x : G} (hs : s ∈ (S : Subgroup G)) (hx : x ∈ sZero Ω W S) :
    s * x * s⁻¹ ∈ sZero Ω W S := by
  obtain ⟨hxS, m, hm, h⟩ := hx
  have hsN := C.le_normalizer_W hs
  have hsM : s ∈ Subgroup.normalizer (MGrp Ω W : Set G) := S24B.le_normalizer_MGrp C.D.c.hΩ hsN
  refine ⟨S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs), s * m * s⁻¹,
    (Subgroup.mem_normalizer_iff.mp hsM m).mp hm, fun w hw => ?_⟩
  have hw' : s⁻¹ * w * s⁻¹⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsN) w).mp hw
  calc s * x * s⁻¹ * w * (s * x * s⁻¹)⁻¹ = s * (x * (s⁻¹ * w * s⁻¹⁻¹) * x⁻¹) * s⁻¹ := by group
    _ = s * (m * (s⁻¹ * w * s⁻¹⁻¹) * m⁻¹) * s⁻¹ := by rw [h _ hw']
    _ = s * m * s⁻¹ * w * (s * m * s⁻¹)⁻¹ := by group

include C in
theorem piG_eq_one_of_trivMu {m : G} (hm : m ∈ MGrp Ω W) (hT : S24B.TrivMu Ω W m) :
    Thompson.piG W m = 1 := by
  have hcent : ∀ y : ↥(muGroup Ω W), S24B.piM Ω W ⟨m, hm⟩ * y = y * S24B.piM Ω W ⟨m, hm⟩ := by
    intro y
    obtain ⟨n, rfl⟩ := S24B.piM_surjective W y
    have h1 : S24B.piM Ω W (⟨m, hm⟩ * n * (⟨m, hm⟩)⁻¹ * n⁻¹) = 1 := by
      apply Subtype.ext
      rw [S24B.piM_apply]
      exact Thompson.piG_of_mem_sup (hT n n.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 := mul_inv_eq_one.mp h1
    calc S24B.piM Ω W ⟨m, hm⟩ * S24B.piM Ω W n
        = S24B.piM Ω W ⟨m, hm⟩ * S24B.piM Ω W n * (S24B.piM Ω W ⟨m, hm⟩)⁻¹ *
            S24B.piM Ω W ⟨m, hm⟩ := by group
      _ = S24B.piM Ω W n * S24B.piM Ω W ⟨m, hm⟩ := by rw [h2]
  have hφ : ∀ σ : Equiv.Perm (Fin 4),
      C.D.φ (S24B.piM Ω W ⟨m, hm⟩) * σ = σ * C.D.φ (S24B.piM Ω W ⟨m, hm⟩) := by
    intro σ
    have h2 := congrArg C.D.φ (hcent (C.D.φ.symm σ))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  have hq1 : S24B.piM Ω W ⟨m, hm⟩ = 1 := by
    have h := S24B.perm4_center _ (hφ _) (hφ _) (hφ _)
    exact C.D.φ.injective (h.trans (map_one C.D.φ).symm)
  have h := congrArg Subtype.val hq1
  rw [S24B.piM_apply] at h
  exact h

include C in
theorem conjSub_eq_of_conj {L : Subgroup G} (hL : L ∈ Ω) {x m : G} (hx : x ∈ L)
    (o : orderOf x = 4) (h : m⁻¹ * x * m = x ∨ m⁻¹ * x * m = x⁻¹) : conjSub m L = L := by
  have hxm : x ∈ conjSub m L := by
    rw [mem_conjSub_iff]
    rcases h with h | h <;> rw [h]
    · exact hx
    · exact L.inv_mem hx
  have h2 : IsPGroup 2 ↥(Subgroup.zpowers x) := T7A.isPGroup_zpowers_of_orderOf_four o
  have h4 : 4 ≤ Nat.card ↥(Subgroup.zpowers x) := by rw [Nat.card_zpowers, o]
  exact C.D.c.hΩ.eq_of_le_of_le (C.D.c.hΩ.conjInvariant m L hL) hL h2 h4
    (Subgroup.zpowers_le.mpr hxm) (Subgroup.zpowers_le.mpr hx)

include C in
theorem not_inv_of_mem_MGrp {m : G} (hm : m ∈ MGrp Ω W) (hinv : ∀ w ∈ W, m * w * m⁻¹ = w⁻¹) :
    False := by
  have hmN := Thompson.MGrp_le_normalizer Ω W hm
  have hinv' := inv_conj_of_inv hinv
  have h1 : conjSub m C.D.F.ρ.K = C.D.F.ρ.K :=
    conjSub_eq_of_conj C C.D.F.ρ.hK (by rw [C.hK]; exact C.x₁_mem_K) C.orderOf_x₁
      (Or.inr (hinv' _ C.D.x₁_mem))
  have h2 : conjSub m C.D.F.ρ'.K = C.D.F.ρ'.K :=
    conjSub_eq_of_conj C C.D.F.ρ'.hK (by rw [C.hK']; exact C.x₂_mem_K') C.orderOf_x₂
      (Or.inr (hinv' _ C.D.x₂_mem))
  have h3 : conjSub m C.D.F.ρ₃.K = C.D.F.ρ₃.K :=
    conjSub_eq_of_conj C C.D.F.ρ₃.hK C.x₃_mem_J C.orderOf_x₃ (Or.inr (hinv' _ C.D.x₃_mem))
  have hT := C.trivMu_of_fix hmN h1 h2 h3
  have hmW : m ∈ W ⊔ OCW W := (Thompson.piG_eq_one_iff hmN).mp (piG_eq_one_of_trivMu C hm hT)
  have e1 := conj_eq_of_mem_centralizer (sup_OCW_le_centralizer C hmW) C.D.x₁_mem
  rw [hinv _ C.D.x₁_mem] at e1
  have e2 : C.D.x₁ ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← e1]
    exact inv_mul_cancel _
  have := orderOf_dvd_of_pow_eq_one e2
  rw [C.orderOf_x₁] at this
  omega

include C in
theorem not_mem_sZero {c : G} (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) : c ∉ sZero Ω W S := by
  rintro ⟨-, m, hm, h⟩
  exact not_inv_of_mem_MGrp C hm fun w hw => (h w hw).symm.trans (hinv w hw)

include C in
theorem mem_or_inv_mul_mem_sZero {c y : G} (hcS : c ∈ (S : Subgroup G))
    (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) (hyS : y ∈ (S : Subgroup G)) :
    y ∈ sZero Ω W S ∨ c⁻¹ * y ∈ sZero Ω W S := by
  obtain ⟨x, hxP, t, htS, hT, rfl⟩ := C.exists_decomp hyS
  rcases acts_pm C htS hT with ht | ht
  · left
    refine ⟨S.mul_mem hxP.1 htS, x, hxP.2, fun w hw => ?_⟩
    calc x * t * w * (x * t)⁻¹ = x * (t * w * t⁻¹) * x⁻¹ := by group
      _ = x * w * x⁻¹ := by rw [ht w hw]
  · right
    have hcinv := inv_conj_of_inv hinv
    refine ⟨S.mul_mem (S.inv_mem hcS) (S.mul_mem hxP.1 htS), x, hxP.2, fun w hw => ?_⟩
    have hxN := C.le_normalizer_W hxP.1
    have hxw : x * w * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hxN w).mp hw
    calc c⁻¹ * (x * t) * w * (c⁻¹ * (x * t))⁻¹ = c⁻¹ * (x * (t * w * t⁻¹) * x⁻¹) * c := by group
      _ = c⁻¹ * (x * w⁻¹ * x⁻¹) * c := by rw [ht w hw]
      _ = c⁻¹ * (x * w * x⁻¹)⁻¹ * c := by group
      _ = (x * w * x⁻¹)⁻¹⁻¹ := hcinv _ (W.inv_mem hxw)
      _ = x * w * x⁻¹ := inv_inv _

include C in
theorem commutator_mem_sZero {c : G} (hcS : c ∈ (S : Subgroup G))
    (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) :
    ∀ y₁ ∈ (S : Subgroup G), ∀ y₂ ∈ (S : Subgroup G), y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ sZero Ω W S := by
  intro y₁ hy₁ y₂ hy₂
  have hnorm : ∀ s ∈ (S : Subgroup G), ∀ x ∈ sZero Ω W S, s * x * s⁻¹ ∈ sZero Ω W S :=
    fun s hs x hx => conj_mem_sZero C hs hx
  rcases mem_or_inv_mul_mem_sZero C hcS hinv hy₁ with h₁ | h₁ <;>
    rcases mem_or_inv_mul_mem_sZero C hcS hinv hy₂ with h₂ | h₂
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
      (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
  · have h := hnorm y₂ hy₂ _ (Subgroup.inv_mem _ h₁)
    have e : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ = y₁ * (y₂ * y₁⁻¹ * y₂⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ h₁ h
  · exact Subgroup.mul_mem _ (hnorm y₁ hy₁ y₂ h₂) (Subgroup.inv_mem _ h₂)
  · have hb : y₁⁻¹ * y₂ ∈ sZero Ω W S := by
      have e : y₁⁻¹ * y₂ = (c⁻¹ * y₁)⁻¹ * (c⁻¹ * y₂) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h₁) h₂
    have h3 := hnorm y₁ hy₁ _
      (Subgroup.mul_mem _ (hnorm y₁ hy₁ _ hb) (Subgroup.inv_mem _ hb))
    have e : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ =
        y₁ * (y₁ * (y₁⁻¹ * y₂) * y₁⁻¹ * (y₁⁻¹ * y₂)⁻¹) * y₁⁻¹ := by group
    rw [e]
    exact h3

end Ctx

end S24

end CFSG.ClassicalInvolution.Asc77
