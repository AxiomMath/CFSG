module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalPermCenter
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.AltStdBalAct
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

section Squares

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem sq_mem_sup (h : Setting G L n) (d : Cyc L Q z) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) : c ^ 2 ∈ L ⊔ Q := by
  obtain ⟨e⟩ := h.iso
  have hc2 : c ^ 2 ∈ centralizer ({z} : Set G) := pow_mem hc 2
  rw [mem_sup_iff h d e hc2]
  have : (⟨c ^ 2, centralizer_le_normalizer h d hc2⟩ : normalizer (L : Set G)) =
      ⟨c, centralizer_le_normalizer h d hc⟩ ^ 2 := rfl
  rw [this, map_pow]
  rcases Int.units_eq_one_or (signHom e h.hn ⟨c, centralizer_le_normalizer h d hc⟩) with h1 | h1
  · rw [h1]; rfl
  · rw [h1]; decide

end Squares

section Cyclic

variable {G : Type*} [Group G]

theorem exists_orderOf_eq_of_dvd [Finite G] {T : Subgroup G} (hc : IsCyclic T) {m : ℕ}
    (hm : m ∣ Nat.card T) : ∃ t ∈ T, orderOf t = m := by
  obtain ⟨⟨g, hgT⟩, hgen⟩ := IsCyclic.exists_generator (α := T)
  have hord : orderOf g = Nat.card T := by
    have := orderOf_eq_card_of_forall_mem_zpowers hgen
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨k, hk⟩ := hm
  have hpos : 0 < Nat.card T := Nat.card_pos
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      omega
    · exact h
  refine ⟨g ^ k, pow_mem hgT k, ?_⟩
  have hdvd : k ∣ orderOf g := by
    rw [hord, hk]
    exact Dvd.intro_left m rfl
  rw [orderOf_pow_of_dvd hk0.ne' hdvd, hord, hk]
  exact Nat.mul_div_cancel m hk0

theorem exists_orderOf_eq_two_pow [Finite G] {T : Subgroup G} (hc : IsCyclic T)
    (hp : IsPGroup 2 T) {k : ℕ} (hk : 2 ^ k ≤ Nat.card T) : ∃ t ∈ T, orderOf t = 2 ^ k := by
  obtain ⟨j, hj⟩ := hp.exists_card_eq
  have hkj : k ≤ j := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ j < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hlt
    omega
  exact exists_orderOf_eq_of_dvd hc (by rw [hj]; exact Nat.pow_dvd_pow 2 hkj)

end Cyclic

section Transport

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem sq_eq_one_of_commute_sq (h : Setting G L n) {l x : G} (hl : l ∈ L) (hl2 : orderOf l = 2)
    (hx : x ∈ L) (hxl : x * l = l * x)
    (hsq : ∀ y ∈ L, y * l = l * y → x * y ^ 2 = y ^ 2 * x) (hx4 : x ^ 4 = 1) : x ^ 2 = 1 := by
  obtain ⟨e⟩ := h.iso
  have hσ : orderOf (e ⟨l, hl⟩ : alternatingGroup (Fin n)) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hl2]
  have hcσ : (e ⟨x, hx⟩ : alternatingGroup (Fin n)) ∈
      centralizer ({(e ⟨l, hl⟩ : alternatingGroup (Fin n))} :
        Set (alternatingGroup (Fin n))) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hxl)
  have hcsq : ∀ d' ∈ centralizer ({(e ⟨l, hl⟩ : alternatingGroup (Fin n))} :
      Set (alternatingGroup (Fin n))),
      (e ⟨x, hx⟩ : alternatingGroup (Fin n)) * d' ^ 2 =
        d' ^ 2 * (e ⟨x, hx⟩ : alternatingGroup (Fin n)) := by
    intro d' hd'
    rw [mem_centralizer_singleton_iff] at hd'
    obtain ⟨y, rfl⟩ := e.surjective d'
    have hyl : (y : G) * l = l * y := by
      have h1 : e (y * ⟨l, hl⟩) = e (⟨l, hl⟩ * y) := by
        rw [map_mul, map_mul]
        exact hd'
      exact congrArg Subtype.val (e.injective h1)
    have h2 := hsq y y.2 hyl
    rw [← map_pow, ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (by simpa using h2))
  have hc4 : (e ⟨x, hx⟩ : alternatingGroup (Fin n)) ^ 4 = 1 := by
    rw [← map_pow, ← map_one e]
    exact congrArg e (Subtype.ext (by simpa using hx4))
  have h3 := sq_eq_one_of_commute_sq_centralizer (α := Fin n) (by simpa using h.hn) hσ hcσ hcsq hc4
  rw [← map_pow, ← map_one e] at h3
  have h4 := congrArg Subtype.val (e.injective h3)
  simpa using h4

end Transport

section KeyLemma

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem Cyc.comm_Q (d : Cyc L Q z) {q q' : G} (hq : q ∈ Q) (hq' : q' ∈ Q) : q * q' = q' * q := by
  have : IsCyclic Q := d.cyclic
  have := (IsCyclic.isMulCommutative (α := Q)).is_comm.comm ⟨q, hq⟩ ⟨q', hq'⟩
  exact congrArg Subtype.val this

theorem Cyc.comm_L (d : Cyc L Q z) {q y : G} (hq : q ∈ Q) (hy : y ∈ L) : y * q = q * y :=
  mem_centralizer_iff.1 (d.le hq) y hy

theorem no_order_four_of_commute (h : Setting G L n) (d : Cyc L Q z) {T : Subgroup G}
    (hTc : IsCyclic T) {a : G} (haT : a ∈ T) (ha2 : orderOf a = 2) (hTQ : T ⊓ Q = ⊥)
    (haLQ : a ∈ L ⊔ Q)
    (hsq : ∀ t ∈ T, ∀ y ∈ L, y * a = a * y → t * y ^ 2 = y ^ 2 * t) :
    ∀ t ∈ T, t ∈ L ⊔ Q → orderOf t ≠ 4 := by
  intro t htT htLQ ht4
  obtain ⟨l, hl, q₀, hq₀, hlq₀⟩ := (mem_sup_iff_mul d).1 haLQ
  obtain ⟨x, hx, q, hq, hxq⟩ := (mem_sup_iff_mul d).1 htLQ
  have hLQ : L ⊓ Q = ⊥ := inf_eq_bot h d
  have hTT : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ * t₂ = t₂ * t₁ := fun t₁ h₁ t₂ h₂ =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := T)).is_comm.comm ⟨t₁, h₁⟩ ⟨t₂, h₂⟩)
  have ha2' : a * a = 1 := by
    rw [← sq]
    rw [← ha2]
    exact pow_orderOf_eq_one a
  have hl2 : l * l = 1 := by
    have e1 : (l * l) * (q₀ * q₀) = 1 := by
      calc (l * l) * (q₀ * q₀) = l * (l * q₀) * q₀ := by group
        _ = l * (q₀ * l) * q₀ := by rw [d.comm_L hq₀ hl]
        _ = (l * q₀) * (l * q₀) := by group
        _ = 1 := by rw [hlq₀]; exact ha2'
    have e2 : l * l ∈ L ⊓ Q := Subgroup.mem_inf.2 ⟨mul_mem hl hl, by
      have : l * l = (q₀ * q₀)⁻¹ := eq_inv_of_mul_eq_one_left e1
      rw [this]
      exact Subgroup.inv_mem _ (mul_mem hq₀ hq₀)⟩
    rw [hLQ] at e2
    exact e2
  have hl1 : l ≠ 1 := by
    intro hl1
    rw [hl1, one_mul] at hlq₀
    have : a ∈ T ⊓ Q := ⟨haT, hlq₀ ▸ hq₀⟩
    rw [hTQ] at this
    have ha1 : a = 1 := this
    rw [ha1, orderOf_one] at ha2
    omega
  have hlord : orderOf l = 2 := orderOf_eq_prime (by rw [← sq] at hl2; exact (sq l).symm ▸ hl2) hl1
  have hxl : x * l = l * x := by
    have hta := hTT t htT a haT
    rw [← hxq, ← hlq₀] at hta
    have e : (x * l) * (q * q₀) = (l * x) * (q * q₀) := by
      calc (x * l) * (q * q₀) = x * (l * q) * q₀ := by group
        _ = x * (q * l) * q₀ := by rw [d.comm_L hq hl]
        _ = (x * q) * (l * q₀) := by group
        _ = (l * q₀) * (x * q) := hta
        _ = l * (q₀ * x) * q := by group
        _ = l * (x * q₀) * q := by rw [d.comm_L hq₀ hx]
        _ = (l * x) * (q₀ * q) := by group
        _ = (l * x) * (q * q₀) := by rw [d.comm_Q hq₀ hq]
    exact mul_right_cancel e
  have hxsq : ∀ y ∈ L, y * l = l * y → x * y ^ 2 = y ^ 2 * x := by
    intro y hy hyl
    have hya : y * a = a * y := by
      rw [← hlq₀]
      calc y * (l * q₀) = (y * l) * q₀ := by group
        _ = (l * y) * q₀ := by rw [hyl]
        _ = l * (y * q₀) := by group
        _ = l * (q₀ * y) := by rw [d.comm_L hq₀ hy]
        _ = (l * q₀) * y := by group
    have h1 := hsq t htT y hy hya
    rw [← hxq] at h1
    have hy2 : y ^ 2 ∈ L := pow_mem hy 2
    have e : (x * y ^ 2) * q = (y ^ 2 * x) * q := by
      calc (x * y ^ 2) * q = x * (y ^ 2 * q) := by group
        _ = x * (q * y ^ 2) := by rw [d.comm_L hq hy2]
        _ = (x * q) * y ^ 2 := by group
        _ = y ^ 2 * (x * q) := h1
        _ = (y ^ 2 * x) * q := by group
    exact mul_right_cancel e
  have hcomm : Commute x q := d.comm_L hq hx
  have hx4 : x ^ 4 = 1 := by
    have h4 : t ^ 4 = 1 := by rw [← ht4]; exact pow_orderOf_eq_one t
    rw [← hxq, hcomm.mul_pow] at h4
    have e2 : x ^ 4 ∈ L ⊓ Q := Subgroup.mem_inf.2 ⟨pow_mem hx 4, by
      have : x ^ 4 = (q ^ 4)⁻¹ := eq_inv_of_mul_eq_one_left h4
      rw [this]
      exact Subgroup.inv_mem _ (pow_mem hq 4)⟩
    rw [hLQ] at e2
    exact e2
  have hx2 : x ^ 2 = 1 := sq_eq_one_of_commute_sq h hl hlord hx hxl hxsq hx4
  have ht2 : t ^ 2 = q ^ 2 := by rw [← hxq, hcomm.mul_pow, hx2, one_mul]
  have ht2T : t ^ 2 ∈ T := pow_mem htT 2
  have : t ^ 2 ∈ T ⊓ Q := ⟨ht2T, ht2 ▸ pow_mem hq 2⟩
  rw [hTQ] at this
  have ht21 : t ^ 2 = 1 := this
  have := orderOf_dvd_of_pow_eq_one ht21
  rw [ht4] at this
  omega

end KeyLemma

end CFSG.OddStandard.AltStdBal
