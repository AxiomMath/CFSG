module

public import CFSG.GH74.GLS.C3.Layer1.Th2P64H

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutative_of_card_le_four {H : Subgroup G} (hH : IsPGroup 2 ↥H) (h4 : Nat.card ↥H ≤ 4) :
    ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hH
  have hn2 : n ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  interval_cases n
  · have : Nat.card ↥H = 1 := by simpa using hn
    have hs : Subsingleton ↥H := Finite.card_le_one_iff_subsingleton.1 this.le
    intro a ha b hb
    exact congrArg Subtype.val (Subsingleton.elim (⟨a, ha⟩ : ↥H) ⟨b, hb⟩ ▸ rfl : (⟨a, ha⟩ : ↥H) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩)
  · have h2 : Nat.card ↥H = 2 := by simpa using hn
    have hcy : IsCyclic ↥H := @isCyclic_of_prime_card _ _ 2 ⟨Nat.prime_two⟩ h2
    intro a ha b hb
    exact congrArg Subtype.val
      ((IsCyclic.isMulCommutative (α := ↥H)).is_comm.comm (⟨a, ha⟩ : ↥H) ⟨b, hb⟩)
  · have h4' : Nat.card ↥H = 2 ^ 2 := by simpa using hn
    have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) h4'
    intro a ha b hb
    exact congrArg Subtype.val (hc.is_comm.comm (⟨a, ha⟩ : ↥H) ⟨b, hb⟩)


structure D8Central (T P : Subgroup G) (z : G) : Prop where
  card8 : Nat.card ↥P = 8
  P_le : P ≤ T
  z_mem : z ∈ P
  z_ne : z ≠ 1
  z_sq : z * z = 1
  z_central : ∀ p ∈ P, p * z = z * p
  center_eq : ∀ w ∈ P, (∀ p ∈ P, p * w = w * p) → w = 1 ∨ w = z
  decomp : ∀ s ∈ T, ∃ π ∈ P, ∃ c ∈ T, (∀ g ∈ T, g * c = c * g) ∧ s = π * c

namespace D8Central

variable {T P : Subgroup G} {z : G} (h : D8Central T P z)

include h in
theorem commutator_P {π π' : G} (hπ : π ∈ P) (hπ' : π' ∈ P) : π * π' * π⁻¹ * π'⁻¹ = 1 ∨
    π * π' * π⁻¹ * π'⁻¹ = z := by
  have hc := Th2.Obs.commutator_mem_center_of_card_eight h.card8 ⟨π, hπ⟩ ⟨π', hπ'⟩
  have hmem : π * π' * π⁻¹ * π'⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem (P.mul_mem hπ hπ') (P.inv_mem hπ)) (P.inv_mem hπ')
  refine h.center_eq _ hmem (fun p hp => ?_)
  have := Subgroup.mem_center_iff.1 hc ⟨p, hp⟩
  have h2 := congrArg Subtype.val this
  exact h2

omit [Finite G] in
include h in
theorem z_central_T {g : G} (hg : g ∈ T) : g * z = z * g := by
  obtain ⟨π, hπ, c, hcT, hc, rfl⟩ := h.decomp g hg
  have hzT : z ∈ T := h.P_le h.z_mem
  calc π * c * z = π * (c * z) := by group
    _ = π * (z * c) := by rw [hc z hzT |>.symm]
    _ = (π * z) * c := by group
    _ = (z * π) * c := by rw [h.z_central π hπ]
    _ = z * (π * c) := by group

include h in
theorem conj_mem {b : G} (hb : b ∈ T) {s : G} (hs : s ∈ T) :
    s * b * s⁻¹ = b ∨ s * b * s⁻¹ = b * z := by
  obtain ⟨π, hπ, c, hcT, hc, rfl⟩ := h.decomp s hs
  obtain ⟨πb, hπb, cb, hcbT, hcb, rfl⟩ := h.decomp b hb
  have hπT : π ∈ T := h.P_le hπ
  have hπbT : πb ∈ T := h.P_le hπb
  have hbT' : πb * cb ∈ T := T.mul_mem hπbT hcbT
  have h1 : c * (πb * cb) * c⁻¹ = πb * cb := by
    have := hc (πb * cb) hbT'
    calc c * (πb * cb) * c⁻¹ = ((πb * cb) * c) * c⁻¹ := by rw [this]
      _ = πb * cb := by group
  have h2 : π * c * (πb * cb) * (π * c)⁻¹ = π * (πb * cb) * π⁻¹ := by
    calc π * c * (πb * cb) * (π * c)⁻¹ = π * (c * (πb * cb) * c⁻¹) * π⁻¹ := by group
      _ = π * (πb * cb) * π⁻¹ := by rw [h1]
  have h3 : π * (πb * cb) * π⁻¹ = (π * πb * π⁻¹ * πb⁻¹) * (πb * cb) := by
    have hcπ : cb * π⁻¹ = π⁻¹ * cb := by
      have := hcb π⁻¹ (T.inv_mem hπT)
      exact this.symm
    calc π * (πb * cb) * π⁻¹ = π * πb * (cb * π⁻¹) := by group
      _ = π * πb * (π⁻¹ * cb) := by rw [hcπ]
      _ = (π * πb * π⁻¹ * πb⁻¹) * (πb * cb) := by group
  rw [h2, h3]
  rcases h.commutator_P hπ hπb with hk | hk
  · left
    rw [hk, one_mul]
  · right
    rw [hk]
    have := h.z_central_T hbT'
    exact this.symm


omit [Finite G] in
theorem decomp_mul {π π' c c' : G} (hπ' : π' ∈ T) (hc : ∀ g ∈ T, g * c = c * g) :
    (π * c) * (π' * c') = (π * π') * (c * c') := by
  have h1 : c * π' = π' * c := (hc π' hπ').symm
  calc (π * c) * (π' * c') = π * (c * π') * c' := by group
    _ = π * (π' * c) * c' := by rw [h1]
    _ = (π * π') * (c * c') := by group

include h in
theorem card_le_two_mul_centralizer {b : G} (hb : b ∈ T) :
    Nat.card ↥T ≤ 2 * Nat.card ↥(T ⊓ centralizer ({b} : Set G)) := by
  classical
  have hz2 : z * z = 1 := h.z_sq
  by_cases hall : ∀ s ∈ T, s * b * s⁻¹ = b
  · have hle : T ≤ T ⊓ centralizer ({b} : Set G) := fun s hs =>
      ⟨hs, mem_centralizer_singleton_iff.2 (by
        have := hall s hs
        calc s * b = (s * b * s⁻¹) * s := by group
          _ = b * s := by rw [this])⟩
    have heq : T ⊓ centralizer ({b} : Set G) = T := le_antisymm inf_le_left hle
    rw [heq]
    omega
  · push Not at hall
    obtain ⟨s₀, hs₀T, hs₀⟩ := hall
    have hs₀z : s₀ * b * s₀⁻¹ = b * z := (h.conj_mem hb hs₀T).resolve_left hs₀
    have hzT : z ∈ T := h.P_le h.z_mem
    have hs₀b : s₀⁻¹ * b * s₀ = b * z := by
      have h1 : b = s₀⁻¹ * (b * z) * s₀ := by
        calc b = s₀⁻¹ * (s₀ * b * s₀⁻¹) * s₀ := by group
          _ = s₀⁻¹ * (b * z) * s₀ := by rw [hs₀z]
      have h2 : s₀⁻¹ * (b * z) * s₀ = (s₀⁻¹ * b * s₀) * z := by
        have hz := h.z_central_T (T.inv_mem hs₀T)
        calc s₀⁻¹ * (b * z) * s₀ = s₀⁻¹ * b * (z * s₀) := by group
          _ = s₀⁻¹ * b * (s₀ * z) := by rw [h.z_central_T hs₀T |>.symm]
          _ = (s₀⁻¹ * b * s₀) * z := by group
      rw [h2] at h1
      have h3 : s₀⁻¹ * b * s₀ = b * z⁻¹ := by
        calc s₀⁻¹ * b * s₀ = (s₀⁻¹ * b * s₀) * z * z⁻¹ := by group
          _ = b * z⁻¹ := by rw [← h1]
      rw [h3, inv_eq_of_mul_eq_one_right hz2]
    set C : Subgroup G := T ⊓ centralizer ({b} : Set G) with hC
    have hcen : ∀ s ∈ T, s * b * s⁻¹ = b → s ∈ C := fun s hs hsb =>
      ⟨hs, mem_centralizer_singleton_iff.2 (by
        calc s * b = (s * b * s⁻¹) * s := by group
          _ = b * s := by rw [hsb])⟩
    have hcen' : ∀ s ∈ T, ¬ s * b * s⁻¹ = b → s₀⁻¹ * s ∈ C := by
      intro s hs hsb
      have hsz : s * b * s⁻¹ = b * z := (h.conj_mem hb hs).resolve_left hsb
      refine ⟨T.mul_mem (T.inv_mem hs₀T) hs, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : (s₀⁻¹ * s) * b * (s₀⁻¹ * s)⁻¹ = b := by
        calc (s₀⁻¹ * s) * b * (s₀⁻¹ * s)⁻¹ = s₀⁻¹ * (s * b * s⁻¹) * s₀ := by group
          _ = s₀⁻¹ * (b * z) * s₀ := by rw [hsz]
          _ = (s₀⁻¹ * b * s₀) * z := by
            calc s₀⁻¹ * (b * z) * s₀ = s₀⁻¹ * b * (z * s₀) := by group
              _ = s₀⁻¹ * b * (s₀ * z) := by rw [h.z_central_T hs₀T |>.symm]
              _ = (s₀⁻¹ * b * s₀) * z := by group
          _ = b * z * z := by rw [hs₀b]
          _ = b := by rw [mul_assoc, hz2, mul_one]
      calc (s₀⁻¹ * s) * b = ((s₀⁻¹ * s) * b * (s₀⁻¹ * s)⁻¹) * (s₀⁻¹ * s) := by group
        _ = b * (s₀⁻¹ * s) := by rw [h1]
    let f : ↥T → Bool × ↥C := fun s =>
      if hs : (s : G) * b * (s : G)⁻¹ = b then (false, ⟨s, hcen s s.2 hs⟩)
      else (true, ⟨s₀⁻¹ * s, hcen' s s.2 hs⟩)
    have hf : Function.Injective f := by
      intro s s' hss'
      by_cases h1 : (s : G) * b * (s : G)⁻¹ = b <;> by_cases h2 : (s' : G) * b * (s' : G)⁻¹ = b
      · simp only [f, h1, h2, dite_true, Prod.mk.injEq, true_and] at hss'
        have := congrArg (fun z : ↥C => (z : G)) hss'
        exact Subtype.ext this
      · simp [f, h1, h2] at hss'
      · simp [f, h1, h2] at hss'
      · simp only [f, h1, h2, dite_false, Prod.mk.injEq, true_and] at hss'
        have := congrArg (fun z : ↥C => (z : G)) hss'
        exact Subtype.ext (mul_left_cancel this)
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    exact this

include h in
theorem commutative_centralizer {b : G} (hb : b ∈ T) (hnc : ∃ g ∈ T, g * b ≠ b * g) :
    ∀ u ∈ T ⊓ centralizer ({b} : Set G), ∀ v ∈ T ⊓ centralizer ({b} : Set G), u * v = v * u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨πb, hπb, cb, hcbT, hcb, rfl⟩ := h.decomp b hb
  have hπbT : πb ∈ T := h.P_le hπb
  have hnonc : ∃ p₀ ∈ P, p₀ * πb ≠ πb * p₀ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hgT, hg⟩ := hnc
    apply hg
    obtain ⟨π, hπ, c, hcT, hc, rfl⟩ := h.decomp g hgT
    have hπT : π ∈ T := h.P_le hπ
    have h1 : (π * c) * (πb * cb) = (π * πb) * (c * cb) := decomp_mul hπbT hc
    have h2 : (πb * cb) * (π * c) = (πb * π) * (cb * c) := decomp_mul hπT hcb
    rw [h1, h2, hcon π hπ, hc cb hcbT |>.symm]
  obtain ⟨p₀, hp₀P, hp₀⟩ := hnonc
  set H : Subgroup G := P ⊓ centralizer ({πb} : Set G) with hH
  have hP2 : IsPGroup 2 ↥P := IsPGroup.of_card (n := 3) (by rw [h.card8]; norm_num)
  have hH2 : IsPGroup 2 ↥H := hP2.to_inf_left
  have hHcard : Nat.card ↥H ≤ 4 := by
    have hdvd : Nat.card ↥H ∣ 8 := h.card8 ▸ Subgroup.card_dvd_of_le (inf_le_left : H ≤ P)
    have hlt : Nat.card ↥H < 8 := by
      by_contra hge
      push Not at hge
      have : H = P := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h.card8]; exact hge)
      have hp₀H : p₀ ∈ H := this ▸ hp₀P
      exact hp₀ (mem_centralizer_singleton_iff.1 hp₀H.2)
    generalize Nat.card ↥H = c at hdvd hlt ⊢
    interval_cases c <;> omega
  have hHcomm := commutative_of_card_le_four hH2 hHcard
  have hpart : ∀ u ∈ T ⊓ centralizer ({πb * cb} : Set G), ∃ π ∈ H, ∃ c ∈ T,
      (∀ g ∈ T, g * c = c * g) ∧ u = π * c := by
    intro u hu
    obtain ⟨π, hπ, c, hcT, hc, rfl⟩ := h.decomp u hu.1
    have hπT : π ∈ T := h.P_le hπ
    refine ⟨π, ⟨hπ, mem_centralizer_singleton_iff.2 ?_⟩, c, hcT, hc, rfl⟩
    have hcomm : (π * c) * (πb * cb) = (πb * cb) * (π * c) := mem_centralizer_singleton_iff.1 hu.2
    rw [decomp_mul hπbT hc, decomp_mul hπT hcb, hc cb hcbT |>.symm] at hcomm
    exact mul_right_cancel hcomm
  intro u hu v hv
  obtain ⟨πu, hπu, cu, hcuT, hcu, rfl⟩ := hpart u hu
  obtain ⟨πv, hπv, cv, hcvT, hcv, rfl⟩ := hpart v hv
  have hπuT : πu ∈ T := h.P_le hπu.1
  have hπvT : πv ∈ T := h.P_le hπv.1
  rw [decomp_mul hπvT hcu, decomp_mul hπuT hcv, hHcomm πu hπu πv hπv,
    hcu cv hcvT |>.symm]

end D8Central

theorem centralizes_of_no_involution_outside {T R Q : Subgroup G} (hQT : Q ≤ T) (hQR : Q ≤ R)
    (hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) (hQ4 : Nat.card ↥Q = 4)
    (hQel : CFSG.IsElementaryAbelian 2 ↥Q) {x : G} (hxQ : x ∈ Q) (hx1 : x ≠ 1)
    (hxc : ∀ s ∈ T, s * x = x * s) (hinv : ∀ s ∈ T, orderOf s = 2 → s ∈ R) {t : G} (htT : t ∈ T)
    (htR : t ∉ R) (ht2 : t * t ∈ Q) : ∀ q ∈ Q, t * q = q * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQc, hQsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hQel
  by_contra hcon
  push Not at hcon
  obtain ⟨q, hqQ, hq⟩ := hcon
  have hxo : orderOf x = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hQsq x hxQ) hx1
  set C : Subgroup G := Q ⊓ centralizer ({t} : Set G) with hC
  have hxC : x ∈ C := ⟨hxQ, mem_centralizer_singleton_iff.2 (hxc t htT).symm⟩
  have hqC : q ∉ C := fun h => hq (by
    have := mem_centralizer_singleton_iff.1 h.2
    exact this.symm)
  have hCQ : C ≤ Q := inf_le_left
  have hC2 : Nat.card ↥C = 2 := by
    have hdvd : Nat.card ↥C ∣ 4 := hQ4 ▸ Subgroup.card_dvd_of_le hCQ
    have hlt : Nat.card ↥C < 4 := by
      by_contra hge
      push Not at hge
      have : C = Q := Subgroup.eq_of_le_of_card_ge hCQ (by rw [hQ4]; exact hge)
      exact hqC (this ▸ hqQ)
    have h2 : Nat.card ↥(zpowers x) ∣ Nat.card ↥C :=
      Subgroup.card_dvd_of_le ((zpowers_le).2 hxC)
    rw [Nat.card_zpowers, hxo] at h2
    have hpos : 0 < Nat.card ↥C := Nat.card_pos
    omega
  have hCx : C = zpowers x := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 hxC) ?_
    rw [hC2, Nat.card_zpowers, hxo]
  have hCmem : ∀ g ∈ C, g = 1 ∨ g = x := fun g hg => mem_zpowers_two hxo (hCx ▸ hg)
  set q' : G := t * q * t⁻¹ with hq'
  have hq'Q : q' ∈ Q := hQn t htT q hqQ
  have hcQ : q' * q ∈ Q := Q.mul_mem hq'Q hqQ
  have hat : t * t ∈ Q := ht2
  have haq : (t * t) * q = q * (t * t) := hQc _ hat q hqQ
  have htq' : t * q' * t⁻¹ = q := by
    have h1 : t * q' * t⁻¹ = (t * t) * q * (t * t)⁻¹ := by rw [hq']; group
    rw [h1, haq]
    group
  have hcC : q' * q ∈ C := by
    refine ⟨hcQ, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : t * (q' * q) * t⁻¹ = (t * q' * t⁻¹) * (t * q * t⁻¹) := by group
    rw [htq'] at h1
    have h2 : (q' * q) * t = t * (q' * q) := by
      have h3 : q * q' = q' * q := hQc q hqQ q' hq'Q
      have : t * (q' * q) = (q * q') * t := by
        calc t * (q' * q) = (t * (q' * q) * t⁻¹) * t := by group
          _ = (q * (t * q * t⁻¹)) * t := by rw [h1]
          _ = (q * q') * t := rfl
      rw [this, h3]
    exact h2
  have hc1 : q' * q ≠ 1 := by
    intro h1
    apply hq
    have h2 : q' = q⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : q⁻¹ = q := inv_eq_of_mul_eq_one_right (hQsq q hqQ)
    have h4 : t * q * t⁻¹ = q := by rw [← hq', h2, h3]
    calc t * q = (t * q * t⁻¹) * t := by group
      _ = q * t := by rw [h4]
  have hcx : q' * q = x := (hCmem _ hcC).resolve_left hc1
  have haC : t * t ∈ C := ⟨hat, mem_centralizer_singleton_iff.2 (by group)⟩
  have hat1 : t * t ≠ 1 := by
    intro h1
    have ht1 : t ≠ 1 := fun h => htR (h ▸ one_mem R)
    exact htR (hinv t htT (orderOf_eq_prime (by rw [sq]; exact h1) ht1))
  have hax : t * t = x := (hCmem _ haC).resolve_left hat1
  have htqsq : (t * q) * (t * q) = 1 := by
    have h1 : (t * q) * (t * q) = q' * (t * t) * q := by rw [hq']; group
    rw [h1, hax]
    have h2 : q' = x * q := by
      have : q' = (q' * q) * q⁻¹ := by group
      rw [this, hcx, inv_eq_of_mul_eq_one_right (hQsq q hqQ)]
    rw [h2]
    have hxq : x * q = q * x := hQc x hxQ q hqQ
    calc x * q * x * q = x * (q * x) * q := by group
      _ = x * (x * q) * q := by rw [← hxq]
      _ = (x * x) * (q * q) := by group
      _ = 1 := by rw [hQsq x hxQ, hQsq q hqQ, one_mul]
  have htq1 : t * q ≠ 1 := by
    intro h1
    apply htR
    have : t = q⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact R.inv_mem (hQR hqQ)
  have htqT : t * q ∈ T := T.mul_mem htT (hQT hqQ)
  have hR2 := hinv _ htqT (orderOf_eq_prime (by rw [sq]; exact htqsq) htq1)
  apply htR
  have : t = (t * q) * q⁻¹ := by group
  rw [this]
  exact R.mul_mem hR2 (R.inv_mem (hQR hqQ))

end CFSG.GH74.GLS.Th2.Obs

