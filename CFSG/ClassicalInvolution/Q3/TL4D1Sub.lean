module

public import CFSG.ClassicalInvolution.Q3.TL3T8

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_of_normal_subgroupOf {H K : Subgroup G} (hHK : H ≤ K)
    (hN : (H.subgroupOf K).Normal) {k : G} (hk : k ∈ K) {h : G} (hh : h ∈ H) :
    k * h * k⁻¹ ∈ H :=
  (Subgroup.normal_subgroupOf_iff hHK).mp hN h k hh hk

omit [Finite G] in
theorem le_pCore_of_isSubnormal {p : ℕ} {W : Subgroup G} (hW : W.IsSubnormal)
    {P : Subgroup G} (hPW : P ≤ W) (hPn : ∀ w ∈ W, ∀ x ∈ P, w * x * w⁻¹ ∈ P)
    (hP : IsPGroup p P) : P ≤ pCore p G := by
  induction hW generalizing P with
  | top =>
    have : P.Normal := ⟨fun x hx g => hPn g (Subgroup.mem_top g) x hx⟩
    exact le_sSup ⟨this, hP⟩
  | step H K hHK _ hN ih =>
    set C : Subgroup G := (pCore p ↥H).map H.subtype with hC
    have hPC : P ≤ C := by
      intro x hx
      have hn : (P.subgroupOf H).Normal :=
        ⟨fun a ha g => Subgroup.mem_subgroupOf.mpr (hPn g g.2 a ha)⟩
      have hle : P.subgroupOf H ≤ pCore p ↥H := le_sSup ⟨hn, hP.comap_subtype⟩
      exact ⟨⟨x, hPW hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    refine hPC.trans (ih ((Subgroup.map_subtype_le _).trans hHK) ?_ (pCore_isPGroup.map _))
    rintro k hk _ ⟨c, hc, rfl⟩
    let e : ↥H ≃* ↥H :=
      { toFun := fun h => ⟨k * h * k⁻¹, conj_mem_of_normal_subgroupOf hHK hN hk h.2⟩
        invFun := fun h => ⟨k⁻¹ * h * k, by
          simpa using conj_mem_of_normal_subgroupOf hHK hN (K.inv_mem hk) h.2⟩
        left_inv := fun h => Subtype.ext (by simp [mul_assoc])
        right_inv := fun h => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    have hmem : e c ∈ pCore p ↥H := by
      rw [← pCore_map_iso p e]
      exact ⟨c, hc, rfl⟩
    exact ⟨e c, hmem, rfl⟩

omit [Finite G] in
theorem isSubnormal_open {W : Subgroup G} (hW : W.IsSubnormal) : CFSG.Open.IsSubnormal W ⊤ := by
  induction hW with
  | top => exact CFSG.Open.IsSubnormal.refl _
  | step H K hHK _ hN ih => exact CFSG.Open.IsSubnormal.step hHK hN ih

theorem oddCore_eq_bot_of_isSubnormal (hO : classicalInvolutionOddCore G = ⊥) {W : Subgroup G}
    (hW : W.IsSubnormal) : classicalInvolutionOddCore ↥W = ⊥ :=
  CFSG.ComponentClassification.OddCore.subnormal_corefree hO W (isSubnormal_open hW)

omit [Finite G] in
theorem exists_pow_mul_eq {H : Subgroup G} {q : G}
    (hq : ∀ n : ℕ, ∀ x ∈ H, q ^ n * x * (q ^ n)⁻¹ ∈ H)
    {h : G} (hh : h ∈ H) (n : ℕ) : ∃ h' ∈ H, (h * q) ^ n = h' * q ^ n := by
  induction n with
  | zero => exact ⟨1, H.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨h', hh', he⟩ := ih
    refine ⟨h' * (q ^ n * h * (q ^ n)⁻¹), H.mul_mem hh' (hq n h hh), ?_⟩
    rw [pow_succ, he, pow_succ]
    group

omit [Finite G] in
theorem mem_of_pow_odd_mem {H : Subgroup G} {q : G} (hq : IsPGroup 2 (Subgroup.zpowers q))
    {o : ℕ} (ho : Odd o) (hqo : q ^ o ∈ H) : q ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hq) ⟨q, Subgroup.mem_zpowers q⟩
  have hord : orderOf q = 2 ^ a :=
    (Subgroup.orderOf_coe (⟨q, Subgroup.mem_zpowers q⟩ : Subgroup.zpowers q)).trans ha
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · rw [h0, pow_zero, orderOf_eq_one_iff] at hord
    rw [hord]
    exact H.one_mem
  · have hcop : Nat.Coprime o (2 ^ a) := (Nat.coprime_two_right.mpr ho).pow_right a
    have h1 : 1 < 2 ^ a := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hpos)
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    have : q = (q ^ o) ^ m := by
      rw [← pow_mul, ← pow_mod_orderOf, hord, hm, pow_one]
    rw [this]
    exact H.pow_mem hqo m

omit [Finite G] in
theorem mem_of_odd_of_mem_sup {W Q : Subgroup G} (hW : W.IsSubnormal) (hQn : Q.Normal)
    (hQ2 : IsPGroup 2 Q) {g : G} (hg : g ∈ W ⊔ Q) (hodd : Odd (orderOf g)) : g ∈ W := by
  have : Q.Normal := hQn
  induction hW generalizing g with
  | top => exact Subgroup.mem_top g
  | step H K hHK _ hN ih =>
    have hgK : g ∈ K := ih (sup_le_sup_right hHK Q hg) hodd
    obtain ⟨h, hh, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    have hqK : q ∈ K := by
      have : q = h⁻¹ * (h * q) := by group
      rw [this]
      exact K.mul_mem (K.inv_mem (hHK hh)) hgK
    have hqn : ∀ n : ℕ, ∀ x ∈ H, q ^ n * x * (q ^ n)⁻¹ ∈ H := fun n x hx =>
      conj_mem_of_normal_subgroupOf hHK hN (K.pow_mem hqK n) hx
    obtain ⟨h', hh', he⟩ := exists_pow_mul_eq hqn hh (orderOf (h * q))
    rw [pow_orderOf_eq_one] at he
    have hqo : q ^ orderOf (h * q) ∈ H := by
      rw [eq_inv_of_mul_eq_one_right he.symm]
      exact H.inv_mem hh'
    have hq2 : IsPGroup 2 (Subgroup.zpowers q) :=
      hQ2.to_le (Subgroup.zpowers_le.mpr hq)
    exact H.mul_mem hh (mem_of_pow_odd_mem hq2 hodd hqo)

theorem exists_subnormal_closure (J : Subgroup G) :
    ∃ X : Subgroup G, J ≤ X ∧ X.IsSubnormal ∧
      pSpan {L | ∃ x ∈ X, conjSub x J = L} = X := by
  classical
  have hex : ∃ n : ℕ, ∃ X : Subgroup G, J ≤ X ∧ X.IsSubnormal ∧ Nat.card X = n :=
    ⟨_, ⊤, le_top, Subgroup.IsSubnormal.top, rfl⟩
  obtain ⟨X, hJX, hX, hXn⟩ := Nat.find_spec hex
  set P : Set (Subgroup G) := {L | ∃ x ∈ X, conjSub x J = L} with hP
  have hNX : pSpan P ≤ X := pSpan_le fun L ⟨x, hx, hL⟩ => by
    rw [← hL]
    intro y hy
    rw [mem_conjSub_iff] at hy
    have : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [this]
    exact X.mul_mem (X.mul_mem hx (hJX hy)) (X.inv_mem hx)
  have hJN : J ≤ pSpan P := le_pSpan ⟨1, X.one_mem, conjSub_one J⟩
  have hinv : ∀ x ∈ X, pSpan P ≤ conjSub x⁻¹ (pSpan P) := by
    intro x hx
    refine pSpan_le fun L ⟨x', hx', hL⟩ => ?_
    have hmem : conjSub (x * x') J ∈ P := ⟨x * x', X.mul_mem hx hx', rfl⟩
    have h1 := conjSub_mono (n := x⁻¹) (le_pSpan hmem)
    rwa [conjSub_mul, conjSub_inv_conjSub, hL] at h1
  have hNn : ((pSpan P).subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNX]
    intro y k hy hk
    have h1 := hinv k hk hy
    rw [mem_conjSub_iff, inv_inv] at h1
    exact h1
  have hNs : (pSpan P).IsSubnormal := Subgroup.IsSubnormal.step _ X hNX hX hNn
  have hmin := Nat.find_min' hex ⟨pSpan P, hJN, hNs, rfl⟩
  refine ⟨X, hJX, hX, Subgroup.eq_of_le_of_card_ge hNX ?_⟩
  rw [hXn]
  exact hmin

end CFSG.ClassicalInvolution.Q3.TL4
