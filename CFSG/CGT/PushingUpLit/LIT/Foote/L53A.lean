module

public import CFSG.CGT.PushingUpLit.LIT.Foote.Orbit

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_mul_central {a b s t : G} (hsb : s * b = b * s) (hst : s * t = t * s)
    (hta : t * a = a * t) : ⁅a * s, b * t⁆ = ⁅a, b⁆ := by
  have h1 : ⁅s, b * t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (by
    calc s * (b * t) = (s * b) * t := by group
      _ = (b * s) * t := by rw [hsb]
      _ = b * (s * t) := by group
      _ = b * (t * s) := by rw [hst]
      _ = (b * t) * s := by group)
  have h2 : ⁅a, t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hta.symm
  rw [commutatorElement_mul_left_eq_conj_mul, h1, commutatorElement_mul_right_eq_mul_conj, h2]
  simp

omit [Finite G] in
theorem comm4 {a b c d : G} (hab : a * b = b * a) (hac : a * c = c * a) (had : a * d = d * a)
    (hbc : b * c = c * b) (hbd : b * d = d * b) (hcd : c * d = d * c) :
    (a * b) * (a * c) * (a * d) = (a * a) * (a * b * c * d) := by
  have hk : ∀ x ∈ ({a, b, c, d} : Set G), ∀ y ∈ ({a, b, c, d} : Set G), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | rfl | assumption | exact (by assumption : _ = _).symm
  have : IsMulCommutative (Subgroup.closure ({a, b, c, d} : Set G)) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hk x hx y hy
  let a' : Subgroup.closure ({a, b, c, d} : Set G) := ⟨a, Subgroup.subset_closure (by simp)⟩
  let b' : Subgroup.closure ({a, b, c, d} : Set G) := ⟨b, Subgroup.subset_closure (by simp)⟩
  let c' : Subgroup.closure ({a, b, c, d} : Set G) := ⟨c, Subgroup.subset_closure (by simp)⟩
  let d' : Subgroup.closure ({a, b, c, d} : Set G) := ⟨d, Subgroup.subset_closure (by simp)⟩
  have h : (a' * b') * (a' * c') * (a' * d') = (a' * a') * (a' * b' * c' * d') := by ac_rfl
  exact congrArg Subtype.val h

omit [Finite G] in
theorem mem_centralizer_of_conj_eq {u p : G} (h : u⁻¹ * p * u = p) :
    p ∈ Subgroup.centralizer ({u} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc p * u = u * (u⁻¹ * p * u) := by group
    _ = u * p := by rw [h]

omit [Finite G] in
theorem sq_mem_of_swaps {Ω : Subgroup G} {a b c d u₁ u₂ u₃ : G}
    (hab : a * b = b * a) (hac : a * c = c * a) (had : a * d = d * a)
    (hbc : b * c = c * b) (hbd : b * d = d * b) (hcd : c * d = d * c)
    (h1a : u₁⁻¹ * a * u₁ = b) (h1b : u₁⁻¹ * b * u₁ = a) (h1c : u₁⁻¹ * c * u₁ = d)
    (h1d : u₁⁻¹ * d * u₁ = c) (h2a : u₂⁻¹ * a * u₂ = c) (h2c : u₂⁻¹ * c * u₂ = a)
    (h3a : u₃⁻¹ * a * u₃ = d) (h3d : u₃⁻¹ * d * u₃ = a)
    (hC1 : Subgroup.centralizer ({u₁} : Set G) ≤ Ω) (hC2 : Subgroup.centralizer ({u₂} : Set G) ≤ Ω)
    (hC3 : Subgroup.centralizer ({u₃} : Set G) ≤ Ω) : a * a ∈ Ω := by
  have hp : a * b ∈ Ω := hC1 (mem_centralizer_of_conj_eq (by
    rw [show u₁⁻¹ * (a * b) * u₁ = (u₁⁻¹ * a * u₁) * (u₁⁻¹ * b * u₁) by group, h1a, h1b, hab]))
  have hq : a * c ∈ Ω := hC2 (mem_centralizer_of_conj_eq (by
    rw [show u₂⁻¹ * (a * c) * u₂ = (u₂⁻¹ * a * u₂) * (u₂⁻¹ * c * u₂) by group, h2a, h2c, hac]))
  have hr : a * d ∈ Ω := hC3 (mem_centralizer_of_conj_eq (by
    rw [show u₃⁻¹ * (a * d) * u₃ = (u₃⁻¹ * a * u₃) * (u₃⁻¹ * d * u₃) by group, h3a, h3d, had]))
  have hN : a * b * c * d ∈ Ω := hC1 (mem_centralizer_of_conj_eq (by
    rw [show u₁⁻¹ * (a * b * c * d) * u₁ = (u₁⁻¹ * a * u₁) * (u₁⁻¹ * b * u₁) *
      (u₁⁻¹ * c * u₁) * (u₁⁻¹ * d * u₁) by group, h1a, h1b, h1c, h1d]
    calc b * a * d * c = (b * a) * (d * c) := by group
      _ = (a * b) * (c * d) := by rw [← hab, ← hcd]
      _ = a * b * c * d := by group))
  have hmul := comm4 hab hac had hbc hbd hcd
  have h : a * a = (a * b) * (a * c) * (a * d) * (a * b * c * d)⁻¹ := by
    rw [hmul]
    group
  rw [h]
  exact Ω.mul_mem (Ω.mul_mem (Ω.mul_mem hp hq) hr) (Ω.inv_mem hN)

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

omit [Finite G] c in
theorem rightConjugate_ne_of_ne {W : Subgroup G}
    (hmove : ∀ w ∈ W, w ≠ 1 → rightConjugate J w ≠ J) {a b : G} (ha : a ∈ W) (hb : b ∈ W)
    (hab : a ≠ b) : rightConjugate J a ≠ rightConjugate J b := by
  intro h
  rw [rightConjugate_eq_iff] at h
  have hba : b * a⁻¹ ∈ W := W.mul_mem hb (W.inv_mem ha)
  have hne : b * a⁻¹ ≠ 1 := fun h1 => hab (by simpa using (mul_inv_eq_one.1 h1).symm)
  exact hmove _ hba hne ((rightConjugate_eq_self_iff J _).2 h)

theorem le_of_forall_move {W Ω : Subgroup G} (hWM : W ≤ M)
    (hW2 : ∀ w ∈ W, w * w = 1) (hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w)
    {u v : G} (hu : u ∈ W) (hv : v ∈ W) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hC : ∀ w ∈ W, w ≠ 1 → Subgroup.centralizer ({w} : Set G) ≤ Ω)
    (hmove : ∀ w ∈ W, w ≠ 1 → rightConjugate J w ≠ J) : J ≤ Ω := by
  have hinv : ∀ w ∈ W, w⁻¹ = w := fun w hw => inv_eq_of_mul_eq_one_right (hW2 w hw)
  have hw : u * v ∈ W := W.mul_mem hu hv
  have hw1 : u * v ≠ 1 := fun h => huv (by
    have := mul_eq_one_iff_eq_inv.1 h
    rwa [hinv v hv] at this)
  have h1W : (1 : G) ∈ W := W.one_mem
  have huv' : u * v = v * u := hWc u hu v hv
  have hu2 := hW2 u hu
  have hv2 := hW2 v hv
  have hw2 : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [← huv']
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu2, hv2, one_mul]
  have hodd : ∀ x ∈ J, Odd (orderOf x) → x ∈ Ω := by
    intro x hx hxo
    have key : ∀ {a a' : G}, a ∈ W → a' ∈ W → a ≠ a' → ∀ (y y' : G), y ∈ J → y' ∈ J →
        (a'⁻¹ * y' * a') * (a⁻¹ * y * a) = (a⁻¹ * y * a) * (a'⁻¹ * y' * a') :=
      fun ha ha' haa' _ _ hy hy' => c.commute_conj_elems (hWM ha) (hWM ha')
        (rightConjugate_ne_of_ne hmove ha ha' haa') hy hy'
    have hxb : (u⁻¹ * x * u) * x = x * (u⁻¹ * x * u) := by
      simpa using key h1W hu (Ne.symm hu1) x x hx hx
    have hxc : (v⁻¹ * x * v) * x = x * (v⁻¹ * x * v) := by
      simpa using key h1W hv (Ne.symm hv1) x x hx hx
    have hxd : ((u * v)⁻¹ * x * (u * v)) * x = x * ((u * v)⁻¹ * x * (u * v)) := by
      simpa using key h1W hw (Ne.symm hw1) x x hx hx
    have hbc := key hu hv huv x x hx hx
    have hbd := key hu hw (fun h => hv1 (by
      have h' : u * 1 = u * v := by rw [mul_one]; exact h
      exact (mul_left_cancel h').symm)) x x hx hx
    have hcd := key hv hw (fun h => hu1 (by
      have h' : 1 * v = u * v := by rw [one_mul]; exact h
      exact (mul_right_cancel h').symm)) x x hx hx
    have cj : ∀ w w' y : G, w⁻¹ * (w'⁻¹ * y * w') * w = (w' * w)⁻¹ * y * (w' * w) := by
      intro w w' y
      group
    have cj1 : ∀ w y : G, w * w = 1 → w⁻¹ * (w⁻¹ * y * w) * w = y := by
      intro w y h
      rw [cj, h]
      simp
    have e1 : (u * v) * u = v := by
      calc (u * v) * u = (v * u) * u := by rw [huv']
        _ = v * (u * u) := by group
        _ = v := by rw [hu2, mul_one]
    have hvu : v * u = u * v := huv'.symm
    have hxx := sq_mem_of_swaps (Ω := Ω) (a := x) (b := u⁻¹ * x * u) (c := v⁻¹ * x * v)
      (d := (u * v)⁻¹ * x * (u * v)) (u₁ := u) (u₂ := v) (u₃ := u * v)
      hxb.symm hxc.symm hxd.symm hbc.symm hbd.symm hcd.symm
      rfl (cj1 u x hu2) (by rw [cj, hvu]) (by rw [cj, e1])
      rfl (cj1 v x hv2) rfl (cj1 (u * v) x hw2)
      (hC u hu hu1) (hC v hv hv1) (hC _ hw hw1)
    obtain ⟨k, hk⟩ := hxo
    have hxpow : (x * x) ^ (k + 1) = x := by
      calc (x * x) ^ (k + 1) = x ^ (2 * (k + 1)) := by rw [← pow_two, ← pow_mul]
        _ = x ^ (orderOf x + 1) := by rw [hk]; ring_nf
        _ = x := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
    rw [← hxpow]
    exact Ω.pow_mem hxx _
  have hJ := c.block
  calc J = CFSG.Quasithin.oTwoUpper J := eq_oTwoUpper_of_short hJ.short
    _ ≤ Ω := by
      unfold CFSG.Quasithin.oTwoUpper
      exact (Subgroup.closure_le Ω).2 fun x hx => hodd x hx.1 hx.2

theorem commute_conj_x {x : G} (hxM : x ∈ M) (hxne : rightConjugate J x ≠ J) :
    ∀ a ∈ J, ∀ b ∈ J, a * (x⁻¹ * b * x) = (x⁻¹ * b * x) * a := by
  intro a ha b hb
  have hcm := c.commutator_conj_eq_bot hxM hxne
  have hb' : x⁻¹ * b * x ∈ rightConjugate J x := by
    rw [mem_rightConjugate_iff]
    have e : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
    rw [e]
    exact hb
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcm ha
  exact (Subgroup.mem_centralizer_iff.1 this _ hb').symm

end CE

theorem exists_two_ne_one {W : Subgroup G} (h : 2 < Nat.card W) :
    ∃ u ∈ W, ∃ v ∈ W, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  have := Fintype.ofFinite W
  have h' : 2 < Fintype.card W := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h'
  by_cases ha : (a : G) = 1
  · refine ⟨b, b.2, c, c.2, fun h1 => hab (Subtype.ext (by rw [ha, h1])),
      fun h1 => hac (Subtype.ext (by rw [ha, h1])), fun h1 => hbc (Subtype.ext h1)⟩
  · by_cases hb : (b : G) = 1
    · exact ⟨a, a.2, c, c.2, ha, fun h1 => hbc (Subtype.ext (by rw [hb, h1])),
        fun h1 => hac (Subtype.ext h1)⟩
    · exact ⟨a, a.2, b, b.2, ha, hb, fun h1 => hab (Subtype.ext h1)⟩

end CFSG.CGT.PushingUpLit.LIT.Foote
