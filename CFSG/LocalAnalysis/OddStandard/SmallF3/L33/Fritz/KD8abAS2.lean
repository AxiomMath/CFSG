module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abAS

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab
open CFSG.ComponentClassification.HSFLit.KD8ab

open Sec8

variable {X : Type} [Group X] {t : X} {L : Subgroup X}

namespace SPkg

section Group

variable {A : SDData t L} (P : SPkg A)

theorem fix_mul_z {g y : X} (hz : g * P.z * g⁻¹ = P.z) (h : g * y * g⁻¹ = y) :
    g * (P.z * y) * g⁻¹ = P.z * y := by
  rw [show g * (P.z * y) * g⁻¹ = (g * P.z * g⁻¹) * (g * y * g⁻¹) by group, hz, h]

theorem flip_mul_z {g y : X} (hz : g * P.z * g⁻¹ = P.z) (h : g * y * g⁻¹ = P.z * y) :
    g * (P.z * y) * g⁻¹ = y := by
  rw [show g * (P.z * y) * g⁻¹ = (g * P.z * g⁻¹) * (g * y * g⁻¹) by group, hz, h, ← mul_assoc,
    P.zz, one_mul]

theorem inv_fix {g y : X} (h : g * y * g⁻¹ = y) : g⁻¹ * y * g = y := by
  calc g⁻¹ * y * g = g⁻¹ * (g * y * g⁻¹) * g := by rw [h]
    _ = y := by group

theorem inv_flip {g y : X} (hz : g * P.z * g⁻¹ = P.z) (h : g * y * g⁻¹ = P.z * y) :
    g⁻¹ * y * g = P.z * y := by
  have h1 := P.flip_mul_z hz h
  calc g⁻¹ * y * g = g⁻¹ * (g * (P.z * y) * g⁻¹) * g := by rw [h1]
    _ = P.z * y := by group

theorem conj_flip {a x y : X} (hy : ∀ g ∈ P.T₂, g * y * g⁻¹ = y ∨ g * y * g⁻¹ = P.z * y)
    (ha : a ∈ P.T₂) (hxz : x * P.z * x⁻¹ = P.z) (hx : x * y * x⁻¹ = P.z * y) :
    (a * x * a⁻¹) * y * (a * x * a⁻¹)⁻¹ = P.z * y := by
  have haz := P.conj_z ha
  have e : (a * x * a⁻¹) * y * (a * x * a⁻¹)⁻¹ = a * (x * (a⁻¹ * y * a) * x⁻¹) * a⁻¹ := by
    group
  rcases hy a ha with h | h
  · rw [e, inv_fix h, hx, P.fix_mul_z haz h]
  · rw [e, P.inv_flip haz h, P.flip_mul_z hxz hx, h]

theorem zk_ne_k : P.z * P.k ≠ P.k := fun h => P.z_ne (mul_eq_right.mp h)

theorem zw_ne_w : P.z * P.w ≠ P.w := fun h => P.z_ne (mul_eq_right.mp h)

theorem t_flip_w_z : t * P.z * t⁻¹ = P.z := P.conj_z P.t_mem

theorem flip_kw {g : X} (hk : g * P.k * g⁻¹ = P.z * P.k)
    (hw : g * P.w * g⁻¹ = P.z * P.w) : g * (P.k * P.w) * g⁻¹ = P.k * P.w := by
  rw [show g * (P.k * P.w) * g⁻¹ = (g * P.k * g⁻¹) * (g * P.w * g⁻¹) by group, hk, hw,
    show P.z * P.k * (P.z * P.w) = (P.z * P.z) * (P.k * P.w) by
      rw [mul_assoc, ← mul_assoc P.k, ← P.zk_comm]; group, P.zz, one_mul]

theorem kw_ne_w : P.k * P.w ≠ P.w := fun h => P.k_ne₁ (mul_eq_right.mp h)

theorem zkw_ne_w : P.z * P.k * P.w ≠ P.w := fun h =>
  P.k_ne_z ((inv_eq_of_mul_eq_one_right (mul_eq_right.mp h)).symm.trans P.z_inv)

theorem kw_ne_zw : P.k * P.w ≠ P.z * P.w := fun h => P.k_ne_z (mul_right_cancel h)

theorem zkw_ne_zw : P.z * P.k * P.w ≠ P.z * P.w := fun h => P.k_ne₁ (by
  have h1 := mul_right_cancel h
  rwa [mul_eq_left] at h1)

theorem k_ne_zk : P.k ≠ P.z * P.k := fun h => P.zk_ne_k h.symm

theorem w_ne_zw : P.w ≠ P.z * P.w := fun h => P.zw_ne_w h.symm

end Group

variable [Finite X] {A : SDData t L} (P : SPkg A)

structure SEl (P : SPkg A) where
  s : X
  Q : Subgroup X
  hQ : IsPGroup 2 Q
  hTQ : P.T₂ ≤ Q
  hsQ : s ∈ Q
  hN : s ∈ normalizer (P.T₂ : Set X)
  hsT : s ∉ P.T₂
  hs2 : s * s ∈ P.T₂

theorem nonempty_SEl (hmax : ¬ ∀ R : Subgroup X, IsPGroup 2 R → P.T₂ ≤ R → R = P.T₂) :
    Nonempty P.SEl := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  push Not at hmax
  obtain ⟨Q, hQ, hle, hne⟩ := hmax
  obtain ⟨h, hhQ, hhN, hhP⟩ : ∃ h ∈ Q, h ∈ normalizer (P.T₂ : Set X) ∧ h ∉ P.T₂ := by
    set I := P.T₂.subgroupOf Q with hI
    have hIne : I ≠ ⊤ := by
      intro htop
      apply hne
      refine le_antisymm (fun x hx => ?_) hle
      have : (⟨x, hx⟩ : Q) ∈ I := by rw [htop]; trivial
      exact this
    have hnil : Group.IsNilpotent Q := hQ.isNilpotent
    have hlt : I < normalizer (I : Set Q) :=
      Group.normalizerCondition_of_isNilpotent I (lt_of_le_of_ne le_top hIne)
    obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
    refine ⟨x, x.2, ?_, fun h => hxI h⟩
    have hxsub : x ∈ (normalizer (P.T₂ : Set X)).subgroupOf Q := by
      rw [subgroupOf_normalizer_eq hle]
      exact hxN
    exact mem_subgroupOf.mp hxsub
  obtain ⟨a, ha⟩ := hQ ⟨h, hhQ⟩
  have ha' : h ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  classical
  have hex : ∃ n : ℕ, h ^ 2 ^ n ∈ P.T₂ := ⟨a, by rw [ha']; exact one_mem _⟩
  set n := Nat.find hex with hn
  have hnT : h ^ 2 ^ n ∈ P.T₂ := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hnT
    exact hhP hnT
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hmT : h ^ 2 ^ m ∉ P.T₂ := Nat.find_min hex (by omega)
  refine ⟨⟨h ^ 2 ^ m, Q, hQ, hle, pow_mem hhQ _, pow_mem hhN _, hmT, ?_⟩⟩
  rw [← pow_add, ← two_mul, ← pow_succ', show m + 1 = n by omega]
  exact hnT

namespace SEl

variable {P} (E : P.SEl)

omit [Finite X] in
theorem s_inv_mem_N : E.s⁻¹ ∈ normalizer (P.T₂ : Set X) := inv_mem E.hN

omit [Finite X] in
theorem conj_mem {g : X} (hg : g ∈ P.T₂) : E.s * g * E.s⁻¹ ∈ P.T₂ :=
  Sec7.conj_mem_of_mem_normalizer E.hN hg

omit [Finite X] in
theorem conj_inv_mem {g : X} (hg : g ∈ P.T₂) : E.s⁻¹ * g * E.s ∈ P.T₂ := by
  have := Sec7.conj_mem_of_mem_normalizer E.s_inv_mem_N hg
  rwa [inv_inv] at this

omit [Finite X] in
theorem s_z : E.s * P.z * E.s⁻¹ = P.z := by
  have hc : ∀ h ∈ P.T₂, E.s * P.z * E.s⁻¹ * h = h * (E.s * P.z * E.s⁻¹) := by
    intro h hh
    have h1 := P.z_central _ (E.conj_inv_mem hh)
    calc E.s * P.z * E.s⁻¹ * h = E.s * (P.z * (E.s⁻¹ * h * E.s)) * E.s⁻¹ := by group
      _ = E.s * ((E.s⁻¹ * h * E.s) * P.z) * E.s⁻¹ := by rw [h1]
      _ = h * (E.s * P.z * E.s⁻¹) := by group
  rcases P.center _ (E.conj_mem P.z_mem) hc with h | h
  · exfalso; apply P.z_ne
    calc P.z = E.s⁻¹ * (E.s * P.z * E.s⁻¹) * E.s := by group
      _ = 1 := by rw [h]; group
  · exact h

@[expose] noncomputable def x : X := E.s * t * E.s⁻¹

omit [Finite X] in
theorem x_mem : E.x ∈ P.T₂ := E.conj_mem P.t_mem

omit [Finite X] in
theorem x_z : E.x * P.z * E.x⁻¹ = P.z := P.conj_z E.x_mem

theorem x_flip : E.x * P.k * E.x⁻¹ = P.z * P.k ∧ E.x * P.w * E.x⁻¹ = P.z * P.w := by
  rcases P.fus _ E.x_mem ⟨E.s, rfl⟩ with ⟨g, hg, hgx⟩ | h
  · exfalso
    apply E.hsT
    have hc : (g⁻¹ * E.s) * t = t * (g⁻¹ * E.s) := by
      have h1 : g⁻¹ * E.s * t * (g⁻¹ * E.s)⁻¹ = t := by
        rw [show g⁻¹ * E.s * t * (g⁻¹ * E.s)⁻¹ = g⁻¹ * (E.s * t * E.s⁻¹) * g by group]
        change g⁻¹ * E.x * g = t
        rw [hgx]; group
      calc (g⁻¹ * E.s) * t = (g⁻¹ * E.s * t * (g⁻¹ * E.s)⁻¹) * (g⁻¹ * E.s) := by group
        _ = t * (g⁻¹ * E.s) := by rw [h1]
    have hm := P.mem_Tp_of_comm E.hQ E.hTQ (mul_mem (inv_mem (E.hTQ hg)) E.hsQ) hc
    have := mul_mem hg (P.Tp_le hm)
    rwa [mul_inv_cancel_left] at this
  · exact h

omit [Finite X] in
theorem s_mem_Y {y : X} (hyT : y ∈ P.T₂)
    (hy : ∀ g ∈ P.T₂, g * y * g⁻¹ = y ∨ g * y * g⁻¹ = P.z * y) :
    E.s * y * E.s⁻¹ = 1 ∨ E.s * y * E.s⁻¹ = P.z ∨ E.s * y * E.s⁻¹ = P.k ∨
      E.s * y * E.s⁻¹ = P.z * P.k ∨ E.s * y * E.s⁻¹ = P.w ∨ E.s * y * E.s⁻¹ = P.z * P.w ∨
      E.s * y * E.s⁻¹ = P.k * P.w ∨ E.s * y * E.s⁻¹ = P.z * P.k * P.w := by
  refine P.Y _ (E.conj_mem hyT) fun h hh => ?_
  have e : h * (E.s * y * E.s⁻¹) * h⁻¹ =
      E.s * ((E.s⁻¹ * h * E.s) * y * (E.s⁻¹ * h * E.s)⁻¹) * E.s⁻¹ := by group
  rcases hy _ (E.conj_inv_mem hh) with h1 | h1 <;> rw [e, h1]
  · exact Or.inl rfl
  · right
    rw [show E.s * (P.z * y) * E.s⁻¹ = (E.s * P.z * E.s⁻¹) * (E.s * y * E.s⁻¹) by group, E.s_z]

omit [Finite X] in
theorem x_fix_sk : E.x * (E.s * P.k * E.s⁻¹) * E.x⁻¹ = E.s * P.k * E.s⁻¹ := by
  rw [x, show E.s * t * E.s⁻¹ * (E.s * P.k * E.s⁻¹) * (E.s * t * E.s⁻¹)⁻¹ =
    E.s * (t * P.k * t⁻¹) * E.s⁻¹ by group, P.t_k]

omit [Finite X] in
theorem x_flip_sw : E.x * (E.s * P.w * E.s⁻¹) * E.x⁻¹ = P.z * (E.s * P.w * E.s⁻¹) := by
  rw [x, show E.s * t * E.s⁻¹ * (E.s * P.w * E.s⁻¹) * (E.s * t * E.s⁻¹)⁻¹ =
    E.s * (t * P.w * t⁻¹) * E.s⁻¹ by group, P.t_w,
    show E.s * (P.z * P.w) * E.s⁻¹ = (E.s * P.z * E.s⁻¹) * (E.s * P.w * E.s⁻¹) by group, E.s_z]

omit [Finite X] in
theorem sy_ne_one {y : X} (hy : y ≠ 1) : E.s * y * E.s⁻¹ ≠ 1 := fun h => hy (by
  calc y = E.s⁻¹ * (E.s * y * E.s⁻¹) * E.s := by group
    _ = 1 := by rw [h]; group)

omit [Finite X] in
theorem sy_ne_z {y : X} (hy : y ≠ P.z) : E.s * y * E.s⁻¹ ≠ P.z := fun h => hy (by
  calc y = E.s⁻¹ * (E.s * y * E.s⁻¹) * E.s := by group
    _ = E.s⁻¹ * (E.s * P.z * E.s⁻¹) * E.s := by rw [h, E.s_z]
    _ = P.z := by group)

theorem s_k : E.s * P.k * E.s⁻¹ = P.k * P.w ∨ E.s * P.k * E.s⁻¹ = P.z * P.k * P.w := by
  have hfix := E.x_fix_sk
  obtain ⟨hxk, hxw⟩ := E.x_flip
  rcases E.s_mem_Y P.k_mem P.conj_k with h | h | h | h | h | h | h | h
  · exact absurd h (E.sy_ne_one P.k_ne₁)
  · exact absurd h (E.sy_ne_z P.k_ne_z)
  · rw [h, hxk] at hfix; exact absurd hfix P.zk_ne_k
  · rw [h, P.flip_mul_z E.x_z hxk] at hfix; exact absurd hfix P.k_ne_zk
  · rw [h, hxw] at hfix; exact absurd hfix P.zw_ne_w
  · rw [h, P.flip_mul_z E.x_z hxw] at hfix; exact absurd hfix P.w_ne_zw
  · exact Or.inl h
  · exact Or.inr h

theorem s_w : E.s * P.w * E.s⁻¹ = P.w ∨ E.s * P.w * E.s⁻¹ = P.z * P.w := by
  have hfl := E.x_flip_sw
  obtain ⟨hxk, hxw⟩ := E.x_flip
  have hkw := P.flip_kw hxk hxw
  have hzkw : E.x * (P.z * P.k * P.w) * E.x⁻¹ = P.z * P.k * P.w := by
    rw [show P.z * P.k * P.w = P.z * (P.k * P.w) by group]; exact P.fix_mul_z E.x_z hkw
  have hs2 : (E.s * E.s) * P.w * (E.s * E.s)⁻¹ = P.w ∨
      (E.s * E.s) * P.w * (E.s * E.s)⁻¹ = P.z * P.w := P.conj_w _ E.hs2
  have e2 : (E.s * E.s) * P.w * (E.s * E.s)⁻¹ = E.s * (E.s * P.w * E.s⁻¹) * E.s⁻¹ := by group
  rcases E.s_mem_Y P.w_mem P.conj_w with h | h | h | h | h | h | h | h
  · exact absurd h (E.sy_ne_one P.w_ne₁)
  · exact absurd h (E.sy_ne_z P.w_ne_z)
  · exfalso
    rw [e2, h] at hs2
    rcases E.s_k with h' | h' <;> rw [h'] at hs2 <;> rcases hs2 with h'' | h''
    · exact P.kw_ne_w h''
    · exact P.kw_ne_zw h''
    · exact P.zkw_ne_w h''
    · exact P.zkw_ne_zw h''
  · exfalso
    rw [e2, h, show E.s * (P.z * P.k) * E.s⁻¹ = (E.s * P.z * E.s⁻¹) * (E.s * P.k * E.s⁻¹) by
      group, E.s_z] at hs2
    rcases E.s_k with h' | h' <;> rw [h'] at hs2 <;> rcases hs2 with h'' | h''
    · exact P.zkw_ne_w (by rw [← mul_assoc] at h''; exact h'')
    · exact P.zkw_ne_zw (by rw [← mul_assoc] at h''; exact h'')
    · exact P.kw_ne_w (by
        rw [← mul_assoc, ← mul_assoc, P.zz, one_mul] at h''; exact h'')
    · exact P.kw_ne_zw (by
        rw [← mul_assoc, ← mul_assoc, P.zz, one_mul] at h''; exact h'')
  · exact Or.inl h
  · exact Or.inr h
  · rw [h, hkw] at hfl
    exact absurd hfl.symm (fun h' => P.z_ne (mul_eq_right.mp h'))
  · rw [h, hzkw] at hfl
    exact absurd hfl.symm (fun h' => P.z_ne (mul_eq_right.mp h'))

end SEl

end SPkg

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
