module


import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

variable {Y : Type*} [Group Y]

@[expose] def ConjAgree (L : Subgroup Y) (b l : Y) : Prop :=
  ∀ k ∈ L, b * k * b⁻¹ = l * k * l⁻¹

section ConjAgree

variable {L : Subgroup Y} {b c l m : Y}

theorem ConjAgree.self (hl : l ∈ L) (h : ConjAgree L b l) : b * l * b⁻¹ = l := by
  rw [h l hl]
  group

theorem ConjAgree.commute (hl : l ∈ L) (hm : m ∈ L) (h : ConjAgree L b l) (h' : ConjAgree L b m)
    {k : Y} (hk : k ∈ L) : k * (l⁻¹ * m) = (l⁻¹ * m) * k := by
  have e : l * k * l⁻¹ = m * k * m⁻¹ := (h k hk).symm.trans (h' k hk)
  calc k * (l⁻¹ * m) = l⁻¹ * (l * k * l⁻¹) * m := by group
    _ = l⁻¹ * (m * k * m⁻¹) * m := by rw [e]
    _ = (l⁻¹ * m) * k := by group

theorem ConjAgree.mul (hl : l ∈ L) (hm : m ∈ L) (h : ConjAgree L b l) (h' : ConjAgree L c m) :
    ConjAgree L (b * c) (l * m) := by
  intro k hk
  have h1 : c * k * c⁻¹ = m * k * m⁻¹ := h' k hk
  have h2 : b * m * b⁻¹ = l * m * l⁻¹ := h m hm
  have h3 : b * k * b⁻¹ = l * k * l⁻¹ := h k hk
  have h4 : b * m⁻¹ * b⁻¹ = l * m⁻¹ * l⁻¹ := h m⁻¹ (L.inv_mem hm)
  calc b * c * k * (b * c)⁻¹ = b * (c * k * c⁻¹) * b⁻¹ := by group
    _ = b * (m * k * m⁻¹) * b⁻¹ := by rw [h1]
    _ = (b * m * b⁻¹) * (b * k * b⁻¹) * (b * m⁻¹ * b⁻¹) := by group
    _ = (l * m * l⁻¹) * (l * k * l⁻¹) * (l * m⁻¹ * l⁻¹) := by rw [h2, h3, h4]
    _ = l * m * k * (l * m)⁻¹ := by group

theorem ConjAgree.sq_central (hl : l ∈ L) (h : ConjAgree L b l) (hb : b * b = 1) {k : Y}
    (hk : k ∈ L) : k * (l * l) = (l * l) * k := by
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : b * (b * k * b⁻¹) * b⁻¹ = k := by
    rw [hbi]
    calc b * (b * k * b) * b = (b * b) * k * (b * b) := by group
      _ = k := by rw [hb]; group
  have e1 : b * l * b⁻¹ = l := h.self hl
  have e2 : b * l⁻¹ * b⁻¹ = l⁻¹ := by
    calc b * l⁻¹ * b⁻¹ = (b * l * b⁻¹)⁻¹ := by group
      _ = l⁻¹ := by rw [e1]
  have h2 : b * (b * k * b⁻¹) * b⁻¹ = l * l * k * (l * l)⁻¹ := by
    rw [h k hk]
    calc b * (l * k * l⁻¹) * b⁻¹ = (b * l * b⁻¹) * (b * k * b⁻¹) * (b * l⁻¹ * b⁻¹) := by group
      _ = l * (l * k * l⁻¹) * l⁻¹ := by rw [e1, h k hk, e2]
      _ = l * l * k * (l * l)⁻¹ := by group
  have h3 : l * l * k * (l * l)⁻¹ = k := h2.symm.trans h1
  calc k * (l * l) = (l * l * k * (l * l)⁻¹) * (l * l) := by rw [h3]
    _ = (l * l) * k := by group

theorem exists_involutory_lift (hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1)
    (hb : b * b = 1) (hl : l ∈ L) (h : ConjAgree L b l) :
    ∃ m, m ∈ L ∧ ConjAgree L b m ∧ m * m = 1 := by
  have hz : l * l ∈ L := L.mul_mem hl hl
  have hzc : ∀ k ∈ L, k * (l * l) = (l * l) * k := fun k hk => h.sq_central hl hb hk
  have hz3 : (l * l) ^ 3 = 1 := hZ _ hz hzc
  refine ⟨l * (l * l), L.mul_mem hl hz, ?_, ?_⟩
  · intro k hk
    have hzk : (l * l) * k * (l * l)⁻¹ = k := by
      rw [← hzc k hk]
      group
    calc b * k * b⁻¹ = l * k * l⁻¹ := h k hk
      _ = l * ((l * l) * k * (l * l)⁻¹) * l⁻¹ := by rw [hzk]
      _ = l * (l * l) * k * (l * (l * l))⁻¹ := by group
  · calc l * (l * l) * (l * (l * l)) = (l * l) ^ 3 := by rw [pow_three]; group
      _ = 1 := hz3

theorem ConjAgree.eq_of_sq_eq_one (hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1)
    (hl : l ∈ L) (hm : m ∈ L) (h : ConjAgree L b l) (h' : ConjAgree L b m) (hl2 : l * l = 1)
    (hm2 : m * m = 1) : m = l := by
  obtain ⟨z, hzdef⟩ : ∃ z, z = l⁻¹ * m := ⟨_, rfl⟩
  have hzL : z ∈ L := by rw [hzdef]; exact L.mul_mem (L.inv_mem hl) hm
  have hzc : ∀ k ∈ L, k * z = z * k := fun k hk => by
    rw [hzdef]
    exact ConjAgree.commute hl hm h h' hk
  have hz3 : z ^ 3 = 1 := hZ z hzL hzc
  have hm' : m = l * z := by rw [hzdef]; group
  have hz2 : z * z = 1 := by
    have h1 : m * m = (l * l) * (z * z) := by
      rw [hm']
      calc l * z * (l * z) = l * (z * l) * z := by group
        _ = l * (l * z) * z := by rw [← hzc l hl]
        _ = (l * l) * (z * z) := by group
    rw [hm2, hl2, one_mul] at h1
    exact h1.symm
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2]; group
  rw [hm', hz1, mul_one]

theorem sq_eq_one_of_pow {x : Y} (h4 : x ^ 4 = 1) (h6 : (x * x) ^ 3 = 1) : x * x = 1 := by
  have h6' : x ^ 6 = 1 := by rw [← h6, ← pow_two, ← pow_mul]
  calc x * x = x ^ 2 := (pow_two x).symm
    _ = x ^ 6 * (x ^ 4)⁻¹ := by group
    _ = 1 := by rw [h6', h4]; group

theorem commute_of_central {p q w : Y} (hp : p * p = 1) (hq : q * q = 1)
    (hw : w = (p * q)⁻¹ * (q * p)) (hpw : p * w = w * p) (hw3 : w ^ 3 = 1) : p * q = q * p := by
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  have hinv : (p * q)⁻¹ = q * p := by rw [mul_inv_rev, hpi, hqi]
  have hw' : w = (q * p) * (q * p) := by rw [hw, hinv]
  rw [hw'] at hpw hw3
  have h1 : p * q * p * q * p = q * p * q := by
    calc p * q * p * q * p = p * (q * p * (q * p)) := by group
      _ = q * p * (q * p) * p := hpw
      _ = q * p * q * (p * p) := by group
      _ = q * p * q := by rw [hp, mul_one]
  have h2 : (p * q) ^ 4 = 1 := by
    calc (p * q) ^ 4 = (p * q) * (p * q) * (p * q) * (p * q) := by
          simp only [pow_succ, pow_zero, one_mul]
      _ = (p * q * p * q * p) * q * p * q := by group
      _ = (q * p * q) * q * p * q := by rw [h1]
      _ = q * p * (q * q) * p * q := by group
      _ = q * (p * p) * q := by rw [hq, mul_one]; group
      _ = 1 := by rw [hp, mul_one, hq]
  have h3 : (q * p) ^ 4 = 1 := by rw [← hinv, inv_pow, h2, inv_one]
  have h4 : (q * p) * (q * p) = 1 := sq_eq_one_of_pow h3 hw3
  have h5 : q * p = (q * p)⁻¹ := eq_inv_of_mul_eq_one_left h4
  rw [mul_inv_rev, hpi, hqi] at h5
  exact h5.symm

end ConjAgree

section Hom

variable {L B : Subgroup Y}

theorem exists_lift_hom (hB2 : ∀ b ∈ B, b * b = 1) (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b)
    (hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1)
    (hinner : ∀ b ∈ B, ∃ l ∈ L, ConjAgree L b l) :
    ∃ lB : ↥B →* ↥L, ∀ b : ↥B, ConjAgree L (b : Y) (lB b : Y) := by
  have hex : ∀ b : ↥B, ∃ m : Y, m ∈ L ∧ ConjAgree L (b : Y) m ∧ m * m = 1 := by
    intro b
    obtain ⟨l, hl, h⟩ := hinner b b.2
    exact exists_involutory_lift hZ (hB2 b b.2) hl h
  choose m hmL hmA hm2 using hex
  have huniq : ∀ (b : ↥B) (n : Y), n ∈ L → ConjAgree L (b : Y) n → n * n = 1 → n = m b :=
    fun b n hn hA h2 => ConjAgree.eq_of_sq_eq_one hZ (hmL b) hn (hmA b) hA (hm2 b) h2
  have hcomm : ∀ b c : ↥B, m b * m c = m c * m b := by
    intro b c
    have hbc : (b : Y) * (c : Y) = (c : Y) * (b : Y) := hBc b b.2 c c.2
    have hA1 : ConjAgree L ((b : Y) * (c : Y)) (m b * m c) :=
      ConjAgree.mul (hmL b) (hmL c) (hmA b) (hmA c)
    have hA2 : ConjAgree L ((b : Y) * (c : Y)) (m c * m b) := by
      rw [hbc]
      exact ConjAgree.mul (hmL c) (hmL b) (hmA c) (hmA b)
    have hbcL : m b * m c ∈ L := L.mul_mem (hmL b) (hmL c)
    have hcbL : m c * m b ∈ L := L.mul_mem (hmL c) (hmL b)
    have hzL : (m b * m c)⁻¹ * (m c * m b) ∈ L := L.mul_mem (L.inv_mem hbcL) hcbL
    have hzc : ∀ k ∈ L, k * ((m b * m c)⁻¹ * (m c * m b)) =
        ((m b * m c)⁻¹ * (m c * m b)) * k := fun k hk =>
      ConjAgree.commute hbcL hcbL hA1 hA2 hk
    exact commute_of_central (hm2 b) (hm2 c) rfl (hzc (m b) (hmL b)) (hZ _ hzL hzc)
  refine ⟨MonoidHom.mk' (fun b => ⟨m b, hmL b⟩) fun b c => ?_, fun b => hmA b⟩
  apply Subtype.ext
  show m (b * c) = m b * m c
  symm
  refine huniq (b * c) (m b * m c) (L.mul_mem (hmL b) (hmL c))
    (ConjAgree.mul (hmL b) (hmL c) (hmA b) (hmA c)) ?_
  calc m b * m c * (m b * m c) = m b * (m c * m b) * m c := by group
    _ = m b * (m b * m c) * m c := by rw [← hcomm b c]
    _ = (m b * m b) * (m c * m c) := by group
    _ = 1 := by rw [hm2 b, hm2 c, one_mul]

theorem exists_split_hom (lB : ↥B →* ↥L) (h : ∀ b : ↥B, ConjAgree L (b : Y) (lB b : Y)) :
    ∃ π : ↥L × ↥B →* Y,
      ∀ (l : ↥L) (b : ↥B), π (l, b) = (l : Y) * (lB b : Y)⁻¹ * (b : Y) := by
  have hcen : ∀ (b : ↥B) (k : Y), k ∈ L →
      (b : Y) * k = (lB b : Y) * k * (lB b : Y)⁻¹ * (b : Y) := by
    intro b k hk
    have e : (b : Y) * k * (b : Y)⁻¹ = (lB b : Y) * k * (lB b : Y)⁻¹ := h b k hk
    calc (b : Y) * k = ((b : Y) * k * (b : Y)⁻¹) * (b : Y) := by group
      _ = (lB b : Y) * k * (lB b : Y)⁻¹ * (b : Y) := by rw [e]
  refine ⟨MonoidHom.mk' (fun x : ↥L × ↥B => (x.1 : Y) * (lB x.2 : Y)⁻¹ * (x.2 : Y))
    fun x y => ?_, fun l b => rfl⟩
  obtain ⟨l, b⟩ := x
  obtain ⟨l', b'⟩ := y
  have e1 : (b : Y) * (l' : Y) = (lB b : Y) * (l' : Y) * (lB b : Y)⁻¹ * (b : Y) :=
    hcen b l' l'.2
  have e2 : (b : Y) * (lB b' : Y)⁻¹ =
      (lB b : Y) * (lB b' : Y)⁻¹ * (lB b : Y)⁻¹ * (b : Y) :=
    hcen b _ (L.inv_mem (lB b').2)
  simp only [Prod.mk_mul_mk, map_mul, Subgroup.coe_mul]
  symm
  calc (l : Y) * (lB b : Y)⁻¹ * (b : Y) * (l' * (lB b' : Y)⁻¹ * b')
      = (l : Y) * (lB b : Y)⁻¹ * ((b : Y) * (l' : Y)) * (lB b' : Y)⁻¹ * (b' : Y) := by group
    _ = (l : Y) * (lB b : Y)⁻¹ * ((lB b : Y) * (l' : Y) * (lB b : Y)⁻¹ * (b : Y)) *
          (lB b' : Y)⁻¹ * (b' : Y) := by rw [e1]
    _ = (l : Y) * l' * (lB b : Y)⁻¹ * ((b : Y) * (lB b' : Y)⁻¹) * (b' : Y) := by group
    _ = (l : Y) * l' * (lB b : Y)⁻¹ * ((lB b : Y) * (lB b' : Y)⁻¹ * (lB b : Y)⁻¹ * (b : Y)) *
          (b' : Y) := by rw [e2]
    _ = (l : Y) * l' * ((lB b : Y) * (lB b' : Y))⁻¹ * ((b : Y) * b') := by group

end Hom

end CFSG.LocalAnalysis.RankThreeUC.S15
