module

public import CFSG.CGT.Hall82.ModelFacts
public import CFSG.CGT.Hall82.DModelData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStab

public section

namespace CFSG.CGT.Hall82

open CFSG.ComponentClassification.AS81.Hexa CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.HeTri CFSG.Monster.B.Co2

@[expose] def IsOvalVec (v : Fin 64) : Prop := v.val ∈ hallKList

instance : DecidablePred IsOvalVec := fun v => inferInstanceAs (Decidable (v.val ∈ hallKList))

@[expose] def InHallU (v : Fin 64) : Prop := v.val ∈ hallU0List

instance : DecidablePred InHallU := fun v => inferInstanceAs (Decidable (v.val ∈ hallU0List))

@[expose] def InHallW (k : Fin 64) : Prop := k.val ∈ hallWList

instance : DecidablePred InHallW := fun k => inferInstanceAs (Decidable (k.val ∈ hallWList))

@[expose] def IsHallOrb (k : Fin 64) : Prop := k.val = 1 ∨ k.val = 4 ∨ k.val = 7

instance : DecidablePred IsHallOrb := fun k =>
  inferInstanceAs (Decidable (k.val = 1 ∨ k.val = 4 ∨ k.val = 7))

@[expose] def hallQ0 (k : Fin 64) : Bool := hallQ0List.getD k.val false

@[expose] def xor8 (e f : Fin 8) : Fin 8 := ⟨e.val ^^^ f.val, Nat.xor_lt_two_pow (n := 3) e.2 f.2⟩

@[expose] def stabSub (X : Subgroup (Equiv.Perm (Fin 64))) (v : Fin 64) :
    Subgroup (Equiv.Perm (Fin 64)) :=
  X ⊓ MulAction.stabilizer (Equiv.Perm (Fin 64)) v

@[expose] noncomputable def hallRMPerm (e : Fin 8) : Equiv.Perm (Fin 64) :=
  permOfArr 64 (hallRMArr.getD e.val #[])

@[expose] noncomputable def hallRM : Subgroup (Equiv.Perm (Fin 64)) :=
  Subgroup.closure (Set.range hallRMPerm)

@[expose] def hallX1 : Set (Equiv.Perm (Fin 64)) :=
  {x | ∃ u, InHallU u ∧ ∃ e, x = transl u * hallRMPerm e}

@[expose] def xcode (x : Equiv.Perm (Fin 64)) : Fin 64 :=
  let u := (x 0).val
  let l16 := (x 16).val ^^^ u
  let l2 := (x 2).val ^^^ u
  let l1 := (x 1).val ^^^ u
  ⟨((if u.testBit 0 = u.testBit 2 then 0 else 1) + 2 * (if u.testBit 1 then 1 else 0) +
      4 * (if u.testBit 4 then 1 else 0) + 8 * (if l16 = 21 then 1 else 0) +
      16 * (if l2 = 3 ∨ l2 = 12 then 1 else 0) + 32 * (if l1 = 4 then 1 else 0)) % 64,
    Nat.mod_lt _ (by norm_num)⟩

@[expose] def hallS40 : Set (Fin 64 → Fin 64) :=
  {f | ∃ a ∈ hallS40Arr, ∀ k : Fin 64, (f k).val = a.getD k.val 0}

@[expose] def GoodHall (z : Fin 64 → Fin 64) : Prop :=
  z ∈ hallS40 ∨ ∀ p, IsHallOrb p → ¬ IsHallOrb (z p)

@[expose] def hallRIdx : Fin 3 → Fin 8 := ![1, 2, 4]

@[expose] noncomputable def hallXi (a : Fin 3 → Fin 64) (i : Fin 3) : Equiv.Perm (Fin 64) :=
  transl (a i) * hallRMPerm (hallRIdx i)

@[expose] noncomputable def hallXProd (a : Fin 3 → Fin 64) (e : Fin 8) : Equiv.Perm (Fin 64) :=
  hallXi a 0 ^ (e.val % 2) * hallXi a 1 ^ (e.val / 2 % 2) * hallXi a 2 ^ (e.val / 4 % 2)

structure DModelFacts : Prop where
  lin : ∀ x ∈ hexaM, ∀ v w, x (xorF v w) = xorF (x v) (x w)
  oval_trans : ∀ h h', IsOvalVec h → IsOvalVec h' → ∃ a ∈ hexaL, a h = h'
  five_trans : ∀ v, v ≠ 0 → ¬ IsOvalVec v → ∃ a ∈ hexaL, a 5 = v
  five_not_oval : ¬ IsOvalVec 5
  card_stab_oval : ∀ h, IsOvalVec h → Nat.card (stabSub hexaM h) = 120
  card_stab : ∀ v, v ≠ 0 → ¬ IsOvalVec v → Nat.card (stabSub hexaM v) = 48
  card_stabL_oval : ∀ h, IsOvalVec h → Nat.card (stabSub hexaL h) = 60
  card_stabL : ∀ v, v ≠ 0 → ¬ IsOvalVec v → Nat.card (stabSub hexaL v) = 24
  eq_bot_of_oval : ∀ h, IsOvalVec h → ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hexaM →
    IsPGroup 2 B → (∀ b ∈ B, b h = h) → (∀ a ∈ hexaL, a h = h → ∀ b ∈ B, a * b * a⁻¹ ∈ B) →
    B = ⊥
  rm_mul : ∀ e f, hallRMPerm e * hallRMPerm f = hallRMPerm (xor8 e f)
  rm_inj : Function.Injective hallRMPerm
  mem_rm_iff : ∀ x, x ∈ hallRM ↔ ∃ e, hallRMPerm e = x
  rm_le : hallRM ≤ hexaM
  rm_fix : ∀ e, hallRMPerm e 5 = 5
  rm_not_le : ¬ hallRM ≤ hexaL
  le_rm : ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hexaM → IsPGroup 2 B → (∀ b ∈ B, b 5 = 5) →
    (∀ a ∈ hexaL, a 5 = 5 → ∀ b ∈ B, a * b * a⁻¹ ∈ B) → B ≤ hallRM
  rm_le_or_quad : ∀ B : Subgroup (Equiv.Perm (Fin 64)), B ≤ hallRM →
    (∀ a ∈ hexaL, a 5 = 5 → ∀ b ∈ B, a * b * a⁻¹ ∈ B) →
    hallRM ≤ B ∨ ∀ a ∈ B, ∀ b ∈ B, ∀ v, xorF (xorF (a (b v)) (a v)) (xorF (b v) v) = 0
  u_inv : ∀ s ∈ hexaM, s 5 = 5 → ∀ v, InHallU v → InHallU (s v)
  rm_comm_u : ∀ e v, InHallU v → xorF (hallRMPerm e v) v = 0 ∨ xorF (hallRMPerm e v) v = 5
  rm_eq_zero_of_fix_u : ∀ e, (∀ v, InHallU v → hallRMPerm e v = v) → e = 0
  fix_rm : ∀ v, (∀ e, hallRMPerm e v = v) → v = 0 ∨ v = 5
  u_maximal : ∀ W : Set (Fin 64), (∀ v ∈ W, ∀ w ∈ W, xorF v w ∈ W) → (∀ v, InHallU v → v ∈ W) →
    (∀ a ∈ hexaL, a 5 = 5 → ∀ w ∈ W, a w ∈ W) → W = {v | InHallU v} ∨ W = Set.univ
  zeta_fix : ∀ v, heZeta v = v → v = 0
  zeta_pow : heZeta ^ 3 = 1
  zeta_ne : heZeta ≠ 1
  zeta_conj : ∀ x ∈ hexaM, x * heZeta * x⁻¹ = heZeta ∨ x * heZeta * x⁻¹ = heZeta ^ 2
  lift : ∀ a : Fin 3 → Fin 64,
    (∀ i j, hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = 1 ∨
      hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = transl 5) →
    (∀ i, hallXi a i * hallXi a i = 1 ∨ hallXi a i * hallXi a i = transl 5) →
    (∀ s ∈ hexaM, s 5 = 5 → ∀ i, ∃ u, InHallU u ∧ ∃ e, s * hallXi a i * s⁻¹ =
      transl u * hallXProd a e) →
    ∀ i, InHallU (a i)
  xcode_mul : ∀ x ∈ hallX1, ∀ y ∈ hallX1, xcode (x * y) = xorF (xcode x) (xcode y)
  xcode_eq_zero : ∀ x ∈ hallX1, xcode x = 0 ↔ x = 1 ∨ x = transl 5
  xcode_surj : ∀ k, ∃ x ∈ hallX1, xcode x = k
  xcode_sq : ∀ x ∈ hallX1, x * x = transl 5 ↔ hallQ0 (xcode x) = true
  xcode_orb : ∀ x ∈ hallX1, IsHallOrb (xcode x) → ∃ h, IsOvalVec h ∧ x = transl h
  xcode_conj : ∀ b, ∀ s ∈ hexaM, s 5 = 5 → ∃ σ ∈ hallS40, ∀ x ∈ hallX1,
    xcode (transl b * s * x * (transl b * s)⁻¹) = σ (xcode x)
  xcode_conj_surj : ∀ σ ∈ hallS40, ∃ b, ∃ s ∈ hexaM, s 5 = 5 ∧ ∀ x ∈ hallX1,
    xcode (transl b * s * x * (transl b * s)⁻¹) = σ (xcode x)
  reducible : ∀ y : Fin 64 → Fin 64, (∀ k l, y (xorF k l) = xorF (y k) (y l)) →
    (∀ k, hallQ0 (y k) = hallQ0 k) → (∀ k, y k = 0 → k = 0) → GoodHall y →
    (∀ t ∈ hallS40, GoodHall (y ∘ t ∘ y)) →
    (∀ t ∈ hallS40, ∀ u ∈ hallS40, GoodHall (y ∘ t ∘ y ∘ u ∘ y)) →
    ∀ k, InHallW k → InHallW (y k)

end CFSG.CGT.Hall82
