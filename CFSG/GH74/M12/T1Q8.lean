module

public import CFSG.GH74.M12.T1Basic

public section

namespace CFSG.GH74.M12.Thm1

open Subgroup CFSG.Quasithin
open CFSG.GH74.M12 (Asc03Hyp q8Subgroups)

variable {G : Type*} [Group G] {z : G}

theorem card_mul_card_le_sup [Finite G] (X Y : Subgroup G) :
    Nat.card ↥X * Nat.card ↥Y ≤ Nat.card ↥(X ⊔ Y) * Nat.card ↥(X ⊓ Y) := by
  have h1 : X.relIndex Y ≤ X.relIndex (X ⊔ Y) :=
    Subgroup.relIndex_le_of_le_right le_sup_right
      (show (X.subgroupOf (X ⊔ Y)).index ≠ 0 from Subgroup.index_ne_zero_of_finite)
  have h2 := Subgroup.relIndex_mul_card X Y
  have h3 := Subgroup.relIndex_mul_card X (X ⊔ Y)
  rw [inf_eq_left.2 le_sup_left] at h3
  calc Nat.card ↥X * Nat.card ↥Y = Nat.card ↥X * (X.relIndex Y * Nat.card ↥(X ⊓ Y)) := by rw [h2]
    _ ≤ Nat.card ↥X * (X.relIndex (X ⊔ Y) * Nat.card ↥(X ⊓ Y)) := by gcongr
    _ = Nat.card ↥(X ⊔ Y) * Nat.card ↥(X ⊓ Y) := by rw [← h3]; ring

theorem card_mul_card_le_inf [Finite G] {X Y Q : Subgroup G} (hX : X ≤ Q) (hY : Y ≤ Q) :
    Nat.card ↥Y * Nat.card ↥X ≤ Nat.card ↥(X ⊓ Y) * Nat.card ↥Q := by
  have h1 : X.relIndex Y ≤ X.relIndex Q :=
    Subgroup.relIndex_le_of_le_right hY
      (show (X.subgroupOf Q).index ≠ 0 from Subgroup.index_ne_zero_of_finite)
  have h2 := Subgroup.relIndex_mul_card X Y
  have h3 := Subgroup.relIndex_mul_card X Q
  rw [inf_eq_left.2 hX] at h3
  calc Nat.card ↥Y * Nat.card ↥X = X.relIndex Y * Nat.card ↥(X ⊓ Y) * Nat.card ↥X := by rw [h2]
    _ ≤ X.relIndex Q * Nat.card ↥(X ⊓ Y) * Nat.card ↥X := by gcongr
    _ = Nat.card ↥(X ⊓ Y) * Nat.card ↥Q := by rw [← h3]; ring

section Q8Hom

variable {D : Type*} [Group D]

theorem pow_val_add_eq' [Finite D] {ρ : D} {n : ℕ} (hn : orderOf ρ = n) (i j : ZMod n) :
    ρ ^ ((i + j).val) = ρ ^ i.val * ρ ^ j.val := by
  have : NeZero n := ⟨by rw [← hn]; exact (orderOf_pos ρ).ne'⟩
  have hcong : (i.val + j.val) % n ≡ i.val + j.val [MOD n] := Nat.mod_modEq (i.val + j.val) n
  have hx : ρ ^ n = 1 := by rw [← hn]; exact pow_orderOf_eq_one ρ
  calc ρ ^ ((i + j).val) = ρ ^ ((i.val + j.val) % n) := by rw [ZMod.val_add (n := n) i j]
    _ = ρ ^ (i.val + j.val) := pow_eq_pow_of_modEq hcong hx
    _ = ρ ^ i.val * ρ ^ j.val := by rw [pow_add]

theorem pow_val_sub_zpow' [Finite D] {ρ : D} {n : ℕ} (hn : orderOf ρ = n) (i j : ZMod n) :
    ρ ^ ((j - i).val) = ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by
  have : NeZero n := ⟨by rw [← hn]; exact (orderOf_pos ρ).ne'⟩
  have hji : (i + (j - i) : ZMod n) = j := by simp [sub_eq_add_neg]
  have hval : j.val = (i.val + (j - i).val) % n := by
    calc j.val = (i + (j - i) : ZMod n).val := by rw [hji]
      _ = (i.val + (j - i).val) % n := ZMod.val_add (n := n) i (j - i)
  have hcong : j.val ≡ i.val + (j - i).val [MOD n] := by rw [hval]; exact Nat.mod_modEq _ _
  have hx : ρ ^ n = 1 := by rw [← hn]; exact pow_orderOf_eq_one ρ
  have hp : ρ ^ j.val = ρ ^ i.val * ρ ^ ((j - i).val) := by
    calc ρ ^ j.val = ρ ^ (i.val + (j - i).val) := pow_eq_pow_of_modEq hcong hx
      _ = ρ ^ i.val * ρ ^ ((j - i).val) := by rw [pow_add]
  calc ρ ^ ((j - i).val) = (ρ ^ i.val)⁻¹ * ρ ^ j.val := by rw [hp]; group
    _ = ρ ^ (-(i.val : ℤ)) * ρ ^ (j.val : ℤ) := by
      rw [← zpow_natCast (a := ρ) (n := i.val), ← zpow_neg (a := ρ) (n := (i.val : ℤ)),
        ← zpow_natCast (a := ρ) (n := j.val)]
    _ = ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by rw [← zpow_add]; congr 1; ring

theorem pow_mul_rel' {ρ σ : D} (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (t : ℕ) :
    ρ ^ t * σ = σ * ρ ^ (-(t : ℤ)) := by
  have hconjInv : σ * ρ⁻¹ * σ⁻¹ = ρ := by
    have h := congrArg Inv.inv hrel
    simpa [mul_assoc] using h
  have hρσ : ρ * σ = σ * ρ⁻¹ := by
    calc ρ * σ = (σ * ρ⁻¹ * σ⁻¹) * σ := by rw [hconjInv]
      _ = σ * ρ⁻¹ := by group
  induction t with
  | zero => simp
  | succ t ih =>
      calc ρ ^ (t + 1) * σ = (ρ ^ t * ρ) * σ := by rw [pow_succ]
        _ = ρ ^ t * (ρ * σ) := by rw [mul_assoc]
        _ = ρ ^ t * (σ * ρ⁻¹) := by rw [hρσ]
        _ = (ρ ^ t * σ) * ρ⁻¹ := by rw [mul_assoc]
        _ = (σ * ρ ^ (-(t : ℤ))) * ρ⁻¹ := by rw [ih]
        _ = σ * ρ ^ (-((t + 1 : ℕ) : ℤ)) := by
          rw [mul_assoc, ← zpow_neg_one ρ, ← zpow_add]
          exact congrArg (fun e : ℤ => σ * ρ ^ e) (by omega)

@[expose] noncomputable def q8Hom [Finite D] (i j : D) (hi : orderOf i = 4) (hj : j * j = i * i)
    (hrel : j * i * j⁻¹ = i⁻¹) : QuaternionGroup 2 →* D where
  toFun
    | QuaternionGroup.a k => i ^ k.val
    | QuaternionGroup.xa k => j * i ^ k.val
  map_one' := by
    change i ^ 0 = 1
    simp
  map_mul' := by
    rintro (k | k) (l | l)
    · change i ^ (k + l).val = i ^ k.val * i ^ l.val
      exact pow_val_add_eq' hi k l
    · change j * i ^ (l - k).val = i ^ k.val * (j * i ^ l.val)
      symm
      calc i ^ k.val * (j * i ^ l.val) = (i ^ k.val * j) * i ^ l.val := by rw [mul_assoc]
        _ = (j * i ^ (-(k.val : ℤ))) * i ^ l.val := by rw [pow_mul_rel' hrel k.val]
        _ = j * (i ^ (-(k.val : ℤ)) * i ^ (l.val : ℤ)) := by rw [mul_assoc, zpow_natCast]
        _ = j * i ^ ((l.val : ℤ) - (k.val : ℤ)) := by rw [← zpow_add]; congr 2; ring
        _ = j * i ^ (l - k).val := by rw [pow_val_sub_zpow' hi k l]
    · change j * i ^ (k + l).val = (j * i ^ k.val) * i ^ l.val
      rw [pow_val_add_eq' hi]
      simp [mul_assoc]
    · change i ^ (((2 : ZMod 4) + l - k).val) = (j * i ^ k.val) * (j * i ^ l.val)
      symm
      calc (j * i ^ k.val) * (j * i ^ l.val) = j * (i ^ k.val * j) * i ^ l.val := by group
        _ = j * (j * i ^ (-(k.val : ℤ))) * i ^ l.val := by rw [pow_mul_rel' hrel k.val]
        _ = j ^ 2 * (i ^ (-(k.val : ℤ)) * i ^ (l.val : ℤ)) := by rw [pow_two]; group
        _ = i ^ 2 * (i ^ (-(k.val : ℤ)) * i ^ (l.val : ℤ)) := by rw [pow_two, pow_two, hj]
        _ = i ^ 2 * i ^ ((l.val : ℤ) - (k.val : ℤ)) := by rw [← zpow_add]; congr 2; ring
        _ = i ^ 2 * i ^ (l - k).val := by rw [pow_val_sub_zpow' hi k l]
        _ = i ^ ((2 : ZMod 4) + (l - k)).val := by
          simpa only [show (2 : ZMod 4).val = 2 by decide] using
            (pow_val_add_eq' hi (2 : ZMod 4) (l - k)).symm
        _ = i ^ ((2 : ZMod 4) + l - k).val := by congr 2; ring

theorem q8Hom_a [Finite D] {i j : D} {hi : orderOf i = 4} {hj : j * j = i * i}
    {hrel : j * i * j⁻¹ = i⁻¹} (k : ZMod 4) :
    q8Hom i j hi hj hrel (QuaternionGroup.a k) = i ^ k.val := rfl

theorem q8Hom_xa [Finite D] {i j : D} {hi : orderOf i = 4} {hj : j * j = i * i}
    {hrel : j * i * j⁻¹ = i⁻¹} (k : ZMod 4) :
    q8Hom i j hi hj hrel (QuaternionGroup.xa k) = j * i ^ k.val := rfl

theorem not_mem_zpowers_of_rel [Finite D] {i j : D} (hi : orderOf i = 4)
    (hrel : j * i * j⁻¹ = i⁻¹) : j ∉ Subgroup.zpowers i := by
  intro hj
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hj
  have hcomm : j * i = i * j := by rw [← hk]; exact ((Commute.refl i).zpow_left k).eq
  have h1 : i = i⁻¹ := by
    calc i = j * i * j⁻¹ := by rw [hcomm]; group
      _ = i⁻¹ := hrel
  have h2 : i ^ 2 = 1 := by
    calc i ^ 2 = i * i := pow_two i
      _ = i * i⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel i
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hi] at this
  omega

theorem q8Hom_injective [Finite D] {i j : D} {hi : orderOf i = 4} {hj : j * j = i * i}
    {hrel : j * i * j⁻¹ = i⁻¹} : Function.Injective (q8Hom i j hi hj hrel) := by
  have hpows {k l : ZMod 4} (h : i ^ k.val = i ^ l.val) : k = l := by
    apply ZMod.val_injective
    exact pow_injOn_Iio_orderOf (x := i) (by simpa [hi] using k.val_lt)
      (by simpa [hi] using l.val_lt) h
  rintro (k | k) (l | l) h
  · change i ^ k.val = i ^ l.val at h
    congr 1
    exact hpows h
  · exfalso
    change i ^ k.val = j * i ^ l.val at h
    apply not_mem_zpowers_of_rel hi hrel
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(k.val : ℤ) - (l.val : ℤ), ?_⟩
    calc i ^ ((k.val : ℤ) - (l.val : ℤ)) = i ^ (k.val : ℤ) * i ^ (-(l.val : ℤ)) := by
          rw [sub_eq_add_neg, zpow_add]
      _ = i ^ k.val * (i ^ l.val)⁻¹ := by rw [zpow_natCast, zpow_neg, zpow_natCast]
      _ = (j * i ^ l.val) * (i ^ l.val)⁻¹ := by rw [h]
      _ = j := by group
  · exfalso
    change j * i ^ k.val = i ^ l.val at h
    apply not_mem_zpowers_of_rel hi hrel
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(l.val : ℤ) - (k.val : ℤ), ?_⟩
    calc i ^ ((l.val : ℤ) - (k.val : ℤ)) = i ^ (l.val : ℤ) * i ^ (-(k.val : ℤ)) := by
          rw [sub_eq_add_neg, zpow_add]
      _ = i ^ l.val * (i ^ k.val)⁻¹ := by rw [zpow_natCast, zpow_neg, zpow_natCast]
      _ = (j * i ^ k.val) * (i ^ k.val)⁻¹ := by rw [h]
      _ = j := by group
  · change j * i ^ k.val = j * i ^ l.val at h
    congr 1
    exact hpows (mul_left_cancel h)

end Q8Hom

theorem q8_sq_of_ne (g : QuaternionGroup 2) (h1 : g ≠ 1) (h2 : g ≠ QuaternionGroup.a 2) :
    g * g = QuaternionGroup.a 2 := by
  revert g; decide

theorem q8_center (g : QuaternionGroup 2) (h1 : g * QuaternionGroup.a 1 = QuaternionGroup.a 1 * g)
    (h2 : g * QuaternionGroup.xa 0 = QuaternionGroup.xa 0 * g) :
    g = 1 ∨ g = QuaternionGroup.a 2 := by
  revert g; decide

theorem q8_noncomm : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
    QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide

theorem q8_a_one_sq : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
    QuaternionGroup.a 2 := by decide

theorem q8_xa_zero_sq : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
    QuaternionGroup.a 2 := by decide

theorem q8_eq_a_pow (k : ZMod 4) : (QuaternionGroup.a k : QuaternionGroup 2) =
    QuaternionGroup.a 1 ^ k.val := by
  revert k; decide

theorem q8_eq_xa_mul (k : ZMod 4) : (QuaternionGroup.xa k : QuaternionGroup 2) =
    QuaternionGroup.xa 0 * QuaternionGroup.a 1 ^ k.val := by
  revert k; decide

structure Q8Data (z y : G) (K₁ K₂ : Subgroup G) : Prop where
  le1 : K₁ ≤ ascQ z
  le2 : K₂ ≤ ascQ z
  card1 : Nat.card ↥K₁ = 8
  card2 : Nat.card ↥K₂ = 8
  z1 : z ∈ K₁
  z2 : z ∈ K₂
  sq1 : ∀ k ∈ K₁, k ≠ 1 → k ≠ z → k * k = z
  sq2 : ∀ k ∈ K₂, k ≠ 1 → k ≠ z → k * k = z
  comm : ∀ k ∈ K₁, ∀ l ∈ K₂, k * l = l * k
  inter : ∀ k ∈ K₁, k ∈ K₂ → k = 1 ∨ k = z
  inv1 : ∀ k ∈ K₁, y * k * y⁻¹ ∈ K₁
  inv2 : ∀ k ∈ K₂, y * k * y⁻¹ ∈ K₂
  iso1 : Nonempty (↥K₁ ≃* QuaternionGroup 2)
  prod : ∀ q ∈ ascQ z, ∃ k ∈ K₁, ∃ l ∈ K₂, q = k * l
  cent2 : ∀ x ∈ ascQ z, (∀ k ∈ K₁, k * x = x * k) → x ∈ K₂

theorem exists_sq_eq_z [Finite G] (hyp : Asc03Hyp G z) : ∃ a ∈ ascQ z, a * a = z := by
  have hE := extraspecialAt_ascQ hyp
  by_contra hno
  push Not at hno
  have hsq : ∀ q ∈ ascQ z, q * q = 1 := fun q hq =>
    (hE.sq_mem q hq).resolve_right (hno q hq)
  have hab : ∀ a ∈ ascQ z, ∀ b ∈ ascQ z, a * b = b * a := by
    intro a ha b hb
    have h1 := hsq (a * b) (mul_mem ha hb)
    have h2 := hsq a ha
    have h3 := hsq b hb
    calc a * b = a * b * (b * a * (b * a)) := by rw [hsq _ (mul_mem hb ha), mul_one]
      _ = a * (b * b) * a * (b * a) := by group
      _ = (a * a) * (b * a) := by rw [h3]; group
      _ = b * a := by rw [h2, one_mul]
  have := hE.card_abelian_le le_rfl hab
  rw [hE.card_eq] at this
  omega

theorem noncomm_conj [Finite G] (hyp : Asc03Hyp G z) {y : G} (hy : y ∈ ascH z)
    (hy3 : orderOf y = 3) {a : G} (haQ : a ∈ ascQ z) (haa : a * a = z) :
    a * (y * a * y⁻¹) ≠ (y * a * y⁻¹) * a := by
  have hE := extraspecialAt_ascQ hyp
  intro hab
  set b := y * a * y⁻¹ with hb
  have hbQ : b ∈ ascQ z := conj_mem_ascQ hy haQ
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hy
    calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [this]
      _ = z := by group
  have hbb : b * b = z := by
    calc b * b = y * (a * a) * y⁻¹ := by rw [hb]; group
      _ = z := by rw [haa, hyz]
  set c := y * b * y⁻¹ with hc
  have hcc : c * c = z := by
    calc c * c = y * (b * b) * y⁻¹ := by rw [hc]; group
      _ = z := by rw [hbb, hyz]
  obtain ⟨w, hw, hwm⟩ : ∃ w, (w = 1 ∨ w = z) ∧ a * b * c = w := ⟨_, trip hyp hy hy3 haQ, rfl⟩
  have habab : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [haa, hbb, hE.sq_eq]
  have habQ : a * b ∈ ascQ z := mul_mem haQ hbQ
  have hceq : c = a * b * w := by
    have hinv : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right habab
    calc c = (a * b)⁻¹ * (a * b * c) := by group
      _ = a * b * w := by rw [hwm, hinv]
  have hwc : (a * b) * w = w * (a * b) := by
    rcases hw with rfl | rfl
    · simp
    · exact hE.central _ habQ
  have hww : w * w = 1 := by
    rcases hw with rfl | rfl
    · exact one_mul 1
    · exact hE.sq_eq
  have : c * c = 1 := by
    calc c * c = (a * b * w) * (a * b * w) := by rw [hceq]
      _ = (a * b) * (w * (a * b)) * w := by group
      _ = (a * b) * ((a * b) * w) * w := by rw [hwc]
      _ = ((a * b) * (a * b)) * (w * w) := by group
      _ = 1 := by rw [habab, hww, one_mul]
  exact hE.ne_one (hcc.symm.trans this)

theorem exists_q8Data [Finite G] (hyp : Asc03Hyp G z) {y : G} (hy : y ∈ ascH z)
    (hy3 : orderOf y = 3) : ∃ K₁ K₂ : Subgroup G, Q8Data z y K₁ K₂ := by
  have hE := extraspecialAt_ascQ hyp
  obtain ⟨a, haQ, haa⟩ := exists_sq_eq_z hyp
  set b := y * a * y⁻¹ with hb
  have hbQ : b ∈ ascQ z := conj_mem_ascQ hy haQ
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hy
    calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [this]
      _ = z := by group
  have hbb : b * b = z := by
    calc b * b = y * (a * a) * y⁻¹ := by rw [hb]; group
      _ = z := by rw [haa, hyz]
  have hab : a * b ≠ b * a := noncomm_conj hyp hy hy3 haQ haa
  have ha1 : a ≠ 1 := by
    intro h; rw [h, one_mul] at haa; exact hE.ne_one haa.symm
  have haz : a ≠ z := by
    intro h; rw [h, hE.sq_eq] at haa; exact hE.ne_one haa.symm
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hE.sq_eq
  have hainv : a⁻¹ = z * a := by
    have : a * (z * a) = 1 := by
      calc a * (z * a) = a * (a * z) := by rw [hE.central a haQ]
        _ = (a * a) * z := by group
        _ = 1 := by rw [haa, hE.sq_eq]
    exact inv_eq_of_mul_eq_one_right this
  have hrel : b * a * b⁻¹ = a⁻¹ := by
    rcases hE.comm_mem b hbQ a haQ with h | h
    · exfalso; apply hab
      calc a * b = (b * a * b⁻¹ * a⁻¹)⁻¹ * (b * a) := by group
        _ = b * a := by rw [h]; group
    · calc b * a * b⁻¹ = (b * a * b⁻¹ * a⁻¹) * a := by group
        _ = z * a := by rw [h]
        _ = a⁻¹ := hainv.symm
  have ha4 : orderOf a = 4 := by
    have h1 : ¬ a ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two, haa]; exact hE.ne_one
    have h2 : a ^ 2 ^ (1 + 1) = 1 := by
      calc a ^ 2 ^ (1 + 1) = (a * a) * (a * a) := by norm_num [pow_succ, mul_assoc]
        _ = 1 := by rw [haa, hE.sq_eq]
    have := orderOf_eq_prime_pow h1 h2
    simpa using this
  have hjj : b * b = a * a := by rw [hbb, haa]
  set ψ := q8Hom a b ha4 hjj hrel with hψ
  have hinj : Function.Injective ψ := q8Hom_injective
  have hψa : ψ (QuaternionGroup.a 1) = a := by
    rw [hψ, q8Hom_a, show (1 : ZMod 4).val = 1 by decide, pow_one]
  have hψxa : ψ (QuaternionGroup.xa 0) = b := by
    rw [hψ, q8Hom_xa, show (0 : ZMod 4).val = 0 by decide, pow_zero, mul_one]
  have hψz : ψ (QuaternionGroup.a 2) = z := by
    rw [hψ, q8Hom_a, show (2 : ZMod 4).val = 2 by decide, pow_two, haa]
  set K₁ := ψ.range with hK₁
  have hmem : ∀ k ∈ K₁, ∃ m : ℕ, k = a ^ m ∨ k = b * a ^ m := by
    rintro k ⟨g, rfl⟩
    rcases g with m | m
    · exact ⟨m.val, Or.inl rfl⟩
    · exact ⟨m.val, Or.inr rfl⟩
  have haK : a ∈ K₁ := ⟨_, hψa⟩
  have hbK : b ∈ K₁ := ⟨_, hψxa⟩
  have hzK : z ∈ K₁ := ⟨_, hψz⟩
  have hK1Q : K₁ ≤ ascQ z := by
    intro k hk
    obtain ⟨m, rfl | rfl⟩ := hmem k hk
    · exact pow_mem haQ m
    · exact mul_mem hbQ (pow_mem haQ m)
  have hK1card : Nat.card ↥K₁ = 8 := by
    rw [hK₁, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcentK : ∀ x : G, x * a = a * x → x * b = b * x → ∀ k ∈ K₁, x * k = k * x := by
    intro x hxa hxb k hk
    obtain ⟨m, rfl | rfl⟩ := hmem k hk
    · exact ((Commute.pow_right (show Commute x a from hxa) m)).eq
    · exact (Commute.mul_right (show Commute x b from hxb)
        (Commute.pow_right (show Commute x a from hxa) m)).eq
  have hcenter : ∀ k ∈ K₁, k * a = a * k → k * b = b * k → k = 1 ∨ k = z := by
    rintro k ⟨g, rfl⟩ hka hkb
    have h1 : g * QuaternionGroup.a 1 = QuaternionGroup.a 1 * g := by
      apply hinj; rw [map_mul, map_mul, hψa]; exact hka
    have h2 : g * QuaternionGroup.xa 0 = QuaternionGroup.xa 0 * g := by
      apply hinj; rw [map_mul, map_mul, hψxa]; exact hkb
    rcases q8_center g h1 h2 with rfl | rfl
    · left; exact map_one ψ
    · right; exact hψz
  have hsq1 : ∀ k ∈ K₁, k ≠ 1 → k ≠ z → k * k = z := by
    rintro k ⟨g, rfl⟩ hk1 hkz
    have hg1 : g ≠ 1 := by rintro rfl; exact hk1 (map_one ψ)
    have hg2 : g ≠ QuaternionGroup.a 2 := by rintro rfl; exact hkz hψz
    rw [← map_mul, q8_sq_of_ne g hg1 hg2, hψz]
  set c := y * b * y⁻¹ with hc
  obtain ⟨w, hw, hwm⟩ : ∃ w, (w = 1 ∨ w = z) ∧ a * b * c = w := ⟨_, trip hyp hy hy3 haQ, rfl⟩
  have hwK : w ∈ K₁ := by rcases hw with rfl | rfl; exact one_mem _; exact hzK
  have hcK : c ∈ K₁ := by
    have : c = (a * b)⁻¹ * w := by rw [← hwm]; group
    rw [this]; exact mul_mem (inv_mem (mul_mem haK hbK)) hwK
  have hinv1 : ∀ k ∈ K₁, y * k * y⁻¹ ∈ K₁ := by
    intro k hk
    obtain ⟨m, rfl | rfl⟩ := hmem k hk
    · have : y * a ^ m * y⁻¹ = b ^ m := by rw [hb, conj_pow]
      rw [this]; exact pow_mem hbK m
    · have : y * (b * a ^ m) * y⁻¹ = c * b ^ m := by
        rw [hc, hb, conj_pow]; group
      rw [this]; exact mul_mem hcK (pow_mem hbK m)
  set K₂ := ascQ z ⊓ Subgroup.centralizer (K₁ : Set G) with hK₂
  have hK2Q : K₂ ≤ ascQ z := inf_le_left
  have hmemK2 : ∀ x : G, x ∈ K₂ ↔ x ∈ ascQ z ∧ ∀ k ∈ K₁, k * x = x * k := by
    intro x
    rw [hK₂, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    rfl
  have hzK2 : z ∈ K₂ := (hmemK2 z).2 ⟨hE.mem, fun k hk => hE.central k (hK1Q hk)⟩
  have hcomm : ∀ k ∈ K₁, ∀ l ∈ K₂, k * l = l * k := fun k hk l hl => ((hmemK2 l).1 hl).2 k hk
  have hinter : ∀ k ∈ K₁, k ∈ K₂ → k = 1 ∨ k = z := by
    intro k hk hk2
    exact hcenter k hk (hcomm a haK k hk2).symm (hcomm b hbK k hk2).symm
  have hinv2 : ∀ l ∈ K₂, y * l * y⁻¹ ∈ K₂ := by
    intro l hl
    rw [hmemK2]
    refine ⟨conj_mem_ascQ hy ((hmemK2 l).1 hl).1, fun k hk => ?_⟩
    have hk' : y⁻¹ * k * y ∈ K₁ := inv_conj_mem hy3 hinv1 hk
    have h := hcomm _ hk' l hl
    calc k * (y * l * y⁻¹) = y * ((y⁻¹ * k * y) * l) * y⁻¹ := by group
      _ = y * (l * (y⁻¹ * k * y)) * y⁻¹ := by rw [h]
      _ = y * l * y⁻¹ * k := by group
  have hK2card : Nat.card ↥K₂ = 8 := by
    apply le_antisymm
    · have hi : Nat.card ↥(K₁ ⊓ K₂) ≤ 2 := card_le_two_of_forall (fun k hk => hinter k hk.1 hk.2)
      have := card_mul_card_le_inf hK1Q hK2Q
      rw [hK1card, hE.card_eq] at this
      nlinarith
    · obtain ⟨h16, -⟩ := hE.exists_sq_eq_of_noncentral haQ ha1 haz
      have h2 := card_le_two_mul_card_centralizer hE.sq_eq (A := ascQ z ⊓ Subgroup.centralizer {a})
        b (fun x hx => hE.comm_mem x hx.1 b hbQ) (fun x hx => hE.central x hx.1)
      rw [h16] at h2
      have hle : (ascQ z ⊓ Subgroup.centralizer {a}) ⊓ Subgroup.centralizer {b} ≤ K₂ := by
        intro x hx
        rw [hmemK2]
        refine ⟨hx.1.1, fun k hk => ?_⟩
        have hxa := Subgroup.mem_centralizer_singleton_iff.1 hx.1.2
        have hxb := Subgroup.mem_centralizer_singleton_iff.1 hx.2
        exact (hcentK x hxa hxb k hk).symm
      have := Subgroup.card_le_of_le hle
      omega
  have hsq2 : ∀ l ∈ K₂, l ≠ 1 → l ≠ z → l * l = z := by
    intro l hl hl1 hlz
    have hlQ := hK2Q hl
    by_contra hne
    have hl2 : l * l = 1 := (hE.sq_mem l hlQ).resolve_right hne
    obtain ⟨hLQ, hL8, hLe, hzL, -, -, -⟩ := lineOf_facts hyp hy hy3 hlQ hl2 hl1 hlz
    have hLK : lineOf z l y ≤ K₂ := by
      refine (Subgroup.closure_le _).2 ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hzK2
      · exact hl
      · exact hinv2 l hl
    have hLeq : lineOf z l y = K₂ := Subgroup.eq_of_le_of_card_ge hLK (by rw [hL8, hK2card])
    have hK2ab : ∀ u ∈ K₂, ∀ v ∈ K₂, u * v = v * u := by
      rw [← hLeq]; exact fun u hu v hv => (hLe u hu v hv).2
    have hS : ∀ u ∈ (K₂ : Set G) ∪ {a}, ∀ v ∈ (K₂ : Set G) ∪ {a}, u * v = v * u := by
      rintro u (hu | hu) v (hv | hv)
      · exact hK2ab u hu v hv
      · rw [Set.mem_singleton_iff.1 hv]; exact (hcomm a haK u hu).symm
      · rw [Set.mem_singleton_iff.1 hu]; exact hcomm a haK v hv
      · rw [Set.mem_singleton_iff.1 hu, Set.mem_singleton_iff.1 hv]
    have hcl := Subgroup.isMulCommutative_closure (k := (K₂ : Set G) ∪ {a})
      (fun u hu v hv _ => hS u hu v hv)
    set B := Subgroup.closure ((K₂ : Set G) ∪ {a}) with hB
    have hBab : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := by
      intro u hu v hv
      exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨u, hu⟩ : B) ⟨v, hv⟩)
    have hBQ : B ≤ ascQ z := (Subgroup.closure_le _).2
      (Set.union_subset (fun x hx => hK2Q hx) (Set.singleton_subset_iff.2 haQ))
    have haK2 : a ∉ K₂ := by
      intro h
      rcases hinter a haK h with h' | h'
      · exact ha1 h'
      · exact haz h'
    have hlt : K₂ < B := lt_of_le_of_ne (fun x hx => Subgroup.subset_closure (Or.inl hx))
      (fun h => haK2 (h ▸ Subgroup.subset_closure (Or.inr rfl)))
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := hE.card_abelian_le hBQ hBab
    omega
  have hprod : ∀ q ∈ ascQ z, ∃ k ∈ K₁, ∃ l ∈ K₂, q = k * l := by
    let M : Subgroup G :=
      { carrier := {x | ∃ k ∈ K₁, ∃ l ∈ K₂, x = k * l}
        one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨k, hk, l, hl, rfl⟩ ⟨k', hk', l', hl', rfl⟩
          refine ⟨k * k', mul_mem hk hk', l * l', mul_mem hl hl', ?_⟩
          have := hcomm k' hk' l hl
          calc k * l * (k' * l') = k * (l * k') * l' := by group
            _ = k * (k' * l) * l' := by rw [this]
            _ = k * k' * (l * l') := by group
        inv_mem' := by
          rintro _ ⟨k, hk, l, hl, rfl⟩
          refine ⟨k⁻¹, inv_mem hk, l⁻¹, inv_mem hl, ?_⟩
          have := hcomm k⁻¹ (inv_mem hk) l⁻¹ (inv_mem hl)
          rw [mul_inv_rev, this] }
    have hK1M : K₁ ≤ M := fun k hk => ⟨k, hk, 1, one_mem _, by simp⟩
    have hK2M : K₂ ≤ M := fun l hl => ⟨1, one_mem _, l, hl, by simp⟩
    have hMQ : M ≤ ascQ z := by
      rintro _ ⟨k, hk, l, hl, rfl⟩
      exact mul_mem (hK1Q hk) (hK2Q hl)
    have hsup := card_mul_card_le_sup K₁ K₂
    have hi : Nat.card ↥(K₁ ⊓ K₂) ≤ 2 := card_le_two_of_forall (fun k hk => hinter k hk.1 hk.2)
    rw [hK1card, hK2card] at hsup
    have hsupM : Nat.card ↥(K₁ ⊔ K₂) ≤ Nat.card ↥M := Subgroup.card_le_of_le (sup_le hK1M hK2M)
    have hMcard : Nat.card ↥M = 32 := by
      have := Subgroup.card_le_of_le hMQ
      rw [hE.card_eq] at this
      nlinarith
    have hMeq : M = ascQ z := Subgroup.eq_of_le_of_card_ge hMQ (by rw [hMcard, hE.card_eq])
    intro q hq
    rw [← hMeq] at hq
    exact hq
  exact ⟨K₁, K₂, ⟨hK1Q, hK2Q, hK1card, hK2card, hzK, hzK2, hsq1, hsq2, hcomm, hinter, hinv1,
    hinv2, ⟨(MonoidHom.ofInjective hinj).symm⟩, hprod, fun x hx hxk => (hmemK2 x).2 ⟨hx, hxk⟩⟩⟩

namespace Q8Data

variable {y : G} {K₁ K₂ : Subgroup G}

theorem mem_or_mem [Finite G] (hyp : Asc03Hyp G z) (hd : Q8Data z y K₁ K₂) {q : G}
    (hq : q ∈ ascQ z) (hqq : q * q = z) : q ∈ K₁ ∨ q ∈ K₂ := by
  have hE := extraspecialAt_ascQ hyp
  obtain ⟨k, hk, l, hl, rfl⟩ := hd.prod q hq
  have hkl := hd.comm k hk l hl
  have hsq : k * l * (k * l) = (k * k) * (l * l) := by
    calc k * l * (k * l) = k * (l * k) * l := by group
      _ = k * (k * l) * l := by rw [hkl]
      _ = (k * k) * (l * l) := by group
  rw [hsq] at hqq
  by_cases hk1 : k = 1 ∨ k = z
  · right
    rcases hk1 with rfl | rfl
    · simpa using hl
    · exact mul_mem hd.z2 hl
  · left
    push Not at hk1
    have hkk := hd.sq1 k hk hk1.1 hk1.2
    rw [hkk] at hqq
    have hll : l * l = 1 := by
      have := congrArg (fun x => z⁻¹ * x) hqq
      simpa using this
    by_cases hl1 : l = 1 ∨ l = z
    · rcases hl1 with rfl | rfl
      · simpa using hk
      · exact mul_mem hk hd.z1
    · push Not at hl1
      have := hd.sq2 l hl hl1.1 hl1.2
      rw [hll] at this
      exact absurd this.symm hE.ne_one

theorem ne (hd : Q8Data z y K₁ K₂) : K₁ ≠ K₂ := by
  intro h
  have : Nat.card ↥K₁ ≤ 2 := card_le_two_of_forall (fun k hk => hd.inter k hk (h ▸ hk))
  rw [hd.card1] at this
  omega

end Q8Data

theorem le_of_q8_gens {K L : Subgroup G} (e : ↥K ≃* QuaternionGroup 2)
    (h1 : ((e.symm (QuaternionGroup.a 1) : ↥K) : G) ∈ L)
    (h2 : ((e.symm (QuaternionGroup.xa 0) : ↥K) : G) ∈ L) : K ≤ L := by
  intro x hx
  have hxe : (⟨x, hx⟩ : ↥K) = e.symm (e ⟨x, hx⟩) := (e.symm_apply_apply _).symm
  have hval : x = ((e.symm (e ⟨x, hx⟩) : ↥K) : G) := congrArg Subtype.val hxe
  rw [hval]
  generalize e ⟨x, hx⟩ = g
  rcases g with m | m
  · rw [q8_eq_a_pow m, map_pow, Subgroup.coe_pow]
    exact pow_mem h1 _
  · rw [q8_eq_xa_mul m, map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow]
    exact mul_mem h2 (pow_mem h1 _)

namespace Q8Data

variable {y : G} {K₁ K₂ : Subgroup G}

theorem eq_or_eq [Finite G] (hyp : Asc03Hyp G z) (hd : Q8Data z y K₁ K₂) {K : Subgroup G}
    (hKQ : K ≤ ascQ z) (e : ↥K ≃* QuaternionGroup 2) : K = K₁ ∨ K = K₂ := by
  have hE := extraspecialAt_ascQ hyp
  set k1 : G := ((e.symm (QuaternionGroup.a 1) : ↥K) : G) with hk1
  set k2 : G := ((e.symm (QuaternionGroup.xa 0) : ↥K) : G) with hk2
  set kz : G := ((e.symm (QuaternionGroup.a 2) : ↥K) : G) with hkz
  have hk1K : k1 ∈ K := (e.symm _).2
  have hk2K : k2 ∈ K := (e.symm _).2
  have hcomm8 : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 *
      (QuaternionGroup.a 1)⁻¹ * (QuaternionGroup.xa 0)⁻¹ = QuaternionGroup.a 2 := by decide
  have hc : k1 * k2 * k1⁻¹ * k2⁻¹ = kz := by
    have := congrArg (fun g => ((e.symm g : ↥K) : G)) hcomm8
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hnc : k1 * k2 ≠ k2 * k1 := by
    intro h
    apply q8_noncomm
    apply e.symm.injective
    apply Subtype.ext
    simpa only [map_mul, Subgroup.coe_mul] using h
  have hkzz : kz = z := by
    rcases hE.comm_mem k1 (hKQ hk1K) k2 (hKQ hk2K) with h | h
    · exfalso; apply hnc
      calc k1 * k2 = (k1 * k2 * k1⁻¹ * k2⁻¹) * (k2 * k1) := by group
        _ = k2 * k1 := by rw [h, one_mul]
    · rw [← hc, h]
  have hk1sq : k1 * k1 = z := by
    rw [← hkzz]
    have := congrArg (fun g => ((e.symm g : ↥K) : G)) q8_a_one_sq
    simpa only [map_mul, Subgroup.coe_mul] using this
  have hk2sq : k2 * k2 = z := by
    rw [← hkzz]
    have := congrArg (fun g => ((e.symm g : ↥K) : G)) q8_xa_zero_sq
    simpa only [map_mul, Subgroup.coe_mul] using this
  have hK8 : Nat.card ↥K = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  rcases hd.mem_or_mem hyp (hKQ hk1K) hk1sq with h1 | h1 <;>
    rcases hd.mem_or_mem hyp (hKQ hk2K) hk2sq with h2 | h2
  · left
    exact Subgroup.eq_of_le_of_card_ge (le_of_q8_gens e h1 h2) (by rw [hK8, hd.card1])
  · exact absurd (hd.comm k1 h1 k2 h2) hnc
  · exact absurd (hd.comm k2 h2 k1 h1).symm hnc
  · right
    exact Subgroup.eq_of_le_of_card_ge (le_of_q8_gens e h1 h2) (by rw [hK8, hd.card2])

theorem conj_eq_or_eq [Finite G] (hyp : Asc03Hyp G z) (hd : Q8Data z y K₁ K₂) {h : G}
    (hh : h ∈ ascH z) :
    K₁.map (MulAut.conj h).toMonoidHom = K₁ ∨ K₁.map (MulAut.conj h).toMonoidHom = K₂ := by
  obtain ⟨e⟩ := hd.iso1
  apply hd.eq_or_eq hyp
  · rintro _ ⟨k, hk, rfl⟩
    exact conj_mem_ascQ hh (hd.le1 hk)
  · exact (Subgroup.equivMapOfInjective K₁ (MulAut.conj h).toMonoidHom
      (MulAut.conj h).injective).symm.trans e

end Q8Data

theorem ascH_le_of_gens [Finite G] (hyp : Asc03Hyp G z) {N : Subgroup G} (hQN : ascQ z ≤ N)
    {y v : G} (hy : y ∈ ascH z) (hy3 : orderOf y = 3) (hyN : y ∈ N) (hv : v ∈ ascH z)
    (hvQ : v ∉ ascQ z) (hv2 : v * v = 1) (hvN : v ∈ N) : ascH z ≤ N := by
  set N' := N.subgroupOf (ascH z) with hN'
  set R := N'.map (rho hyp) with hR
  have hyR : rho hyp ⟨y, hy⟩ ∈ R := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hyN)
  have hvR : rho hyp ⟨v, hv⟩ ∈ R := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hvN)
  have hy1 : rho hyp ⟨y, hy⟩ ≠ 1 := by
    rw [Ne, rho_eq_one_iff]; exact not_mem_ascQ_of_order_three hyp hy3
  have hv1 : rho hyp ⟨v, hv⟩ ≠ 1 := by
    rw [Ne, rho_eq_one_iff]; exact hvQ
  have hy3' : orderOf (rho hyp ⟨y, hy⟩) = 3 := by
    refine orderOf_eq_prime ?_ hy1
    rw [← map_pow]
    have : (⟨y, hy⟩ : ↥(ascH z)) ^ 3 = 1 := by
      apply Subtype.ext; simp [← hy3, pow_orderOf_eq_one]
    rw [this, map_one]
  have hv2' : orderOf (rho hyp ⟨v, hv⟩) = 2 := by
    refine orderOf_eq_prime ?_ hv1
    rw [← map_pow]
    have : (⟨v, hv⟩ : ↥(ascH z)) ^ 2 = 1 := by
      apply Subtype.ext; simp [pow_two, hv2]
    rw [this, map_one]
  have h3 : 3 ∣ Nat.card ↥R := by
    have := orderOf_dvd_natCard (⟨_, hyR⟩ : ↥R)
    rwa [Subgroup.orderOf_mk, hy3'] at this
  have h2 : 2 ∣ Nat.card ↥R := by
    have := orderOf_dvd_natCard (⟨_, hvR⟩ : ↥R)
    rwa [Subgroup.orderOf_mk, hv2'] at this
  have hS3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  have h6 : Nat.card ↥R = 6 := by
    have hle : Nat.card ↥R ≤ 6 := by
      have := Subgroup.card_le_card_group R
      rwa [hS3] at this
    have hpos : 0 < Nat.card ↥R := Nat.card_pos
    omega
  have hRtop : R = ⊤ := Subgroup.eq_top_of_card_eq R (by rw [h6, hS3])
  intro h hh
  have : rho hyp ⟨h, hh⟩ ∈ R := by rw [hRtop]; exact Subgroup.mem_top _
  obtain ⟨n, hn, hne⟩ := Subgroup.mem_map.1 this
  have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.1 hn
  have hq : ((n⁻¹ * ⟨h, hh⟩ : ↥(ascH z)) : G) ∈ ascQ z := by
    rw [← rho_eq_one_iff hyp, map_mul, map_inv, hne, inv_mul_cancel]
  have : h = (n : G) * ((n⁻¹ * ⟨h, hh⟩ : ↥(ascH z)) : G) := by simp
  rw [this]
  exact mul_mem hnN (hQN hq)

theorem map_of_mem_q8Subgroups {K : Subgroup ↥(ascH z)}
    (hK : K ∈ q8Subgroups (CFSG.pCore 2 ↥(ascH z))) :
    K.map (ascH z).subtype ≤ ascQ z ∧
      Nonempty (↥(K.map (ascH z).subtype) ≃* QuaternionGroup 2) := by
  obtain ⟨hKQ, ⟨e⟩⟩ := hK
  refine ⟨?_, ⟨(Subgroup.equivMapOfInjective K (ascH z).subtype
    (ascH z).subtype_injective).symm.trans e⟩⟩
  rintro _ ⟨k, hk, rfl⟩
  rw [mem_ascQ_iff]
  exact ⟨k.2, hKQ hk⟩

theorem subgroupOf_mem_q8Subgroups {K : Subgroup G} (hKQ : K ≤ ascQ z)
    (e : Nonempty (↥K ≃* QuaternionGroup 2)) :
    K.subgroupOf (ascH z) ∈ q8Subgroups (CFSG.pCore 2 ↥(ascH z)) := by
  obtain ⟨e⟩ := e
  refine ⟨fun k hk => ?_, ⟨(Subgroup.subgroupOfEquivOfLe
    (hKQ.trans (ascQ_le_ascH z))).trans e⟩⟩
  have := hKQ (Subgroup.mem_subgroupOf.1 hk)
  rw [mem_ascQ_iff] at this
  obtain ⟨_, h⟩ := this
  exact h

theorem normal_iff_conj {K : Subgroup ↥(ascH z)} :
    K.Normal ↔ ∀ h ∈ ascH z, ∀ k ∈ K.map (ascH z).subtype,
      h * k * h⁻¹ ∈ K.map (ascH z).subtype := by
  constructor
  · rintro hn h hh _ ⟨k, hk, rfl⟩
    exact ⟨_, hn.conj_mem k hk ⟨h, hh⟩, rfl⟩
  · intro hc
    refine ⟨fun k hk h => ?_⟩
    obtain ⟨k', hk', hk'e⟩ := hc h h.2 k ⟨k, hk, rfl⟩
    have : k' = h * k * h⁻¹ := Subtype.ext hk'e
    rw [← this]; exact hk'

theorem subgroupOf_normal {K : Subgroup G} (hKH : K ≤ ascH z)
    (hc : ∀ h ∈ ascH z, ∀ k ∈ K, h * k * h⁻¹ ∈ K) : (K.subgroupOf (ascH z)).Normal := by
  rw [normal_iff_conj]
  rintro h hh _ ⟨k, hk, rfl⟩
  exact ⟨⟨_, (ascH z).mul_mem ((ascH z).mul_mem hh (hKH (Subgroup.mem_subgroupOf.1 hk)))
    ((ascH z).inv_mem hh)⟩,
    Subgroup.mem_subgroupOf.2 (hc h hh _ (Subgroup.mem_subgroupOf.1 hk)), rfl⟩

theorem all_normal_of_exists [Finite G] (hyp : Asc03Hyp G z) {y : G} {K₁ K₂ : Subgroup G}
    (hd : Q8Data z y K₁ K₂) (h : ∃ K ∈ q8Subgroups (CFSG.pCore 2 ↥(ascH z)), K.Normal) :
    ∀ K ∈ q8Subgroups (CFSG.pCore 2 ↥(ascH z)), K.Normal := by
  obtain ⟨K0, hK0, hK0n⟩ := h
  obtain ⟨hK0Q, ⟨e0⟩⟩ := map_of_mem_q8Subgroups hK0
  have hK0c := normal_iff_conj.1 hK0n
  have hne := hd.ne
  have hK1 : ∀ h ∈ ascH z, ∀ k ∈ K₁, h * k * h⁻¹ ∈ K₁ := by
    rcases hd.eq_or_eq hyp hK0Q e0 with h0 | h0
    · rw [h0] at hK0c; exact hK0c
    · rw [h0] at hK0c
      intro h hh k hk
      rcases hd.conj_eq_or_eq hyp hh with h1 | h1
      · rw [← h1]; exact ⟨k, hk, rfl⟩
      · exfalso
        apply hne
        have hle : K₁ ≤ K₂ := by
          intro x hx
          have hmem : h * x * h⁻¹ ∈ K₂ := by rw [← h1]; exact ⟨x, hx, rfl⟩
          have := hK0c h⁻¹ (inv_mem hh) _ hmem
          simpa [mul_assoc] using this
        exact Subgroup.eq_of_le_of_card_ge hle (by rw [hd.card1, hd.card2])
  have hK2 : ∀ h ∈ ascH z, ∀ l ∈ K₂, h * l * h⁻¹ ∈ K₂ := by
    intro h hh l hl
    refine hd.cent2 _ (conj_mem_ascQ hh (hd.le2 hl)) fun k hk => ?_
    have hk' : h⁻¹ * k * h ∈ K₁ := by simpa using hK1 h⁻¹ (inv_mem hh) k hk
    have := hd.comm _ hk' l hl
    calc k * (h * l * h⁻¹) = h * ((h⁻¹ * k * h) * l) * h⁻¹ := by group
      _ = h * (l * (h⁻¹ * k * h)) * h⁻¹ := by rw [this]
      _ = h * l * h⁻¹ * k := by group
  intro K hK
  obtain ⟨hKQ, ⟨e⟩⟩ := map_of_mem_q8Subgroups hK
  rw [normal_iff_conj]
  rcases hd.eq_or_eq hyp hKQ e with h1 | h1 <;> rw [h1]
  · exact hK1
  · exact hK2

theorem conj_eq_K₂ [Finite G] (hyp : Asc03Hyp G z) {y : G} {K₁ K₂ : Subgroup G}
    (hd : Q8Data z y K₁ K₂) (hy : y ∈ ascH z) (hy3 : orderOf y = 3)
    (h : ¬ ∃ K ∈ q8Subgroups (CFSG.pCore 2 ↥(ascH z)), K.Normal) {v : G} (hv : v ∈ ascH z)
    (hvQ : v ∉ ascQ z) (hv2 : v * v = 1) : K₁.map (MulAut.conj v).toMonoidHom = K₂ := by
  have hE := extraspecialAt_ascQ hyp
  rcases hd.conj_eq_or_eq hyp hv with h1 | h1
  · exfalso
    apply h
    have hQN : ascQ z ≤ Subgroup.normalizer (K₁ : Set G) := fun q hq =>
      mem_normalizer_of_conj (fun k hk => conj_mem_of_z_mem hE hd.le1 hd.z1 hq hk)
    have hyN : y ∈ Subgroup.normalizer (K₁ : Set G) := mem_normalizer_of_conj hd.inv1
    have hvN : v ∈ Subgroup.normalizer (K₁ : Set G) := mem_normalizer_of_conj (fun k hk => by
      rw [← h1]; exact ⟨k, hk, rfl⟩)
    have hHN := ascH_le_of_gens hyp hQN hy hy3 hyN hv hvQ hv2 hvN
    refine ⟨K₁.subgroupOf (ascH z), subgroupOf_mem_q8Subgroups hd.le1 hd.iso1,
      subgroupOf_normal (hd.le1.trans (ascQ_le_ascH z)) fun g hg k hk => ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (hHN hg) k).1 hk
  · exact h1

end CFSG.GH74.M12.Thm1
