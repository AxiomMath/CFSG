module

public import CFSG.CGT.Foote81L6.Bridge.SD

public section

namespace CFSG.CGT.Foote81L6.Bridge

@[ext] structure PHat (n : ℕ) where
  x₁ : SD n
  x₂ : SD n
  x₃ : SD n
  e : ZMod 2
deriving DecidableEq

namespace PHat

variable {n : ℕ}

@[expose] def sw₁ (e : ZMod 2) (y : PHat n) : SD n := if e = 0 then y.x₁ else y.x₂

@[expose] def sw₂ (e : ZMod 2) (y : PHat n) : SD n := if e = 0 then y.x₂ else y.x₁

@[simp] theorem sw₁_zero (y : PHat n) : sw₁ 0 y = y.x₁ := rfl

@[simp] theorem sw₁_one (y : PHat n) : sw₁ 1 y = y.x₂ := rfl

@[simp] theorem sw₂_zero (y : PHat n) : sw₂ 0 y = y.x₂ := rfl

@[simp] theorem sw₂_one (y : PHat n) : sw₂ 1 y = y.x₁ := rfl

instance : Mul (PHat n) :=
  ⟨fun a b => ⟨a.x₁ * sw₁ a.e b, a.x₂ * sw₂ a.e b, a.x₃ * b.x₃, a.e + b.e⟩⟩

instance : One (PHat n) := ⟨⟨1, 1, 1, 0⟩⟩

instance : Inv (PHat n) := ⟨fun a => ⟨(sw₁ a.e a)⁻¹, (sw₂ a.e a)⁻¹, a.x₃⁻¹, a.e⟩⟩

@[simp] theorem mul_x₁ (a b : PHat n) : (a * b).x₁ = a.x₁ * sw₁ a.e b := rfl

@[simp] theorem mul_x₂ (a b : PHat n) : (a * b).x₂ = a.x₂ * sw₂ a.e b := rfl

@[simp] theorem mul_x₃ (a b : PHat n) : (a * b).x₃ = a.x₃ * b.x₃ := rfl

@[simp] theorem mul_e (a b : PHat n) : (a * b).e = a.e + b.e := rfl

@[simp] theorem one_x₁ : (1 : PHat n).x₁ = 1 := rfl

@[simp] theorem one_x₂ : (1 : PHat n).x₂ = 1 := rfl

@[simp] theorem one_x₃ : (1 : PHat n).x₃ = 1 := rfl

@[simp] theorem one_e : (1 : PHat n).e = 0 := rfl

@[simp] theorem inv_x₁ (a : PHat n) : a⁻¹.x₁ = (sw₁ a.e a)⁻¹ := rfl

@[simp] theorem inv_x₂ (a : PHat n) : a⁻¹.x₂ = (sw₂ a.e a)⁻¹ := rfl

@[simp] theorem inv_x₃ (a : PHat n) : a⁻¹.x₃ = a.x₃⁻¹ := rfl

@[simp] theorem inv_e (a : PHat n) : a⁻¹.e = a.e := rfl

theorem one_add_one_zmod_two : (1 : ZMod 2) + 1 = 0 := rfl

theorem one_add_one_add_zmod_two (x : ZMod 2) : 1 + (1 + x) = x := by
  rw [← add_assoc, one_add_one_zmod_two, zero_add]

instance : Group (PHat n) :=
  Group.ofLeftAxioms
    (fun a b c => by
      obtain ⟨a₁, a₂, a₃, ae⟩ := a
      obtain ⟨b₁, b₂, b₃, be⟩ := b
      rcases zmod_two_eq_zero_or_one ae with rfl | rfl <;>
        rcases zmod_two_eq_zero_or_one be with rfl | rfl <;>
        ext <;> simp [mul_assoc, add_assoc, one_add_one_zmod_two, one_add_one_add_zmod_two])
    (fun a => by ext <;> simp)
    (fun a => by
      obtain ⟨a₁, a₂, a₃, ae⟩ := a
      rcases zmod_two_eq_zero_or_one ae with rfl | rfl <;>
        ext <;> simp [one_add_one_zmod_two])

@[expose] def det (a : PHat n) : ZMod 2 := a.x₁.det + a.x₂.det + a.x₃.det

theorem det_mul (a b : PHat n) : (a * b).det = a.det + b.det := by
  obtain ⟨a₁, a₂, a₃, ae⟩ := a
  rcases zmod_two_eq_zero_or_one ae with rfl | rfl <;>
    · simp only [det, mul_x₁, mul_x₂, mul_x₃, SD.det_mul, sw₁_zero, sw₂_zero, sw₁_one, sw₂_one]
      ring

@[expose] def detHom : PHat n →* Multiplicative (ZMod 2) where
  toFun a := Multiplicative.ofAdd a.det
  map_one' := by simp [det]
  map_mul' a b := by rw [det_mul, ofAdd_add]

theorem detHom_surjective : Function.Surjective (detHom (n := n)) := by
  intro d
  rcases zmod_two_eq_zero_or_one d.toAdd with h | h
  · refine ⟨1, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [map_one, toAdd_one, h]
  · refine ⟨⟨SD.σ, 1, 1, 0⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    change det _ = d.toAdd
    simp [det, SD.det_σ, h]

@[expose] def equivProd : PHat n ≃ SD n × SD n × SD n × ZMod 2 where
  toFun a := (a.x₁, a.x₂, a.x₃, a.e)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (PHat n) := Fintype.ofEquiv _ equivProd.symm

instance : Finite (PHat n) := Finite.of_equiv _ equivProd.symm

theorem card : Nat.card (PHat n) = 2 ^ (3 * n + 4) := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod, Nat.card_prod, SD.card,
    Nat.card_zmod]
  ring

@[expose] def blockHom : SD n × SD n × SD n →* PHat n where
  toFun x := ⟨x.1, x.2.1, x.2.2, 0⟩
  map_one' := rfl
  map_mul' x y := by ext <;> simp

theorem blockHom_apply (x : SD n × SD n × SD n) : blockHom x = ⟨x.1, x.2.1, x.2.2, 0⟩ := rfl

theorem blockHom_injective : Function.Injective (blockHom (n := n)) := by
  intro x y h
  have h1 := congrArg PHat.x₁ h
  have h2 := congrArg PHat.x₂ h
  have h3 := congrArg PHat.x₃ h
  exact Prod.ext h1 (Prod.ext h2 h3)

theorem mk_zero_pow (x₁ x₂ x₃ : SD n) (k : ℕ) :
    (⟨x₁, x₂, x₃, 0⟩ : PHat n) ^ k = ⟨x₁ ^ k, x₂ ^ k, x₃ ^ k, 0⟩ := by
  rw [show (⟨x₁, x₂, x₃, 0⟩ : PHat n) = blockHom (x₁, x₂, x₃) from rfl, ← map_pow]
  rfl

theorem orderOf_mk_zero (x₁ x₂ x₃ : SD n) :
    orderOf (⟨x₁, x₂, x₃, 0⟩ : PHat n) = orderOf (x₁, x₂, x₃) := by
  rw [show (⟨x₁, x₂, x₃, 0⟩ : PHat n) = blockHom (x₁, x₂, x₃) from rfl,
    orderOf_injective _ blockHom_injective]

@[expose] def c : PHat n := ⟨SD.z, SD.z, SD.z, 0⟩

theorem det_c : (c : PHat n).det = 0 := by
  simp [det, c, SD.det_z]

theorem c_comm (a : PHat n) : a * c = c * a := by
  obtain ⟨a₁, a₂, a₃, ae⟩ := a
  rcases zmod_two_eq_zero_or_one ae with rfl | rfl <;>
    ext <;> simp [c, SD.z_comm]

theorem c_mul_c : (c : PHat n) * c = 1 := by
  ext <;> simp [c, SD.z_mul_self]

end PHat

@[expose] def P (n : ℕ) : Subgroup (PHat n) := PHat.detHom.ker

theorem mem_P {n : ℕ} {a : PHat n} : a ∈ P n ↔ a.det = 0 := by
  rw [P, MonoidHom.mem_ker]
  exact Multiplicative.ofAdd.injective.eq_iff' rfl

theorem card_P (n : ℕ) : Nat.card (P n) = 2 ^ (3 * n + 3) := by
  have h := Subgroup.card_mul_index (P n)
  rw [P, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ PHat.detHom_surjective,
    Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, PHat.card,
    show 3 * n + 4 = (3 * n + 3) + 1 by ring, pow_succ] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

@[expose] def cP (n : ℕ) : P n := ⟨PHat.c, mem_P.2 PHat.det_c⟩

theorem cP_mem_center (n : ℕ) : cP n ∈ Subgroup.center (P n) :=
  Subgroup.mem_center_iff.2 fun g => Subtype.ext (PHat.c_comm (g : PHat n))

theorem cP_mul_cP (n : ℕ) : cP n * cP n = 1 :=
  Subtype.ext PHat.c_mul_c

theorem cP_ne_one {n : ℕ} (hn : 2 ≤ n) : cP n ≠ 1 := fun h =>
  SD.z_ne_one hn (congrArg PHat.x₁ (congrArg Subtype.val h))

theorem orderOf_cP {n : ℕ} (hn : 2 ≤ n) : orderOf (cP n) = 2 :=
  orderOf_eq_prime (by rw [pow_two, cP_mul_cP]) (cP_ne_one hn)

instance zpowers_cP_normal (n : ℕ) : (Subgroup.zpowers (cP n)).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 (cP_mem_center n))

theorem mem_zpowers_cP {n : ℕ} {y : P n} : y ∈ Subgroup.zpowers (cP n) ↔ y = 1 ∨ y = cP n := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h2 : cP n ^ 2 = 1 := by rw [pow_two, cP_mul_cP]
    rw [zpow_eq_zpow_emod' k h2]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

abbrev SModel (n : ℕ) : Type := ↥(P n) ⧸ Subgroup.zpowers (cP n)

theorem card_SModel {n : ℕ} (hn : 2 ≤ n) : Nat.card (SModel n) = 2 ^ (3 * n + 2) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (cP n))
  rw [Nat.card_zpowers, orderOf_cP hn, card_P, show 3 * n + 3 = (3 * n + 2) + 1 by ring,
    pow_succ] at h
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm

theorem SModel.mk_eq_mk_iff {n : ℕ} (x y : P n) :
    (QuotientGroup.mk x : SModel n) = QuotientGroup.mk y ↔ y = x ∨ y = x * cP n := by
  rw [QuotientGroup.eq, mem_zpowers_cP, inv_mul_eq_one, inv_mul_eq_iff_eq_mul]
  exact or_congr eq_comm Iff.rfl

end CFSG.CGT.Foote81L6.Bridge
