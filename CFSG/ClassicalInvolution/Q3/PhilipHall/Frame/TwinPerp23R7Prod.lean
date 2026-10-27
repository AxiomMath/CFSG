module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7J

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F94
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.F7E

section Lift

variable {Y : Type} [Group Y] [Finite Y] {C : Subgroup Y}

theorem conj_eq_of_conjSub_eq {W : Subgroup Y} (hWC : W ≤ C) (hW2 : IsPGroup 2 W) {x : ↥C}
    (hx : ∀ n ∈ C, n ∈ Subgroup.normalizer (W : Set Y) → n * x * n⁻¹ = x)
    (q d : ↥C ⧸ classicalInvolutionOddCore ↥C)
    (h : conjSub q ((W.subgroupOf C).map (F7I.piC C)) =
      conjSub d ((W.subgroupOf C).map (F7I.piC C))) :
    q * F7I.piC C x * q⁻¹ = d * F7I.piC C x * d⁻¹ := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
  obtain ⟨c', rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) d
  change conjSub (F7I.piC C c) _ = conjSub (F7I.piC C c') _ at h
  change F7I.piC C c * F7I.piC C x * (F7I.piC C c)⁻¹ =
    F7I.piC C c' * F7I.piC C x * (F7I.piC C c')⁻¹
  have h1 : conjSub (F7I.piC C (c'⁻¹ * c)) ((W.subgroupOf C).map (F7I.piC C)) =
      (W.subgroupOf C).map (F7I.piC C) := by
    rw [map_mul, map_inv, conjSub_mul, h, conjSub_inv_conjSub]
  rw [F7I.conjSub_map_piC] at h1
  have hcW : conjSub ((c'⁻¹ * c : ↥C) : Y) W ≤ C :=
    (conjSub_mono hWC).trans (conjSub_eq_self_of_mem (c'⁻¹ * c).2).le
  obtain ⟨o, ho, hon⟩ := F7I.frattini_W hWC hW2 (F7I.sup_eq_of_map_eq hcW hWC h1)
  have hoC : o ∈ C := oddCoreOf_le_self C ho
  have hnC : o * ((c'⁻¹ * c : ↥C) : Y) ∈ C := C.mul_mem hoC (c'⁻¹ * c).2
  have hpn : F7I.piC C ⟨_, hnC⟩ = F7I.piC C (c'⁻¹ * c) := by
    have e : (⟨_, hnC⟩ : ↥C) = ⟨o, hoC⟩ * (c'⁻¹ * c) := rfl
    rw [e, map_mul, (F7I.piC_eq_one_iff ⟨o, hoC⟩).mpr ho, one_mul]
  have key : F7I.piC C (c'⁻¹ * c) * F7I.piC C x * (F7I.piC C (c'⁻¹ * c))⁻¹ = F7I.piC C x := by
    rw [← hpn, ← map_mul, ← map_inv, ← map_mul]
    exact congrArg _ (Subtype.ext (hx _ hnC hon))
  rw [map_mul, map_inv] at key
  calc F7I.piC C c * F7I.piC C x * (F7I.piC C c)⁻¹
      = F7I.piC C c' * ((F7I.piC C c')⁻¹ * F7I.piC C c * F7I.piC C x *
          ((F7I.piC C c')⁻¹ * F7I.piC C c)⁻¹) * (F7I.piC C c')⁻¹ := by group
    _ = F7I.piC C c' * F7I.piC C x * (F7I.piC C c')⁻¹ := by rw [key]

end Lift

section Gen

variable {Q : Type} [Group Q]

theorem modZ_mul {z : Q} (hz : ∀ q : Q, q * z = z * q) (hz2 : z * z = 1) {x x' y y' : Q}
    (h1 : ModZ z x' x) (h2 : ModZ z y' y) : ModZ z (x' * y') (x * y) := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2]
  · exact Or.inl rfl
  · right
    exact (mul_assoc _ _ _).symm
  · right
    calc x * z * y = x * (z * y) := mul_assoc _ _ _
      _ = x * (y * z) := by rw [hz y]
      _ = x * y * z := (mul_assoc _ _ _).symm
  · left
    calc x * z * (y * z) = x * (z * y) * z := by group
      _ = x * (y * z) * z := by rw [hz y]
      _ = x * y * (z * z) := by group
      _ = x * y := by rw [hz2, mul_one]

theorem pow_conj_of_shift {x w c : Q} (hxw : x * w * x⁻¹ = w * c) (hxc : x * c * x⁻¹ = c) :
    ∀ j : ℕ, x ^ j * w * (x ^ j)⁻¹ = w * c ^ j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hcj : x * c ^ j * x⁻¹ = c ^ j := by rw [← conj_pow, hxc]
    calc x ^ (j + 1) * w * (x ^ (j + 1))⁻¹ = x * (x ^ j * w * (x ^ j)⁻¹) * x⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          simp only [mul_assoc]
      _ = (x * w * x⁻¹) * (x * c ^ j * x⁻¹) := by
          rw [ih]
          simp only [mul_assoc, inv_mul_cancel_left]
      _ = w * c ^ (j + 1) := by
          rw [hxw, hcj, pow_succ', mul_assoc]

theorem eq_one_of_odd_shift {x w c : Q} {k : ℕ} (hk : x ^ k = 1) (hodd : Odd k)
    (hc8 : orderOf c ∣ 8) (hxw : x * w * x⁻¹ = w * c) (hxc : x * c * x⁻¹ = c) : c = 1 := by
  have h := pow_conj_of_shift hxw hxc k
  rw [hk, one_mul, inv_one, mul_one] at h
  have hck : c ^ k = 1 := by
    have h' : w * c ^ k = w * 1 := by rw [← h, mul_one]
    exact mul_left_cancel h'
  have hcop : Nat.Coprime k (2 ^ 3) := Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hck) hc8)

theorem cent_of_odd_q8 [Finite Q] {A : Subgroup Q} {z : Q} (hz : ∀ q : Q, q * z = z * q)
    (hs : IsUniqueInvolution A z) (h8 : Nat.card A = 8) (hnab : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x)
    {x : Q} {k : ℕ} (hk : x ^ k = 1) (hodd : Odd k) (hxA : ∀ w ∈ A, x * w * x⁻¹ ∈ A)
    {a : Q} (ha : a ∈ A) (ha1 : a ≠ 1) (haz : a ≠ z) (hxa : ModZ z (x * a * x⁻¹) a) :
    ∀ w ∈ A, x * w * x⁻¹ = w := by
  have hc8 : ∀ c ∈ A, orderOf c ∣ 8 := fun c hc => h8 ▸ A.orderOf_dvd_natCard hc
  have hxz : x * z * x⁻¹ = z := by rw [hz x, mul_inv_cancel_right]
  have hxa' : x * a * x⁻¹ = a := by
    rcases hxa with h | h
    · exact h
    · exact absurd (eq_one_of_odd_shift hk hodd (hc8 z hs.mem) h hxz) hs.ne_one
  intro w hw
  obtain ⟨c, hcdef⟩ : ∃ c, c = w⁻¹ * (x * w * x⁻¹) := ⟨_, rfl⟩
  have hcA : c ∈ A := by rw [hcdef]; exact A.mul_mem (A.inv_mem hw) (hxA w hw)
  have hxw : x * w * x⁻¹ = w * c := by rw [hcdef, mul_inv_cancel_left]
  have hκ : x * (w * a * w⁻¹ * a⁻¹) * x⁻¹ = w * a * w⁻¹ * a⁻¹ := by
    rcases commutator_eq_q8 hs h8 hnab hw ha with h | h <;> rw [h]
    · rw [mul_one, mul_inv_cancel]
    · exact hxz
  have h1 : (x * w * x⁻¹) * a * (x * w * x⁻¹)⁻¹ = w * a * w⁻¹ := by
    have e : x * (w * a * w⁻¹ * a⁻¹) * x⁻¹ =
        (x * w * x⁻¹) * (x * a * x⁻¹) * (x * w * x⁻¹)⁻¹ * (x * a * x⁻¹)⁻¹ := by group
    rw [e, hxa'] at hκ
    calc (x * w * x⁻¹) * a * (x * w * x⁻¹)⁻¹
        = ((x * w * x⁻¹) * a * (x * w * x⁻¹)⁻¹ * a⁻¹) * a := by group
      _ = w * a * w⁻¹ := by rw [hκ]; group
  have hac : a * c = c * a := by
    apply comm_of_conj_eq'
    calc c * a * c⁻¹ = w⁻¹ * ((x * w * x⁻¹) * a * (x * w * x⁻¹)⁻¹) * w := by rw [hcdef]; group
      _ = a := by rw [h1]; group
  have hxc : x * c * x⁻¹ = c := by
    by_cases hc1 : c = 1
    · rw [hc1, mul_one, mul_inv_cancel]
    by_cases hcz : c = z
    · rw [hcz]; exact hxz
    rcases modZ_of_comm_q8 hs h8 hnab ha hcA ha1 haz hc1 hcz hac with h | h <;> rw [h]
    · exact hxa'
    · calc x * (a * z) * x⁻¹ = (x * a * x⁻¹) * (x * z * x⁻¹) := by group
        _ = a * z := by rw [hxa', hxz]
  have := eq_one_of_odd_shift hk hodd (hc8 c hcA) hxw hxc
  rw [hxw, this, mul_one]

theorem triple_q8 [Finite Q] {A : Subgroup Q} {z : Q} (hz : ∀ q : Q, q * z = z * q)
    (hs : IsUniqueInvolution A z) (h8 : Nat.card A = 8) (hnab : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x)
    {x y w : Q} (hx : x ∈ A) (hy : y ∈ A) (hw : w ∈ A)
    (hxy : x * y ≠ y * x) (hxw : x * w ≠ w * x) (hyw : y * w ≠ w * y) :
    x * y * w = 1 ∨ x * y * w = z := by
  have hz2 := hs.sq
  have hwx : w * x = x * w * z :=
    (comm_or_q8 hs h8 hnab hw hx).resolve_left fun h => hxw h.symm
  have hwy : w * y = y * w * z :=
    (comm_or_q8 hs h8 hnab hw hy).resolve_left fun h => hyw h.symm
  have hc : x * y * w = w * (x * y) := by
    calc x * y * w = x * y * w * (z * z) := by rw [hz2, mul_one]
      _ = x * (y * w * z) * z := by group
      _ = x * (w * y) * z := by rw [hwy]
      _ = x * w * (y * z) := by group
      _ = x * w * (z * y) := by rw [hz y]
      _ = (x * w * z) * y := by group
      _ = w * (x * y) := by rw [← hwx]; group
  have hxy1 : x * y ≠ 1 := by
    intro h
    apply hxy
    rw [eq_inv_of_mul_eq_one_right h, mul_inv_cancel, inv_mul_cancel]
  have hxyz : x * y ≠ z := by
    intro h
    apply hxy
    have hy' : y = x⁻¹ * z := by rw [← h, inv_mul_cancel_left]
    rw [hy']
    calc x * (x⁻¹ * z) = z := by group
      _ = x⁻¹ * (x * z) := by group
      _ = x⁻¹ * z * x := by rw [hz x]; group
  have hw1 : w ≠ 1 := by rintro rfl; exact hxw (by rw [one_mul, mul_one])
  have hwz : w ≠ z := by rintro rfl; exact hxw (hz x)
  have hxx := mul_self_eq_q8 hs h8 hnab (A.mul_mem hx hy) hxy1 hxyz
  rcases modZ_of_comm_q8 hs h8 hnab (A.mul_mem hx hy) hw hxy1 hxyz hw1 hwz hc with h | h
  · right; rw [h, hxx]
  · left; rw [h, ← mul_assoc, hxx, hz2]

theorem rearr {p e P₁ E₁ P₂ E₂ : Q} (h1 : e * P₁ = P₁ * e) (h2 : E₁ * P₂ = P₂ * E₁)
    (h3 : e * P₂ = P₂ * e) : p * e * (P₁ * E₁) * (P₂ * E₂) = p * P₁ * P₂ * (e * E₁ * E₂) := by
  calc p * e * (P₁ * E₁) * (P₂ * E₂) = p * (e * P₁) * (E₁ * P₂) * E₂ := by group
    _ = p * (P₁ * e) * (P₂ * E₁) * E₂ := by rw [h1, h2]
    _ = p * P₁ * (e * P₂) * E₁ * E₂ := by group
    _ = p * P₁ * P₂ * (e * E₁ * E₂) := by rw [h3]; group

theorem sq3 {x y w : Q} (hxy : x * y = y * x) (hxw : x * w = w * x) (hyw : y * w = w * y)
    (hx : x * x = 1) (hy : y * y = 1) (hw : w * w = 1) : x * y * w * (x * y * w) = 1 := by
  calc x * y * w * (x * y * w) = x * y * (w * x) * y * w := by group
    _ = x * y * (x * w) * y * w := by rw [← hxw]
    _ = x * (y * x) * (w * y) * w := by group
    _ = x * (x * y) * (y * w) * w := by rw [← hxy, ← hyw]
    _ = (x * x) * (y * y) * (w * w) := by group
    _ = 1 := by rw [hx, hy, hw]; group

theorem perm3 {x y w : Q} (hxy : x * y = y * x) (hxw : x * w = w * x) (hyw : y * w = w * y) :
    x * w * y = x * y * w ∧ y * x * w = x * y * w ∧ y * w * x = x * y * w ∧
      w * x * y = x * y * w ∧ w * y * x = x * y * w := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_assoc, ← hyw, ← mul_assoc]
  · rw [← hxy]
  · rw [mul_assoc, ← hxw, ← mul_assoc, ← hxy]
  · rw [← hxw, mul_assoc, ← hyw, ← mul_assoc]
  · rw [← hyw, mul_assoc, ← hxw, ← mul_assoc, ← hxy]

theorem fix_of_odd {A B : Subgroup Q} (hAB : A ≠ B) {x : Q} {m : ℕ} (hm : Odd m)
    (hxm : x ^ m = 1)
    (hperm : (conjSub x A = A ∧ conjSub x B = B) ∨ (conjSub x A = B ∧ conjSub x B = A)) :
    conjSub x A = A := by
  rcases hperm with ⟨h, -⟩ | ⟨h1, h2⟩
  · exact h
  exfalso
  have hev : ∀ j : ℕ, conjSub (x ^ (2 * j)) A = A := by
    intro j
    induction j with
    | zero => rw [Nat.mul_zero, pow_zero, conjSub_one]
    | succ j ih => rw [mul_add, mul_one, pow_add, conjSub_mul, pow_two, conjSub_mul, h1, h2, ih]
  obtain ⟨i, rfl⟩ := hm
  apply hAB
  calc A = conjSub (x ^ (2 * i + 1)) A := by rw [hxm, conjSub_one]
    _ = B := by rw [pow_succ', conjSub_mul, hev i, h1]

theorem dec_of_modZ [Finite Q] {A B : Subgroup Q} {z : Q} (hz : ∀ q : Q, q * z = z * q) (hz2 : z * z = 1)
    (hzB : z ∈ B) (hinf : ∀ w ∈ A, w ∈ B → w = 1 ∨ w = z) {a a' b b' : Q} (ha : a ∈ A)
    (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (h : ModZ z (a' * b') (a * b)) :
    ModZ z a' a ∧ ModZ z b' b := by
  rcases h with h | h
  · exact dec_modZ hz hz2 hinf ha ha' hb hb' h.symm
  · have := dec_modZ hz hz2 hinf ha ha' (B.mul_mem hb hzB) hb' (by rw [h]; group)
    exact ⟨this.1, ModZ.trans hz2 this.2 (ModZ.mul_right_z b)⟩

theorem noncomm_of_not_modZ [Finite Q] {A B : Subgroup Q} {z : Q} (hz : ∀ q : Q, q * z = z * q)
    (hsA : IsUniqueInvolution A z) (hsB : IsUniqueInvolution B z) (h8A : Nat.card A = 8)
    (h8B : Nat.card B = 8) (hnabA : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x)
    (hnabB : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x) (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    {α α' β β' : Q} (hα : α ∈ A) (hα' : α' ∈ A) (hβ : β ∈ B) (hβ' : β' ∈ B) (hα1 : α ≠ 1)
    (hαz : α ≠ z) (hα'1 : α' ≠ 1) (hα'z : α' ≠ z) (hβ1 : β ≠ 1) (hβz : β ≠ z) (hβ'1 : β' ≠ 1)
    (hβ'z : β' ≠ z) (hc : (α * β) * (α' * β') = (α' * β') * (α * β))
    (hn : ¬ ModZ z (α' * β') (α * β)) : α * α' ≠ α' * α ∧ β * β' ≠ β' * β := by
  have hiff := (prod_comm_iff hz hsA hsB h8A h8B hnabA hnabB hcomm hα hα' hβ hβ').mp hc
  have key : ¬ (α * α' = α' * α) := by
    intro h
    have m1 : ModZ z α' α := modZ_of_comm_q8 hsA h8A hnabA hα hα' hα1 hαz hα'1 hα'z h
    have m2 : ModZ z β' β := modZ_of_comm_q8 hsB h8B hnabB hβ hβ' hβ1 hβz hβ'1 hβ'z (hiff.mp h)
    exact hn (modZ_mul hz hsA.sq m1 m2)
  exact ⟨key, fun h => key (hiff.mpr h)⟩

end Gen

end F7J

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
