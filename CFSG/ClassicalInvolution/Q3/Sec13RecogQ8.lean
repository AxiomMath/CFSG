module

public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.ClassicalInvolution.Q3.AE.Bar
import CFSG.ClassicalInvolution.Q3.TL3T48

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG.ClassicalInvolution.Generic

variable {G : Type*} [Group G]

theorem mul_self_eq_one_or_eq_of_q8 {A : Subgroup G} {z : G} (hz : IsUniqueInvolution A z)
    (h8 : Nat.card A = 8) (hnab : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) {a : G} (ha : a ∈ A) :
    a * a = 1 ∨ a * a = z := by
  have ha8 : a ^ 8 = 1 := orderOf_dvd_iff_pow_eq_one.mp (h8 ▸ A.orderOf_dvd_natCard ha)
  rcases hz.unique _ (A.pow_mem ha 4) (by rw [← pow_add]; exact ha8) with h4 | h4
  · refine hz.unique _ (A.mul_mem ha ha) ?_
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h4
  have : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have hn : ¬ a ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, h4]
    exact hz.ne_one
  have hf : a ^ 2 ^ (2 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (2 + 1) = 8 by norm_num]
    exact ha8
  have hord : orderOf a = 8 := by
    rw [orderOf_eq_prime_pow hn hf]
    norm_num
  have heq : Subgroup.zpowers a = A :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ha) (by rw [h8, Nat.card_zpowers, hord])
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  rw [← heq, Subgroup.mem_zpowers_iff] at hx hy
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := hy
  exact absurd (Commute.zpow_zpow_self a m k).eq hxy

theorem eq_or_eq_of_le_sup_of_q8 {A B X : Subgroup G} {z w : G} (hA : IsUniqueInvolution A z)
    (hA8 : Nat.card A = 8) (hAnab : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x)
    (hB : IsUniqueInvolution B z) (hB8 : Nat.card B = 8)
    (hBnab : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x) (hAB : Commutes A B)
    (hinf : A ⊓ B ≤ Subgroup.zpowers z) (hX : X ≤ A ⊔ B) (hX8 : Nat.card X = 8)
    (hw : IsUniqueInvolution X w) : X = A ∨ X = B := by
  have hsqA := fun a (ha : a ∈ A) => mul_self_eq_one_or_eq_of_q8 hA hA8 hAnab ha
  have hsqB := fun b (hb : b ∈ B) => mul_self_eq_one_or_eq_of_q8 hB hB8 hBnab hb
  have hmul : ∀ a ∈ A, ∀ b ∈ B, a * b * (a * b) = a * a * (b * b) := fun a ha b hb => by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hAB a ha b hb]
      _ = a * a * (b * b) := by group
  have hinf' : ∀ c ∈ A, c ∈ B → c = 1 ∨ c = z := fun c hcA hcB => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hinf ⟨hcA, hcB⟩)
    exact hA.unique _ hcA (by rw [← (Commute.refl z).mul_zpow, hA.sq, one_zpow])
  have hsq : ∀ a ∈ A, ∀ b ∈ B, a * b * (a * b) = 1 ∨ a * b * (a * b) = z := by
    intro a ha b hb
    rw [hmul a ha b hb]
    rcases hsqA a ha with h1 | h1 <;> rcases hsqB b hb with h2 | h2 <;> simp [h1, h2, hA.sq]
  have hwz : w = z := by
    obtain ⟨x, hx, hx1⟩ : ∃ x ∈ X, x * x ≠ 1 := by
      by_contra! hcon
      have hle : X ≤ Subgroup.zpowers w := fun x hx => by
        rcases hw.unique x hx (hcon x hx) with rfl | rfl
        · exact one_mem _
        · exact Subgroup.mem_zpowers _
      have hw2 : w ^ 2 = 1 := by rw [pow_two]; exact hw.sq
      have := (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, hw2⟩).finite_zpowers
      have h1 := (Subgroup.card_le_of_le hle).trans_eq (Nat.card_zpowers w)
      have h2 := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hw2)
      omega
    obtain ⟨a, ha, b, hb, rfl⟩ := ModelFacts.Orth15.InnerL4.mem_sup_of_comm hAB (hX hx)
    have hz := (hsq a ha b hb).resolve_left hx1
    exact ((hw.unique z (hz ▸ X.mul_mem hx hx) hA.sq).resolve_left hA.ne_one).symm
  have hmem : ∀ g ∈ X, g ∈ A ∨ g ∈ B := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := ModelFacts.Orth15.InnerL4.mem_sup_of_comm hAB (hX hg)
    rcases hsqA a ha with h1 | h1
    · rcases hA.unique a ha h1 with rfl | rfl
      · exact Or.inr (by rwa [one_mul])
      · exact Or.inr (B.mul_mem hB.mem hb)
    rcases hsqB b hb with h2 | h2
    · rcases hB.unique b hb h2 with rfl | rfl
      · exact Or.inl (by rwa [mul_one])
      · exact Or.inl (A.mul_mem ha hA.mem)
    have hab : a * b ∈ B := by
      rcases hw.unique _ hg (by rw [hmul a ha b hb, h1, h2, hA.sq]) with h | h
      · rw [h]
        exact B.one_mem
      · rw [h, hwz]
        exact hB.mem
    have haB : a ∈ B := by simpa using B.mul_mem hab (B.inv_mem hb)
    rcases hinf' a ha haB with rfl | rfl
    · exact absurd (h1.symm.trans (one_mul 1)) hA.ne_one
    · exact absurd (h1.symm.trans hA.sq) hA.ne_one
  have hle : X ≤ A ∨ X ≤ B := by
    by_contra! hcon
    obtain ⟨x, hx, hxA⟩ := SetLike.not_le_iff_exists.mp hcon.1
    obtain ⟨y, hy, hyB⟩ := SetLike.not_le_iff_exists.mp hcon.2
    have hxB := (hmem x hx).resolve_left hxA
    have hyA := (hmem y hy).resolve_right hyB
    rcases hmem (x * y) (X.mul_mem hx hy) with h | h
    · exact hxA (by simpa using A.mul_mem h (A.inv_mem hyA))
    · exact hyB (by simpa using B.mul_mem (B.inv_mem hxB) h)
  have : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have : Finite B := Nat.finite_of_card_ne_zero (by omega)
  exact hle.imp (fun h => Subgroup.eq_of_le_of_card_ge h (hA8.trans hX8.symm).le)
    fun h => Subgroup.eq_of_le_of_card_ge h (hB8.trans hX8.symm).le

section Model

open CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}

theorem isUniqueInvolution_memBar (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    IsUniqueInvolution (memBar α h b) (zBar α h) where
  mem := zBar_mem_memBar α h b
  ne_one := zBar_ne_one hn α h
  sq := zBar_mul_self α h
  unique _ hy hy2 := eq_of_mem_memBar_mul_self hn hy hy2

theorem eq_memBar_of_le_sup_memBar (hn : 5 ≤ n) {α : Finset (Fin n)} {h : α.card = 4}
    {X : Subgroup (AEQ n)} (hX : X ≤ memBar α h true ⊔ memBar α h false) (h8 : Nat.card X = 8)
    {w : AEQ n} (hw : IsUniqueInvolution X w) : X = memBar α h true ∨ X = memBar α h false := by
  refine eq_or_eq_of_le_sup_of_q8 (isUniqueInvolution_memBar hn α h true)
    (natCard_memBar hn α h true) (exists_not_comm_memBar hn α h true)
    (isUniqueInvolution_memBar hn α h false) (natCard_memBar hn α h false)
    (exists_not_comm_memBar hn α h false) (TC.Thin.memBar_twin_comm α h true) ?_ hX h8 hw
  intro x hx
  rcases inf_memBar_true_false hn (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2 with
    rfl | rfl
  · exact one_mem _
  · exact Subgroup.mem_zpowers _

end Model

end CFSG.ClassicalInvolution.Q3.Sec13
