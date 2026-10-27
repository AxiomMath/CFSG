module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RNGen
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {G : Type} [Group G]

@[expose] def Dsub (s z : G) : Subgroup G := Subgroup.closure ({s * s, s * z} : Set G)

variable {s z t : G}

theorem a_mem_Dsub : s * s ∈ Dsub s z := by
  unfold Dsub
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem b_mem_Dsub : s * z ∈ Dsub s z := by
  unfold Dsub
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem Dsub_le {S : Subgroup G} (hs : s ∈ S) (hzS : z ∈ S) : Dsub s z ≤ S := by
  unfold Dsub
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact mul_mem hs hs
  · exact mul_mem hs hzS

theorem a_sq (hs4 : s ^ 4 = t) : (s * s) * (s * s) = t := by
  rw [← hs4, show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  simp only [pow_two]

theorem b_sq (hz2 : z * z = 1) (hzs : z * s * z⁻¹ = s⁻¹) : (s * z) * (s * z) = 1 := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzs' : z * s = s⁻¹ * z := by
    rw [hzi] at hzs
    calc z * s = z * s * z * z := by rw [mul_assoc (z * s) z z, hz2, mul_one]
      _ = s⁻¹ * z := by rw [hzs]
  calc (s * z) * (s * z) = s * (z * s) * z := by group
    _ = s * (s⁻¹ * z) * z := by rw [hzs']
    _ = z * z := by group
    _ = 1 := hz2

theorem t_mem_Dsub (hs4 : s ^ 4 = t) : t ∈ Dsub s z := by
  rw [← a_sq hs4]
  exact mul_mem a_mem_Dsub a_mem_Dsub

theorem b_inv_a (hz2 : z * z = 1) (hzs : z * s * z⁻¹ = s⁻¹) :
    (s * z) * (s * s) * (s * z)⁻¹ = (s * s)⁻¹ := by
  have hconj : z * (s * s) * z⁻¹ = (s * s)⁻¹ := by
    calc z * (s * s) * z⁻¹ = (z * s * z⁻¹) * (z * s * z⁻¹) := by group
      _ = s⁻¹ * s⁻¹ := by rw [hzs]
      _ = (s * s)⁻¹ := by group
  calc (s * z) * (s * s) * (s * z)⁻¹ = s * (z * (s * s) * z⁻¹) * s⁻¹ := by group
    _ = (s * s)⁻¹ := by rw [hconj]; group

theorem Dsub_eq_closure_invol (hz2 : z * z = 1) (hzs : z * s * z⁻¹ = s⁻¹) :
    Dsub s z = Subgroup.closure {y | y ∈ Dsub s z ∧ y * y = 1} := by
  have hb : s * z * (s * z) = 1 := b_sq hz2 hzs
  have hba : s * z * (s * s) = (s * s)⁻¹ * (s * z) := by
    have h := b_inv_a hz2 hzs
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  have hab : s * s * (s * z) * (s * s * (s * z)) = 1 := by
    calc s * s * (s * z) * (s * s * (s * z)) = s * s * (s * z * (s * s)) * (s * z) := by group
      _ = s * s * ((s * s)⁻¹ * (s * z)) * (s * z) := by rw [hba]
      _ = s * z * (s * z) := by group
      _ = 1 := hb
  have hX1 : s * s * (s * z) ∈ Subgroup.closure {y | y ∈ Dsub s z ∧ y * y = 1} :=
    Subgroup.subset_closure (show s * s * (s * z) ∈ {y | y ∈ Dsub s z ∧ y * y = 1} from
      ⟨mul_mem a_mem_Dsub b_mem_Dsub, hab⟩)
  have hX2 : s * z ∈ Subgroup.closure {y | y ∈ Dsub s z ∧ y * y = 1} :=
    Subgroup.subset_closure (show s * z ∈ {y | y ∈ Dsub s z ∧ y * y = 1} from
      ⟨b_mem_Dsub, hb⟩)
  apply le_antisymm
  · show Subgroup.closure ({s * s, s * z} : Set G) ≤ _
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · have h := mul_mem hX1 hX2
      have e : s * s * (s * z) * (s * z) = s * s := by
        calc s * s * (s * z) * (s * z) = s * s * (s * z * (s * z)) := by group
          _ = s * s := by rw [hb, mul_one]
      rwa [e] at h
    · exact hX2
  · exact (Subgroup.closure_le _).2 fun y hy => hy.1

theorem inv_s_eq_pow (hs8 : s ^ 8 = 1) : s⁻¹ = s ^ 7 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ']
  exact hs8

theorem z_mul_pow_s (hz2 : z * z = 1) (hzs : z * s * z⁻¹ = s⁻¹) (hs8 : s ^ 8 = 1) (k : ℕ) :
    z * s ^ k = s ^ (7 * k) * z := by
  have h1 : z * s ^ k * z⁻¹ = s ^ (7 * k) := by
    rw [← conj_pow, hzs, inv_s_eq_pow hs8, ← pow_mul]
  calc z * s ^ k = z * s ^ k * z⁻¹ * z := by simp [mul_assoc]
    _ = s ^ (7 * k) * z := by rw [h1]

theorem sz_mul_sz (hz2 : z * z = 1) (hzs : z * s * z⁻¹ = s⁻¹) (hs8 : s ^ 8 = 1) (k m : ℕ) :
    (s ^ k * z) * (s ^ m * z) = s ^ (k + 7 * m) := by
  calc (s ^ k * z) * (s ^ m * z) = s ^ k * (z * s ^ m) * z := by simp only [mul_assoc]
    _ = s ^ k * (s ^ (7 * m) * z) * z := by rw [z_mul_pow_s hz2 hzs hs8]
    _ = s ^ k * s ^ (7 * m) * (z * z) := by simp only [mul_assoc]
    _ = s ^ (k + 7 * m) := by rw [hz2, mul_one, pow_add]

theorem z_pow_two_mul (hz2 : z * z = 1) (r : ℕ) : z ^ (2 * r) = 1 := by
  rw [pow_mul, pow_two, hz2, one_pow]

theorem z_pow_two_mul_add_one (hz2 : z * z = 1) (r : ℕ) : z ^ (2 * r + 1) = z := by
  rw [pow_succ, z_pow_two_mul hz2 r, one_mul]

theorem Dsub_parity (hz2 : z * z = 1) (hzs : z * s * z⁻¹ = s⁻¹) (hs8 : s ^ 8 = 1) :
    ∀ y ∈ Dsub s z, (∃ i : ℕ, y = s ^ (2 * i)) ∨ ∃ i : ℕ, y = s ^ (2 * i + 1) * z := by
  intro y hy
  unfold Dsub at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inl ⟨1, by rw [mul_one, pow_two]⟩
    · exact Or.inr ⟨0, by simp⟩
  | one => exact Or.inl ⟨0, by simp⟩
  | mul x y _ _ hx hy =>
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨i + j, by rw [← pow_add, mul_add]⟩
    · exact Or.inr ⟨i + j, by
        rw [← mul_assoc, ← pow_add, show 2 * i + (2 * j + 1) = 2 * (i + j) + 1 by ring]⟩
    · exact Or.inr ⟨i + 7 * j, by
        rw [mul_assoc, z_mul_pow_s hz2 hzs hs8, ← mul_assoc, ← pow_add,
          show 2 * i + 1 + 7 * (2 * j) = 2 * (i + 7 * j) + 1 by ring]⟩
    · exact Or.inl ⟨i + 7 * j + 4, by
        rw [sz_mul_sz hz2 hzs hs8, show 2 * i + 1 + 7 * (2 * j + 1) = 2 * (i + 7 * j + 4) by ring]⟩
  | inv x _ hx =>
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inl ⟨7 * i, by
        rw [← inv_pow, inv_s_eq_pow hs8, ← pow_mul, show 7 * (2 * i) = 2 * (7 * i) by ring]⟩
    · exact Or.inr ⟨i, inv_eq_of_mul_eq_one_right (by
        rw [sz_mul_sz hz2 hzs hs8, show 2 * i + 1 + 7 * (2 * i + 1) = 8 * (2 * i + 1) by ring,
          pow_mul, hs8, one_pow])⟩

theorem z_not_mem_Dsub (hz2 : z * z = 1) (hs8 : s ^ 8 = 1) (hzs : z * s * z⁻¹ = s⁻¹)
    (hord : orderOf s = 8) (hzns : z ∉ zpowers s) : z ∉ Dsub s z := by
  intro hz
  rcases Dsub_parity hz2 hzs hs8 z hz with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact hzns (by rw [hi]; exact pow_mem (mem_zpowers s) _)
  · have h1 : s ^ (2 * i + 1) = 1 :=
      mul_right_cancel (a := s ^ (2 * i + 1)) (b := z) (c := 1) (by rw [one_mul, ← hi])
    have h8 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h8
    omega

theorem card_Dsub {S : Subgroup G} [Finite G] (hs : s ∈ S) (hzS : z ∈ S) (hs8 : s ^ 8 = 1)
    (hz2 : z * z = 1) (hzs : z * s * z⁻¹ = s⁻¹) (hord : orderOf s = 8) (hzns : z ∉ zpowers s)
    (hgen : ∀ y ∈ S, ∃ i j : ℕ, y = s ^ i * z ^ j) (hS16 : Nat.card ↥S = 16) :
    Nat.card ↥(Dsub s z) = 8 := by
  have hDS : Dsub s z ≤ S := Dsub_le hs hzS
  have hK : zpowers (s * s) ≤ Dsub s z := zpowers_le.2 a_mem_Dsub
  have hKs : zpowers (s * s) ≤ zpowers s :=
    zpowers_le.2 (mul_mem (mem_zpowers s) (mem_zpowers s))
  have hord2 : orderOf (s * s) = 4 := by
    have h2 : orderOf (s ^ 2) = orderOf s / 2 := orderOf_pow_of_dvd (by norm_num) (by omega)
    rw [← pow_two, h2, hord] <;> norm_num
  have hKcard : Nat.card (zpowers (s * s)) = 4 := by
    rw [Nat.card_zpowers, hord2]
  have hKD : 4 ∣ Nat.card ↥(Dsub s z) := by
    have h := Subgroup.card_dvd_of_le hK
    rwa [hKcard] at h
  have hDD : Nat.card ↥(Dsub s z) ∣ 16 := by
    have h := Subgroup.card_dvd_of_le hDS
    rwa [hS16] at h
  have hzD : z ∉ Dsub s z := z_not_mem_Dsub hz2 hs8 hzs hord hzns
  have key : Nat.card ↥(Dsub s z) = 4 ∨ Nat.card ↥(Dsub s z) = 8 ∨
      Nat.card ↥(Dsub s z) = 16 := by
    have hle : Nat.card ↥(Dsub s z) ≤ 16 := Nat.le_of_dvd (by norm_num) hDD
    generalize Nat.card ↥(Dsub s z) = n at hle hDD hKD ⊢
    interval_cases n <;> omega
  rcases key with h | h | h
  · exfalso
    have heq : zpowers (s * s) = Dsub s z :=
      Subgroup.eq_of_le_of_card_ge hK (le_of_eq (by rw [h, hKcard]))
    have hb' : s * z ∈ zpowers (s * s) := by
      rw [heq]
      exact b_mem_Dsub
    have h2 : s * z ∈ zpowers s := hKs hb'
    apply hzns
    have h3 : z = s⁻¹ * (s * z) := by group
    rw [h3]
    exact mul_mem (inv_mem (mem_zpowers s)) h2
  · exact h
  · exfalso
    have heq : Dsub s z = S := Subgroup.eq_of_le_of_card_ge hDS (le_of_eq (by rw [hS16, h]))
    apply hzD
    rw [heq]
    exact hzS

theorem invol_mem_Dsub {S : Subgroup G} (hz2 : z * z = 1) (hs8 : s ^ 8 = 1) (hs4 : s ^ 4 = t)
    (hzs : z * s * z⁻¹ = s⁻¹) (hord : orderOf s = 8)
    (hgen : ∀ y ∈ S, ∃ i j : ℕ, y = s ^ i * z ^ j) :
    ∀ y ∈ S, y * y = 1 → y ≠ 1 → (∀ k : ℕ, y ≠ s ^ (2 * k) * z) → y ∈ Dsub s z := by
  intro y hyS hy2 _ hnot
  obtain ⟨i, j, rfl⟩ := hgen y hyS
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [z_pow_two_mul hz2 r, mul_one] at hy2 ⊢
    have hs2 : s ^ (i + i) = 1 := by rw [pow_add]; exact hy2
    have h8 : 8 ∣ i + i := by
      have h := orderOf_dvd_of_pow_eq_one hs2
      rwa [hord] at h
    obtain ⟨q, rfl⟩ : 4 ∣ i := by omega
    have h4 : s ^ 4 ∈ Dsub s z := by
      rw [hs4]
      exact t_mem_Dsub hs4
    rw [pow_mul]
    exact pow_mem h4 q
  · rw [z_pow_two_mul_add_one hz2 r] at hnot ⊢
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
    · exact (hnot k rfl).elim
    · have e1 : s ^ (2 * k + 1) * z = s ^ (2 * k) * (s * z) := by
        rw [pow_succ, mul_assoc]
      have e2 : (s * s) ^ k = s ^ (2 * k) := by
        rw [← pow_two, ← pow_mul]
      rw [e1, ← e2]
      exact mul_mem (pow_mem a_mem_Dsub k) b_mem_Dsub

end CFSG.EvenSporadicStandard.Fin76b
