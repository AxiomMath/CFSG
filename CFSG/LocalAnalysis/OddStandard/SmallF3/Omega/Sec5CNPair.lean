module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CNQ8

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {π : SL23 × SL23 →* G} {K₃ K₄ : Subgroup G} {z : G}

theorem Sec5CNPi.comm_pm (h : Sec5CNPi π K₃ K₄ z) {t₃ t₄ a₃ a₄ : SL23} (ht₃ : t₃ * t₃ = -1)
    (ht₄ : t₄ * t₄ = -1) (ha₃ : a₃ * a₃ = -1) (ha₄ : a₄ * a₄ = -1)
    (hc : π (t₃, t₄) * π (a₃, a₄) = π (a₃, a₄) * π (t₃, t₄))
    (hside : (a₃ = t₃ ∨ a₃ = -t₃) ∨ (a₄ = t₄ ∨ a₄ = -t₄)) :
    π (a₃, a₄) = π (t₃, t₄) ∨ π (a₃, a₄) = π (t₃, t₄) * z := by
  have hzc : z * π (t₃, t₄) = π (t₃, t₄) * z := h.z_comm (h.mk_mem t₃ t₄)
  rcases (h.comm_iff t₃ t₄ a₃ a₄).mp hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e₃ := (sec5cn_comm_iff_pm t₃ a₃ ht₃ ha₃).mp h1.symm
    have e₄ := (sec5cn_comm_iff_pm t₄ a₄ ht₄ ha₄).mp h2.symm
    rcases e₃ with rfl | rfl <;> rcases e₄ with rfl | rfl
    · left
      rfl
    · right
      rw [h.neg_right, hzc]
    · right
      rw [h.neg_left, hzc]
    · left
      exact h.neg_both _ _
  · exfalso
    rcases hside with e | e
    · have h3 := (sec5cn_comm_iff_pm t₃ a₃ ht₃ ha₃).mpr e
      rw [h3] at h1
      exact sec5cn_neg_absurd (w := a₃ * t₃) (w' := a₃ * t₃) rfl h1
    · have h3 := (sec5cn_comm_iff_pm t₄ a₄ ht₄ ha₄).mpr e
      rw [h3] at h2
      exact sec5cn_neg_absurd (w := a₄ * t₄) (w' := a₄ * t₄) rfl h2

theorem Sec5CNPi.cent_pair (h : Sec5CNPi π K₃ K₄ z) {a b q : G} (ha : a ∈ K₃ ⊔ K₄)
    (hb : b ∈ K₃ ⊔ K₄) (hq : q ∈ K₃ ⊔ K₄) (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (haz : a ≠ z) (hbz : b ≠ z) (hba : b ≠ a) (hbaz : b ≠ a * z)
    (hab : a * b = b * a) (hq4 : q ^ 4 = 1) (hqa : q * a = a * q) (hqb : q * b = b * q) :
    ∃ i j k : Fin 2, q = z ^ (k : ℕ) * a ^ (i : ℕ) * b ^ (j : ℕ) := by
  obtain ⟨a₃, a₄, ha₃, ha₄, rfl⟩ := h.invol ha ha2 ha1 haz
  obtain ⟨b₃, b₄, hb₃, hb₄, rfl⟩ := h.invol hb hb2 hb1 hbz
  obtain ⟨⟨p₁, p₂⟩, rfl⟩ := h.mem_iff.mp hq
  obtain ⟨hp₁, hp₂⟩ := (h.pow4_iff p₁ p₂).mp hq4
  have hanti : a₃ * b₃ = -(b₃ * a₃) ∧ a₄ * b₄ = -(b₄ * a₄) := by
    rcases (h.comm_iff a₃ a₄ b₃ b₄).mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      have e₃ := (sec5cn_comm_iff_pm a₃ b₃ ha₃ hb₃).mp h1.symm
      rcases h.comm_pm ha₃ ha₄ hb₃ hb₄ hab (Or.inl e₃) with h3 | h3
      · exact hba h3
      · exact hbaz h3
    · rw [h1, h2, sec5cn_neg_neg, sec5cn_neg_neg]
      exact ⟨rfl, rfl⟩
  obtain ⟨i, j, k, hp₁e, hj, hi⟩ := sec5cn_pair_expand a₃ b₃ p₁ ha₃ hb₃ hanti.1 hp₁
  obtain ⟨i', j', k', hp₂e, hj', hi'⟩ := sec5cn_pair_expand a₄ b₄ p₂ ha₄ hb₄ hanti.2 hp₂
  have hjj : j = j' := sec5cn_sign_match ((h.comm_iff p₁ p₂ a₃ a₄).mp hqa) hj hj'
  have hii : i = i' := sec5cn_sign_match ((h.comm_iff p₁ p₂ b₃ b₄).mp hqb) hi hi'
  subst hjj hii
  have hsign : π ((-1 : SL23) ^ (k : ℕ), (-1 : SL23) ^ (k' : ℕ)) = 1 ∨
      π ((-1 : SL23) ^ (k : ℕ), (-1 : SL23) ^ (k' : ℕ)) = z := by
    refine h.sign_mem ?_ ?_
    · fin_cases k <;> simp
    · fin_cases k' <;> simp
  have key : π (p₁, p₂) = π ((-1 : SL23) ^ (k : ℕ), (-1 : SL23) ^ (k' : ℕ)) *
      π (a₃, a₄) ^ (i : ℕ) * π (b₃, b₄) ^ (j : ℕ) := by
    rw [sec5cn_pi_pow_mk, sec5cn_pi_pow_mk, sec5cn_pi_mul_mk, sec5cn_pi_mul_mk, hp₁e, hp₂e]
  rcases hsign with hs | hs
  · exact ⟨i, j, 0, by rw [key, hs]; simp⟩
  · exact ⟨i, j, 1, by rw [key, hs]; simp⟩

theorem Sec5CNPi.rho_split (h : Sec5CNPi π K₃ K₄ z) {t a ρ : G} (ht : t ∈ K₃ ⊔ K₄)
    (ha : a ∈ K₃ ⊔ K₄) (hρ : ρ ∈ K₃ ⊔ K₄) (ht2 : t * t = 1) (ha2 : a * a = 1) (ht1 : t ≠ 1)
    (ha1 : a ≠ 1) (htz : t ≠ z) (haz : a ≠ z) (hat : a ≠ t) (hatz : a ≠ t * z)
    (hta : t * a = a * t) (hconj : ρ⁻¹ * t * ρ = a) :
    ∃ u v : SL23, π (u, v) = ρ ∧ u ^ 4 ≠ 1 ∧ v ^ 4 ≠ 1 := by
  obtain ⟨t₃, t₄, ht₃, ht₄, rfl⟩ := h.invol ht ht2 ht1 htz
  obtain ⟨a₃, a₄, ha₃, ha₄, rfl⟩ := h.invol ha ha2 ha1 haz
  obtain ⟨⟨u, v⟩, rfl⟩ := h.mem_iff.mp hρ
  have e : (π (u, v))⁻¹ * π (t₃, t₄) * π (u, v) = π (u⁻¹ * t₃ * u, v⁻¹ * t₄ * v) := by
    rw [sec5cn_pi_inv_mk, sec5cn_pi_mul_mk, sec5cn_pi_mul_mk]
  rw [e, h.eq_iff] at hconj
  have hm : (a₃ = u⁻¹ * t₃ * u ∧ a₄ = v⁻¹ * t₄ * v) ∨
      (a₃ = u⁻¹ * t₃ * u * (-1) ∧ a₄ = v⁻¹ * t₄ * v * (-1)) := by
    rcases hconj with h1 | h1
    · left
      exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
    · right
      exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
  have ht₃4 : t₃ ^ 4 = 1 := sec5cn_pow4_of_sq t₃ (Or.inr ht₃)
  have ht₄4 : t₄ ^ 4 = 1 := sec5cn_pow4_of_sq t₄ (Or.inr ht₄)
  refine ⟨u, v, rfl, fun hu => ?_, fun hv => ?_⟩
  · have e₃ := sec5cn_pm_of_conj t₃ u a₃ ht₃4 hu (hm.imp (fun h1 => h1.1) (fun h1 => h1.1))
    rcases h.comm_pm ht₃ ht₄ ha₃ ha₄ hta (Or.inl e₃) with h3 | h3
    · exact hat h3
    · exact hatz h3
  · have e₄ := sec5cn_pm_of_conj t₄ v a₄ ht₄4 hv (hm.imp (fun h1 => h1.2) (fun h1 => h1.2))
    rcases h.comm_pm ht₃ ht₄ ha₃ ha₄ hta (Or.inr e₄) with h3 | h3
    · exact hat h3
    · exact hatz h3

theorem Sec5CNPi.exists_comm_onto (h : Sec5CNPi π K₃ K₄ z) {u v : SL23} (hu3 : u ^ 3 = 1)
    (hv3 : v ^ 3 = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) {x : G} (hx : x ∈ K₃ ⊔ K₄)
    (hx4 : x ^ 4 = 1) :
    ∃ y ∈ K₃ ⊔ K₄, y ^ 4 = 1 ∧
      (y⁻¹ * (π (u, v))⁻¹ * y * π (u, v) = x ∨
        y⁻¹ * (π (u, v))⁻¹ * y * π (u, v) = z * x) := by
  obtain ⟨⟨p, q⟩, rfl⟩ := h.mem_iff.mp hx
  obtain ⟨hp, hq⟩ := (h.pow4_iff p q).mp hx4
  obtain ⟨y₁, hy₁, hy₁'⟩ := sec5cn_commutator_onto u hu3 hu1 p hp
  obtain ⟨y₂, hy₂, hy₂'⟩ := sec5cn_commutator_onto v hv3 hv1 q hq
  refine ⟨π (y₁, y₂), h.mk_mem y₁ y₂, (h.pow4_iff y₁ y₂).mpr ⟨hy₁, hy₂⟩, ?_⟩
  have e : (π (y₁, y₂))⁻¹ * (π (u, v))⁻¹ * π (y₁, y₂) * π (u, v) =
      π (y₁⁻¹ * u⁻¹ * y₁ * u, y₂⁻¹ * v⁻¹ * y₂ * v) := by
    rw [sec5cn_pi_inv_mk, sec5cn_pi_inv_mk, sec5cn_pi_mul_mk, sec5cn_pi_mul_mk,
      sec5cn_pi_mul_mk]
  rw [e]
  rcases hy₁' with h1 | h1 <;> rcases hy₂' with h2 | h2
  · left
    rw [h1, h2]
  · right
    rw [h1, h2, h.neg_right]
  · right
    rw [h1, h2, h.neg_left]
  · left
    rw [h1, h2, h.neg_both]

end CFSG.OddStandard.SmallF3.Omega
