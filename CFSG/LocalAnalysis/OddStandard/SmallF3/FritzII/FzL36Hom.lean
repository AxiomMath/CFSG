module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL36HomA

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzJ36 CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G] {t x₁ x₂ lam : G} {T₂ : Subgroup G} {a₁₂ a₂₂ a₃₂ : G}

private theorem fzl_q8Hom_mem {p q : G} (hpq : IsQ8Pair p q) (hp : p ∈ T₂) (hq : q ∈ T₂)
    (r : Q8) : q8Hom hpq r ∈ T₂ := by
  cases r with
  | a i => change p ^ i.val ∈ T₂; exact T₂.pow_mem hp _
  | xa i => change q * p ^ i.val ∈ T₂; exact T₂.mul_mem hq (T₂.pow_mem hp _)

private theorem fzl_lamHom_mem (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂)
    (e : Multiplicative (ZMod 2)) : fzl_lamHom lam hsh.lam_sq e ∈ T₂ := by
  have hlam : lam ∈ T₂ := by rw [hsh.gen]; exact Subgroup.subset_closure (by simp)
  rcases fzl_forall_eq e with rfl | rfl
  · rw [fzl_lamHom_one]; exact T₂.one_mem
  · rw [fzl_lamHom_gen]; exact hlam

private theorem fzl_range_le (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    (fzl_pi hsh).range ≤ T₂ := by
  rintro g ⟨m, rfl⟩
  obtain ⟨n, e⟩ := m
  obtain ⟨a, b, c⟩ := n
  rw [fzl_pi_mk, fzl_fn_apply]
  have h₁ : x₁ * t ∈ T₂ := by rw [hsh.gen]; exact Subgroup.subset_closure (by simp)
  have h₂ : a₁₂ ∈ T₂ := by rw [hsh.gen]; exact Subgroup.subset_closure (by simp)
  have h₃ : x₂ * t ∈ T₂ := by rw [hsh.gen]; exact Subgroup.subset_closure (by simp)
  have h₄ : a₂₂ ∈ T₂ := by rw [hsh.gen]; exact Subgroup.subset_closure (by simp)
  have h₅ : (x₁ * x₂)⁻¹ * t ∈ T₂ := by
    rw [hsh.gen]; exact Subgroup.subset_closure (by simp)
  have h₆ : a₃₂ ∈ T₂ := by rw [hsh.gen]; exact Subgroup.subset_closure (by simp)
  exact T₂.mul_mem (T₂.mul_mem (fzl_q8Hom_mem hsh.quat₁ h₁ h₂ a)
    (T₂.mul_mem (fzl_q8Hom_mem hsh.quat₂ h₃ h₄ b)
      (fzl_q8Hom_mem hsh.quat₃ h₅ h₆ c))) (fzl_lamHom_mem hsh e)

private theorem fzl_le_range (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    T₂ ≤ (fzl_pi hsh).range := by
  have h : Subgroup.closure
      ({x₁ * t, a₁₂, x₂ * t, a₂₂, (x₁ * x₂)⁻¹ * t, a₃₂, lam} : Set G)
      ≤ (fzl_pi hsh).range := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact MonoidHom.mem_range.mpr ⟨⟨(QuaternionGroup.a 1, 1, 1), 1⟩, by
        simp only [fzl_pi_mk, fzl_fn_apply, fzl_lamHom_one, map_one, mul_one, one_mul,
          fzl_q8Hom_a_one hsh.quat₁]⟩
    · exact MonoidHom.mem_range.mpr ⟨⟨(QuaternionGroup.xa 0, 1, 1), 1⟩, by
        simp only [fzl_pi_mk, fzl_fn_apply, fzl_lamHom_one, map_one, mul_one, one_mul,
          fzl_q8Hom_xa_zero hsh.quat₁]⟩
    · exact MonoidHom.mem_range.mpr ⟨⟨(1, QuaternionGroup.a 1, 1), 1⟩, by
        simp only [fzl_pi_mk, fzl_fn_apply, fzl_lamHom_one, map_one, mul_one, one_mul,
          fzl_q8Hom_a_one hsh.quat₂]⟩
    · exact MonoidHom.mem_range.mpr ⟨⟨(1, QuaternionGroup.xa 0, 1), 1⟩, by
        simp only [fzl_pi_mk, fzl_fn_apply, fzl_lamHom_one, map_one, mul_one, one_mul,
          fzl_q8Hom_xa_zero hsh.quat₂]⟩
    · exact MonoidHom.mem_range.mpr ⟨⟨(1, 1, QuaternionGroup.a 1), 1⟩, by
        simp only [fzl_pi_mk, fzl_fn_apply, fzl_lamHom_one, map_one, mul_one, one_mul,
          fzl_q8Hom_a_one hsh.quat₃]⟩
    · exact MonoidHom.mem_range.mpr ⟨⟨(1, 1, QuaternionGroup.xa 0), 1⟩, by
        simp only [fzl_pi_mk, fzl_fn_apply, fzl_lamHom_one, map_one, mul_one, one_mul,
          fzl_q8Hom_xa_zero hsh.quat₃]⟩
    · exact MonoidHom.mem_range.mpr ⟨⟨1, Multiplicative.ofAdd 1⟩, by
        simp only [fzl_pi_mk, fzl_fn_one, fzl_lamHom_gen, one_mul]⟩
  rw [← hsh.gen] at h
  exact h

private theorem fzl_range_eq (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    (fzl_pi hsh).range = T₂ :=
  (le_antisymm (fzl_le_range hsh) (fzl_range_le hsh)).symm

private theorem fzl_pi_zeta (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    fzl_pi hsh zeta = 1 := by
  simp only [zeta, fzl_pi_mk, fzl_fn_apply, fzl_q8Hom_a_two, fzl_lamHom_one, mul_one]
  rw [hsh.sq_eq]
  set z1 : G := (x₁ * t) ^ 2 with hz1def
  set z2 : G := (x₂ * t) ^ 2 with hz2def
  have hz1 : z1 * z1 = 1 := by rw [hz1def, ← pow_add]; exact hsh.quat₁.1
  have hz2 : z2 * z2 = 1 := by rw [hz2def, ← pow_add]; exact hsh.quat₂.1
  have hc : Commute z1 z2 := by
    rw [hz1def, hz2def]
    exact ((hsh.comm₁₂ (x₁ * t) (by simp) (x₂ * t) (by simp)).pow_left 2).pow_right 2
  calc z1 * (z2 * (z1 * z2)) = (z1 * z2) * (z1 * z2) := by group
    _ = (z1 * z2) ^ 2 := by rw [pow_two]
    _ = z1 ^ 2 * z2 ^ 2 := hc.mul_pow 2
    _ = 1 := by rw [pow_two, pow_two, hz1, hz2, mul_one]

private def fzl_Ksub : Subgroup Model where
  carrier := {x | x = 1 ∨ x = zeta}
  mul_mem' := by
    rintro x y (rfl | rfl) (rfl | rfl) <;> simp [zeta_mul_zeta]
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro x (rfl | rfl)
    · exact Or.inl (by simp)
    · exact Or.inr (inv_eq_of_mul_eq_one_left zeta_mul_zeta)

private theorem fzl_mem_Ksub (x : Model) : x ∈ fzl_Ksub ↔ x = 1 ∨ x = zeta := Iff.rfl

private theorem fzl_Ksub_eq_zpowers : fzl_Ksub = Subgroup.zpowers zeta := by
  apply le_antisymm
  · rintro x (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers zeta
  · rw [Subgroup.zpowers_le]
    exact Or.inr rfl

private theorem fzl_card_zpowers : Nat.card (Subgroup.zpowers zeta) = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_zpowers,
    orderOf_eq_prime (by rw [pow_two]; exact zeta_mul_zeta) zeta_ne_one]

private theorem fzl_card_ker (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    Nat.card (fzl_pi hsh).ker = 2 := by
  have h := Subgroup.card_ker_mul_card_range (fzl_pi hsh)
  rw [fzl_range_eq, hsh.card, card_model] at h
  rw [show (2 : ℕ) ^ 9 = 512 from by norm_num] at h
  omega

private theorem fzl_ker_eq (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    (fzl_pi hsh).ker = fzl_Ksub := by
  have hz : zeta ∈ (fzl_pi hsh).ker := MonoidHom.mem_ker.mpr (fzl_pi_zeta hsh)
  have hle : fzl_Ksub ≤ (fzl_pi hsh).ker := by
    rw [fzl_Ksub_eq_zpowers, Subgroup.zpowers_le]
    exact hz
  have hker : fzl_Ksub = (fzl_pi hsh).ker :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [fzl_card_ker hsh, fzl_Ksub_eq_zpowers, fzl_card_zpowers])
  exact hker.symm

private theorem fzl_pi_eq_iff (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    ∀ g h : Model, fzl_pi hsh g = fzl_pi hsh h ↔ KEq g h := by
  intro g h
  constructor
  · intro hgh
    have hmem : h⁻¹ * g ∈ (fzl_pi hsh).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]
    rw [fzl_ker_eq, fzl_mem_Ksub] at hmem
    rcases hmem with h1 | hz
    · left
      exact (inv_mul_eq_one.mp h1).symm
    · right
      calc g = h * (h⁻¹ * g) := by group
        _ = h * zeta := by rw [hz]
  · rintro (rfl | hz)
    · rfl
    · rw [hz, map_mul, fzl_pi_zeta, mul_one]

theorem fzl_model_hom (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    ∃ π : Model →* G,
      (∀ q : Q8, π (⟨(q, 1, 1), 1⟩ : Model) = q8Hom hsh.quat₁ q) ∧
      (∀ q : Q8, π (⟨(1, q, 1), 1⟩ : Model) = q8Hom hsh.quat₂ q) ∧
      (∀ q : Q8, π (⟨(1, 1, q), 1⟩ : Model) = q8Hom hsh.quat₃ q) ∧
      π (⟨1, Multiplicative.ofAdd 1⟩ : Model) = lam ∧ π.range = T₂ ∧
      ∀ g h : Model, π g = π h ↔ KEq g h := by
  refine ⟨fzl_pi hsh, ?_, ?_, ?_, ?_, fzl_range_eq hsh, fzl_pi_eq_iff hsh⟩
  · intro q
    simp only [fzl_pi_mk, fzl_fn_apply, fzl_lamHom_one, map_one, mul_one, one_mul]
  · intro q
    simp only [fzl_pi_mk, fzl_fn_apply, fzl_lamHom_one, map_one, mul_one, one_mul]
  · intro q
    simp only [fzl_pi_mk, fzl_fn_apply, fzl_lamHom_one, map_one, mul_one, one_mul]
  · simp only [fzl_pi_mk, fzl_fn_apply, fzl_lamHom_gen, map_one, one_mul]

end CFSG.OddStandard.SmallF3.FritzII
