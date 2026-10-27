module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstructionBasic
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.NFacts
public import CFSG.LocalAnalysis.ABGTheoremB.CorollaryV61

public section

namespace CFSG.ABGTheoremB.TotallyInverted.DataConstruction

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

variable {G : Type} [Group G] {σ : Setting G}

theorem x₃_def (σ : Setting G) : σ.x₃ = σ.x * σ.x₂ := rfl

theorem conj_eq_iff_mul_eq {g y : G} : g * y * g⁻¹ = y ↔ g * y = y * g :=
  mul_inv_eq_iff_eq_mul

theorem inv_conj_of_conj {g y z : G} (h : g * y * g⁻¹ = z) : g⁻¹ * z * g⁻¹⁻¹ = y := by
  rw [← h]
  group

theorem conj_mul_conj (g y z : G) : g * (y * z) * g⁻¹ = g * y * g⁻¹ * (g * z * g⁻¹) := by
  group

theorem x_mul_x [Finite G] (hσ : σ.IsValid) : σ.x * σ.x = 1 := by
  rw [← sq, ← hσ.x_order, pow_orderOf_eq_one]

theorem x₂_mul_x₂ [Finite G] (hσ : σ.IsValid) : σ.x₂ * σ.x₂ = 1 := by
  rw [← sq, ← hσ.x₂_order, pow_orderOf_eq_one]

theorem x_ne_one [Finite G] (hσ : σ.IsValid) : σ.x ≠ 1 := fun h => by
  have := hσ.x_order
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem x₂_ne_one [Finite G] (hσ : σ.IsValid) : σ.x₂ ≠ 1 := fun h => by
  have := hσ.x₂_order
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem x₂_mul_x [Finite G] (hσ : σ.IsValid) : σ.x₂ * σ.x = σ.x₃ := hσ.commute.symm

theorem x_mul_x₃ [Finite G] (hσ : σ.IsValid) : σ.x * σ.x₃ = σ.x₂ := by
  rw [x₃_def, ← mul_assoc, x_mul_x hσ, one_mul]

theorem x₃_mul_x [Finite G] (hσ : σ.IsValid) : σ.x₃ * σ.x = σ.x₂ := by
  rw [x₃_def, mul_assoc, ← hσ.commute, ← mul_assoc, x_mul_x hσ, one_mul]

theorem x₂_mul_x₃ [Finite G] (hσ : σ.IsValid) : σ.x₂ * σ.x₃ = σ.x := by
  rw [x₃_def, ← mul_assoc, ← hσ.commute, mul_assoc, x₂_mul_x₂ hσ, mul_one]

theorem x₃_mul_x₂ [Finite G] (hσ : σ.IsValid) : σ.x₃ * σ.x₂ = σ.x := by
  rw [x₃_def, mul_assoc, x₂_mul_x₂ hσ, mul_one]

theorem x₃_mul_x₃ [Finite G] (hσ : σ.IsValid) : σ.x₃ * σ.x₃ = 1 := by
  calc σ.x₃ * σ.x₃ = σ.x * (σ.x₂ * σ.x) * σ.x₂ := by rw [x₃_def]; group
    _ = σ.x * σ.x * (σ.x₂ * σ.x₂) := by rw [← hσ.commute]; group
    _ = 1 := by rw [x_mul_x hσ, x₂_mul_x₂ hσ, one_mul]

theorem x₃_ne_one [Finite G] (hσ : σ.IsValid) : σ.x₃ ≠ 1 := fun h => by
  apply hσ.x_ne_x₂
  calc σ.x = σ.x * (σ.x₂ * σ.x₂) := by rw [x₂_mul_x₂ hσ, mul_one]
    _ = σ.x₃ * σ.x₂ := by rw [x₃_def]; group
    _ = σ.x₂ := by rw [h, one_mul]

theorem x₃_ne_x [Finite G] (hσ : σ.IsValid) : σ.x₃ ≠ σ.x := fun h => by
  apply x₂_ne_one hσ
  calc σ.x₂ = σ.x * σ.x₃ := (x_mul_x₃ hσ).symm
    _ = 1 := by rw [h, x_mul_x hσ]

theorem x₃_ne_x₂ [Finite G] (hσ : σ.IsValid) : σ.x₃ ≠ σ.x₂ := fun h => by
  apply x_ne_one hσ
  calc σ.x = σ.x₃ * σ.x₂ := (x₃_mul_x₂ hσ).symm
    _ = 1 := by rw [h, x₂_mul_x₂ hσ]

theorem mem_T_iff [Finite G] (hσ : σ.IsValid) {g : G} :
    g ∈ σ.T ↔ g = 1 ∨ g = σ.x ∨ g = σ.x₂ ∨ g = σ.x₃ := by
  have hinv : ∀ y : G, y * y = 1 → y⁻¹ = y := fun y h => inv_eq_of_mul_eq_one_right h
  constructor
  · intro hg
    refine Subgroup.closure_induction
      (p := fun g _ => g = 1 ∨ g = σ.x ∨ g = σ.x₂ ∨ g = σ.x₃) ?_ ?_ ?_ ?_ hg
    · intro y hy
      rcases hy with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl rfl
    · intro y z _ _ hy hz
      rcases hy with hy | hy | hy | hy <;> rcases hz with hz | hz | hz | hz <;> rw [hy, hz] <;>
        simp [x_mul_x hσ, x₂_mul_x₂ hσ, x₃_mul_x₃ hσ, ← x₃_def, x₂_mul_x hσ, x_mul_x₃ hσ,
          x₃_mul_x hσ, x₂_mul_x₃ hσ, x₃_mul_x₂ hσ]
    · intro y _ hy
      rcases hy with hy | hy | hy | hy <;> rw [hy]
      · simp
      · rw [hinv _ (x_mul_x hσ)]; simp
      · rw [hinv _ (x₂_mul_x₂ hσ)]; simp
      · rw [hinv _ (x₃_mul_x₃ hσ)]; simp
  · rintro (h | h | h | h) <;> rw [h]
    · exact one_mem _
    · exact σ.x_mem_T
    · exact σ.x₂_mem_T
    · exact σ.T.mul_mem σ.x_mem_T σ.x₂_mem_T

theorem sq_eq_one_of_mem_T [Finite G] (hσ : σ.IsValid) {t : G} (ht : t ∈ σ.T) : t ^ 2 = 1 := by
  rw [sq]
  rcases (mem_T_iff hσ).mp ht with h | h | h | h <;> rw [h]
  · exact one_mul 1
  · exact x_mul_x hσ
  · exact x₂_mul_x₂ hσ
  · exact x₃_mul_x₃ hσ

theorem mem_C_iff {g : G} : g ∈ σ.C ↔ g * σ.x = σ.x * g ∧ g * σ.x₂ = σ.x₂ * g := by
  rw [Setting.C, Setting.T, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨(h σ.x (Set.mem_insert _ _)).symm, (h σ.x₂ (Set.mem_insert_of_mem _ rfl)).symm⟩
  · rintro ⟨h1, h2⟩ y hy
    rcases hy with rfl | hy
    · exact h1.symm
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact h2.symm

theorem mem_C_of_conj {g : G} (h1 : g * σ.x * g⁻¹ = σ.x) (h2 : g * σ.x₂ * g⁻¹ = σ.x₂) :
    g ∈ σ.C :=
  mem_C_iff.mpr ⟨conj_eq_iff_mul_eq.mp h1, conj_eq_iff_mul_eq.mp h2⟩

theorem C_le_normalizer_T : σ.C ≤ Subgroup.normalizer (σ.T : Set G) :=
  Subgroup.centralizer_le_normalizer _

theorem normalizer_T_le_M : Subgroup.normalizer (σ.T : Set G) ≤ σ.M := by
  intro g hg
  rw [Setting.M, ← conjSub_eq_self_iff, Setting.C, conjSub_centralizer,
    conjSub_eq_self_of_mem hg]

theorem C_le_M : σ.C ≤ σ.M := Subgroup.le_normalizer

theorem D_le_normalizer_T : σ.D ≤ Subgroup.normalizer (σ.T : Set G) := inf_le_right

theorem conj_mem_T {g t : G} (hg : g ∈ Subgroup.normalizer (σ.T : Set G)) (ht : t ∈ σ.T) :
    g * t * g⁻¹ ∈ σ.T :=
  (Subgroup.mem_normalizer_iff.mp hg t).mp ht

theorem conj_cases [Finite G] (hσ : σ.IsValid) {g t : G}
    (hg : g ∈ Subgroup.normalizer (σ.T : Set G)) (ht : t ∈ σ.T) (ht1 : t ≠ 1) :
    g * t * g⁻¹ = σ.x ∨ g * t * g⁻¹ = σ.x₂ ∨ g * t * g⁻¹ = σ.x₃ := by
  rcases (mem_T_iff hσ).mp (conj_mem_T hg ht) with h | h | h | h
  · exact absurd (conj_eq_one_iff.mp h) ht1
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem exists_three_element [Finite G] (hA : automizerIndex σ.T = 6) :
    ∃ g ∈ Subgroup.normalizer (σ.T : Set G), g ∉ σ.C ∧ ∃ k : ℕ, g ^ 3 ^ k = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf 3 (Subgroup.normalizer (σ.T : Set G))
  by_contra hcon
  push Not at hcon
  have hPC : P ≤ σ.C := by
    intro g hg
    by_contra hgC
    obtain ⟨k, hk⟩ := hP.isPGroup ⟨g, hg⟩
    exact hcon g (hP.le hg) hgC k (by simpa using congrArg Subtype.val hk)
  have h1 := Subgroup.relIndex_mul_relIndex P σ.C _ hPC C_le_normalizer_T
  have h2 : σ.C.relIndex (Subgroup.normalizer (σ.T : Set G)) = 6 := hA
  have h3 := (isSylowOf_iff.mp hP).2.2
  rw [← h1, h2] at h3
  exact h3 (dvd_mul_of_dvd_right (by norm_num) _)

theorem mem_C_of_sq_mem_C {g : G} {k : ℕ} (hk : g ^ 3 ^ k = 1) (h : g ^ 2 ∈ σ.C) :
    g ∈ σ.C := by
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have : g = (g ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = 3 ^ k + 1 by omega, pow_succ, hk, one_mul]
  rw [this]
  exact σ.C.pow_mem h _

theorem exists_a [Finite G] (hσ : σ.IsValid) (hA : automizerIndex σ.T = 6) :
    ∃ a ∈ Subgroup.normalizer (σ.T : Set G), (∃ k : ℕ, a ^ 3 ^ k = 1) ∧
      a * σ.x * a⁻¹ = σ.x₂ ∧ a * σ.x₂ * a⁻¹ = σ.x₃ := by
  obtain ⟨g, hgN, hgC, k, hk⟩ := exists_three_element hA
  have hsq : g ^ 2 * σ.x * (g ^ 2)⁻¹ = σ.x → g ^ 2 * σ.x₂ * (g ^ 2)⁻¹ = σ.x₂ → False :=
    fun hx hx₂ => hgC (mem_C_of_sq_mem_C hk (mem_C_of_conj hx hx₂))
  have e2 : ∀ y : G, g ^ 2 * y * (g ^ 2)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := fun y => by
    rw [sq]; group
  have e3 : g * σ.x₃ * g⁻¹ = g * σ.x * g⁻¹ * (g * σ.x₂ * g⁻¹) := by
    rw [x₃_def, conj_mul_conj]
  have hinj : g * σ.x * g⁻¹ ≠ g * σ.x₂ * g⁻¹ := fun h =>
    hσ.x_ne_x₂ (mul_left_cancel (mul_right_cancel h))
  rcases conj_cases hσ hgN σ.x_mem_T (x_ne_one hσ) with h1 | h1 | h1 <;>
    rcases conj_cases hσ hgN σ.x₂_mem_T (x₂_ne_one hσ) with h2 | h2 | h2
  · exact (hinj (h1.trans h2.symm)).elim
  · exact (hgC (mem_C_of_conj h1 h2)).elim
  · exact (hsq (by rw [e2, h1, h1]) (by rw [e2, h2, e3, h1, h2, x_mul_x₃ hσ])).elim
  · exact (hsq (by rw [e2, h1, h2]) (by rw [e2, h2, h1])).elim
  · exact (hinj (h1.trans h2.symm)).elim
  · exact ⟨g, hgN, ⟨k, hk⟩, h1, h2⟩
  · refine ⟨g⁻¹, inv_mem hgN, ⟨k, by rw [inv_pow, hk, inv_one]⟩, inv_conj_of_conj h2,
      inv_conj_of_conj ?_⟩
    rw [e3, h1, h2, x₃_mul_x hσ]
  · exact (hsq (by rw [e2, h1, e3, h1, h2, x₃_mul_x₂ hσ]) (by rw [e2, h2, h2])).elim
  · exact (hinj (h1.trans h2.symm)).elim

theorem xs_cycle [Finite G] (hσ : σ.IsValid) {a : G} (h1 : a * σ.x * a⁻¹ = σ.x₂)
    (h2 : a * σ.x₂ * a⁻¹ = σ.x₃) (i : Fin 3) : a * σ.xs i * a⁻¹ = σ.xs (i + 1) := by
  fin_cases i
  · exact h1
  · exact h2
  · show a * σ.x₃ * a⁻¹ = σ.x
    rw [x₃_def, conj_mul_conj, h1, h2, x₂_mul_x₃ hσ]

theorem pow_conj_xs {a : G} (ha : ∀ i : Fin 3, a * σ.xs i * a⁻¹ = σ.xs (i + 1)) (i j : Fin 3) :
    a ^ (i : ℕ) * σ.xs j * (a ^ (i : ℕ))⁻¹ = σ.xs (j + i) := by
  fin_cases i
  · show a ^ 0 * σ.xs j * (a ^ 0)⁻¹ = σ.xs (j + 0)
    simp
  · show a ^ 1 * σ.xs j * (a ^ 1)⁻¹ = σ.xs (j + 1)
    rw [pow_one]
    exact ha j
  · show a ^ 2 * σ.xs j * (a ^ 2)⁻¹ = σ.xs (j + 2)
    rw [show a ^ 2 * σ.xs j * (a ^ 2)⁻¹ = a * (a * σ.xs j * a⁻¹) * a⁻¹ by rw [sq]; group, ha, ha,
      add_assoc]
    rfl

theorem pow_three_conj_xs {a : G} (ha : ∀ i : Fin 3, a * σ.xs i * a⁻¹ = σ.xs (i + 1))
    (j : Fin 3) : a ^ 3 * σ.xs j * (a ^ 3)⁻¹ = σ.xs j := by
  have h2 := pow_conj_xs ha 2 j
  rw [show ((2 : Fin 3) : ℕ) = 2 from rfl] at h2
  rw [show a ^ 3 * σ.xs j * (a ^ 3)⁻¹ = a * (a ^ 2 * σ.xs j * (a ^ 2)⁻¹) * a⁻¹ by
    rw [pow_succ']; group, h2, ha, add_assoc, show (2 + 1 : Fin 3) = 0 from rfl, add_zero]

theorem pow_three_mem_C {a : G} (ha : ∀ i : Fin 3, a * σ.xs i * a⁻¹ = σ.xs (i + 1)) :
    a ^ 3 ∈ σ.C :=
  mem_C_of_conj (pow_three_conj_xs ha 0) (pow_three_conj_xs ha 1)

theorem D_eq_S [Finite G] (hσ : σ.IsValid) (hh : σ.height ≠ 1) : σ.D = σ.S :=
  inf_eq_left.mpr (hσ.T_normal hh)

theorem conj_x_of_mem_D [Finite G] (hσ : σ.IsValid) {d : G} (hd : d ∈ σ.D) :
    d * σ.x * d⁻¹ = σ.x :=
  conj_eq_iff_mul_eq.mpr (Subgroup.mem_centralizer_iff.mp hσ.x_mem_center.2 d (σ.D_le_S hd))

theorem exists_d_of_height_ne_one [Finite G] (hσ : σ.IsValid) (hh : σ.height ≠ 1) :
    ∃ d ∈ σ.D, d * σ.x₂ * d⁻¹ = σ.x₃ := by
  have hx₂ : σ.x₂ ∉ Subgroup.centralizer ((σ.S : Subgroup G) : Set G) := fun h =>
    hσ.x_ne_x₂ (hσ.center_involution _ ⟨hσ.x₂_mem, h⟩ hσ.x₂_order).symm
  rw [Subgroup.mem_centralizer_iff] at hx₂
  push Not at hx₂
  obtain ⟨s, hs, hsx₂⟩ := hx₂
  have hsD : s ∈ σ.D := ⟨hs, hσ.T_normal hh hs⟩
  have hsx : s * σ.x * s⁻¹ = σ.x := conj_x_of_mem_D hσ hsD
  refine ⟨s, hsD, ?_⟩
  rcases conj_cases hσ (D_le_normalizer_T hsD) σ.x₂_mem_T (x₂_ne_one hσ) with h | h | h
  · exact (hσ.x_ne_x₂ (mul_left_cancel (mul_right_cancel (hsx.trans h.symm)))).elim
  · exact (hsx₂ (conj_eq_iff_mul_eq.mp h)).elim
  · exact h

theorem F₀_eq (σ : Setting G) : σ.F₀ = (σ.S : Subgroup G) ⊓ σ.C := by
  rw [Setting.F₀, Setting.D, inf_assoc, inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)]
  rfl

theorem F₀_le_C : σ.F₀ ≤ σ.C := inf_le_right

theorem isPGroup_D : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S

theorem isPGroup_T [Finite G] (hσ : σ.IsValid) : IsPGroup 2 σ.T :=
  σ.S.isPGroup'.to_le (σ.T_le_S hσ)

theorem isSylowOf_S [Finite G] : IsSylowOf 2 (σ.S : Subgroup G) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isSylowOf_iff.mpr ⟨le_top, σ.S.isPGroup',
    by rw [Subgroup.relIndex_top_right]; exact σ.S.not_dvd_index⟩

theorem isSylowOf_F₀_of_height_ne_one [Finite G] (hσ : σ.IsValid) (hh : σ.height ≠ 1) :
    IsSylowOf 2 σ.F₀ σ.C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylowOf 2 (σ.S : Subgroup G) (Subgroup.normalizer (σ.T : Set G)) :=
    isSylowOf_S.of_le (hσ.T_normal hh) le_top
  rw [F₀_eq]
  exact hS.inf_of_le_normalizer C_le_normalizer_T (normalizer_T_le_M)

theorem mem_T_of_mem_C [Finite G] (hF₀ : IsSylowOf 2 σ.F₀ σ.C) (hT : σ.TIFacts) {t : G}
    (ht : t ∈ σ.C) (ht2 : t ^ 2 = 1) : t ∈ σ.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 (Subgroup.zpowers t) := by
    rintro ⟨y, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (t ^ n) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  obtain ⟨c, hc, hle⟩ := exists_le_conjSub_of_isSylowOf hF₀
    (Subgroup.zpowers_le.mpr ht) hzp
  have htc : c⁻¹ * t * c ∈ σ.F₀ := mem_conjSub_iff.mp (hle (Subgroup.mem_zpowers t))
  have htc2 : (c⁻¹ * t * c) ^ 2 = 1 := by
    rw [sq, show c⁻¹ * t * c * (c⁻¹ * t * c) = c⁻¹ * (t * t) * c by group, ← sq, ht2]
    group
  have hT' := hT.F₀_omega _ htc htc2
  have hcomm := Subgroup.mem_centralizer_iff.mp hc _ hT'
  have : t = c⁻¹ * t * c := by
    calc t = c * (c⁻¹ * t * c) * c⁻¹ := by group
      _ = c⁻¹ * t * c * c * c⁻¹ := by rw [← hcomm]
      _ = c⁻¹ * t * c := by group
  rw [this]
  exact hT'

theorem M_le_normalizer_T [Finite G] (hσ : σ.IsValid) (hF₀ : IsSylowOf 2 σ.F₀ σ.C)
    (hT : σ.TIFacts) : σ.M ≤ Subgroup.normalizer (σ.T : Set G) := by
  intro m hm
  refine mem_normalizer_of_conj_mem fun t ht => mem_T_of_mem_C hF₀ hT ?_ ?_
  · exact (Subgroup.mem_normalizer_iff.mp hm t).mp (σ.T_le_C hσ ht)
  · rw [conj_pow, sq_eq_one_of_mem_T hσ ht, mul_one, mul_inv_cancel]

theorem M_eq [Finite G] (hσ : σ.IsValid) (hF₀ : IsSylowOf 2 σ.F₀ σ.C) (hT : σ.TIFacts) {a d : G}
    (ha : a ∈ Subgroup.normalizer (σ.T : Set G)) (ha1 : a * σ.x * a⁻¹ = σ.x₂)
    (ha2 : a * σ.x₂ * a⁻¹ = σ.x₃) (hd : d ∈ σ.D) (hd1 : d * σ.x * d⁻¹ = σ.x)
    (hd2 : d * σ.x₂ * d⁻¹ = σ.x₃) : σ.M = σ.C ⊔ Subgroup.closure ({d, a} : Set G) := by
  set K := σ.C ⊔ Subgroup.closure ({d, a} : Set G)
  have hdK : d ∈ K := Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_insert _ _))
  have haK : a ∈ K :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  refine le_antisymm (fun m hm => ?_) (sup_le C_le_M ?_)
  · have hmT := M_le_normalizer_T hσ hF₀ hT hm
    have key : ∀ m' ∈ Subgroup.normalizer (σ.T : Set G), m' * σ.x * m'⁻¹ = σ.x → m' ∈ K := by
      intro m' hm' hx
      rcases conj_cases hσ hm' σ.x₂_mem_T (x₂_ne_one hσ) with h | h | h
      · exact (hσ.x_ne_x₂ (mul_left_cancel (mul_right_cancel (hx.trans h.symm)))).elim
      · exact Subgroup.mem_sup_left (mem_C_of_conj hx h)
      · have hC : d⁻¹ * m' ∈ σ.C := by
          refine mem_C_of_conj ?_ ?_
          · rw [show d⁻¹ * m' * σ.x * (d⁻¹ * m')⁻¹ = d⁻¹ * (m' * σ.x * m'⁻¹) * d⁻¹⁻¹ by group,
              hx, inv_conj_of_conj hd1]
          · rw [show d⁻¹ * m' * σ.x₂ * (d⁻¹ * m')⁻¹ = d⁻¹ * (m' * σ.x₂ * m'⁻¹) * d⁻¹⁻¹ by group,
              h, inv_conj_of_conj hd2]
        rw [show m' = d * (d⁻¹ * m') by group]
        exact K.mul_mem hdK (Subgroup.mem_sup_left hC)
    rcases conj_cases hσ hmT σ.x_mem_T (x_ne_one hσ) with h | h | h
    · exact key m hmT h
    · have hm' := key (a⁻¹ * m) (Subgroup.mul_mem _ (inv_mem ha) hmT) (by
        rw [show a⁻¹ * m * σ.x * (a⁻¹ * m)⁻¹ = a⁻¹ * (m * σ.x * m⁻¹) * a⁻¹⁻¹ by group, h,
          inv_conj_of_conj ha1])
      rw [show m = a * (a⁻¹ * m) by group]
      exact K.mul_mem haK hm'
    · have hb : (a * a) * σ.x * (a * a)⁻¹ = σ.x₃ := by
        rw [show a * a * σ.x * (a * a)⁻¹ = a * (a * σ.x * a⁻¹) * a⁻¹ by group, ha1, ha2]
      have hm' := key ((a * a)⁻¹ * m) (Subgroup.mul_mem _ (inv_mem (Subgroup.mul_mem _ ha ha))
        hmT) (by
        rw [show (a * a)⁻¹ * m * σ.x * ((a * a)⁻¹ * m)⁻¹ =
            (a * a)⁻¹ * (m * σ.x * m⁻¹) * (a * a)⁻¹⁻¹ by group, h, inv_conj_of_conj hb])
      rw [show m = (a * a) * ((a * a)⁻¹ * m) by group]
      exact K.mul_mem (K.mul_mem haK haK) hm'
  · rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact normalizer_T_le_M (D_le_normalizer_T hd)
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact normalizer_T_le_M ha

theorem L_le_N [Finite G] (hσ : σ.IsValid) : σ.L ≤ σ.N := sup_le hσ.L₀_le_N (σ.S_le_N hσ)

theorem L₀_le_L : σ.L₀ ≤ σ.L := le_sup_left

theorem ON_le_L [Finite G] (hσ : σ.IsValid) : σ.ON ≤ σ.L := hσ.ON_le_L₀.trans L₀_le_L

theorem T_le_L [Finite G] (hσ : σ.IsValid) : σ.T ≤ σ.L := (σ.T_le_S hσ).trans le_sup_right

theorem N_le_normalizer_L [Finite G] (hσ : σ.IsValid) (hT : σ.TIFacts) :
    σ.N ≤ Subgroup.normalizer (σ.L : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_mem fun l hl => ?_
  have hc : g * l * g⁻¹ * l⁻¹ ∈ σ.L₀ := by
    have := Subgroup.commutator_mem_commutator hg (L_le_N hσ hl)
    rw [commutatorElement_def] at this
    exact hT.commutator_le this
  have := σ.L.mul_mem (L₀_le_L hc) hl
  rwa [show g * l * g⁻¹ * l⁻¹ * l = g * l * g⁻¹ by group] at this

@[expose] def NoExceptionalLayer (σ : Setting G) : Prop :=
  ∀ J : Subgroup G, J ≤ σ.L₀ → σ.L₀ = J ⊔ σ.ON → J ≤ Subgroup.centralizer (σ.ON : Set G) →
    σ.N ≤ Subgroup.normalizer (J : Set G) →
      ¬ (σ.q = 9 ∧ σ.height = 1 ∧ Nat.card (J ⊓ σ.ON : Subgroup G) = 3)

theorem noExceptionalLayer_of_height_ne_one (hh : σ.height ≠ 1) : NoExceptionalLayer σ :=
  fun _ _ _ _ _ h => hh h.2.1

theorem exists_layerComplement [Finite G] (hJ : NoExceptionalLayer σ) (hV : σ.CorollaryV61) :
    ∃ J : Subgroup G, σ.IsLayerComplement J ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = σ.q ∧ Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨J, hJle, hsup, hcent, hnorm, h⟩ := hV.layer
  rcases h with ⟨hinf, hsl⟩ | h
  · exact ⟨J, ⟨hJle, hsup, hinf, hnorm, hcent⟩, hsl⟩
  · exact absurd h (hJ J hJle hsup hcent hnorm)

theorem J_le_N [Finite G] (hσ : σ.IsValid) {J : Subgroup G} (hJ : σ.IsLayerComplement J) :
    J ≤ σ.N :=
  hJ.le.trans hσ.L₀_le_N

theorem J_le_L [Finite G] {J : Subgroup G} (hJ : σ.IsLayerComplement J) : J ≤ σ.L :=
  hJ.le.trans L₀_le_L

theorem inf_C_eq_bot [Finite G] {r : ℕ} (hr : r.Prime) (hti : σ.TotallyInverted r)
    {X : Subgroup G} (hX : IsPGroup r X) (hXL : X ≤ σ.L) : X ⊓ σ.C = ⊥ :=
  eq_bot_of_isPGroup_of_le hr (hX.to_le inf_le_left) (le_inf inf_le_right
    (inf_le_left.trans hXL)) hti

theorem inf_L_eq_bot [Finite G] {r : ℕ} (hr : r.Prime) (hti : σ.TotallyInverted r)
    {X : Subgroup G} (hX : IsPGroup r X) (hXC : X ≤ σ.C) : X ⊓ σ.L = ⊥ :=
  eq_bot_of_isPGroup_of_le hr (hX.to_le inf_le_left) (le_inf (inf_le_left.trans hXC)
    inf_le_right) hti

theorem isCyclic_W [Finite G] (hT : σ.TIFacts) {J : Subgroup G} (hJ : σ.IsLayerComplement J) :
    IsCyclic (oddCoreIn (σ.C ⊓ J)) :=
  have := hT.cyclic J hJ
  Subgroup.isCyclic_of_le (oddCoreIn_le _)

theorem not_dvd_card_W [Finite G] {r : ℕ} (hti : σ.TotallyInverted r) {J : Subgroup G}
    (hJ : σ.IsLayerComplement J) : ¬ r ∣ Nat.card (oddCoreIn (σ.C ⊓ J)) := fun h =>
  hti (h.trans (Subgroup.card_dvd_of_le ((oddCoreIn_le _).trans
    (inf_le_inf_left _ (J_le_L hJ)))))

theorem pCoreIn_C_eq_bot [Finite G] (hT : σ.TIFacts) {r : ℕ} (hr : r.Prime)
    (hti : σ.TotallyInverted r) {J : Subgroup G} (hJ : σ.IsLayerComplement J) :
    pCoreIn r σ.C = ⊥ := by
  set X := pCoreIn r σ.C
  have hXC : X ≤ σ.C := pCoreIn_le r σ.C
  have hXL : X ⊓ σ.L = ⊥ := inf_L_eq_bot hr hti (isPGroup_pCoreIn r σ.C) hXC
  have hCJ : σ.C ≤ Subgroup.normalizer ((σ.C ⊓ J : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer (σ.C_le_N.trans hJ.normal)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hinf : X ⊓ (σ.C ⊓ J) = ⊥ :=
    eq_bot_iff.mpr (hXL ▸ inf_le_inf_left X (inf_le_right.trans (J_le_L hJ)))
  have hcent : X ≤ Subgroup.centralizer ((σ.C ⊓ J : Subgroup G) : Set G) :=
    le_centralizer_of_inf_eq_bot (hXC.trans hCJ)
      (inf_le_left.trans (le_normalizer_pCoreIn r σ.C)) hinf
  have hXL' : X ≤ σ.L := fun g hg => hT.centralizer_le J hJ g (hXC hg) (hcent hg)
  rw [← inf_eq_left.mpr hXL', hXL]

end CFSG.ABGTheoremB.TotallyInverted.DataConstruction
