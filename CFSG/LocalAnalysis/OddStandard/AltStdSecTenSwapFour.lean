module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapPair

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup

section Rigidity

variable {G : Type} [Group G] {a b c : G}

private lemma ab_inv (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    (a * b)⁻¹ = a * b := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb, hab.symm]

private lemma ab_mul_ab (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    (a * b) * (a * b) = 1 := by
  calc (a * b) * (a * b) = (a * b) * (a * b)⁻¹ := by rw [ab_inv ha hb hab]
    _ = 1 := mul_inv_cancel (a * b)

private lemma a_mul_ab (ha : a * a = 1) : a * (a * b) = b := by
  rw [← mul_assoc, ha, one_mul]

private lemma ab_mul_a (ha : a * a = 1) (hab : a * b = b * a) : (a * b) * a = b := by
  rw [mul_assoc, hab.symm, ← mul_assoc, ha, one_mul]

private lemma b_mul_ab (hb : b * b = 1) (hab : a * b = b * a) : b * (a * b) = a := by
  rw [← mul_assoc, hab.symm, mul_assoc, hb, mul_one]

private lemma ab_mul_b (hb : b * b = 1) : (a * b) * b = a := by
  rw [mul_assoc, hb, mul_one]

private lemma a_mul_ac (ha : a * a = 1) : a * (a * c) = c := by
  rw [← mul_assoc, ha, one_mul]

private lemma ac_mul_a (ha : a * a = 1) (hac : a * c = c * a) : (a * c) * a = c := by
  rw [mul_assoc, hac.symm, ← mul_assoc, ha, one_mul]

private lemma b_mul_bc (hb : b * b = 1) : b * (b * c) = c := by
  rw [← mul_assoc, hb, one_mul]

private lemma bc_mul_b (hb : b * b = 1) (hbc : b * c = c * b) : (b * c) * b = c := by
  rw [mul_assoc, hbc.symm, ← mul_assoc, hb, one_mul]

private lemma hABc (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    (a * b) * c = c * (a * b) := by
  calc (a * b) * c = a * (b * c) := mul_assoc a b c
    _ = a * (c * b) := by rw [hbc]
    _ = (a * c) * b := by rw [← mul_assoc]
    _ = (c * a) * b := by rw [hac.symm]
    _ = c * (a * b) := by rw [mul_assoc]

private lemma hAbc (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    a * (b * c) = (b * c) * a := by
  calc a * (b * c) = (a * b) * c := (mul_assoc a b c).symm
    _ = (b * a) * c := by rw [hab]
    _ = b * (a * c) := by rw [mul_assoc]
    _ = b * (c * a) := by rw [hac]
    _ = (b * c) * a := by rw [← mul_assoc]

private lemma hBac (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    b * (a * c) = (a * c) * b := by
  calc b * (a * c) = (b * a) * c := (mul_assoc b a c).symm
    _ = (a * b) * c := by rw [hab.symm]
    _ = a * (b * c) := by rw [mul_assoc]
    _ = a * (c * b) := by rw [hbc]
    _ = (a * c) * b := by rw [← mul_assoc]

private lemma abc_eq_ac_mul_b (hbc : b * c = c * b) : a * b * c = (a * c) * b := by
  calc a * b * c = a * (b * c) := mul_assoc a b c
    _ = a * (c * b) := by rw [hbc]
    _ = (a * c) * b := by rw [← mul_assoc]

private lemma ab_mul_abc (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    (a * b) * (a * b * c) = c := by
  rw [← mul_assoc (a * b) (a * b), ab_mul_ab ha hb hab, one_mul]

private lemma abc_mul_ab (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) : (a * b * c) * (a * b) = c := by
  calc (a * b * c) * (a * b) = ((a * b) * c) * (a * b) := rfl
    _ = (a * b) * (c * (a * b)) := by rw [mul_assoc]
    _ = (a * b) * ((a * b) * c) := by rw [hABc hab hac hbc]
    _ = ((a * b) * (a * b)) * c := by rw [← mul_assoc]
    _ = c := by rw [ab_mul_ab ha hb hab, one_mul]

private lemma ab_mul_ac (ha : a * a = 1) (hab : a * b = b * a) :
    (a * b) * (a * c) = b * c := by
  calc (a * b) * (a * c) = a * (b * (a * c)) := mul_assoc a b (a * c)
    _ = a * ((b * a) * c) := congrArg (fun x => a * x) (mul_assoc b a c).symm
    _ = a * ((a * b) * c) := by rw [hab.symm]
    _ = a * (a * (b * c)) := by rw [mul_assoc]
    _ = (a * a) * (b * c) := by rw [← mul_assoc]
    _ = b * c := by rw [ha, one_mul]

private lemma b_mul_ac (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    b * (a * c) = a * b * c := by
  rw [hBac hab hac hbc, ← abc_eq_ac_mul_b hbc]

private lemma ac_mul_ab (ha : a * a = 1) (hac : a * c = c * a) (hbc : b * c = c * b) :
    (a * c) * (a * b) = b * c := by
  calc (a * c) * (a * b) = a * (c * (a * b)) := mul_assoc a c (a * b)
    _ = a * ((c * a) * b) := congrArg (fun x => a * x) (mul_assoc c a b).symm
    _ = a * ((a * c) * b) := by rw [hac.symm]
    _ = a * (a * (c * b)) := congrArg (fun x => a * x) (mul_assoc a c b)
    _ = (a * a) * (c * b) := (mul_assoc a a (c * b)).symm
    _ = c * b := by rw [ha, one_mul]
    _ = b * c := by rw [hbc.symm]

private lemma comm_ab_ac (ha : a * a = 1) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) : (a * b) * (a * c) = (a * c) * (a * b) := by
  rw [ab_mul_ac ha hab, ac_mul_ab ha hac hbc]

private theorem mem_F_iff (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) {F : Subgroup G}
    (hF : ∀ p, p ∈ F ↔ ∃ i j k : Fin 2, p = a ^ (i : ℕ) * b ^ (j : ℕ) * c ^ (k : ℕ)) :
    ∀ p : G, p ∈ F ↔
      p = 1 ∨ p = a ∨ p = b ∨ p = a * b ∨ p = c ∨ p = a * c ∨ p = b * c ∨ p = a * b * c := by
  intro p
  constructor
  · intro hp
    obtain ⟨i, j, k, rfl⟩ := (hF p).mp hp
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp
  · intro hp
    rcases hp with h | h | h | h | h | h | h | h
    · rw [h]; exact (hF 1).mpr ⟨0, 0, 0, by simp⟩
    · rw [h]; exact (hF a).mpr ⟨1, 0, 0, by simp⟩
    · rw [h]; exact (hF b).mpr ⟨0, 1, 0, by simp⟩
    · rw [h]; exact (hF (a * b)).mpr ⟨1, 1, 0, by simp⟩
    · rw [h]; exact (hF c).mpr ⟨0, 0, 1, by simp⟩
    · rw [h]; exact (hF (a * c)).mpr ⟨1, 0, 1, by simp⟩
    · rw [h]; exact (hF (b * c)).mpr ⟨0, 1, 1, by simp⟩
    · rw [h]; exact (hF (a * b * c)).mpr ⟨1, 1, 1, by simp⟩

private theorem pairOrder_class
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hc1 : c ≠ 1) (hca : c ≠ a) (hcb : c ≠ b)
    (hcab : c ≠ a * b)
    {F : Subgroup G}
    (hF : ∀ p, p ∈ F ↔ ∃ i j k : Fin 2, p = a ^ (i : ℕ) * b ^ (j : ℕ) * c ^ (k : ℕ))
    {N₁ N₄ N₅ : ℕ} (h14 : N₁ ≠ N₄) (h15 : N₁ ≠ N₅)
    (e1 : pairOrder a b = N₁) (e2 : pairOrder a c = N₄) (e3 : pairOrder a (b * c) = N₅)
    (e4 : pairOrder b c = N₄) (e5 : pairOrder b (a * c) = N₅) (e6 : pairOrder (a * b) c = N₄)
    (e7 : pairOrder (a * b) (a * c) = N₅)
    {u v : G} (hu : u ∈ F) (hv : v ∈ F) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) :
    (pairOrder u v = N₁ ∧ ({u, v, u * v} : Set G) = {a, b, a * b}) ∨
      (pairOrder u v = N₄ ∧ c ∈ ({u, v, u * v} : Set G)) ∨ (pairOrder u v = N₅) := by
  have t_ab : pairOrder a b = N₁ := e1
  have t_ba : pairOrder b a = N₁ := by rw [pairOrder_comm, e1]
  have t_a_ab : pairOrder a (a * b) = N₁ := by rw [pairOrder_mul_right hab, e1]
  have t_ab_a : pairOrder (a * b) a = N₁ := by rw [pairOrder_comm, pairOrder_mul_right hab, e1]
  have t_b_ab : pairOrder b (a * b) = N₁ := by rw [pairOrder_mul_left hab, e1]
  have t_ab_b : pairOrder (a * b) b = N₁ := by rw [pairOrder_comm, pairOrder_mul_left hab, e1]
  have t_ac₀ : pairOrder a c = N₄ := e2
  have t_ca : pairOrder c a = N₄ := by rw [pairOrder_comm, e2]
  have t_a_ac : pairOrder a (a * c) = N₄ := by rw [pairOrder_mul_right hac, e2]
  have t_ac_a : pairOrder (a * c) a = N₄ := by rw [pairOrder_comm, pairOrder_mul_right hac, e2]
  have t_c_ac : pairOrder c (a * c) = N₄ := by rw [pairOrder_mul_left hac, e2]
  have t_ac_c : pairOrder (a * c) c = N₄ := by rw [pairOrder_comm, pairOrder_mul_left hac, e2]
  have t_bc₀ : pairOrder b c = N₄ := e4
  have t_cb : pairOrder c b = N₄ := by rw [pairOrder_comm, e4]
  have t_b_bc : pairOrder b (b * c) = N₄ := by rw [pairOrder_mul_right hbc, e4]
  have t_bc_b : pairOrder (b * c) b = N₄ := by rw [pairOrder_comm, pairOrder_mul_right hbc, e4]
  have t_c_bc : pairOrder c (b * c) = N₄ := by rw [pairOrder_mul_left hbc, e4]
  have t_bc_c : pairOrder (b * c) c = N₄ := by rw [pairOrder_comm, pairOrder_mul_left hbc, e4]
  have t_ab_c : pairOrder (a * b) c = N₄ := e6
  have t_c_ab : pairOrder c (a * b) = N₄ := by rw [pairOrder_comm, e6]
  have t_ab_abc : pairOrder (a * b) (a * b * c) = N₄ := by
    rw [pairOrder_mul_right (hABc hab hac hbc), e6]
  have t_abc_ab : pairOrder (a * b * c) (a * b) = N₄ := by
    rw [pairOrder_comm, pairOrder_mul_right (hABc hab hac hbc), e6]
  have t_c_abc : pairOrder c (a * b * c) = N₄ := by
    rw [pairOrder_mul_left (hABc hab hac hbc), e6]
  have t_abc_c : pairOrder (a * b * c) c = N₄ := by
    rw [pairOrder_comm, pairOrder_mul_left (hABc hab hac hbc), e6]
  have t_a_bc : pairOrder a (b * c) = N₅ := e3
  have t_bc_a : pairOrder (b * c) a = N₅ := by rw [pairOrder_comm, e3]
  have t_a_abc : pairOrder a (a * b * c) = N₅ := by
    rw [mul_assoc, pairOrder_mul_right (hAbc hab hac hbc), e3]
  have t_abc_a : pairOrder (a * b * c) a = N₅ := by
    rw [pairOrder_comm, mul_assoc, pairOrder_mul_right (hAbc hab hac hbc), e3]
  have t_bc_abc : pairOrder (b * c) (a * b * c) = N₅ := by
    rw [mul_assoc, pairOrder_mul_left (hAbc hab hac hbc), e3]
  have t_abc_bc : pairOrder (a * b * c) (b * c) = N₅ := by
    rw [pairOrder_comm, mul_assoc, pairOrder_mul_left (hAbc hab hac hbc), e3]
  have t_b_ac : pairOrder b (a * c) = N₅ := e5
  have t_ac_b : pairOrder (a * c) b = N₅ := by rw [pairOrder_comm, e5]
  have t_b_abc : pairOrder b (a * b * c) = N₅ := by
    rw [← b_mul_ac hab hac hbc, pairOrder_mul_right (hBac hab hac hbc), e5]
  have t_abc_b : pairOrder (a * b * c) b = N₅ := by
    rw [pairOrder_comm, ← b_mul_ac hab hac hbc, pairOrder_mul_right (hBac hab hac hbc), e5]
  have t_ac_abc : pairOrder (a * c) (a * b * c) = N₅ := by
    rw [← b_mul_ac hab hac hbc, pairOrder_mul_left (hBac hab hac hbc), e5]
  have t_abc_ac : pairOrder (a * b * c) (a * c) = N₅ := by
    rw [pairOrder_comm, ← b_mul_ac hab hac hbc, pairOrder_mul_left (hBac hab hac hbc), e5]
  have t_ab_ac : pairOrder (a * b) (a * c) = N₅ := e7
  have t_ac_ab : pairOrder (a * c) (a * b) = N₅ := by rw [pairOrder_comm, e7]
  have hcomm : (a * b) * (a * c) = (a * c) * (a * b) := comm_ab_ac ha hab hac hbc
  have t_ab_bc : pairOrder (a * b) (b * c) = N₅ := by
    rw [← ab_mul_ac ha hab, pairOrder_mul_right hcomm, e7]
  have t_bc_ab : pairOrder (b * c) (a * b) = N₅ := by
    rw [pairOrder_comm, ← ab_mul_ac ha hab, pairOrder_mul_right hcomm, e7]
  have t_ac_bc : pairOrder (a * c) (b * c) = N₅ := by
    rw [← ab_mul_ac ha hab, pairOrder_mul_left hcomm, e7]
  have t_bc_ac : pairOrder (b * c) (a * c) = N₅ := by
    rw [pairOrder_comm, ← ab_mul_ac ha hab, pairOrder_mul_left hcomm, e7]
  have htab : ∀ {x y : G}, (x = a ∧ y = b) → pairOrder x y = N₁ := by
    rintro x y ⟨rfl, rfl⟩; exact t_ab
  rw [mem_F_iff ha hb hc hab hac hbc hF u] at hu
  rw [mem_F_iff ha hb hc hab hac hbc hF v] at hv
  rcases hu with hu | hu | hu | hu | hu | hu | hu | hu <;> subst u <;>
    rcases hv with hv | hv | hv | hv | hv | hv | hv | hv <;> subst v
  all_goals
    first
    | exact absurd rfl hu1
    | exact absurd rfl hv1
    | exact absurd rfl huv
    | skip
  all_goals simp only [t_ab, t_ba, t_a_ab, t_ab_a, t_b_ab, t_ab_b, t_ac₀, t_ca, t_a_ac, t_ac_a,
        t_c_ac, t_ac_c, t_bc₀, t_cb, t_b_bc, t_bc_b, t_c_bc, t_bc_c, t_ab_c, t_c_ab, t_ab_abc,
        t_abc_ab, t_c_abc, t_abc_c, t_a_bc, t_bc_a, t_a_abc, t_abc_a, t_bc_abc, t_abc_bc, t_b_ac,
        t_ac_b,
        t_b_abc, t_abc_b, t_ac_abc, t_abc_ac, t_ab_ac, t_ac_ab, t_ab_bc, t_bc_ab, t_ac_bc,
        t_bc_ac]
  all_goals
    first
    | exact Or.inl ⟨trivial, by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        try simp only [a_mul_ab ha, ab_mul_a ha hab, b_mul_ab hb hab, ab_mul_b hb, hab.symm]
        simp only [or_comm, or_left_comm, or_assoc]⟩
    | exact Or.inl ⟨trivial, trivial⟩
    | exact Or.inr (Or.inl ⟨trivial, by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        try simp only [a_mul_ac ha, ac_mul_a ha hac, b_mul_bc hb, bc_mul_b hb hbc,
          ab_mul_abc ha hb hab, abc_mul_ab ha hb hab hac hbc]
        simp only [or_comm, or_left_comm, or_assoc, eq_self_iff_true, or_true, true_or, or_false,
          false_or]⟩)
    | exact Or.inr (Or.inr trivial)

end Rigidity

variable {G : Type} [Group G]

theorem commute_of_mem_normalizer_of_pairOrder
    {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hc1 : c ≠ 1) (hca : c ≠ a) (hcb : c ≠ b)
    (hcab : c ≠ a * b)
    {F : Subgroup G}
    (hF : ∀ p, p ∈ F ↔ ∃ i j k : Fin 2, p = a ^ (i : ℕ) * b ^ (j : ℕ) * c ^ (k : ℕ))
    {N₁ N₄ N₅ : ℕ} (h14 : N₁ ≠ N₄) (h15 : N₁ ≠ N₅) (h45 : N₄ ≠ N₅)
    (e1 : pairOrder a b = N₁) (e2 : pairOrder a c = N₄) (e3 : pairOrder a (b * c) = N₅)
    (e4 : pairOrder b c = N₄) (e5 : pairOrder b (a * c) = N₅)
    (e6 : pairOrder (a * b) c = N₄) (e7 : pairOrder (a * b) (a * c) = N₅)
    (hz1 : ∀ g : G, g * a * g⁻¹ ≠ b) (hz2 : ∀ g : G, g * a * g⁻¹ ≠ a * b)
    (hb' : ∀ g : G, g * a = a * g → g * b * g⁻¹ ≠ a * b)
    {g : G} (hg : g ∈ normalizer (F : Set G)) :
    g * a = a * g ∧ g * b = b * g ∧ g * c = c * g := by
  have hg' : ∀ p : G, p ∈ F ↔ g * p * g⁻¹ ∈ F :=
    (Subgroup.mem_set_normalizer_iff).mp hg
  have inj : ∀ {p q : G}, g * p * g⁻¹ = g * q * g⁻¹ → p = q := by
    intro p q h
    have h' := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using h'
  have haF : a ∈ F := (hF a).mpr ⟨1, 0, 0, by simp⟩
  have hbF : b ∈ F := (hF b).mpr ⟨0, 1, 0, by simp⟩
  have hcF : c ∈ F := (hF c).mpr ⟨0, 0, 1, by simp⟩
  set p1 : G := g * a * g⁻¹ with hp1
  set p2 : G := g * b * g⁻¹ with hp2
  set p3 : G := g * c * g⁻¹ with hp3
  have hp1F : p1 ∈ F := by rw [hp1]; exact (hg' a).mp haF
  have hp2F : p2 ∈ F := by rw [hp2]; exact (hg' b).mp hbF
  have hp3F : p3 ∈ F := by rw [hp3]; exact (hg' c).mp hcF
  have hp1ne : p1 ≠ 1 := fun h => ha1 (inj (p := a) (q := 1) (by rw [← hp1, h]; group))
  have hp2ne : p2 ≠ 1 := fun h => hb1 (inj (p := b) (q := 1) (by rw [← hp2, h]; group))
  have hp3ne : p3 ≠ 1 := fun h => hc1 (inj (p := c) (q := 1) (by rw [← hp3, h]; group))
  have hp1ne2 : p1 ≠ p2 :=
    fun h => hba (inj (p := a) (q := b) (by rw [← hp1, ← hp2]; exact h)).symm
  have hp1ne3 : p1 ≠ p3 :=
    fun h => hca (inj (p := a) (q := c) (by rw [← hp1, ← hp3]; exact h)).symm
  have hp2ne3 : p2 ≠ p3 :=
    fun h => hcb (inj (p := b) (q := c) (by rw [← hp2, ← hp3]; exact h)).symm
  have v12 : pairOrder p1 p2 = N₁ := by rw [hp1, hp2, pairOrder_conj g a b, e1]
  have v13 : pairOrder p1 p3 = N₄ := by rw [hp1, hp3, pairOrder_conj g a c, e2]
  have v23 : pairOrder p2 p3 = N₄ := by rw [hp2, hp3, pairOrder_conj g b c, e4]
  have k12 := pairOrder_class ha hb hc hab hac hbc ha1 hb1 hba hc1 hca hcb hcab hF h14 h15
    e1 e2 e3 e4 e5 e6 e7 hp1F hp2F hp1ne hp2ne hp1ne2
  have hset12 : ({p1, p2, p1 * p2} : Set G) = {a, b, a * b} := by
    rcases k12 with ⟨-, h⟩ | ⟨h4, -⟩ | h5
    · exact h
    · exact absurd (v12.symm.trans h4) h14
    · exact absurd (v12.symm.trans h5) h15
  have hp1mem : p1 ∈ ({a, b, a * b} : Set G) := by rw [← hset12]; simp
  have hp2mem : p2 ∈ ({a, b, a * b} : Set G) := by rw [← hset12]; simp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp1mem hp2mem
  have hp1a : p1 = a := by
    rcases hp1mem with h | h | h
    · exact h
    · exact absurd (hp1.symm.trans h) (hz1 g)
    · exact absurd (hp1.symm.trans h) (hz2 g)
  have hga : g * a = a * g :=
    (mul_inv_eq_iff_eq_mul).mp (by rw [← hp1]; exact hp1a)
  have hp2ne_a : p2 ≠ a := fun h => hp1ne2 (hp1a.trans h.symm)
  have hp2b : p2 = b := by
    rcases hp2mem with h | h | h
    · exact absurd h hp2ne_a
    · exact h
    · exact absurd (hp2.symm.trans h) (hb' g hga)
  have hgb : g * b = b * g := (mul_inv_eq_iff_eq_mul).mp (by rw [← hp2]; exact hp2b)
  have k13 := pairOrder_class ha hb hc hab hac hbc ha1 hb1 hba hc1 hca hcb hcab hF h14 h15
    e1 e2 e3 e4 e5 e6 e7 hp1F hp3F hp1ne hp3ne hp1ne3
  have k23 := pairOrder_class ha hb hc hab hac hbc ha1 hb1 hba hc1 hca hcb hcab hF h14 h15
    e1 e2 e3 e4 e5 e6 e7 hp2F hp3F hp2ne hp3ne hp2ne3
  have hc13 : c ∈ ({p1, p3, p1 * p3} : Set G) := by
    rcases k13 with ⟨h1, -⟩ | ⟨h4, hm⟩ | h5
    · exact absurd (v13.symm.trans h1).symm h14
    · exact hm
    · exact absurd (v13.symm.trans h5) h45
  have hc23 : c ∈ ({p2, p3, p2 * p3} : Set G) := by
    rcases k23 with ⟨h1, -⟩ | ⟨h4, hm⟩ | h5
    · exact absurd (v23.symm.trans h1).symm h14
    · exact hm
    · exact absurd (v23.symm.trans h5) h45
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc13 hc23
  have hp3c : p3 = c := by
    by_contra hne
    have h1 : p1 * p3 = c := by
      rcases hc13 with h | h | h
      · exact absurd (h.trans hp1a) hca
      · exact absurd h.symm hne
      · exact h.symm
    have h2 : p2 * p3 = c := by
      rcases hc23 with h | h | h
      · exact absurd (h.trans hp2b) hcb
      · exact absurd h.symm hne
      · exact h.symm
    exact hp1ne2 (mul_right_cancel (h1.trans h2.symm))
  have hgc : g * c = c * g := (mul_inv_eq_iff_eq_mul).mp (by rw [← hp3]; exact hp3c)
  exact ⟨hga, hgb, hgc⟩

end CFSG.OddStandard.AltStdSec.SwapPattern
