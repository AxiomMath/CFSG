module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.PairTypes
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapTgrp

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G]

section Helpers

variable {a b c : G}

private lemma ab_inv (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    (a * b)⁻¹ = a * b := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb, hab.symm]

private lemma ac_inv (ha : a * a = 1) (hc : c * c = 1) (hac : a * c = c * a) :
    (a * c)⁻¹ = a * c := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hc, hac.symm]

private lemma bc_inv (hb : b * b = 1) (hc : c * c = 1) (hbc : b * c = c * b) :
    (b * c)⁻¹ = b * c := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb, inv_eq_of_mul_eq_one_right hc, hbc.symm]

private lemma ab_mul_ab (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    (a * b) * (a * b) = 1 := by
  calc (a * b) * (a * b) = (a * b) * (a * b)⁻¹ := by rw [ab_inv ha hb hab]
    _ = 1 := mul_inv_cancel (a * b)

private lemma ac_mul_ac (ha : a * a = 1) (hc : c * c = 1) (hac : a * c = c * a) :
    (a * c) * (a * c) = 1 := by
  calc (a * c) * (a * c) = (a * c) * (a * c)⁻¹ := by rw [ac_inv ha hc hac]
    _ = 1 := mul_inv_cancel (a * c)

private lemma bc_mul_bc (hb : b * b = 1) (hc : c * c = 1) (hbc : b * c = c * b) :
    (b * c) * (b * c) = 1 := by
  calc (b * c) * (b * c) = (b * c) * (b * c)⁻¹ := by rw [bc_inv hb hc hbc]
    _ = 1 := mul_inv_cancel (b * c)

private lemma c_mul_ac (hc : c * c = 1) (hac : a * c = c * a) : c * (a * c) = a := by
  rw [← mul_assoc, hac.symm, mul_assoc, hc, mul_one]

private lemma ac_mul_c (hc : c * c = 1) : (a * c) * c = a := by
  rw [mul_assoc, hc, mul_one]

private lemma c_mul_bc (hc : c * c = 1) (hbc : b * c = c * b) : c * (b * c) = b := by
  rw [← mul_assoc, hbc.symm, mul_assoc, hc, mul_one]

private lemma bc_mul_c (hc : c * c = 1) : (b * c) * c = b := by
  rw [mul_assoc, hc, mul_one]

private lemma ab_mul_a (ha : a * a = 1) (hab : a * b = b * a) : (a * b) * a = b := by
  rw [mul_assoc, hab.symm, ← mul_assoc, ha, one_mul]

private lemma ab_mul_b (hb : b * b = 1) : (a * b) * b = a := by
  rw [mul_assoc, hb, mul_one]

private lemma a_mul_ab (ha : a * a = 1) : a * (a * b) = b := by
  rw [← mul_assoc, ha, one_mul]

private lemma b_mul_ab (hb : b * b = 1) (hab : a * b = b * a) : b * (a * b) = a := by
  rw [← mul_assoc, hab.symm, mul_assoc, hb, mul_one]

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

private lemma abc_eq_bc_mul_a (hab : a * b = b * a) (hac : a * c = c * a) :
    a * b * c = (b * c) * a := by
  calc a * b * c = (a * b) * c := rfl
    _ = (b * a) * c := by rw [hab]
    _ = b * (a * c) := by rw [mul_assoc]
    _ = b * (c * a) := by rw [hac]
    _ = (b * c) * a := by rw [← mul_assoc]

private lemma ac_mul_abc (ha : a * a = 1) (hc : c * c = 1) (hac : a * c = c * a)
    (hbc : b * c = c * b) : (a * c) * (a * b * c) = b := by
  calc (a * c) * (a * b * c) = (a * c) * ((a * c) * b) := by rw [abc_eq_ac_mul_b hbc]
    _ = ((a * c) * (a * c)) * b := by rw [← mul_assoc]
    _ = b := by rw [ac_mul_ac ha hc hac, one_mul]

private lemma abc_mul_ac (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    (a * b * c) * (a * c) = b := by
  calc (a * b * c) * (a * c) = ((a * c) * b) * (a * c) := by rw [abc_eq_ac_mul_b hbc]
    _ = (a * c) * (b * (a * c)) := by rw [mul_assoc]
    _ = (a * c) * ((a * c) * b) := by rw [hBac hab hac hbc]
    _ = ((a * c) * (a * c)) * b := by rw [← mul_assoc]
    _ = b := by rw [ac_mul_ac ha hc hac, one_mul]

private lemma bc_mul_abc (hb : b * b = 1) (hc : c * c = 1) (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) : (b * c) * (a * b * c) = a := by
  calc (b * c) * (a * b * c) = (b * c) * ((b * c) * a) := by rw [abc_eq_bc_mul_a hab hac]
    _ = ((b * c) * (b * c)) * a := by rw [← mul_assoc]
    _ = a := by rw [bc_mul_bc hb hc hbc, one_mul]

private lemma abc_mul_bc (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    (a * b * c) * (b * c) = a := by
  calc (a * b * c) * (b * c) = ((b * c) * a) * (b * c) := by rw [abc_eq_bc_mul_a hab hac]
    _ = (b * c) * (a * (b * c)) := by rw [mul_assoc]
    _ = (b * c) * ((b * c) * a) := by rw [hAbc hab hac hbc]
    _ = ((b * c) * (b * c)) * a := by rw [← mul_assoc]
    _ = a := by rw [bc_mul_bc hb hc hbc, one_mul]

private lemma ac_mul_bc (hc : c * c = 1) (hbc : b * c = c * b) :
    (a * c) * (b * c) = a * b := by
  calc (a * c) * (b * c) = a * (c * (b * c)) := mul_assoc a c (b * c)
    _ = a * ((c * b) * c) := congrArg (fun x => a * x) (mul_assoc c b c).symm
    _ = a * ((b * c) * c) := by rw [hbc.symm]
    _ = a * (b * (c * c)) := congrArg (fun x => a * x) (mul_assoc b c c)
    _ = a * b := by rw [hc, mul_one]

private lemma c_mul_abc (hc : c * c = 1) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) : c * (a * b * c) = a * b := by
  calc c * (a * b * c) = c * ((a * b) * c) := rfl
    _ = (c * (a * b)) * c := (mul_assoc c (a * b) c).symm
    _ = ((a * b) * c) * c := by rw [← hABc hab hac hbc]
    _ = (a * b) * (c * c) := mul_assoc (a * b) c c
    _ = a * b := by rw [hc, mul_one]

private lemma bc_mul_ac (hc : c * c = 1) (hab : a * b = b * a) (hac : a * c = c * a) :
    (b * c) * (a * c) = a * b := by
  calc (b * c) * (a * c) = b * (c * (a * c)) := mul_assoc b c (a * c)
    _ = b * ((c * a) * c) := congrArg (fun x => b * x) (mul_assoc c a c).symm
    _ = b * ((a * c) * c) := by rw [hac.symm]
    _ = b * (a * (c * c)) := congrArg (fun x => b * x) (mul_assoc a c c)
    _ = b * a := by rw [hc, mul_one]
    _ = a * b := hab.symm

private lemma abc_mul_c (hc : c * c = 1) : (a * b * c) * c = a * b := by
  calc (a * b * c) * c = ((a * b) * c) * c := rfl
    _ = (a * b) * (c * c) := mul_assoc (a * b) c c
    _ = a * b := by rw [hc, mul_one]

private lemma mul_self_of_commute {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : (x * y) * (x * y) = 1 := by
  calc (x * y) * (x * y) = ((x * y) * x) * y := (mul_assoc (x * y) x y).symm
    _ = (x * (y * x)) * y := congrArg (fun z => z * y) (mul_assoc x y x)
    _ = (x * (x * y)) * y := by rw [hxy.symm]
    _ = ((x * x) * y) * y := congrArg (fun z => z * y) (mul_assoc x x y).symm
    _ = (x * x) * (y * y) := mul_assoc (x * x) y y
    _ = 1 := by rw [hx, hy, mul_one]

private lemma abc_mul_abc (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    (a * b * c) * (a * b * c) = 1 :=
  mul_self_of_commute (ab_mul_ab ha hb hab) hc (hABc hab hac hbc)

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

private lemma Ec_mul_Ec (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    ∀ {x y : G}, x ∈ ({c, a * c, b * c, a * b * c} : Set G) →
      y ∈ ({c, a * c, b * c, a * b * c} : Set G) → x * y ∈ ({1, a, b, a * b} : Set G) := by
  intro x y hx hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
    subst x <;> subst y
  all_goals
    simp only [ha, hb, hc, ab_mul_b hb, ab_mul_a ha hab, a_mul_ab ha, b_mul_ab hb hab,
      c_mul_ac hc hac, c_mul_bc hc hbc, c_mul_abc hc hab hac hbc,
      ac_mul_c hc, ac_mul_ac ha hc hac, ac_mul_bc hc hbc, ac_mul_abc ha hc hac hbc,
      bc_mul_c hc, bc_mul_ac hc hab hac, bc_mul_bc hb hc hbc,
      bc_mul_abc hb hc hab hac hbc,
      abc_mul_c hc, abc_mul_ac ha hb hc hab hac hbc,
      abc_mul_bc ha hb hc hab hac hbc, abc_mul_abc ha hb hc hab hac hbc]
  all_goals simp

private lemma exists_pow_of_mem_Ec {x : G}
    (hx : x ∈ ({c, a * c, b * c, a * b * c} : Set G)) :
    ∃ i j : Fin 2, x = a ^ (i : ℕ) * b ^ (j : ℕ) * c := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by simp⟩
  · exact ⟨1, 0, by simp⟩
  · exact ⟨0, 1, by simp⟩
  · exact ⟨1, 1, by simp⟩

private lemma mem_Ec_of_mem_F_not_E (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) {F : Subgroup G}
    (hF : ∀ p, p ∈ F ↔ ∃ i j k : Fin 2, p = a ^ (i : ℕ) * b ^ (j : ℕ) * c ^ (k : ℕ))
    {x : G} (hx : x ∈ F) (hx1 : x ≠ 1) (hne : x ∉ ({a, b, a * b} : Set G)) :
    x ∈ ({c, a * c, b * c, a * b * c} : Set G) := by
  have h8 := (mem_F_iff ha hb hc hab hac hbc hF x).mp hx
  rcases h8 with h | h | h | h | h | h | h | h
  · exact absurd h hx1
  · exact absurd (h ▸ by simp) hne
  · exact absurd (h ▸ by simp) hne
  · exact absurd (h ▸ by simp) hne
  · rw [h]; simp
  · rw [h]; simp
  · rw [h]; simp
  · rw [h]; simp

private lemma mem_Esharp_of_mem_E {x : G} (hx : x ∈ ({1, a, b, a * b} : Set G))
    (hx1 : x ≠ 1) : x ∈ ({a, b, a * b} : Set G) := by
  rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with
    h | h | h | h
  · exact absurd h hx1
  · rw [h]; simp
  · rw [h]; simp
  · rw [h]; simp

private lemma image_Esharp_key {F : Subgroup G} {N : ℕ}
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hc2 : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (hF : ∀ p, p ∈ F ↔ ∃ i j k : Fin 2, p = a ^ (i : ℕ) * b ^ (j : ℕ) * c ^ (k : ℕ))
    (hH : ∀ w ∈ ({a, b, a * b} : Set G), ∀ i j : Fin 2,
      pairOrder w (a ^ (i : ℕ) * b ^ (j : ℕ) * c) ≠ N)
    {u u' u'' : G} (hu : u ∈ F) (hu' : u' ∈ F)
    (hu1 : u ≠ 1) (hu'1 : u' ≠ 1) (hu''1 : u'' ≠ 1)
    (hprod : u * u' = u'') (hp1 : pairOrder u u' = N) (hp2 : pairOrder u u'' = N) :
    u ∈ ({a, b, a * b} : Set G) := by
  by_contra hne
  have huEc := mem_Ec_of_mem_F_not_E ha2 hb2 hc2 hab hac hbc hF hu hu1 hne
  obtain ⟨i, j, hu_eq⟩ := exists_pow_of_mem_Ec huEc
  have hu'notE : u' ∉ ({a, b, a * b} : Set G) := by
    intro hu'E
    have hcontra := hH u' hu'E i j
    rw [← hu_eq] at hcontra
    exact hcontra (by rw [pairOrder_comm]; exact hp1)
  have hu'Ec := mem_Ec_of_mem_F_not_E ha2 hb2 hc2 hab hac hbc hF hu' hu'1 hu'notE
  have hu''_E : u'' ∈ ({1, a, b, a * b} : Set G) := by
    rw [← hprod]
    exact Ec_mul_Ec ha2 hb2 hc2 hab hac hbc huEc hu'Ec
  have hu''_Esharp := mem_Esharp_of_mem_E hu''_E hu''1
  have hcontra := hH u'' hu''_Esharp i j
  rw [← hu_eq] at hcontra
  exact hcontra (by rw [pairOrder_comm]; exact hp2)

end Helpers

theorem image_Esharp_subset {a b c : G} {F : Subgroup G} {N : ℕ}
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hc2 : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab1 : a * b ≠ 1)
    (hF : ∀ p, p ∈ F ↔ ∃ i j k : Fin 2, p = a ^ (i : ℕ) * b ^ (j : ℕ) * c ^ (k : ℕ))
    (h1 : pairOrder a b = N) (h2 : pairOrder a (a * b) = N) (h3 : pairOrder b (a * b) = N)
    (hH : ∀ w ∈ ({a, b, a * b} : Set G), ∀ i j : Fin 2,
      pairOrder w (a ^ (i : ℕ) * b ^ (j : ℕ) * c) ≠ N)
    {g : G} (hg : g ∈ normalizer (F : Set G)) :
    ∀ w ∈ ({a, b, a * b} : Set G), g * w * g⁻¹ ∈ ({a, b, a * b} : Set G) := by
  have hg' : ∀ p : G, p ∈ F ↔ g * p * g⁻¹ ∈ F :=
    (Subgroup.mem_set_normalizer_iff).mp hg
  have inj : ∀ {p q : G}, g * p * g⁻¹ = g * q * g⁻¹ → p = q := by
    intro p q h
    have h' := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using h'
  have haF : a ∈ F := (hF a).mpr ⟨1, 0, 0, by simp⟩
  have hbF : b ∈ F := (hF b).mpr ⟨0, 1, 0, by simp⟩
  have habF : a * b ∈ F := (hF (a * b)).mpr ⟨1, 1, 0, by simp⟩
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with hw | hw | hw
  · subst w
    refine image_Esharp_key ha2 hb2 hc2 hab hac hbc hF hH
      (u := g * a * g⁻¹) (u' := g * b * g⁻¹) (u'' := g * (a * b) * g⁻¹)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (hg' a).mp haF
    · exact (hg' b).mp hbF
    · intro h; exact ha1 (inj (p := a) (q := 1) (by simpa using h))
    · intro h; exact hb1 (inj (p := b) (q := 1) (by simpa using h))
    · intro h; exact hab1 (inj (p := a * b) (q := 1) (by simpa using h))
    · group
    · rw [pairOrder_conj g a b, h1]
    · rw [pairOrder_conj g a (a * b), h2]
  · subst w
    refine image_Esharp_key ha2 hb2 hc2 hab hac hbc hF hH
      (u := g * b * g⁻¹) (u' := g * a * g⁻¹) (u'' := g * (a * b) * g⁻¹)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (hg' b).mp hbF
    · exact (hg' a).mp haF
    · intro h; exact hb1 (inj (p := b) (q := 1) (by simpa using h))
    · intro h; exact ha1 (inj (p := a) (q := 1) (by simpa using h))
    · intro h; exact hab1 (inj (p := a * b) (q := 1) (by simpa using h))
    · rw [show (g * b * g⁻¹) * (g * a * g⁻¹) = g * (b * a) * g⁻¹ by group, hab.symm]
    · rw [pairOrder_conj g b a, pairOrder_comm b a, h1]
    · rw [pairOrder_conj g b (a * b), h3]
  · subst w
    refine image_Esharp_key ha2 hb2 hc2 hab hac hbc hF hH
      (u := g * (a * b) * g⁻¹) (u' := g * a * g⁻¹) (u'' := g * b * g⁻¹)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact (hg' (a * b)).mp habF
    · exact (hg' a).mp haF
    · intro h; exact hab1 (inj (p := a * b) (q := 1) (by simpa using h))
    · intro h; exact ha1 (inj (p := a) (q := 1) (by simpa using h))
    · intro h; exact hb1 (inj (p := b) (q := 1) (by simpa using h))
    · rw [show (g * (a * b) * g⁻¹) * (g * a * g⁻¹) = g * ((a * b) * a) * g⁻¹
          by group, ab_mul_a ha2 hab]
    · rw [pairOrder_conj g (a * b) a, pairOrder_comm (a * b) a, h2]
    · rw [pairOrder_conj g (a * b) b, pairOrder_comm (a * b) b, h3]

variable [Finite G] {z : G} {ι : Perm (Fin 10) →* G}

theorem normalizer_Tgrp_preserves_Esharp (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP1 : IsConj z (z * ι τ₀)) {Q : Subgroup (Perm (Fin 10))} (hQ : GoodQ Q) {g : G}
    (hg : g ∈ normalizer (Tgrp z ι Q : Set G)) :
    ∀ w ∈ ({z, ι τ₀, z * ι τ₀} : Set G), g * w * g⁻¹ ∈ ({z, ι τ₀, z * ι τ₀} : Set G) := by
  have hρ4sq : ρ₄ * ρ₄ = 1 := by rw [← liftS8_ρ₄', ← map_mul, ρ₄'_mul_self, map_one]
  have ha2 : z * z = 1 := hC.mul_self
  have hb2 : ι τ₀ * ι τ₀ = 1 := by rw [← map_mul, τ₀_mul_self, map_one]
  have hc2 : ι ρ₄ * ι ρ₄ = 1 := by rw [← map_mul, hρ4sq, map_one]
  have hab : z * ι τ₀ = ι τ₀ * z := hC.comm τ₀
  have hac : z * ι ρ₄ = ι ρ₄ * z := hC.comm ρ₄
  have hbc : ι τ₀ * ι ρ₄ = ι ρ₄ * ι τ₀ := by
    rw [← map_mul, ← map_mul, ← liftS8_ρ₄']
    exact congrArg ι (liftS8_mul_τ₀ ρ₄').symm
  have ha1 : z ≠ 1 := by
    intro h
    have hz1 : orderOf z = 1 := by rw [h, orderOf_one]
    rw [hC.order] at hz1
    exact absurd hz1 (by decide)
  have hb1 : ι τ₀ ≠ 1 := by
    intro h
    have hτ : τ₀ = 1 := hC.inj (by rw [h, map_one])
    exact absurd hτ (by decide)
  have hab1 : z * ι τ₀ ≠ 1 := by
    intro h
    have hz : ι τ₀ = z := by
      calc ι τ₀ = (z * z) * ι τ₀ := by rw [ha2, one_mul]
        _ = z * (z * ι τ₀) := by rw [mul_assoc]
        _ = z := by rw [h, mul_one]
    exact hC.ne_z τ₀ hz
  obtain ⟨h1, h2, h3⟩ := pairOrder_E hC
  refine image_Esharp_subset (a := z) (b := ι τ₀) (c := ι ρ₄)
    (F := Fgrp (Tgrp z ι Q)) (N := N10 1)
    ha2 hb2 hc2 hab hac hbc ha1 hb1 hab1 (fun p => mem_Fgrp_iff hC hQ) h1 h2 h3 ?_ ?_
  · intro w hw i j
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact pairOrder_z_ne_N10_one hC i j
    · exact pairOrder_x_ne_N10_one hC hx i j
    · exact pairOrder_x₂_ne_N10_one hC hP1 i j
  · exact normalizer_le_normalizer_Fgrp (Tgrp z ι Q) hg

end CFSG.OddStandard.AltStdSec.SwapPartner
