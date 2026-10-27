module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open Equiv Equiv.Perm
open scoped Pointwise

theorem zpowers_eq_zpowers_iff_of_orderOf_three {K : Type*} [Group K] {a b : K}
    (ha : orderOf a = 3) (hb : orderOf b = 3) :
    Subgroup.zpowers a = Subgroup.zpowers b ↔ b = a ∨ b = a⁻¹ := by
  have h3a : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  constructor
  · intro h
    have hb_mem : b ∈ Subgroup.zpowers a := h ▸ Subgroup.mem_zpowers b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb_mem
    have hmod : a ^ (k % 3) = b := by
      have h1 := zpow_mod_orderOf a k
      have h3 : ((orderOf a : ℕ) : ℤ) = 3 := by rw [ha]; norm_num
      rw [h3] at h1
      rw [h1, hk]
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
    · rw [h0, zpow_zero] at hmod
      rw [← hmod, orderOf_one] at hb
      exact absurd hb (by norm_num)
    · rw [h1, zpow_one] at hmod
      exact Or.inl hmod.symm
    · rw [h2, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast] at hmod
      right
      have hab : a * b = 1 := by
        rw [← hmod, ← pow_succ']
        exact h3a
      exact eq_inv_of_mul_eq_one_right hab
  · rintro (rfl | rfl)
    · rfl
    · rw [Subgroup.zpowers_inv]

theorem alt4_pair_decide : ∀ a b : alternatingGroup (Fin 4), a ^ 3 = 1 → a ≠ 1 → b ^ 3 = 1 →
    b ≠ 1 → b ≠ a → b ≠ a⁻¹ → ((a * b) ^ 2 = 1 ↔ (a * b⁻¹) ^ 2 ≠ 1) := by
  decide

theorem alt4_pair_iff (a b : alternatingGroup (Fin 4)) (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hne : Subgroup.zpowers a ≠ Subgroup.zpowers b) :
    (a * b) ^ 2 = 1 ↔ (a * b⁻¹) ^ 2 ≠ 1 := by
  have hbne : b ≠ a ∧ b ≠ a⁻¹ := by
    constructor
    · rintro rfl
      exact hne rfl
    · rintro rfl
      exact hne (by rw [Subgroup.zpowers_inv])
  have h3a : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have h3b : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; exact absurd ha (by norm_num)
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; exact absurd hb (by norm_num)
  exact alt4_pair_decide a b h3a ha1 h3b hb1 hbne.1 hbne.2

set_option maxRecDepth 20000 in
theorem alt5_dichotomy_decide : ∀ a b : alternatingGroup (Fin 5), a ^ 3 = 1 → a ≠ 1 →
    b ^ 3 = 1 → b ≠ 1 →
    ((a * b) ^ 5 = 1 ∧ (b⁻¹ * a * b * a) ^ 2 = 1) ∨
      (∃ i : Fin 5, (a : Perm (Fin 5)) i = i ∧ (b : Perm (Fin 5)) i = i) ∨
      (∃ T : Finset (Fin 5), T.card = 2 ∧ (a : Perm (Fin 5)) • T = T ∧
        (b : Perm (Fin 5)) • T = T) := by
  decide

theorem alt5_moves_point : ∀ i : Fin 5, ∃ g : alternatingGroup (Fin 5), (g : Perm (Fin 5)) i ≠ i := by
  decide

theorem alt5_moves_pair : ∀ T : Finset (Fin 5), T.card = 2 →
    ∃ g : alternatingGroup (Fin 5), (g : Perm (Fin 5)) • T ≠ T := by
  decide

theorem alt5_relations (a b : alternatingGroup (Fin 5)) (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hgen : Subgroup.closure ({a, b} : Set (alternatingGroup (Fin 5))) = ⊤) :
    (a * b) ^ 5 = 1 ∧ (b⁻¹ * a * b * a) ^ 2 = 1 := by
  have h3a : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have h3b : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; exact absurd ha (by norm_num)
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; exact absurd hb (by norm_num)
  have ha_mem : a ∈ Subgroup.closure ({a, b} : Set (alternatingGroup (Fin 5))) :=
    Subgroup.subset_closure (by simp)
  have hb_mem : b ∈ Subgroup.closure ({a, b} : Set (alternatingGroup (Fin 5))) :=
    Subgroup.subset_closure (by simp)
  rcases alt5_dichotomy_decide a b h3a ha1 h3b hb1 with h | ⟨i, hai, hbi⟩ | ⟨T, hT, haT, hbT⟩
  · exact h
  · exfalso
    let H : Subgroup (alternatingGroup (Fin 5)) :=
      (MulAction.stabilizer (Perm (Fin 5)) i).subgroupOf (alternatingGroup (Fin 5))
    have haH : a ∈ H := by
      rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact hai
    have hbH : b ∈ H := by
      rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact hbi
    have hle : Subgroup.closure ({a, b} : Set (alternatingGroup (Fin 5))) ≤ H :=
      Subgroup.closure_le H |>.mpr (Set.insert_subset_iff.mpr
        ⟨haH, Set.singleton_subset_iff.mpr hbH⟩)
    rw [hgen] at hle
    obtain ⟨g, hg⟩ := alt5_moves_point i
    have hgH : g ∈ H := hle trivial
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at hgH
    exact hg hgH
  · exfalso
    let H : Subgroup (alternatingGroup (Fin 5)) :=
      (MulAction.stabilizer (Perm (Fin 5)) T).subgroupOf (alternatingGroup (Fin 5))
    have haH : a ∈ H := by
      rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
      exact haT
    have hbH : b ∈ H := by
      rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
      exact hbT
    have hle : Subgroup.closure ({a, b} : Set (alternatingGroup (Fin 5))) ≤ H :=
      Subgroup.closure_le H |>.mpr (Set.insert_subset_iff.mpr
        ⟨haH, Set.singleton_subset_iff.mpr hbH⟩)
    rw [hgen] at hle
    obtain ⟨g, hg⟩ := alt5_moves_pair T hT
    have hgH : g ∈ H := hle trivial
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff] at hgH
    exact hg hgH

theorem pow_eq_one_iff_of_mulEquiv {K H : Type*} [Group K] [Group H] (e : K ≃* H) (n : ℕ)
    (g : K) : e g ^ n = 1 ↔ g ^ n = 1 := by
  rw [← map_pow, ← map_one e, e.injective.eq_iff]

theorem transport_alt4_pair_iff {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 4))
    {a b : K} (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hne : Subgroup.zpowers a ≠ Subgroup.zpowers b) :
    (a * b) ^ 2 = 1 ↔ (a * b⁻¹) ^ 2 ≠ 1 := by
  have hxa : orderOf (e a) = 3 := by
    rw [← ha]; exact orderOf_injective e.toMonoidHom e.injective a
  have hxb : orderOf (e b) = 3 := by
    rw [← hb]; exact orderOf_injective e.toMonoidHom e.injective b
  have hne' : Subgroup.zpowers (e a) ≠ Subgroup.zpowers (e b) := by
    intro h
    rw [zpowers_eq_zpowers_iff_of_orderOf_three hxa hxb] at h
    apply hne
    rw [zpowers_eq_zpowers_iff_of_orderOf_three ha hb]
    rcases h with h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (by apply e.injective; rw [h, map_inv])
  have key := alt4_pair_iff (e a) (e b) hxa hxb hne'
  have k1 : (a * b) ^ 2 = 1 ↔ (e a * e b) ^ 2 = 1 := by
    rw [← map_mul, pow_eq_one_iff_of_mulEquiv]
  have k2 : (e a * (e b)⁻¹) ^ 2 = 1 ↔ (a * b⁻¹) ^ 2 = 1 := by
    rw [← map_inv, ← map_mul, pow_eq_one_iff_of_mulEquiv]
  exact k1.trans (key.trans (not_congr k2))

theorem transport_alt5_relations {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 5))
    {a b : K} (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hgen : Subgroup.closure ({a, b} : Set K) = ⊤) :
    (a * b) ^ 5 = 1 ∧ (b⁻¹ * a * b * a) ^ 2 = 1 := by
  have hxa : orderOf (e a) = 3 := by
    rw [← ha]; exact orderOf_injective e.toMonoidHom e.injective a
  have hxb : orderOf (e b) = 3 := by
    rw [← hb]; exact orderOf_injective e.toMonoidHom e.injective b
  have hle : (Subgroup.closure ({a, b} : Set K)).map e.toMonoidHom ≤
      Subgroup.closure ({e a, e b} : Set (alternatingGroup (Fin 5))) := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hgen' : Subgroup.closure ({e a, e b} : Set (alternatingGroup (Fin 5))) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hk : e.symm x ∈ Subgroup.closure ({a, b} : Set K) := by rw [hgen]; trivial
    have hmem := hle (Subgroup.mem_map_of_mem _ hk)
    simpa using hmem
  obtain ⟨h5, hrel⟩ := alt5_relations (e a) (e b) hxa hxb hgen'
  constructor
  · have k : (a * b) ^ 5 = 1 ↔ (e a * e b) ^ 5 = 1 := by
      rw [← map_mul, pow_eq_one_iff_of_mulEquiv]
    exact k.mpr h5
  · have k : (b⁻¹ * a * b * a) ^ 2 = 1 ↔ ((e b)⁻¹ * e a * e b * e a) ^ 2 = 1 := by
      rw [← pow_eq_one_iff_of_mulEquiv e 2 (b⁻¹ * a * b * a)]
      simp only [map_mul, map_inv]
    exact k.mpr hrel

end CFSG.HardMathSupport.RichardWeiss.Proving

end
