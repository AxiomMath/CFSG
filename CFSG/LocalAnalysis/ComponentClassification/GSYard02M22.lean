module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02M12

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup Blueprint SylowTab

def m22x₁ : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

def m22x₂ : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

theorem m22x₁_mem : m22x₁ ∈ NativeSporadic.M22 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem m22x₂_mem : m22x₂ ∈ NativeSporadic.M22 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

@[expose] def m22w_e1 (a b : Equiv.Perm (Fin 22)) : Equiv.Perm (Fin 22) :=
  b * a * b⁻¹ * a * (b * a) * (b * a) * b⁻¹ * a * b * (b * a) * (b * a) * (b⁻¹ * a) * (b⁻¹ * a) * b * a * b⁻¹

@[expose] def m22w_e2 (a b : Equiv.Perm (Fin 22)) : Equiv.Perm (Fin 22) :=
  a * (b * a) * (b * a) * (b * a) * (b * a) * (b * a) * (b⁻¹ * a) * (b⁻¹ * a) * (b⁻¹ * a) * (b⁻¹ * a) * (b⁻¹ * a)

@[expose] def m22w_e3 (a b : Equiv.Perm (Fin 22)) : Equiv.Perm (Fin 22) :=
  (b * a * b) * (b * a * b) * a * (b⁻¹ * a) * (b⁻¹ * a) * b * (b * a) * (b * a) * (b * a) * b⁻¹ * a * b * b * a * b⁻¹

@[expose] def m22w_e4 (a b : Equiv.Perm (Fin 22)) : Equiv.Perm (Fin 22) :=
  (b⁻¹ * a) * (b⁻¹ * a) * b * (b * a) * (b * a) * (b * a) * (b⁻¹ * a) * (b⁻¹ * a) * b * b * (a * b) * (a * b)

@[expose] def m22w_k1 (a b : Equiv.Perm (Fin 22)) : Equiv.Perm (Fin 22) :=
  a * b * b * (a * b⁻¹) * (a * b⁻¹) * (a * b * b * a * b⁻¹ * a * b * a * b⁻¹) * (a * b * b * a * b⁻¹ * a * b * a * b⁻¹)

@[expose] def m22w_k2 (a b : Equiv.Perm (Fin 22)) : Equiv.Perm (Fin 22) :=
  b⁻¹ * (a * b⁻¹) * (a * b⁻¹) * (a * b) * (a * b) * (a * b) * (a * b⁻¹) * (a * b⁻¹) * (a * b⁻¹) * (a * b) * (a * b) * (a * b)

@[expose] def m22w_k3 (a b : Equiv.Perm (Fin 22)) : Equiv.Perm (Fin 22) :=
  b⁻¹ * (a * b⁻¹ * a * b) * (a * b⁻¹ * a * b) * (b * a) * (b * a) * b⁻¹ * (a * b) * (a * b)

theorem m22w_e1_mem {H : Subgroup (Equiv.Perm (Fin 22))} {a b : Equiv.Perm (Fin 22)}
    (ha : a ∈ H) (hb : b ∈ H) : m22w_e1 a b ∈ H := by
  unfold m22w_e1
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb

theorem m22w_e2_mem {H : Subgroup (Equiv.Perm (Fin 22))} {a b : Equiv.Perm (Fin 22)}
    (ha : a ∈ H) (hb : b ∈ H) : m22w_e2 a b ∈ H := by
  unfold m22w_e2
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb

theorem m22w_e3_mem {H : Subgroup (Equiv.Perm (Fin 22))} {a b : Equiv.Perm (Fin 22)}
    (ha : a ∈ H) (hb : b ∈ H) : m22w_e3 a b ∈ H := by
  unfold m22w_e3
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb

theorem m22w_e4_mem {H : Subgroup (Equiv.Perm (Fin 22))} {a b : Equiv.Perm (Fin 22)}
    (ha : a ∈ H) (hb : b ∈ H) : m22w_e4 a b ∈ H := by
  unfold m22w_e4
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb

theorem m22w_k1_mem {H : Subgroup (Equiv.Perm (Fin 22))} {a b : Equiv.Perm (Fin 22)}
    (ha : a ∈ H) (hb : b ∈ H) : m22w_k1 a b ∈ H := by
  unfold m22w_k1
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb

theorem m22w_k2_mem {H : Subgroup (Equiv.Perm (Fin 22))} {a b : Equiv.Perm (Fin 22)}
    (ha : a ∈ H) (hb : b ∈ H) : m22w_k2 a b ∈ H := by
  unfold m22w_k2
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb

theorem m22w_k3_mem {H : Subgroup (Equiv.Perm (Fin 22))} {a b : Equiv.Perm (Fin 22)}
    (ha : a ∈ H) (hb : b ∈ H) : m22w_k3 a b ∈ H := by
  unfold m22w_k3
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb

abbrev m22e1 : Equiv.Perm (Fin 22) := m22w_e1 m22x₁ m22x₂

abbrev m22e2 : Equiv.Perm (Fin 22) := m22w_e2 m22x₁ m22x₂

abbrev m22e3 : Equiv.Perm (Fin 22) := m22w_e3 m22x₁ m22x₂

abbrev m22e4 : Equiv.Perm (Fin 22) := m22w_e4 m22x₁ m22x₂

abbrev m22k1 : Equiv.Perm (Fin 22) := m22w_k1 m22x₁ m22x₂

abbrev m22k2 : Equiv.Perm (Fin 22) := m22w_k2 m22x₁ m22x₂

abbrev m22k3 : Equiv.Perm (Fin 22) := m22w_k3 m22x₁ m22x₂

theorem m22e1_mem : m22e1 ∈ NativeSporadic.M22 := m22w_e1_mem m22x₁_mem m22x₂_mem
theorem m22e2_mem : m22e2 ∈ NativeSporadic.M22 := m22w_e2_mem m22x₁_mem m22x₂_mem
theorem m22e3_mem : m22e3 ∈ NativeSporadic.M22 := m22w_e3_mem m22x₁_mem m22x₂_mem
theorem m22e4_mem : m22e4 ∈ NativeSporadic.M22 := m22w_e4_mem m22x₁_mem m22x₂_mem
theorem m22k1_mem : m22k1 ∈ NativeSporadic.M22 := m22w_k1_mem m22x₁_mem m22x₂_mem
theorem m22k2_mem : m22k2 ∈ NativeSporadic.M22 := m22w_k2_mem m22x₁_mem m22x₂_mem
theorem m22k3_mem : m22k3 ∈ NativeSporadic.M22 := m22w_k3_mem m22x₁_mem m22x₂_mem

@[expose] def m22gsE : List (Equiv.Perm (Fin 22)) := [m22e1, m22e2, m22e3, m22e4]

@[expose] def m22gsK : List (Equiv.Perm (Fin 22)) := [m22k1, m22k2, m22k3]

theorem m22_gsE_mem : ∀ g ∈ m22gsE, g ∈ NativeSporadic.M22 := by
  intro g hg
  simp only [m22gsE, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  exacts [m22e1_mem, m22e2_mem, m22e3_mem, m22e4_mem]

theorem m22_gsK_mem : ∀ g ∈ m22gsK, g ∈ NativeSporadic.M22 := by
  intro g hg
  simp only [m22gsK, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  exacts [m22k1_mem, m22k2_mem, m22k3_mem]

theorem m22_E_table : TableClosed 22 m22gsE := by decide +kernel

theorem m22_K_table : TableClosed 22 m22gsK := by decide +kernel

theorem m22_EK_table : TablePair 22 m22gsE m22gsK := by decide +kernel

theorem sylowFourJoined_M22 :
    SylowFourJoined NativeSporadic.M22 := by
  have hcard : Nat.card NativeSporadic.M22 = 2 ^ (m22gsE.length + m22gsK.length) * 3465 := by
    rw [CFSG.Sporadic.Mathieu.card_M22]
    norm_num [m22gsE, m22gsK]
  exact sylowFourJoined_of_tables NativeSporadic.M22 m22gsE m22gsK 3465 m22_gsE_mem
    m22_gsK_mem m22_E_table m22_K_table m22_EK_table (by decide) hcard (by decide)

theorem leafM22_holds : LeafSporadic .M22 := by
  intro X _ _ _ _ hX
  obtain ⟨e⟩ := hX
  have e' : ↥NativeSporadic.M22 ≃* X := e.symm
  exact SylowFourJoined.of_mulEquiv e' sylowFourJoined_M22

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
