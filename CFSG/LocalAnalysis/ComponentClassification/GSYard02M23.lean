module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02M12

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup Blueprint SylowTab

def m23x₁ : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

def m23x₂ : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem m23x₁_mem : m23x₁ ∈ NativeSporadic.M23 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem m23x₂_mem : m23x₂ ∈ NativeSporadic.M23 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

@[expose] def m23w_e1 (a b : Equiv.Perm (Fin 23)) : Equiv.Perm (Fin 23) :=
  b * b * a * (b⁻¹ * a) * (b⁻¹ * a) * (b⁻¹ * a) * (b * a) * (b * a) * (b * b * a) * (b * b * a) * b⁻¹ * a * b⁻¹ * (a * b) * (a * b) * (a * b) * (a * b) * b

@[expose] def m23w_e2 (a b : Equiv.Perm (Fin 23)) : Equiv.Perm (Fin 23) :=
  (a * b) * (a * b) * (a * b) * b * a * b⁻¹ * a * b * b * a * b * (a * b⁻¹) * (a * b⁻¹) * (a * b) * (a * b) * b * a * b⁻¹ * (a * b⁻¹ * a * b) * (a * b⁻¹ * a * b) * b

@[expose] def m23w_e3 (a b : Equiv.Perm (Fin 23)) : Equiv.Perm (Fin 23) :=
  a * b * a * b⁻¹ * a * ((b⁻¹ * a * b * a) * (b⁻¹ * a * b * a) * b * a * b⁻¹ * a) * ((b⁻¹ * a * b * a) * (b⁻¹ * a * b * a) * b * a * b⁻¹ * a)

@[expose] def m23w_e4 (a b : Equiv.Perm (Fin 23)) : Equiv.Perm (Fin 23) :=
  a * b * (b * a * b⁻¹ * a * b) * (b * a * b⁻¹ * a * b) * (a * b * b * (a * b) * (a * b)) * (a * b * b * (a * b) * (a * b)) * b * a * b * b

@[expose] def m23w_k1 (a b : Equiv.Perm (Fin 23)) : Equiv.Perm (Fin 23) :=
  (b * a) * (b * a) * (b * a) * (b * a) * b⁻¹ * a * b * (a * b⁻¹) * (a * b⁻¹) * (a * b⁻¹) * (a * b⁻¹)

@[expose] def m23w_k2 (a b : Equiv.Perm (Fin 23)) : Equiv.Perm (Fin 23) :=
  a * (b * b * a) * (b * b * a) * ((b⁻¹ * a) * (b⁻¹ * a) * (b * a) * (b * a)) * ((b⁻¹ * a) * (b⁻¹ * a) * (b * a) * (b * a)) * b * (a * b) * (a * b) * b * a

@[expose] def m23w_k3 (a b : Equiv.Perm (Fin 23)) : Equiv.Perm (Fin 23) :=
  a * (b * a) * (b * a) * (b * a) * b⁻¹ * (a * b) * (a * b) * b * a * b⁻¹ * a * b * (b * a) * (b * a) * (b * a * (b⁻¹ * a) * (b⁻¹ * a)) * (b * a * (b⁻¹ * a) * (b⁻¹ * a))

theorem m23w_e1_mem {H : Subgroup (Equiv.Perm (Fin 23))} {a b : Equiv.Perm (Fin 23)}
    (ha : a ∈ H) (hb : b ∈ H) : m23w_e1 a b ∈ H := by
  unfold m23w_e1
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb

theorem m23w_e2_mem {H : Subgroup (Equiv.Perm (Fin 23))} {a b : Equiv.Perm (Fin 23)}
    (ha : a ∈ H) (hb : b ∈ H) : m23w_e2 a b ∈ H := by
  unfold m23w_e2
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb

theorem m23w_e3_mem {H : Subgroup (Equiv.Perm (Fin 23))} {a b : Equiv.Perm (Fin 23)}
    (ha : a ∈ H) (hb : b ∈ H) : m23w_e3 a b ∈ H := by
  unfold m23w_e3
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb

theorem m23w_e4_mem {H : Subgroup (Equiv.Perm (Fin 23))} {a b : Equiv.Perm (Fin 23)}
    (ha : a ∈ H) (hb : b ∈ H) : m23w_e4 a b ∈ H := by
  unfold m23w_e4
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb

theorem m23w_k1_mem {H : Subgroup (Equiv.Perm (Fin 23))} {a b : Equiv.Perm (Fin 23)}
    (ha : a ∈ H) (hb : b ∈ H) : m23w_k1 a b ∈ H := by
  unfold m23w_k1
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb

theorem m23w_k2_mem {H : Subgroup (Equiv.Perm (Fin 23))} {a b : Equiv.Perm (Fin 23)}
    (ha : a ∈ H) (hb : b ∈ H) : m23w_k2 a b ∈ H := by
  unfold m23w_k2
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb

theorem m23w_k3_mem {H : Subgroup (Equiv.Perm (Fin 23))} {a b : Equiv.Perm (Fin 23)}
    (ha : a ∈ H) (hb : b ∈ H) : m23w_k3 a b ∈ H := by
  unfold m23w_k3
  repeat' (first | apply mul_mem | apply inv_mem)
  all_goals first | exact ha | exact hb


abbrev m23e1 : Equiv.Perm (Fin 23) := m23w_e1 m23x₁ m23x₂

abbrev m23e2 : Equiv.Perm (Fin 23) := m23w_e2 m23x₁ m23x₂

abbrev m23e3 : Equiv.Perm (Fin 23) := m23w_e3 m23x₁ m23x₂

abbrev m23e4 : Equiv.Perm (Fin 23) := m23w_e4 m23x₁ m23x₂

abbrev m23k1 : Equiv.Perm (Fin 23) := m23w_k1 m23x₁ m23x₂

abbrev m23k2 : Equiv.Perm (Fin 23) := m23w_k2 m23x₁ m23x₂

abbrev m23k3 : Equiv.Perm (Fin 23) := m23w_k3 m23x₁ m23x₂

theorem m23e1_mem : m23e1 ∈ NativeSporadic.M23 := m23w_e1_mem m23x₁_mem m23x₂_mem
theorem m23e2_mem : m23e2 ∈ NativeSporadic.M23 := m23w_e2_mem m23x₁_mem m23x₂_mem
theorem m23e3_mem : m23e3 ∈ NativeSporadic.M23 := m23w_e3_mem m23x₁_mem m23x₂_mem
theorem m23e4_mem : m23e4 ∈ NativeSporadic.M23 := m23w_e4_mem m23x₁_mem m23x₂_mem
theorem m23k1_mem : m23k1 ∈ NativeSporadic.M23 := m23w_k1_mem m23x₁_mem m23x₂_mem
theorem m23k2_mem : m23k2 ∈ NativeSporadic.M23 := m23w_k2_mem m23x₁_mem m23x₂_mem
theorem m23k3_mem : m23k3 ∈ NativeSporadic.M23 := m23w_k3_mem m23x₁_mem m23x₂_mem

@[expose] def m23gsE : List (Equiv.Perm (Fin 23)) := [m23e1, m23e2, m23e3, m23e4]

@[expose] def m23gsK : List (Equiv.Perm (Fin 23)) := [m23k1, m23k2, m23k3]

theorem m23_gsE_mem : ∀ g ∈ m23gsE, g ∈ NativeSporadic.M23 := by
  intro g hg
  simp only [m23gsE, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  exacts [m23e1_mem, m23e2_mem, m23e3_mem, m23e4_mem]

theorem m23_gsK_mem : ∀ g ∈ m23gsK, g ∈ NativeSporadic.M23 := by
  intro g hg
  simp only [m23gsK, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  exacts [m23k1_mem, m23k2_mem, m23k3_mem]

theorem m23_E_table : TableClosed 23 m23gsE := by decide +kernel

theorem m23_K_table : TableClosed 23 m23gsK := by decide +kernel

theorem m23_EK_table : TablePair 23 m23gsE m23gsK := by decide +kernel

theorem sylowFourJoined_M23 :
    SylowFourJoined NativeSporadic.M23 := by
  have hcard : Nat.card NativeSporadic.M23 = 2 ^ (m23gsE.length + m23gsK.length) * 79695 := by
    rw [CFSG.Sporadic.Schreier.m23_card]
    norm_num [m23gsE, m23gsK]
  exact sylowFourJoined_of_tables NativeSporadic.M23 m23gsE m23gsK 79695 m23_gsE_mem
    m23_gsK_mem m23_E_table m23_K_table m23_EK_table (by decide) hcard (by decide)

theorem leafM23_holds : LeafSporadic .M23 := by
  intro X _ _ _ _ hX
  obtain ⟨e⟩ := hX
  have e' : ↥NativeSporadic.M23 ≃* X := e.symm
  exact SylowFourJoined.of_mulEquiv e' sylowFourJoined_M23

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
