module

public import CFSG.CharacterTheory.Semidihedral.FourPointMatrices
public import Mathlib.GroupTheory.IndexNormal

public section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace CFSG.Semidihedral.GL2ThreeStructure

open Matrix
open FourPointMatrices

abbrev H := GeneralLinearGroup (Fin 2) (ZMod 3)
@[expose] def K : Subgroup H := GeneralLinearGroup.det.ker
abbrev z : H := FourPointMatrices.Z
abbrev Coordinates := Fin 2 × Fin 6 × Fin 4

@[expose] noncomputable def normalEquiv : Coordinates ≃ H :=
  Equiv.ofBijective normalUnit ⟨normalUnit_injective, normalUnit_surjective⟩

theorem normalEquiv_apply (i : Coordinates) : normalEquiv i = normalUnit i := rfl

theorem card48 : Nat.card H = 48 := GL2_three_card

theorem z_matrix : (z : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1 := Z_matrix

theorem z_order : orderOf z = 2 := Z_order

theorem z_mem_K : z ∈ K := by
  change GeneralLinearGroup.det z = 1
  apply Units.ext
  change matrixZ.det = 1
  decide

@[expose] def zK : K := ⟨z, z_mem_K⟩

@[expose] def matrixU : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 1; 0, 1]
@[expose] def matrixV : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 0; 1, 1]

@[expose] def U : H :=
  ⟨matrixU, !![1, 2; 0, 1], by decide, by decide⟩

@[expose] def V : H :=
  ⟨matrixV, !![1, 0; 2, 1], by decide, by decide⟩

theorem U_mem_K : U ∈ K := by
  change GeneralLinearGroup.det U = 1
  apply Units.ext
  change matrixU.det = 1
  decide

theorem V_mem_K : V ∈ K := by
  change GeneralLinearGroup.det V = 1
  apply Units.ext
  change matrixV.det = 1
  decide

theorem commuting_unipotents_scalar
    (M : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (hM : M.det ≠ 0)
    (hu : M * matrixU = matrixU * M)
    (hv : M * matrixV = matrixV * M) : M = 1 ∨ M = matrixZ := by
  revert M
  decide

theorem centralizes_unipotents_iff (g : H) :
    (g * U = U * g ∧ g * V = V * g) ↔ g = 1 ∨ g = z := by
  constructor
  · rintro ⟨hu, hv⟩
    rcases commuting_unipotents_scalar (g : Matrix (Fin 2) (Fin 2) (ZMod 3))
      (GeneralLinearGroup.det_ne_zero g)
      (congrArg Units.val hu) (congrArg Units.val hv) with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  · rintro (rfl | rfl)
    · simp
    · exact ⟨(Subgroup.mem_center_iff.mp Z_mem_center U).symm,
        (Subgroup.mem_center_iff.mp Z_mem_center V).symm⟩

theorem centerH : Subgroup.center H = Subgroup.zpowers z := by
  apply le_antisymm
  · intro g hg
    have hu := (Subgroup.mem_center_iff.mp hg U).symm
    have hv := (Subgroup.mem_center_iff.mp hg V).symm
    rcases (centralizes_unipotents_iff g).mp ⟨hu, hv⟩ with rfl | rfl
    · exact (Subgroup.zpowers z).one_mem
    · exact Subgroup.mem_zpowers z
  · exact Subgroup.zpowers_le.mpr Z_mem_center

theorem zK_mem_center : zK ∈ Subgroup.center K := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp Z_mem_center (g : H)

theorem centerK : (Subgroup.center K).map K.subtype = Subgroup.zpowers z := by
  apply le_antisymm
  · rintro g ⟨a, ha, rfl⟩
    change (a : H) ∈ Subgroup.zpowers z
    have hu := congrArg (fun x : K => (x : H))
      ((Subgroup.mem_center_iff.mp ha ⟨U, U_mem_K⟩).symm)
    have hv := congrArg (fun x : K => (x : H))
      ((Subgroup.mem_center_iff.mp ha ⟨V, V_mem_K⟩).symm)
    rcases (centralizes_unipotents_iff (a : H)).mp ⟨hu, hv⟩ with h | h
    · rw [h]
      exact (Subgroup.zpowers z).one_mem
    · rw [h]
      exact Subgroup.mem_zpowers z
  · apply Subgroup.zpowers_le.mpr
    exact ⟨zK, zK_mem_center, rfl⟩

theorem K_index : K.index = 2 := by
  rw [K, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (GeneralLinearGroup.det_surjective (n := Fin 2)),
    Subgroup.card_top, Nat.card_units]
  norm_num

theorem K_card : Nat.card K = 24 := by
  have h := K.index_mul_card
  rw [K_index, card48] at h
  omega

theorem determinant_one_unipotent_word
    (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) (hM : M.det = 1) :
    ∃ a b c d : Fin 3,
      matrixU ^ a.val * matrixV ^ b.val * matrixU ^ c.val * matrixV ^ d.val = M := by
  revert M
  decide

theorem unipotents_generate_K : Subgroup.closure {U, V} = K := by
  apply le_antisymm
  · apply (Subgroup.closure_le K).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact U_mem_K
    · exact V_mem_K
  · intro g hg
    change GeneralLinearGroup.det g = 1 at hg
    have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 :=
      congrArg Units.val hg
    obtain ⟨a, b, c, d, hw⟩ := determinant_one_unipotent_word _ hdet
    have heq : U ^ a.val * V ^ b.val * U ^ c.val * V ^ d.val = g := Units.ext hw
    rw [← heq]
    have hu : U ∈ Subgroup.closure {U, V} := Subgroup.subset_closure (by simp)
    have hv : V ∈ Subgroup.closure {U, V} := Subgroup.subset_closure (by simp)
    let L := Subgroup.closure {U, V}
    exact L.mul_mem (L.mul_mem (L.mul_mem (L.pow_mem hu _) (L.pow_mem hv _))
      (L.pow_mem hu _)) (L.pow_mem hv _)

theorem C_U_commutator : C * U * C⁻¹ * U⁻¹ = U := by
  apply Units.ext
  change matrixC * matrixU * matrixC * !![1, 2; 0, 1] = matrixU
  decide

theorem C_V_commutator : C * V * C⁻¹ * V⁻¹ = V := by
  apply Units.ext
  change matrixC * matrixV * matrixC * !![1, 0; 2, 1] = matrixV
  decide

theorem commutatorH : commutator H = K := by
  apply le_antisymm
  · change ⁅(⊤ : Subgroup H), ⊤⁆ ≤ GeneralLinearGroup.det.ker
    apply Subgroup.commutator_le.mpr
    intro g _ h _
    change GeneralLinearGroup.det (g * h * g⁻¹ * h⁻¹) = 1
    simp
  · rw [← unipotents_generate_K]
    apply (Subgroup.closure_le (commutator H)).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · change U ∈ commutator H
      have h : C * U * C⁻¹ * U⁻¹ ∈ commutator H :=
        @Subgroup.commutator_mem_commutator H _ C U ⊤ ⊤ (by trivial) (by trivial)
      simpa only [C_U_commutator] using h
    · change V ∈ commutator H
      have h : C * V * C⁻¹ * V⁻¹ ∈ commutator H :=
        @Subgroup.commutator_mem_commutator H _ C V ⊤ ⊤ (by trivial) (by trivial)
      simpa only [C_V_commutator] using h

theorem uniqueindex2 (L : Subgroup H) (hL : L.index = 2) : L = K := by
  have : L.Normal := Subgroup.normal_of_index_eq_two hL
  have hcard : Nat.card (H ⧸ L) = 2 := hL
  have : IsCyclic (H ⧸ L) := isCyclic_of_prime_card hcard
  have hcomm : commutator H ≤ L :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  rw [commutatorH] at hcomm
  have hcL : Nat.card L = 24 := by
    have h := L.index_mul_card
    rw [hL, card48] at h
    omega
  exact (Subgroup.eq_of_le_of_card_ge hcomm (by rw [hcL, K_card])).symm

theorem index_two_iff (L : Subgroup H) : L.index = 2 ↔ L = K := by
  exact ⟨uniqueindex2 L, fun h => h ▸ K_index⟩

theorem center_index_two (L : Subgroup H) (hL : L.index = 2) :
    (Subgroup.center L).map L.subtype = Subgroup.zpowers z := by
  obtain rfl := uniqueindex2 L hL
  exact centerK

@[expose] def coordinateOrder (i : Coordinates) : ℕ :=
  if normalMatrix i = 1 then 1
  else if normalMatrix i ^ 2 = 1 then 2
  else if normalMatrix i ^ 3 = 1 then 3
  else if normalMatrix i ^ 4 = 1 then 4
  else if normalMatrix i ^ 6 = 1 then 6
  else 8

theorem coordinateOrder_spec : ∀ i : Coordinates,
    0 < coordinateOrder i ∧ normalMatrix i ^ coordinateOrder i = 1 ∧
      ∀ m : Fin 8, 0 < m.val → m.val < coordinateOrder i → normalMatrix i ^ m.val ≠ 1 := by
  decide

theorem coordinateOrder_mem : ∀ i : Coordinates,
    coordinateOrder i ∈ ({1, 2, 3, 4, 6, 8} : Finset ℕ) := by
  decide

theorem normalUnit_order (i : Coordinates) : orderOf (normalUnit i) = coordinateOrder i := by
  obtain ⟨hpos, hpow, hleast⟩ := coordinateOrder_spec i
  have hle : coordinateOrder i ≤ 8 := by
    have h := coordinateOrder_mem i
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    omega
  apply (orderOf_eq_iff hpos).mpr
  constructor
  · apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, normalUnit_matrix] using hpow
  · intro m hm hmp heq
    have hM := congrArg Units.val heq
    have hne := hleast ⟨m, lt_of_lt_of_le hm hle⟩ hmp hm
    apply hne
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, normalUnit_matrix] using hM

theorem order_exhaustive (g : H) : orderOf g ∈ ({1, 2, 3, 4, 6, 8} : Finset ℕ) := by
  obtain ⟨i, rfl⟩ := normalUnit_surjective g
  rw [normalUnit_order]
  exact coordinateOrder_mem i

theorem order_card (n : ℕ) :
    Nat.card {g : H // orderOf g = n} =
      Fintype.card {i : Coordinates // coordinateOrder i = n} := by
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact (normalEquiv.subtypeEquiv (fun i => by
    simp only [normalEquiv_apply, normalUnit_order])).symm

theorem coordinate_order_counts :
    Fintype.card {i : Coordinates // coordinateOrder i = 1} = 1 ∧
    Fintype.card {i : Coordinates // coordinateOrder i = 2} = 13 ∧
    Fintype.card {i : Coordinates // coordinateOrder i = 3} = 8 ∧
    Fintype.card {i : Coordinates // coordinateOrder i = 4} = 6 ∧
    Fintype.card {i : Coordinates // coordinateOrder i = 6} = 8 ∧
    Fintype.card {i : Coordinates // coordinateOrder i = 8} = 12 := by
  decide

theorem element_order_counts :
    Nat.card {g : H // orderOf g = 1} = 1 ∧
    Nat.card {g : H // orderOf g = 2} = 13 ∧
    Nat.card {g : H // orderOf g = 3} = 8 ∧
    Nat.card {g : H // orderOf g = 4} = 6 ∧
    Nat.card {g : H // orderOf g = 6} = 8 ∧
    Nat.card {g : H // orderOf g = 8} = 12 := by
  simpa only [order_card] using coordinate_order_counts

theorem order_three_coordinates_conjugate : ∀ i : Coordinates,
    coordinateOrder i = 3 →
      ∃ j : Coordinates, normalUnit j * U * (normalUnit j)⁻¹ = normalUnit i := by
  decide

theorem order_three_conjugate_U (a : H) (ha : orderOf a = 3) : IsConj U a := by
  obtain ⟨i, rfl⟩ := normalUnit_surjective a
  rw [normalUnit_order] at ha
  obtain ⟨j, hj⟩ := order_three_coordinates_conjugate i ha
  exact isConj_iff.mpr ⟨normalUnit j, hj⟩

theorem order_three_conjugate (a b : H) (ha : orderOf a = 3) (hb : orderOf b = 3) :
    IsConj a b :=
  (order_three_conjugate_U a ha).symm.trans (order_three_conjugate_U b hb)

theorem U_order : orderOf U = 3 := by
  apply orderOf_eq_prime
  · apply Units.ext
    change matrixU ^ 3 = 1
    decide
  · intro h
    have hM : matrixU = 1 := congrArg Units.val h
    have hn : matrixU ≠ 1 := by decide
    exact hn hM

theorem mem_zpowers_z_iff (g : H) : g ∈ Subgroup.zpowers z ↔ g = 1 ∨ g = z := by
  rw [← centerH]
  constructor
  · intro hg
    exact (centralizes_unipotents_iff g).mp
      ⟨(Subgroup.mem_center_iff.mp hg U).symm, (Subgroup.mem_center_iff.mp hg V).symm⟩
  · rintro (rfl | rfl)
    · exact (Subgroup.center H).one_mem
    · exact Z_mem_center

theorem C_not_mem_zpowers_z : C ∉ Subgroup.zpowers z := by
  rw [mem_zpowers_z_iff]
  have hC1 : C ≠ 1 := by
    intro h
    have hM : matrixC = 1 := congrArg Units.val h
    have hn : matrixC ≠ 1 := by decide
    exact hn hM
  have hCz : C ≠ z := by
    intro h
    have hM : matrixC = matrixZ := congrArg Units.val h
    have hn : matrixC ≠ matrixZ := by decide
    exact hn hM
  exact not_or.mpr ⟨hC1, hCz⟩

theorem C_order : orderOf C = 2 := by
  apply orderOf_eq_prime C_square
  intro h
  exact C_not_mem_zpowers_z (h ▸ (Subgroup.zpowers z).one_mem)

theorem C_inverts_U : C * U * C⁻¹ = U⁻¹ := by
  apply Units.ext
  change matrixC * matrixU * matrixC = !![1, 2; 0, 1]
  decide

theorem order_three_inverting_involution (a : H) (ha : orderOf a = 3) :
    ∃ b : H, orderOf b = 2 ∧ b ∉ Subgroup.zpowers z ∧
      b * a * b⁻¹ = a⁻¹ ∧ Commute b z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (order_three_conjugate_U a ha)
  let e : H ≃* H := MulAut.conj g
  have hea : e U = a := hg
  have hez : e z = z := by
    change g * z * g⁻¹ = z
    rw [Subgroup.mem_center_iff.mp Z_mem_center g]
    simp [mul_assoc]
  refine ⟨e C, ?_, ?_, ?_, ?_⟩
  · rw [e.orderOf_eq, C_order]
  · intro h
    rw [mem_zpowers_z_iff] at h
    rcases h with h | h
    · apply C_not_mem_zpowers_z
      rw [mem_zpowers_z_iff]
      exact Or.inl (e.injective (h.trans e.map_one.symm))
    · apply C_not_mem_zpowers_z
      rw [mem_zpowers_z_iff]
      exact Or.inr (e.injective (h.trans hez.symm))
  · have h := congrArg e C_inverts_U
    simpa only [map_mul, map_inv, hea] using h
  · change e C * z = z * e C
    exact Subgroup.mem_center_iff.mp Z_mem_center (e C)

theorem full_structure_and_element_profile :
    Nat.card H = 48 ∧ orderOf z = 2 ∧
    (z : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1 ∧
    Subgroup.center H = Subgroup.zpowers z ∧
    (Subgroup.center K).map K.subtype = Subgroup.zpowers z ∧
    commutator H = K ∧ K.index = 2 ∧ (∀ L : Subgroup H, L.index = 2 → L = K) ∧
    Nat.card {g : H // orderOf g = 1} = 1 ∧
    Nat.card {g : H // orderOf g = 2} = 13 ∧
    Nat.card {g : H // orderOf g = 3} = 8 ∧
    Nat.card {g : H // orderOf g = 4} = 6 ∧
    Nat.card {g : H // orderOf g = 6} = 8 ∧
    Nat.card {g : H // orderOf g = 8} = 12 ∧
    (∀ g : H, orderOf g ∈ ({1, 2, 3, 4, 6, 8} : Finset ℕ)) ∧
    (∀ a b : H, orderOf a = 3 → orderOf b = 3 → IsConj a b) ∧
    (∀ a : H, orderOf a = 3 → ∃ b : H, orderOf b = 2 ∧ b ∉ Subgroup.zpowers z ∧
      b * a * b⁻¹ = a⁻¹ ∧ Commute b z) := by
  obtain ⟨h1, h2, h3, h4, h6, h8⟩ := element_order_counts
  exact ⟨card48, z_order, z_matrix, centerH, centerK, commutatorH, K_index, uniqueindex2,
    h1, h2, h3, h4, h6, h8, order_exhaustive, order_three_conjugate,
    order_three_inverting_involution⟩

end CFSG.Semidihedral.GL2ThreeStructure
