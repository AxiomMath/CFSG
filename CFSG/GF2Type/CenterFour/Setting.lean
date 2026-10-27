module

public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def coreAt (u : G) : Subgroup G :=
  CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({u} : Set G))

@[expose] def centerAt (u : G) : Subgroup G :=
  (center (coreAt u)).map (coreAt u).subtype

omit [Finite G] in
private lemma centralizer_singleton_conj (u g : G) :
    (centralizer ({u} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
      centralizer ({g⁻¹ * u * g} : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    calc g⁻¹ * y * g * (g⁻¹ * u * g) = g⁻¹ * (y * u) * g := by group
      _ = g⁻¹ * (u * y) * g := by rw [hy]
      _ = g⁻¹ * u * g * (g⁻¹ * y * g) := by group
  · intro hx
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · calc g * x * g⁻¹ * u = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by rw [hx]
        _ = u * (g * x * g⁻¹) := by group
    · group

omit [Finite G] in
private def restrictIso (φ : G ≃* G) (H H' : Subgroup G) (h : H.map φ.toMonoidHom = H') :
    H ≃* H' :=
  (MulEquiv.subgroupMap φ H).trans (MulEquiv.subgroupCongr h)

omit [Finite G] in
private lemma inSubgroup_pCore_map (φ : G ≃* G) (H H' : Subgroup G)
    (h : H.map φ.toMonoidHom = H') :
    CFSG.inSubgroup (CFSG.pCore 2) H' = (CFSG.inSubgroup (CFSG.pCore 2) H).map φ.toMonoidHom := by
  have key := CFSG.pCore_map_iso 2 (restrictIso φ H H' h)
  unfold CFSG.inSubgroup
  rw [← key, Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] in
private lemma center_map_restrictIso (φ : G ≃* G) (H H' : Subgroup G)
    (h : H.map φ.toMonoidHom = H') :
    (center H').map H'.subtype = ((center H).map H.subtype).map φ.toMonoidHom := by
  rw [← Subgroup.map_center_eq (restrictIso φ H H' h), Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] in
theorem coreAt_conj (u g : G) : coreAt (g⁻¹ * u * g) = CFSG.conjugate (coreAt u) g := by
  unfold coreAt CFSG.conjugate
  exact inSubgroup_pCore_map (MulAut.conj g⁻¹) _ _ (centralizer_singleton_conj u g)

omit [Finite G] in
theorem centerAt_conj (u g : G) : centerAt (g⁻¹ * u * g) = CFSG.conjugate (centerAt u) g := by
  unfold centerAt CFSG.conjugate
  exact center_map_restrictIso (MulAut.conj g⁻¹) (coreAt u) (coreAt (g⁻¹ * u * g))
    (coreAt_conj u g).symm

structure Config (z : G) (n : ℕ) : Prop where
  orderOf_eq : orderOf z = 2
  three_le : 3 ≤ n
  mem_center : z ∈ centerAt z
  center_cyclic : IsCyclic (centerAt z)
  card_center : Nat.card (centerAt z) = 4
  normalizer_center : normalizer (centerAt z : Set G) = centralizer ({z} : Set G)
  selfCentralizing : ∀ h ∈ centralizer ({z} : Set G),
    (∀ q ∈ coreAt z, h * q = q * h) → h ∈ coreAt z
  sq_eq : ∀ x ∈ coreAt z, x ^ 2 = 1 ∨ x ^ 2 = z
  comm_eq : ∀ x ∈ coreAt z, ∀ y ∈ coreAt z, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z
  card_core : Nat.card (coreAt z) = 2 ^ (2 * n + 2)
  card_elem_le : ∀ U : Subgroup G, U ≤ coreAt z → CFSG.Open.IsElemAbelian 2 U →
    Nat.card U ≤ 2 ^ (n + 1)
  card_elem_le_of_disjoint : ∀ U : Subgroup G, U ≤ coreAt z → CFSG.Open.IsElemAbelian 2 U →
    U ⊓ centerAt z = ⊥ → Nat.card U ≤ 2 ^ n
  card_pairwise_le : ∀ (s : ℕ) (f : Fin s → G), (∀ i, f i ∈ coreAt z) →
    (∀ i j, i ≠ j → ⁅f i, f j⁆ = z) → s ≤ 2 * n + 1
  center_le_iff : ∀ g : G, CFSG.conjugate (centerAt z) g ≤ centralizer ({z} : Set G) ↔
    g⁻¹ * z * g ∈ coreAt z
  mem_core_of_centralizes : ∀ g : G, g⁻¹ * z * g ∈ centralizer (centerAt z : Set G) →
    g⁻¹ * z * g ∈ coreAt z
  exists_fused : ∃ g : G, g⁻¹ * z * g ∈ coreAt z ∧ g⁻¹ * z * g ≠ z

end CFSG.GF2Type.CenterFour
