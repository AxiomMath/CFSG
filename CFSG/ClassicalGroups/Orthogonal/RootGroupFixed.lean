module

public import CFSG.ClassicalGroups.F2Fixed
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups.F2Fixed QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

abbrev Gom (Q : QuadraticForm K V) : Type _ := ↥(elementaryGroup Q)

@[expose] def Gom.app (g : Gom Q) (v : V) : V := (g : V ≃ₗ[K] V) v

theorem Gom.app_mul (g h : Gom Q) (v : V) : (g * h).app v = g.app (h.app v) := rfl

theorem Gom.app_one (v : V) : (1 : Gom Q).app v = v := rfl

theorem Gom.app_inv_app (g : Gom Q) (v : V) : g⁻¹.app (g.app v) = v :=
  LinearEquiv.inv_apply_apply' (g : V ≃ₗ[K] V) v

theorem Gom.app_app_inv (g : Gom Q) (v : V) : g.app (g⁻¹.app v) = v := by
  have := Gom.app_inv_app g⁻¹ v
  rwa [inv_inv] at this

theorem Gom.map_add (g : Gom Q) (v w : V) : g.app (v + w) = g.app v + g.app w :=
  _root_.map_add (g : V ≃ₗ[K] V) v w

theorem Gom.map_smul (g : Gom Q) (c : K) (v : V) : g.app (c • v) = c • g.app v :=
  _root_.map_smul (g : V ≃ₗ[K] V) c v

theorem Gom.map_of_mem (g : Gom Q) (v : V) : Q (g.app v) = Q v :=
  CFSG.ClassicalGroups.Orthogonal.map_of_mem (elementaryGroup_le_orthogonalGroup Q g.2) v

theorem Gom.polar_app (g : Gom Q) (v w : V) : polar Q (g.app v) (g.app w) = polar Q v w :=
  polar_map_of_mem (elementaryGroup_le_orthogonalGroup Q g.2) v w

@[expose] def Lom (Q : QuadraticForm K V) (u : V) : Subgroup (Gom Q) :=
  (rootGroup Q u).subgroupOf (elementaryGroup Q)

theorem mem_Lom {u : V} {g : Gom Q} : g ∈ Lom Q u ↔ (g : V ≃ₗ[K] V) ∈ rootGroup Q u := Iff.rfl

theorem conj_mem_Lom (g : Gom Q) {u : V} {x : Gom Q} (hx : x ∈ Lom Q u) :
    g * x * g⁻¹ ∈ Lom Q (g.app u) :=
  conj_mem_rootGroup (elementaryGroup_le_orthogonalGroup Q g.2) hx

theorem image_conj_Lom (g : Gom Q) (u : V) :
    (fun s => g * s * g⁻¹) '' (Lom Q u : Set (Gom Q)) = (Lom Q (g.app u) : Set (Gom Q)) := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact conj_mem_Lom g hs
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    have := conj_mem_Lom g⁻¹ hy
    rwa [Gom.app_inv_app] at this

theorem card_fixedSub_Lom {M : Type*} [AddCommGroup M] [DistribMulAction (Gom Q) M]
    (g : Gom Q) (u : V) :
    Nat.card (fixedSub M (Lom Q (g.app u) : Set (Gom Q))) =
      Nat.card (fixedSub M (Lom Q u : Set (Gom Q))) := by
  rw [← image_conj_Lom g u]
  exact card_fixedSub_conj _ g

theorem rootGroup_le_smul {u : V} {s : K} (hs : s ≠ 0) : rootGroup Q u ≤ rootGroup Q (s • u) := by
  intro g hg
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
  refine mem_rootGroup.mpr ⟨s⁻¹ • w, ?_, ?_⟩
  · rw [polar_smul_left_eq, polar_smul_right_eq, hw, mul_zero, mul_zero]
  · rw [eichler_smul_left, smul_smul, mul_inv_cancel₀ hs, one_smul]

theorem Lom_smul {u : V} {s : K} (hs : s ≠ 0) : Lom Q (s • u) = Lom Q u := by
  ext g
  rw [mem_Lom, mem_Lom]
  constructor
  · intro h
    have := rootGroup_le_smul (Q := Q) (u := s • u) (inv_ne_zero hs) h
    rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
  · intro h
    exact rootGroup_le_smul hs h

end CFSG.ClassicalGroups.Orthogonal
