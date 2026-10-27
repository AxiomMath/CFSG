module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.Fin76b

section Group

variable {G : Type*} [Group G]

theorem card_conj_orbit_mul_card_cent (M : Subgroup G) (z : G) :
    Set.ncard {u : G | ∃ m ∈ M, u = m * z * m⁻¹} *
      Nat.card ↥(M ⊓ Subgroup.centralizer ({z} : Set G)) = Nat.card ↥M := by
  let M' : Subgroup (ConjAct G) := M.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom
  have horb : MulAction.orbit ↥M' z = {u : G | ∃ m ∈ M, u = m * z * m⁻¹} := by
    ext u
    constructor
    · rintro ⟨⟨_, m, hm, rfl⟩, rfl⟩
      exact ⟨m, hm, ConjAct.toConjAct_smul m z⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨ConjAct.toConjAct m, m, hm, rfl⟩, ConjAct.toConjAct_smul m z⟩
  let φ : MulAction.stabilizer ↥M' z →* G :=
    (ConjAct.ofConjAct : ConjAct G ≃* G).toMonoidHom.comp
      (M'.subtype.comp (MulAction.stabilizer ↥M' z).subtype)
  have hφ : Function.Injective φ :=
    ConjAct.ofConjAct.injective.comp (M'.subtype_injective.comp Subtype.val_injective)
  have hrange : φ.range = M ⊓ Subgroup.centralizer ({z} : Set G) := by
    ext x
    constructor
    · rintro ⟨⟨⟨_, m, hm, rfl⟩, hg⟩, rfl⟩
      have h1 : m * z * m⁻¹ = z := (ConjAct.toConjAct_smul m z).symm.trans hg
      have h2 : m * z = z * m := by
        calc m * z = m * z * m⁻¹ * m := by group
          _ = z * m := by rw [h1]
      exact ⟨hm, Subgroup.mem_centralizer_singleton_iff.2 h2⟩
    · rintro ⟨hm, hc⟩
      refine ⟨⟨⟨ConjAct.toConjAct x, x, hm, rfl⟩, ?_⟩, rfl⟩
      have h1 : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 hc
      show ConjAct.toConjAct x • z = z
      rw [ConjAct.toConjAct_smul, h1, mul_inv_cancel_right]
  have hstab : Nat.card (MulAction.stabilizer ↥M' z) =
      Nat.card ↥(M ⊓ Subgroup.centralizer ({z} : Set G)) :=
    Nat.card_congr ((MonoidHom.ofInjective hφ).toEquiv.trans
      (MulEquiv.subgroupCongr hrange).toEquiv)
  have hM : Nat.card ↥M' = Nat.card ↥M :=
    Subgroup.card_map_of_injective ConjAct.toConjAct.injective
  rw [← Nat.card_coe_set_eq, ← horb, ← hstab, ← hM, ← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥M' z)

theorem ncard_commuting_conj (X : Set G) (m : G) (hX : ∀ v ∈ X, m * v * m⁻¹ ∈ X)
    (hX' : ∀ v ∈ X, m⁻¹ * v * m ∈ X) (u : G) :
    Set.ncard {w : G | w ∈ X ∧ w * (m * u * m⁻¹) = (m * u * m⁻¹) * w} =
      Set.ncard {w : G | w ∈ X ∧ w * u = u * w} := by
  have himage : {w : G | w ∈ X ∧ w * (m * u * m⁻¹) = (m * u * m⁻¹) * w} =
      (fun w => m * w * m⁻¹) '' {w : G | w ∈ X ∧ w * u = u * w} := by
    ext w
    constructor
    · rintro ⟨hw, hc⟩
      refine ⟨m⁻¹ * w * m, ⟨hX' w hw, ?_⟩, by group⟩
      calc m⁻¹ * w * m * u = m⁻¹ * (w * (m * u * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * u * m⁻¹) * w) * m := by rw [hc]
        _ = u * (m⁻¹ * w * m) := by group
    · rintro ⟨v, ⟨hv, hc⟩, rfl⟩
      refine ⟨hX v hv, ?_⟩
      calc m * v * m⁻¹ * (m * u * m⁻¹) = m * (v * u) * m⁻¹ := by group
        _ = m * (u * v) * m⁻¹ := by rw [hc]
        _ = m * u * m⁻¹ * (m * v * m⁻¹) := by group
  have hinj : Function.Injective (fun w : G => m * w * m⁻¹) := fun a b h => by simpa using h
  rw [himage, Set.ncard_image_of_injective _ hinj]

theorem ncard_image_mul_left (s : G) (C : Set G) :
    Set.ncard ((fun e => s * e) '' C) = Set.ncard C :=
  Set.ncard_image_of_injective C (mul_right_injective s)

end Group

section Finite

variable {G : Type*} [Finite G]

theorem ncard_filter_union {A B : Set G} (hAB : Disjoint A B) (P : G → Prop) :
    Set.ncard {w : G | w ∈ A ∪ B ∧ P w} =
      Set.ncard {w : G | w ∈ A ∧ P w} + Set.ncard {w : G | w ∈ B ∧ P w} := by
  have h : {w : G | w ∈ A ∪ B ∧ P w} = {w : G | w ∈ A ∧ P w} ∪ {w : G | w ∈ B ∧ P w} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    tauto
  rw [h]
  exact Set.ncard_union_eq (hAB.mono (fun w hw => hw.1) (fun w hw => hw.1))

theorem ncard_split_by_prop (C : Set G) (P : G → Prop) :
    Set.ncard C = Set.ncard {w : G | w ∈ C ∧ P w} + Set.ncard {w : G | w ∈ C ∧ ¬ P w} :=
  (Set.ncard_inter_add_ncard_sdiff_eq_ncard C {w | P w}).symm

end Finite

end CFSG.EvenSporadicStandard.Fin76b
