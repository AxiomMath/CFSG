module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75F1

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

theorem sec47_K0 {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S) {E T K₀ : Subgroup S}
    (hEphi : ∀ x ∈ E, x ∈ phi T → x = 1) (hK₀T : K₀ ≤ T) (hEK₀ : E ≤ K₀)
    (hE8 : Nat.card E = 8) (hK16 : Nat.card K₀ = 16) : IsElemAbelian 2 K₀ := by
  have hE'card : Nat.card (E.subgroupOf K₀) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK₀).toEquiv, hE8]
  have hidx : (E.subgroupOf K₀).index = 2 := by
    have h := Subgroup.card_mul_index (E.subgroupOf K₀)
    rw [hE'card, hK16] at h
    omega
  have : (E.subgroupOf K₀).Normal := Subgroup.normal_of_index_eq_two hidx
  have := IsPGroup.isNilpotent (hS.to_subgroup K₀)
  have hcoatom : IsCoatom (E.subgroupOf K₀) :=
    (IsPGroup.isCoatom_iff_index_eq_prime (hS.to_subgroup K₀)).mpr hidx
  obtain ⟨hsq, hcom⟩ := coatom_props (hS.to_subgroup K₀) hcoatom
  have hsqE : ∀ x ∈ K₀, x ^ 2 ∈ E := fun x hx => by
    have h := hsq ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf] at h
    exact h
  have hcomE : ∀ x ∈ K₀, ∀ y ∈ K₀, x * y * x⁻¹ * y⁻¹ ∈ E := fun x hx y hy => by
    have h := hcom ⟨x, hx⟩ ⟨y, hy⟩
    rw [Subgroup.mem_subgroupOf] at h
    exact h
  have hsq1 : ∀ x ∈ K₀, x ^ 2 = 1 := fun x hx =>
    hEphi _ (hsqE x hx) (sq_mem_phi hS (hK₀T hx))
  have hcom1 : ∀ x ∈ K₀, ∀ y ∈ K₀, x * y * x⁻¹ * y⁻¹ = 1 := fun x hx y hy =>
    hEphi _ (hcomE x hx y hy) (comm_mem_phi hS (hK₀T hx) (hK₀T hy))
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hsq1 x hx⟩
  apply Subtype.ext
  have h := hcom1 (a : S) a.2 (b : S) b.2
  show (a : S) * (b : S) = (b : S) * (a : S)
  calc (a : S) * (b : S)
      = (a : S) * (b : S) * (a : S)⁻¹ * (b : S)⁻¹ * ((b : S) * (a : S)) := by group
    _ = (b : S) * (a : S) := by rw [h, one_mul]

end CFSG.EvenSporadicStandard.Fin76b
