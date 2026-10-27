module

public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowContainment

public section

namespace CFSG.GroupTheory

open scoped Pointwise

theorem coprime_normalized_sylow_intersection {A G : Type*} [Group A] [Group G]
    [MulDistribMulAction A G] [Finite A] [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hA : IsPGroup p A) (hp : ¬ p ∣ Nat.card G) (P : Sylow q G)
    (hP : ∀ a : A, ∀ x ∈ (P : Subgroup G), a • x ∈ (P : Subgroup G)) (H : Subgroup G)
    (hH : ∀ a : A, ∀ x ∈ H, a • x ∈ H)
    (hCH : fixedPointSubgroup A G ≤ Subgroup.normalizer (H : Set G)) :
    (∃ R : Sylow q H, (R : Subgroup H).map H.subtype = (P : Subgroup G) ⊓ H) ∧
      ∀ a : A, ∀ x ∈ (P : Subgroup G) ⊓ H, a • x ∈ (P : Subgroup G) ⊓ H := by
  have hinvPH : ∀ a : A, ∀ x ∈ (P : Subgroup G) ⊓ H, a • x ∈ (P : Subgroup G) ⊓ H :=
    fun a x hx => ⟨hP a x hx.1, hH a x hx.2⟩
  refine ⟨?_, hinvPH⟩
  have hcopG : Nat.Coprime p (Nat.card G) := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hp
  have : CFSG.IsInvariant A G H :=
    ⟨fun a g => ⟨hH a g, fun h => by simpa using hH a⁻¹ _ h⟩⟩
  have hcopH : Nat.Coprime p (Nat.card H) :=
    hcopG.coprime_dvd_right (Subgroup.card_subgroup_dvd_card H)
  have hIq : IsPGroup q ((P : Subgroup G).subgroupOf H) :=
    P.isPGroup'.comap_of_injective _ H.subtype_injective
  have hIinv : ∀ a : A, ∀ x ∈ (P : Subgroup G).subgroupOf H,
      a • x ∈ (P : Subgroup G).subgroupOf H := fun a x hx =>
    Subgroup.mem_subgroupOf.mpr (hP a x (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨R, hIR, hRinv⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing p q
    Fact.out Fact.out hA hcopH _ hIq hIinv
  have hRmem : ∀ a : A, ∀ x ∈ (R : Subgroup H), a • x ∈ (R : Subgroup H) := by
    intro a x hx
    have heq : a • (R : Subgroup H) = (R : Subgroup H) := by
      rw [← Sylow.pointwise_smul_def, hRinv a]
    rw [← heq]
    exact Subgroup.smul_mem_pointwise_smul x a _ hx
  have hRGq : IsPGroup q ((R : Subgroup H).map H.subtype) := R.isPGroup'.map H.subtype
  have hRGinv : ∀ a : A, ∀ x ∈ (R : Subgroup H).map H.subtype,
      a • x ∈ (R : Subgroup H).map H.subtype := by
    rintro a _ ⟨y, hy, rfl⟩
    exact ⟨a • y, hRmem a y hy, rfl⟩
  obtain ⟨S, hRS, hSinv⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing p q
    Fact.out Fact.out hA hcopG _ hRGq hRGinv
  have hSmem : ∀ a : A, ∀ x ∈ (S : Subgroup G), a • x ∈ (S : Subgroup G) := by
    intro a x hx
    have heq : a • (S : Subgroup G) = (S : Subgroup G) := by
      rw [← Sylow.pointwise_smul_def, hSinv a]
    rw [← heq]
    exact Subgroup.smul_mem_pointwise_smul x a _ hx
  have hSH : (S : Subgroup G) ⊓ H = (R : Subgroup H).map H.subtype := by
    have hq' : IsPGroup q (((S : Subgroup G) ⊓ H).subgroupOf H) :=
      (S.isPGroup'.to_le inf_le_left).comap_of_injective _ H.subtype_injective
    have hle : (R : Subgroup H) ≤ ((S : Subgroup G) ⊓ H).subgroupOf H := fun x hx =>
      Subgroup.mem_subgroupOf.mpr ⟨hRS (Subgroup.mem_map_of_mem H.subtype hx), x.2⟩
    have heq := R.is_maximal' hq' hle
    have hmap := congrArg (Subgroup.map H.subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at hmap
  obtain ⟨c, hc, hcSP⟩ :=
    CFSG.SolvableHall.coprime_invariant_sylow_conjugacy hA hp S P hSmem hP
  have hHc : H.map (MulAut.conj c⁻¹).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hCH (inv_mem hc))
  have hPH : (P : Subgroup G) ⊓ H =
      ((S : Subgroup G) ⊓ H).map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj c⁻¹).injective, hcSP, hHc]
  have hcard : Nat.card ((P : Subgroup G) ⊓ H : Subgroup G) = Nat.card (R : Subgroup H) := by
    rw [hPH, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hSH,
      Subgroup.card_map_of_injective H.subtype_injective]
  have hIcard : Nat.card ((P : Subgroup G).subgroupOf H) = Nat.card (R : Subgroup H) := by
    rw [← hcard, ← Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
  have hIeq : (P : Subgroup G).subgroupOf H = R :=
    Subgroup.eq_of_le_of_card_ge hIR hIcard.ge
  refine ⟨R, ?_⟩
  rw [← hIeq, Subgroup.subgroupOf_map_subtype]

end CFSG.GroupTheory
