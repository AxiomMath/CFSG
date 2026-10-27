module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.PPrime
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Central
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open CFSG.LieType.Steinberg
open scoped commutatorElement

universe u v w

section Perfect

variable {R : Type*} [Group R]

theorem eq_top_of_perfect_of_central [Group.IsPerfect R] {S Z : Subgroup R}
    (hZ : Z ≤ Subgroup.center R) (h : ∀ r : R, ∃ s ∈ S, ∃ z ∈ Z, r = s * z) : S = ⊤ := by
  have hcomm : commutator R ≤ S := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨s, hs, z, hz, rfl⟩ := h x
    obtain ⟨t, ht, w, hw, rfl⟩ := h y
    rw [comm_central_mul_right (hZ hz), comm_mul_central_right (hZ hw), commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem hs ht) (S.inv_mem hs)) (S.inv_mem ht)
  rw [eq_top_iff]
  intro g _
  exact hcomm (by rw [Group.IsPerfect.commutator_eq_top]; trivial)

end Perfect

section Commutator

variable {R H : Type*} [Group R] [Group H] (ρ : R →* H)

theorem surjective_comp_commutator [Group.IsPerfect H] (hρ : Function.Surjective ρ) :
    Function.Surjective (ρ.comp (commutator R).subtype) := by
  have h : (commutator R).map ρ = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective ρ hρ,
      ← commutator_def, Group.IsPerfect.commutator_eq_top]
  intro x
  have hx : x ∈ (commutator R).map ρ := by rw [h]; trivial
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨y, hy⟩, rfl⟩

theorem isPerfect_commutator [Group.IsPerfect H] (hρ : Function.Surjective ρ)
    (hcen : ρ.ker ≤ Subgroup.center R) : Group.IsPerfect (commutator R) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
  have hdec : ∀ r : R, ∃ y ∈ commutator R, ∃ n ∈ Subgroup.center R, r = y * n := by
    intro r
    obtain ⟨y, hy⟩ := surjective_comp_commutator ρ hρ (ρ r)
    refine ⟨y, y.2, (y : R)⁻¹ * r, hcen ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (ρ (y : R))⁻¹ * ρ r = 1
    rw [show ρ (y : R) = ρ r from hy, inv_mul_cancel]
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  obtain ⟨y₁, hy₁, n₁, hn₁, rfl⟩ := hdec g₁
  obtain ⟨y₂, hy₂, n₂, hn₂, rfl⟩ := hdec g₂
  rw [comm_central_mul_right hn₁, comm_mul_central_right hn₂]
  exact Subgroup.commutator_mem_commutator hy₁ hy₂

end Commutator

section Split

variable {Q : ℕ → Prop}

theorem exists_section_of_noCover (hQ : ∀ m n, m ∣ n → Q n → Q m) {H : Type v} [Group H]
    [Group.IsPerfect H] (hH : NoCover.{w} Q H) {R : Type w} [Group R] [Finite R] (ρ : R →* H)
    (hρ : Function.Surjective ρ) (hcen : ρ.ker ≤ Subgroup.center R)
    (hQρ : Q (Nat.card ρ.ker)) : ∃ s : H →* R, ∀ x, ρ (s x) = x := by
  have : Group.IsPerfect (commutator R) := isPerfect_commutator ρ hρ hcen
  let φ : commutator R →* H := ρ.comp (commutator R).subtype
  have hφ : Function.Surjective φ := surjective_comp_commutator ρ hρ
  have hφc : φ.ker ≤ Subgroup.center (commutator R) := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hcen hy) z)
  have hQφ : Q (Nat.card φ.ker) := by
    refine hQ _ _ ?_ hQρ
    have hle : φ.ker.map (commutator R).subtype ≤ ρ.ker := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy
    have h1 := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (commutator R).subtype_injective] at h1
  have hbot : φ.ker = ⊥ := hH ↥(commutator R) φ hφ hφc hQφ
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hbot
  let e : commutator R ≃* H := MulEquiv.ofBijective φ ⟨hinj, hφ⟩
  refine ⟨(commutator R).subtype.comp e.symm.toMonoidHom, fun x => ?_⟩
  change φ (e.symm x) = x
  exact e.apply_symm_apply x

theorem card_ker_pullbackFst_dvd {H : Type v} [Group H] {E : Type u} [Group E] {G : Type*} [Group G]
    (α : H →* G) (π : E →* G) : Nat.card (pullbackFst α π).ker ∣ Nat.card π.ker := by
  let f : (pullbackFst α π).ker →* π.ker :=
    { toFun := fun y => ⟨((y : pullback α π) : H × E).2,
        (snd_mem_ker_of_mem_ker_pullbackFst y.2).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Subgroup.card_dvd_of_injective f fun y₁ y₂ h => ?_
  refine Subtype.ext (Subtype.ext (Prod.ext ?_ (congrArg Subtype.val h)))
  rw [(snd_mem_ker_of_mem_ker_pullbackFst y₁.2).1, (snd_mem_ker_of_mem_ker_pullbackFst y₂.2).1]

theorem exists_lift_of_noCover (hQ : ∀ m n, m ∣ n → Q n → Q m) {H : Type v} [Group H] [Finite H]
    [Group.IsPerfect H] {E : Type u} [Group E] [Finite E] (hH : NoCover.{max v u} Q H)
    {G : Type*} [Group G] (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hQπ : Q (Nat.card π.ker)) (α : H →* G) :
    ∃ β : H →* E, π.comp β = α := by
  have hQ' : Q (Nat.card (pullbackFst α π).ker) :=
    hQ _ _ (card_ker_pullbackFst_dvd α π) hQπ
  obtain ⟨s, hs⟩ := exists_section_of_noCover hQ hH (pullbackFst α π)
    (pullbackFst_surjective hπ) (ker_pullbackFst_le_center hcen) hQ'
  refine ⟨(MonoidHom.snd H E).comp ((pullback α π).subtype.comp s), ?_⟩
  ext x
  have h1 : ((s x : pullback α π) : H × E).1 = x := hs x
  have h2 := mem_pullback.1 (s x).2
  rw [h1] at h2
  exact h2.symm

end Split

end CFSG.ClassicalInvolution.ModelFacts.OddCover
