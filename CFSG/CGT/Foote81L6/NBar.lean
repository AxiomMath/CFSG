module

public import CFSG.Quasithin.Background.B1Transvection

public section

namespace CFSG.CGT.Foote81L6.NBar

open Subgroup CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type*} [Group G] (F : Subgroup G)

abbrev Q : Type _ := ↥(normalizer (F : Set G)) ⧸ F.normalizerMonoidHom.ker

noncomputable abbrev π : ↥(normalizer (F : Set G)) →* Q F := QuotientGroup.mk' _

noncomputable def ρ : Q F →* MulAut ↥F := QuotientGroup.kerLift F.normalizerMonoidHom

theorem ρ_π (n : ↥(normalizer (F : Set G))) (v : ↥F) :
    ((ρ F (π F n) v : ↥F) : G) = n * v * (n : G)⁻¹ := by
  simp [ρ, π]

theorem ρ_injective : Function.Injective (ρ F) := QuotientGroup.kerLift_injective _

theorem π_surjective : Function.Surjective (π F) := QuotientGroup.mk'_surjective _

theorem π_eq_one_iff (n : ↥(normalizer (F : Set G))) :
    π F n = 1 ↔ ∀ v ∈ F, (n : G) * v * (n : G)⁻¹ = v := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, MonoidHom.mem_ker]
  constructor
  · intro h v hv
    have := congrArg (fun φ : MulAut ↥F => ((φ ⟨v, hv⟩ : ↥F) : G)) h
    simpa using this
  · intro h
    ext v
    simpa using h v v.2

theorem π_eq_one_of_mem (hF : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (n : ↥(normalizer (F : Set G)))
    (hn : (n : G) ∈ F) : π F n = 1 := by
  rw [π_eq_one_iff]
  intro v hv
  rw [hF _ hn _ hv, mul_inv_cancel_right]

theorem π_eq_π_iff (n n' : ↥(normalizer (F : Set G))) :
    π F n = π F n' ↔ ∀ v ∈ F, (n : G) * v * (n : G)⁻¹ = (n' : G) * v * (n' : G)⁻¹ := by
  constructor
  · intro h v hv
    rw [← ρ_π F n ⟨v, hv⟩, ← ρ_π F n' ⟨v, hv⟩, h]
  · intro h
    apply ρ_injective F
    ext v
    rw [ρ_π, ρ_π, h v v.2]

theorem isTransvectionWith_of_commutator [IsMulCommutative F] (n : ↥(normalizer (F : Set G)))
    {w : G} (hw : w ∈ F) (hw1 : w ≠ 1) (hw2 : w * w = 1)
    (hc : ⁅F, zpowers (n : G)⁆ ≤ zpowers w) :
    IsTransvectionWith (ρ F (π F n)) ⟨w, hw⟩ := by
  refine ⟨fun h => hw1 (congrArg Subtype.val h), fun v => ?_⟩
  have hmem : ⁅(v : G), (n : G)⁆ ∈ zpowers w :=
    hc (commutator_mem_commutator v.2 (mem_zpowers _))
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hmem
  rw [zpow_eq_zpow_emod' j (show w ^ 2 = 1 by rw [sq]; exact hw2)] at hj
  have hcomm : (v : G) * w = w * v := by
    have := mul_comm v (⟨w, hw⟩ : ↥F)
    exact congrArg Subtype.val this
  rcases Int.emod_two_eq_zero_or_one j with h0 | h1
  · left
    apply Subtype.ext
    rw [ρ_π]
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero, commutatorElement_def] at hj
    calc (n : G) * v * (n : G)⁻¹ = ((v : G) * n * (v : G)⁻¹ * (n : G)⁻¹)⁻¹ * v := by group
      _ = v := by rw [← hj, inv_one, one_mul]
  · right
    apply Subtype.ext
    rw [ρ_π]
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one, commutatorElement_def] at hj
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    calc (n : G) * v * (n : G)⁻¹ = ((v : G) * n * (v : G)⁻¹ * (n : G)⁻¹)⁻¹ * v := by group
      _ = v * w := by rw [← hj, hwinv, ← hcomm]
      _ = ((v * ⟨w, hw⟩ : ↥F) : G) := rfl

theorem eq_of_isTransvectionWith {V : Type*} [CommGroup V] {t : MulAut V} {w w' : V}
    (h : IsTransvectionWith t w) (h' : IsTransvectionWith t w') (ht : t ≠ 1) : w = w' := by
  obtain ⟨v, hv⟩ := B1.exists_moved_of_ne_one ht
  rcases h.2 v with h1 | h1
  · exact absurd h1 hv
  rcases h'.2 v with h2 | h2
  · exact absurd h2 hv
  exact mul_left_cancel (h1.symm.trans h2)

variable [Finite G]

noncomputable def sylowImage {p : ℕ} [Fact p.Prime] (P : Sylow p ↥(normalizer (F : Set G))) :
    Sylow p (Q F) :=
  P.mapSurjective (π_surjective F)

theorem coe_sylowImage {p : ℕ} [Fact p.Prime] (P : Sylow p ↥(normalizer (F : Set G))) :
    (sylowImage F P : Subgroup (Q F)) = (P : Subgroup _).map (π F) :=
  Sylow.coe_mapSurjective _ P

end CFSG.CGT.Foote81L6.NBar
