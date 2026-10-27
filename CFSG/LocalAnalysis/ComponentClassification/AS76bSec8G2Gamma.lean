module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Rad

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Open (IsElemAbelian)

section Conj

variable {K : Type} [Field K] [CharP K 2]

theorem coe_conj_g2Xc
    (γ : Fin Tag.G2.rank → ℤ) (s : K)
    (y : ↥(adjointGroup .G2 K)) :
    ((g2Xc γ s * y * (g2Xc γ s)⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) =
      pinnedX .G2 K γ s * y * pinnedX .G2 K γ s := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, pinnedX_inv_eq]

theorem conj_r_radical_iff
    (s : K) (y : ↥(adjointGroup .G2 K)) :
    (y : ModGL .G2 K) ∈ g2ShortRadical K ↔
      ((g2Xc g2r s * y * (g2Xc g2r s)⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈
        g2ShortRadical K := by
  rw [coe_conj_g2Xc]
  refine ⟨conj_r_mem_g2ShortRadical s, fun h => ?_⟩
  have h1 := conj_r_mem_g2ShortRadical s h
  rwa [show pinnedX .G2 K g2r s * (pinnedX .G2 K g2r s * y * pinnedX .G2 K g2r s) *
      pinnedX .G2 K g2r s = y by
    rw [← mul_assoc, ← mul_assoc, pinnedX_mul_self, one_mul, mul_assoc, pinnedX_mul_self,
      mul_one]] at h1

theorem conj_u_radical_iff
    (s : K) (y : ↥(adjointGroup .G2 K)) :
    (y : ModGL .G2 K) ∈ g2ShortRadical K ↔
      ((g2Xc g2u s * y * (g2Xc g2u s)⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈
        g2ShortRadical K := by
  rw [coe_conj_g2Xc]
  refine ⟨conj_u_mem_g2ShortRadical s, fun h => ?_⟩
  have h1 := conj_u_mem_g2ShortRadical s h
  rwa [show pinnedX .G2 K g2u s * (pinnedX .G2 K g2u s * y * pinnedX .G2 K g2u s) *
      pinnedX .G2 K g2u s = y by
    rw [← mul_assoc, ← mul_assoc, pinnedX_mul_self, one_mul, mul_assoc, pinnedX_mul_self,
      mul_one]] at h1

theorem conj_r_bc
    (s : K) (y : ↥(adjointGroup .G2 K))
    (hy : (y : ModGL .G2 K) ∈ g2BCGroup K) : g2Xc g2r s * y * (g2Xc g2r s)⁻¹ = y :=
  Subtype.ext (by rw [coe_conj_g2Xc]; exact conj_r_eq_of_mem_g2BCGroup s hy)

theorem conj_u_bc
    (s : K) (y : ↥(adjointGroup .G2 K))
    (hy : (y : ModGL .G2 K) ∈ g2BCGroup K) : g2Xc g2u s * y * (g2Xc g2u s)⁻¹ = y :=
  Subtype.ext (by rw [coe_conj_g2Xc]; exact conj_u_eq_of_mem_g2BCGroup s hy)

theorem conj_r_comm_bc
    (s : K) (y : ↥(adjointGroup .G2 K))
    (hy : (y : ModGL .G2 K) ∈ g2ShortRadical K) :
    ((g2Xc g2r s * y * (g2Xc g2r s)⁻¹ * y⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈
      g2BCGroup K := by
  have e : ((g2Xc g2r s * y * (g2Xc g2r s)⁻¹ * y⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) =
      ((g2Xc g2r s * y * (g2Xc g2r s)⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) *
        (y : ModGL .G2 K)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e, coe_conj_g2Xc]
  obtain ⟨x, e', f, hxy⟩ := hy
  rw [hxy, conj_r_radical, g2N_zero_inv, g2N_zero_mul_g2N_zero]
  exact ⟨x * s, 0, g2N_eq_g2N rfl (by ring) (by ring) (by char2_ring) (by char2_ring)
    (by char2_ring)⟩

theorem conj_u_comm_bc
    (s : K) (y : ↥(adjointGroup .G2 K))
    (hy : (y : ModGL .G2 K) ∈ g2ShortRadical K) :
    ((g2Xc g2u s * y * (g2Xc g2u s)⁻¹ * y⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈
      g2BCGroup K := by
  have e : ((g2Xc g2u s * y * (g2Xc g2u s)⁻¹ * y⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) =
      ((g2Xc g2u s * y * (g2Xc g2u s)⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) *
        (y : ModGL .G2 K)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e, coe_conj_g2Xc]
  obtain ⟨x, e', f, hxy⟩ := hy
  rw [hxy, conj_u_radical, g2N_zero_inv, g2N_zero_mul_g2N_zero]
  exact ⟨0, x * s, g2N_eq_g2N rfl (by ring) (by ring) (by char2_ring) (by char2_ring)
    (by char2_ring)⟩

theorem conj_r_g2YGroup_iff
    (s α γ : K) (y : ↥(adjointGroup .G2 K)) :
    (y : ModGL .G2 K) ∈ g2YGroup K α γ ↔
      ((g2Xc g2r s * y * (g2Xc g2r s)⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈
        g2YGroup K (α + s) γ := by
  rw [coe_conj_g2Xc]
  refine ⟨conj_r_mem_g2YGroup s, fun h => ?_⟩
  have h1 := conj_r_mem_g2YGroup s h
  rwa [show pinnedX .G2 K g2r s * (pinnedX .G2 K g2r s * y * pinnedX .G2 K g2r s) *
      pinnedX .G2 K g2r s = y by
    rw [← mul_assoc, ← mul_assoc, pinnedX_mul_self, one_mul, mul_assoc, pinnedX_mul_self,
      mul_one], add_assoc, CharTwo.add_self_eq_zero, add_zero] at h1

theorem conj_u_g2YGroup_iff
    (s α γ : K) (y : ↥(adjointGroup .G2 K)) :
    (y : ModGL .G2 K) ∈ g2YGroup K α γ ↔
      ((g2Xc g2u s * y * (g2Xc g2u s)⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈
        g2YGroup K α (γ + s) := by
  rw [coe_conj_g2Xc]
  refine ⟨conj_u_mem_g2YGroup s, fun h => ?_⟩
  have h1 := conj_u_mem_g2YGroup s h
  rwa [show pinnedX .G2 K g2u s * (pinnedX .G2 K g2u s * y * pinnedX .G2 K g2u s) *
      pinnedX .G2 K g2u s = y by
    rw [← mul_assoc, ← mul_assoc, pinnedX_mul_self, one_mul, mul_assoc, pinnedX_mul_self,
      mul_one], add_assoc, CharTwo.add_self_eq_zero, add_zero] at h1

end Conj

section Gamma

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

omit [Finite K] in
theorem g2YGroup_comm
    (α γ : K) :
    ∀ u ∈ g2YGroup K α γ, ∀ v ∈ g2YGroup K α γ, u * v = v * u :=
  fun u hu v hv => g2ShortRadical_comm u (g2YGroup_le α γ hu) v (g2YGroup_le α γ hv)

omit [Finite K] in
theorem g2YGroup_sq
    (α γ : K) : ∀ u ∈ g2YGroup K α γ, u ^ 2 = 1 :=
  fun u hu => g2ShortRadical_sq u (g2YGroup_le α γ hu)

omit [Finite K] in
theorem sq_g2Xc
    (γ : Fin Tag.G2.rank → ℤ) (s : K) : g2Xc γ s ^ 2 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact pinnedX_mul_self γ s)

omit [Finite G] [Finite K] in
theorem exists_lift_r_mem
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (s : K) :
    ∃ a : G, ∃ ha : a ∈ A, ψ ⟨a, le_normalizer ha⟩ = MulAut.conj (g2Xc g2r s) ∧
      a ∈ unipStab A (twoLift ψ (g2ShortRadical K)) (twoLift ψ (g2BCGroup K)) ∧
      ∀ α γ : K, (twoLift ψ (g2YGroup K α γ)).map (MulAut.conj a).toMonoidHom =
        twoLift ψ (g2YGroup K (α + s) γ) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  obtain ⟨a, ha, -, hac⟩ := exists_sq_eq_one_of_sq hψ hZ (g2Xc g2r s) (sq_g2Xc g2r s)
  exact ⟨a, ha, hac, lift_mem_unipStab hZA hψ ha hac (conj_r_radical_iff s) (conj_r_bc s)
    (conj_r_comm_bc s), fun α γ => map_conj_twoLift hψ hZ (g2YGroup_comm α γ)
      (g2YGroup_comm (α + s) γ) ha hac (conj_r_g2YGroup_iff s α γ)⟩

omit [Finite G] [Finite K] in
theorem exists_lift_u_mem
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (s : K) :
    ∃ a : G, ∃ ha : a ∈ A, ψ ⟨a, le_normalizer ha⟩ = MulAut.conj (g2Xc g2u s) ∧
      a ∈ unipStab A (twoLift ψ (g2ShortRadical K)) (twoLift ψ (g2BCGroup K)) ∧
      ∀ α γ : K, (twoLift ψ (g2YGroup K α γ)).map (MulAut.conj a).toMonoidHom =
        twoLift ψ (g2YGroup K α (γ + s)) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  obtain ⟨a, ha, -, hac⟩ := exists_sq_eq_one_of_sq hψ hZ (g2Xc g2u s) (sq_g2Xc g2u s)
  exact ⟨a, ha, hac, lift_mem_unipStab hZA hψ ha hac (conj_u_radical_iff s) (conj_u_bc s)
    (conj_u_comm_bc s), fun α γ => map_conj_twoLift hψ hZ (g2YGroup_comm α γ)
      (g2YGroup_comm α (γ + s)) ha hac (conj_u_g2YGroup_iff s α γ)⟩

omit [Finite G] in
theorem map_conj_mul (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      H.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] [Finite K] in
theorem exists_lift_ru
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (α γ : K) :
    ∃ u ∈ unipStab A (twoLift ψ (g2ShortRadical K)) (twoLift ψ (g2BCGroup K)),
      (twoLift ψ (g2YGroup K 0 0)).map (MulAut.conj u).toMonoidHom =
        twoLift ψ (g2YGroup K α γ) := by
  obtain ⟨a, -, -, haD, ha⟩ := exists_lift_r_mem hZA hψ α
  obtain ⟨b, -, -, hbD, hb⟩ := exists_lift_u_mem hZA hψ γ
  refine ⟨b * a, mul_mem hbD haD, ?_⟩
  rw [← map_conj_mul, ha, hb, zero_add, zero_add]

end Gamma

section Conjugates

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

omit [Finite K] [CharP K 2] in
theorem twoLift_le_normalizer_R (hc : Sec3 A R T g) (U : Subgroup (ModGL .G2 K)) :
    twoLift ψ U ≤ normalizer (R : Set G) := by
  intro b hb
  refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun r hr => ?_)
  exact (mem_centralizer_iff.1 (hc.sylowR.le hr) b (twoLift_le hb)).symm

omit [Finite K] [CharP K 2] in
theorem exists_mul_of_mem_sup_twoLift (hc : Sec3 A R T g) (U : Subgroup (ModGL .G2 K))
    {x : G} (hx : x ∈ R ⊔ twoLift ψ U) : ∃ r ∈ R, ∃ b ∈ twoLift ψ U, r * b = x := by
  have hx' : x ∈ ((R ⊔ twoLift ψ U : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left R _ (twoLift_le_normalizer_R hc U), Set.mem_mul] at hx'
  exact hx'

theorem sup_lift_inf_le
    (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {α γ α' γ' : K} (h : α ≠ α' ∨ γ ≠ γ') :
    (R ⊔ twoLift ψ (g2YGroup K α γ)) ⊓ (R ⊔ twoLift ψ (g2YGroup K α' γ')) ≤ R := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := mem_inf.1 hx
  obtain ⟨r₁, hr₁, z₁, hz₁, rfl⟩ := exists_mul_of_mem_sup_twoLift hc _ hx₁
  obtain ⟨r₂, hr₂, z₂, hz₂, he⟩ := exists_mul_of_mem_sup_twoLift hc _ hx₂
  have hrr : r₂⁻¹ * r₁ = z₂ * z₁⁻¹ := by
    calc r₂⁻¹ * r₁ = r₂⁻¹ * (r₁ * z₁) * z₁⁻¹ := by group
      _ = r₂⁻¹ * (r₂ * z₂) * z₁⁻¹ := by rw [he]
      _ = z₂ * z₁⁻¹ := by group
  have hrA : r₂⁻¹ * r₁ ∈ R ⊓ A :=
    mem_inf.2 ⟨mul_mem (inv_mem hr₂) hr₁, by
      rw [hrr]; exact mul_mem (twoLift_le hz₂) (inv_mem (twoLift_le hz₁))⟩
  rw [inf_eq_bot_sec3 hc hZA, mem_bot, hrr, mul_inv_eq_one] at hrA
  subst hrA
  obtain ⟨hzA, hz2, y, hy, hyU⟩ := (mem_twoLift hψ hZ (g2YGroup_comm α γ)).1 hz₁
  obtain ⟨_, -, y', hy', hyU'⟩ := (mem_twoLift hψ hZ (g2YGroup_comm α' γ')).1 hz₂
  have hyy : y = y' := hinj (hy.symm.trans hy')
  subst hyy
  have hy1 : (y : ModGL .G2 K) ∈ g2YGroup K α γ ⊓ g2YGroup K α' γ' := mem_inf.2 ⟨hyU, hyU'⟩
  rw [g2YGroup_inf_g2YGroup h, mem_bot] at hy1
  have hy1' : y = 1 := Subtype.ext hy1
  rw [hy1', map_one] at hy
  have hz1 : z₂ = 1 := eq_of_sq_eq_one hψ hZ hzA (one_mem A) hz2 (one_pow 2)
    (by rw [hy]; exact (map_one ψ).symm)
  rw [hz1, mul_one]
  exact hr₁

omit [Finite G] in
theorem card_twoLift_g2YGroup
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (α γ : K) : Nat.card (twoLift ψ (g2YGroup K α γ)) = Nat.card K := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hAvC : g2YGroup K α γ ≤ adjointGroup .G2 K := fun q hq =>
    g2LongRadical_le_adjointGroup (g2ShortRadical_le_g2LongRadical (g2YGroup_le α γ hq))
  rw [card_twoLift hψ hZ (g2YGroup_comm α γ) (g2YGroup_sq α γ) hZC, ← card_g2YGroup α γ]
  have h1 := Subgroup.card_map_of_injective (K := (g2YGroup K α γ).subgroupOf
    (adjointGroup .G2 K)) (adjointGroup .G2 K).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAvC] at h1
  exact h1.symm

end Conjugates

end CFSG.ComponentClassification.RankTwoExceptional
