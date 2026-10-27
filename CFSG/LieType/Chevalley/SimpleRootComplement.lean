module

public import CFSG.LieType.Chevalley.PositiveRootCollection

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag}

theorem two_le_height_nsmul_add_nsmul {α β : Fin τ.rank → ℤ} (hα : 0 < height α)
    (hβ : 0 < height β) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 2 ≤ height (a • α + b • β) := by
  rw [height_nsmul_add_nsmul]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

theorem nsmul_add_nsmul_mem_complement
    {i : Fin τ.rank} {α β : Fin τ.rank → ℤ}
    (hα : 0 < height α) (hβ : 0 < height β) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hr : IsRoot τ (a • α + b • β)) :
    a • α + b • β ∈ {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1} := by
  have h2 := two_le_height_nsmul_add_nsmul hα hβ ha hb
  refine ⟨hr, by omega, fun h => ?_⟩
  rw [h, height_single] at h2
  omega

theorem rootSubgroup_single_sup_rootSpan_complement
    (R : Type*) [CommRing R] (i : Fin τ.rank) :
    rootSubgroup τ R (Pi.single i 1) ⊔
        rootSpan τ R {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1} =
      posUnipotent τ R := by
  refine le_antisymm (sup_le (le_iSup₂_of_le (Pi.single i 1)
    ⟨isRoot_single τ i, by rw [height_single]; exact one_pos⟩ le_rfl)
    (iSup₂_le fun γ hγ => le_iSup₂_of_le γ ⟨hγ.1, hγ.2.1⟩ le_rfl)) (iSup₂_le fun γ hγ => ?_)
  by_cases h : γ = Pi.single i 1
  · subst h
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂_of_le γ ⟨hγ.1, hγ.2, h⟩ le_rfl)

theorem simple_positive_root_complement
    (τ : Tag) (R : Type) [CommRing R] (i : Fin τ.rank) :
    rootSpan τ R {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1} ≤ posUnipotent τ R ∧
    ((rootSpan τ R {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1}).subgroupOf
      (posUnipotent τ R)).Normal ∧
    (posUnipotent τ R : Set (Module.End R (RootModule τ R))ˣ) =
      (rootSubgroup τ R (Pi.single i 1) : Set (Module.End R (RootModule τ R))ˣ) *
        (rootSpan τ R {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1} :
          Set (Module.End R (RootModule τ R))ˣ) ∧
    (posUnipotent τ R : Set (Module.End R (RootModule τ R))ˣ) =
      (rootSpan τ R {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1} :
          Set (Module.End R (RootModule τ R))ˣ) *
        (rootSubgroup τ R (Pi.single i 1) : Set (Module.End R (RootModule τ R))ˣ) ∧
    rootSubgroup τ R (Pi.single i 1) ⊓
        rootSpan τ R {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1} = ⊥ ∧
    (∀ a ∈ rootSubgroup τ R (Pi.single i 1), ∀ a' ∈ rootSubgroup τ R (Pi.single i 1),
      ∀ b ∈ rootSpan τ R {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1},
      ∀ b' ∈ rootSpan τ R {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1},
        a * b = a' * b' → a = a' ∧ b = b') ∧
    ∀ a ∈ rootSubgroup τ R (Pi.single i 1), ∀ a' ∈ rootSubgroup τ R (Pi.single i 1),
      ∀ b ∈ rootSpan τ R {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1},
      ∀ b' ∈ rootSpan τ R {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1},
        b * a = b' * a' → a = a' ∧ b = b' := by
  set Si : Set (Fin τ.rank → ℤ) := {γ | IsRoot τ γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1} with hSi
  set U := rootSubgroup τ R (Pi.single i 1)
  set N := rootSpan τ R Si
  have hpos1 : 0 < height (Pi.single i 1 : Fin τ.rank → ℤ) := by rw [height_single]; exact one_pos
  obtain ⟨hle, hnorm⟩ := positive_root_ideal_normality τ R (J := Si)
    (S := {γ | IsRoot τ γ ∧ 0 < height γ}) (fun γ hγ => ⟨hγ.1, hγ.2.1⟩) (fun γ hγ => hγ)
    (fun α hα β hβ a b ha hb hr => nsmul_add_nsmul_mem_complement hα.2 hβ.2.1 ha hb hr)
  have hnormal :
      posUnipotent τ R ≤ Subgroup.normalizer (N : Set (Module.End R (RootModule τ R))ˣ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hnorm
  have hU : U ≤ posUnipotent τ R := le_iSup₂_of_le (Pi.single i 1) ⟨isRoot_single τ i, hpos1⟩ le_rfl
  have hsup := rootSubgroup_single_sup_rootSpan_complement R i
  have hinf : U ⊓ N = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxU, hxN⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hxU
    have hfin : Si.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1
    set s := hfin.toFinset
    let β : Fin s.card → Fin τ.rank → ℤ := fun k => (s.equivFin.symm k : Fin τ.rank → ℤ)
    have hβinj : Function.Injective β := fun k l h =>
      s.equivFin.symm.injective (Subtype.ext h)
    have hβS : ∀ k, β k ∈ Si := fun k => hfin.mem_toFinset.1 (s.equivFin.symm k).2
    have hβrange : Set.range β = Si := by
      ext γ
      refine ⟨fun ⟨k, hk⟩ => hk ▸ hβS k, fun hγ => ⟨s.equivFin ⟨γ, hfin.mem_toFinset.2 hγ⟩, ?_⟩⟩
      simp [β]
    obtain ⟨d, -, hd⟩ := (bijOn_prod_pinnedX R (S := Si) (fun γ hγ => ⟨hγ.1, hγ.2.1⟩)
      (fun α hα β' hβ' a b ha hb hr => nsmul_add_nsmul_mem_complement hα.2.1 hβ'.2.1 ha hb hr)
      β hβinj hβrange).2.2 hxN
    let γ : Fin (s.card + 1) → Fin τ.rank → ℤ := Fin.cons (Pi.single i 1) β
    have hγinj : Function.Injective γ :=
      Fin.cons_injective_iff.2 ⟨fun ⟨k, hk⟩ => (hβS k).2.2 hk, hβinj⟩
    have hγpos : ∀ k, IsRoot τ (γ k) ∧ 0 < height (γ k) := fun k => by
      refine Fin.cases ⟨isRoot_single τ i, hpos1⟩ (fun k => ?_) k
      exact ⟨(hβS k).1, (hβS k).2.1⟩
    have hprod := (positive_root_product_injectivity τ R γ hγinj hγpos).2
      (a₁ := Fin.cons c 0) (a₂ := Fin.cons 0 d)
    have heq :
        (List.ofFn fun k => pinnedX τ R (γ k) ((Fin.cons c 0 : Fin (s.card + 1) → R) k)).prod =
          (List.ofFn fun k =>
            pinnedX τ R (γ k) ((Fin.cons 0 d : Fin (s.card + 1) → R) k)).prod := by
      simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons, γ, Pi.zero_apply,
        pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow, mul_one, one_mul]
      exact hd.symm
    have hc := congrFun (hprod heq) 0
    simp only [Fin.cons_zero] at hc
    rw [hc, pinnedX_zero]
    exact Subgroup.one_mem _
  have hprod1 : (posUnipotent τ R : Set (Module.End R (RootModule τ R))ˣ) =
      (U : Set (Module.End R (RootModule τ R))ˣ) * (N : Set (Module.End R (RootModule τ R))ˣ) := by
    rw [← hsup, Subgroup.coe_mul_of_left_le_normalizer_right U N (hU.trans hnormal)]
  have hprod2 : (posUnipotent τ R : Set (Module.End R (RootModule τ R))ˣ) =
      (N : Set (Module.End R (RootModule τ R))ˣ) * (U : Set (Module.End R (RootModule τ R))ˣ) := by
    rw [← hsup, sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left N U (hU.trans hnormal)]
  refine ⟨hle, hnorm, hprod1, hprod2, hinf, fun a ha a' ha' b hb b' hb' h => ?_,
    fun a ha a' ha' b hb b' hb' h => ?_⟩
  · have hm : a'⁻¹ * a = b' * b⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    have h1 : a'⁻¹ * a ∈ U ⊓ N :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha') ha, hm ▸ mul_mem hb' (inv_mem hb)⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h1
    subst h1
    exact ⟨rfl, mul_left_cancel h⟩
  · have hm : a * a'⁻¹ = b⁻¹ * b' := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h, inv_mul_cancel_left]
    have h1 : a * a'⁻¹ ∈ U ⊓ N :=
      Subgroup.mem_inf.2 ⟨mul_mem ha (inv_mem ha'), hm ▸ mul_mem (inv_mem hb) hb'⟩
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h1
    subst h1
    exact ⟨rfl, mul_right_cancel h⟩

end CFSG.LieType.Chevalley
