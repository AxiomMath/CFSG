module

public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.LieType.Chevalley.RootCommutatorCertificate

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open scoped commutatorElement

@[expose] def g2LongRoots : Set (Fin Tag.G2.rank → ℤ) :=
  {![1, 0], ![1, 3], ![2, 3], ![-1, 0], ![-1, -3], ![-2, -3]}

@[expose] def g2LongRootGroup (K : Type) [Field K] : Subgroup (ModGL .G2 K) :=
  rootSpan .G2 K g2LongRoots

variable {K : Type} [Field K]

theorem orbitCertRoot_G2_seven : orbitCertRoot .G2 7 = ![1, 0] :=
  List.ofFn_injective (by decide +kernel)

theorem orbitCertRoot_G2_ten : orbitCertRoot .G2 10 = ![1, 3] :=
  List.ofFn_injective (by decide +kernel)

theorem orbitCertRoot_G2_eleven : orbitCertRoot .G2 11 = ![2, 3] :=
  List.ofFn_injective (by decide +kernel)

open MvPolynomial in
theorem g2_pinnedX_commutator_long (s t : K) :
    pinnedX .G2 K (orbitCertRoot .G2 7) s * pinnedX .G2 K (orbitCertRoot .G2 10) t *
        pinnedX .G2 K (orbitCertRoot .G2 7) (-s) * pinnedX .G2 K (orbitCertRoot .G2 10) (-t) =
      pinnedX .G2 K (orbitCertRoot .G2 11) (s * t) := by
  have hr : ((7, 10, 12, [(1, 1, 11, 1)]) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have h := ((rank_two_pair_certificate .G2).2 _ hr).2.2.2.2.2.2.2.2.2.2.2
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one,
    Int.cast_one, one_mul] at h
  set g : MvPolynomial (Fin 2) ℤ →+* K := eval₂Hom (Int.castRingHom K) ![s, t]
  have hg0 : g (X 0) = s := eval₂Hom_X' _ _ _
  have hg1 : g (X 1) = t := eval₂Hom_X' _ _ _
  have hL := (((baseChange_pinnedX (τ := .G2) g (orbitCertRoot .G2 7) (X 0)).mul
    (baseChange_pinnedX g (orbitCertRoot .G2 10) (X 1))).mul
    (baseChange_pinnedX g (orbitCertRoot .G2 7) (-X 0))).mul
    (baseChange_pinnedX g (orbitCertRoot .G2 10) (-X 1))
  rw [map_neg, map_neg, hg0, hg1] at hL
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, h] at hL
  have hR := baseChange_pinnedX (τ := .G2) g (orbitCertRoot .G2 11) (X 0 * X 1)
  simp only [map_mul, hg0, hg1] at hR
  refine Units.ext ?_
  simp only [Units.val_mul]
  exact hL.unique hR

theorem g2_long_pinnedX_mem_commutator {S : Subgroup (ModGL .G2 K)} (w : WeylGroup .G2)
    (ha : ∀ x, pinnedX .G2 K (w • orbitCertRoot .G2 7) x ∈ S)
    (hb : ∀ x, pinnedX .G2 K (w • orbitCertRoot .G2 10) x ∈ S) (x : K) :
    pinnedX .G2 K (w • orbitCertRoot .G2 11) x ∈ ⁅S, S⁆ := by
  have hr7 : IsRoot .G2 (orbitCertRoot .G2 7) := isRoot_decodeVec_witness (by decide)
  have hr10 : IsRoot .G2 (orbitCertRoot .G2 10) := isRoot_decodeVec_witness (by decide)
  have hr11 : IsRoot .G2 (orbitCertRoot .G2 11) := isRoot_decodeVec_witness (by decide)
  obtain ⟨ε₁, -, h₁⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hr7
  obtain ⟨ε₂, -, h₂⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hr10
  obtain ⟨ε₃, hε₃, h₃⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hr11
  obtain ⟨t, ht⟩ : ∃ t : K, ε₃ * (1 * t) = x := ⟨ε₃ * x, by rw [one_mul, ← mul_assoc, hε₃,
    one_mul]⟩
  set n := canonicalRep (coxeterSystem .G2) K w
  have hid := congrArg (fun y => n * y * n⁻¹) (g2_pinnedX_commutator_long (K := K) 1 t)
  have e : ∀ a₁ a₂ a₃ a₄ : ModGL .G2 K, n * (a₁ * a₂ * a₃ * a₄) * n⁻¹ =
      (n * a₁ * n⁻¹) * (n * a₂ * n⁻¹) * (n * a₃ * n⁻¹) * (n * a₄ * n⁻¹) := fun _ _ _ _ => by
    group
  rw [e, h₁, h₁, h₂, h₂, h₃, ht, mul_neg, mul_neg, ← pinnedX_neg, ← pinnedX_neg,
    ← commutatorElement_def] at hid
  rw [← hid]
  exact Subgroup.commutator_mem_commutator (ha _) (hb _)

theorem exists_smul_long {γ : Fin Tag.G2.rank → ℤ} (hγ : γ ∈ g2LongRoots) :
    ∃ w : WeylGroup .G2, w • orbitCertRoot .G2 11 = γ ∧ w • orbitCertRoot .G2 7 ∈ g2LongRoots ∧
      w • orbitCertRoot .G2 10 ∈ g2LongRoots := by
  set s₁ : WeylGroup .G2 := simple .G2 ⟨0, by decide⟩
  set s₂ : WeylGroup .G2 := simple .G2 ⟨1, by decide⟩
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨s₂ * s₁, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))),
      Or.inr (Or.inr (Or.inl ?_))⟩ <;> simp only [s₁, s₂, mul_smul, simple_smul] <;>
      exact List.ofFn_injective (by decide +kernel)
  · refine ⟨s₁, ?_, Or.inr (Or.inr (Or.inr (Or.inl ?_))), Or.inr (Or.inr (Or.inl ?_))⟩
      <;> simp only [s₁, simple_smul] <;> exact List.ofFn_injective (by decide +kernel)
  · refine ⟨1, ?_, Or.inl ?_, Or.inr (Or.inl ?_)⟩ <;> simp only [one_smul] <;>
      exact List.ofFn_injective (by decide +kernel)
  · refine ⟨s₁ * s₂ * s₁, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))),
      Or.inr (Or.inl ?_)⟩ <;> simp only [s₁, s₂, mul_smul, simple_smul] <;>
      exact List.ofFn_injective (by decide +kernel)
  · refine ⟨s₂ * s₁ * s₂ * s₁, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))), Or.inl ?_⟩
      <;> simp only [s₁, s₂, mul_smul, simple_smul] <;>
      exact List.ofFn_injective (by decide +kernel)
  · refine ⟨s₁ * s₂ * s₁ * s₂ * s₁, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))),
      Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩ <;> simp only [s₁, s₂, mul_smul, simple_smul] <;>
      exact List.ofFn_injective (by decide +kernel)

theorem pinnedX_mem_g2LongRootGroup {γ : Fin Tag.G2.rank → ℤ} (hγ : γ ∈ g2LongRoots) (x : K) :
    pinnedX .G2 K γ x ∈ g2LongRootGroup K :=
  pinnedX_mem_rootSpan hγ x

theorem G2_long_root_subgroup_perfect (K : Type) [Field K] :
    g2LongRootGroup K ≤ adjointGroup .G2 K ∧ g2LongRootGroup K ≠ ⊥ ∧
      ⁅g2LongRootGroup K, g2LongRootGroup K⁆ = g2LongRootGroup K ∧
      pinnedX .G2 K ![1, 0] 1 ∈ g2LongRootGroup K ∧
      (ringChar K = 2 → orderOf (pinnedX .G2 K ![1, 0] 1) = 2) := by
  have ha : (![1, 0] : Fin Tag.G2.rank → ℤ) ∈ g2LongRoots := Or.inl rfl
  have hne : pinnedX .G2 K ![1, 0] 1 ≠ 1 := fun h =>
    one_ne_zero (pinnedX_injective .G2 K _ (h.trans (pinnedX_zero .G2 K _).symm))
  refine ⟨iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α, fun h => ?_, le_antisymm ?_ ?_,
    pinnedX_mem_g2LongRootGroup ha 1, fun hK => ?_⟩
  · have hx := pinnedX_mem_g2LongRootGroup (K := K) ha 1
    rw [h, Subgroup.mem_bot] at hx
    exact hne hx
  · refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
  · refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨w, hw, hwa, hwb⟩ := exists_smul_long hγ
    rw [← hw]
    exact g2_long_pinnedX_mem_commutator w (pinnedX_mem_g2LongRootGroup hwa)
      (pinnedX_mem_g2LongRootGroup hwb) x
  · have : CharP K 2 := ringChar.eq_iff.1 hK
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    refine orderOf_eq_prime ?_ hne
    rw [← orbitCertRoot_G2_seven, sq, ← pinnedX_add, one_add_one_eq_two, h2, pinnedX_zero]

end CFSG.ComponentClassification.UnbalancedCatalog
