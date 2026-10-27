module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.D5Frame
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureBlockDefs
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeDFive
import CFSG.LieType.Universal.SpinOmega.IsometryRoots
public import CFSG.ClassicalGroups.Orthogonal.PolarPairPlane
import CFSG.RankThree.PartOne.KC.OrthogonalSupportCharts

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.LieType.CurtisTits CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.RankThree.PartOne.KCOrthogonal QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private def d5EmbA : Fin 3 ↪ Fin 5 :=
  ⟨fun a => ⟨a.val + 2, by have := a.isLt; omega⟩, by
    intro a b h
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)⟩

omit [Finite K] [CharP K 2] in
private theorem d5PlaneVec_mem (i j : Fin 4) (a b : K) :
    ((0 : F × F), d5PlaneVec i j a b) ∈
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) i ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) j := by
  have h1 : ((0 : F × F), Pi.single i a) ∈
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) i :=
    mem_coordPlane.mpr ⟨a, rfl⟩
  have h2 : ((0 : F × F), Pi.single j b) ∈
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) j :=
    mem_coordPlane.mpr ⟨b, rfl⟩
  have h := Submodule.add_mem_sup h1 h2
  rw [d5PlaneVec]
  have hsum : ((0 : F × F), (Pi.single i a : Fin 4 → K) + (Pi.single j b : Fin 4 → K)) =
      ((0 : F × F), (Pi.single i a : Fin 4 → K)) +
        ((0 : F × F), (Pi.single j b : Fin 4 → K)) := by
    rw [Prod.mk_add_mk, zero_add]
  rw [hsum]
  exact h

omit [Finite K] in
private theorem d5n_add_self (x : K) : x + x = 0 := CharTwo.add_self_eq_zero x

omit [Finite K] [CharP K 2] in
private theorem d5n_PlaneVec_add (i j : Fin 4) (a b c d : K) :
    d5PlaneVec i j a b + d5PlaneVec i j c d = d5PlaneVec i j (a + c) (b + d) := by
  unfold d5PlaneVec
  rw [Pi.single_add, Pi.single_add]
  abel

omit [Finite K] [CharP K 2] in
private theorem d5n_PlaneVec_smul (i j : Fin 4) (a : F) (x y : K) :
    a • d5PlaneVec i j x y =
      d5PlaneVec i j (algebraMap F K a * x) (algebraMap F K a * y) := by
  unfold d5PlaneVec
  rw [smul_add]
  congr 1
  · rw [← Pi.single_smul, Algebra.smul_def]
  · rw [← Pi.single_smul, Algebra.smul_def]

private theorem d5n_tau_sq_add_tau :
    d5Tau E ^ 2 + d5Tau E = d5Tau E * unitaryInvolution K 2 f (d5Tau E) := by
  have h1 : d5Tau E + 1 = unitaryInvolution K 2 f (d5Tau E) := by
    calc d5Tau E + 1 =
        d5Tau E + (d5Tau E + unitaryInvolution K 2 f (d5Tau E)) := by
          rw [d5Tau_add_sigma E]
      _ = (d5Tau E + d5Tau E) + unitaryInvolution K 2 f (d5Tau E) := by abel
      _ = unitaryInvolution K 2 f (d5Tau E) := by rw [d5n_add_self, zero_add]
  calc d5Tau E ^ 2 + d5Tau E = d5Tau E * (d5Tau E + 1) := by ring
    _ = d5Tau E * unitaryInvolution K 2 f (d5Tau E) := by rw [h1]

private theorem d5n_sigma_tau :
    unitaryInvolution K 2 f (d5Tau E) = 1 + d5Tau E := by
  calc unitaryInvolution K 2 f (d5Tau E)
      = (d5Tau E + d5Tau E) + unitaryInvolution K 2 f (d5Tau E) := by
        rw [d5n_add_self, zero_add]
    _ = (d5Tau E + unitaryInvolution K 2 f (d5Tau E)) + d5Tau E := by abel
    _ = 1 + d5Tau E := by rw [d5Tau_add_sigma E]

omit [Finite K] [CharP K 2] in
private theorem d5n_smul_single (a : F) (i : Fin 4) (x : K) :
    a • (Pi.single i x : Fin 4 → K) = Pi.single i (algebraMap F K a * x) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [Algebra.smul_def]
  · simp [hk, Algebra.smul_def]

private theorem d5n_fun_CD (i j : Fin 4) :
    d5PlaneVec i j (d5Tau E) (d5Tau E) +
        d5PlaneVec i j (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E) =
      Pi.single i (1 : K) := by
  rw [d5n_PlaneVec_add, d5Tau_add_sigma E, d5n_add_self, d5PlaneVec]
  simp

private theorem d5n_fun_B_nA_i (i j : Fin 4) (n : F)
    (hn : algebraMap F K n = d5Tau E * unitaryInvolution K 2 f (d5Tau E)) :
    (d5PlaneVec i j (d5Tau E) (d5Tau E) +
      d5PlaneVec i j (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) +
        n • d5PlaneVec i j 1 1 = Pi.single i (d5Tau E) := by
  rw [d5n_PlaneVec_smul, mul_one, hn]
  simp only [d5n_PlaneVec_add]
  have h1 : (d5Tau E + d5Tau E * unitaryInvolution K 2 f (d5Tau E)) +
      d5Tau E * unitaryInvolution K 2 f (d5Tau E) = d5Tau E := by
    rw [add_assoc, d5n_add_self, add_zero]
  have h2 : (d5Tau E + d5Tau E ^ 2) +
      d5Tau E * unitaryInvolution K 2 f (d5Tau E) = 0 := by
    rw [← d5n_tau_sq_add_tau E]
    have h : (d5Tau E + d5Tau E ^ 2) + (d5Tau E ^ 2 + d5Tau E) =
        (d5Tau E + d5Tau E) + (d5Tau E ^ 2 + d5Tau E ^ 2) := by abel
    rw [h]
    simp only [d5n_add_self]
  rw [h1, h2, d5PlaneVec]
  simp

private theorem d5n_fun_AD (i j : Fin 4) :
    (d5PlaneVec i j 1 1 + d5PlaneVec i j (d5Tau E) (d5Tau E)) +
        d5PlaneVec i j (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E) =
      Pi.single j (1 : K) := by
  simp only [d5n_PlaneVec_add]
  have h1 : (1 + d5Tau E) + unitaryInvolution K 2 f (d5Tau E) = 0 := by
    rw [add_assoc, d5Tau_add_sigma E]
    simp only [d5n_add_self]
  have h2 : (1 + d5Tau E) + d5Tau E = 1 := by
    rw [add_assoc, d5n_add_self, add_zero]
  rw [h1, h2, d5PlaneVec]
  simp

private theorem d5n_fun_B_nA_j (i j : Fin 4) (n : F)
    (hn : algebraMap F K n = d5Tau E * unitaryInvolution K 2 f (d5Tau E)) :
    d5PlaneVec i j (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2) +
        n • d5PlaneVec i j 1 1 = Pi.single j (d5Tau E) := by
  rw [d5n_PlaneVec_smul, mul_one, hn]
  simp only [d5n_PlaneVec_add]
  have h1 : d5Tau E * unitaryInvolution K 2 f (d5Tau E) +
      d5Tau E * unitaryInvolution K 2 f (d5Tau E) = 0 := d5n_add_self _
  have h2 : d5Tau E ^ 2 + d5Tau E * unitaryInvolution K 2 f (d5Tau E) = d5Tau E := by
    rw [← d5n_tau_sq_add_tau E]
    have h : d5Tau E ^ 2 + (d5Tau E ^ 2 + d5Tau E) =
        (d5Tau E ^ 2 + d5Tau E ^ 2) + d5Tau E := by abel
    rw [h]
    simp only [d5n_add_self, zero_add]
  rw [h1, h2, d5PlaneVec]
  simp

private theorem d5n_basis_tau (x : K) :
    ∃ a b : F, x = algebraMap F K a + algebraMap F K b * d5Tau E := by
  have hfix : unitaryInvolution K 2 f (x + unitaryInvolution K 2 f x) =
      x + unitaryInvolution K 2 f x := by
    rw [map_add, E.isUnitary.invol]
    exact add_comm _ _
  obtain ⟨b, hb⟩ := E.exists_of_fix _ hfix
  have hsigx : unitaryInvolution K 2 f x = x + algebraMap F K b := by
    rw [hb, ← add_assoc, d5n_add_self, zero_add]
  have hfix2 : unitaryInvolution K 2 f (x + algebraMap F K b * d5Tau E) =
      x + algebraMap F K b * d5Tau E := by
    rw [map_add, map_mul, E.fix, d5n_sigma_tau E, hsigx, mul_add, mul_one]
    have h : (x + algebraMap F K b) + (algebraMap F K b + algebraMap F K b * d5Tau E) =
        x + (algebraMap F K b + algebraMap F K b) + algebraMap F K b * d5Tau E := by abel
    rw [h, d5n_add_self, add_zero]
  obtain ⟨a, ha⟩ := E.exists_of_fix _ hfix2
  exact ⟨a, b, by rw [ha, add_assoc, d5n_add_self, add_zero]⟩

private theorem span_d5PlaneVecs {i j : Fin 4} (_hij : i ≠ j) :
    Submodule.span F {((0 : F × F), d5PlaneVec i j 1 1),
        (0, d5PlaneVec i j (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)),
        (0, d5PlaneVec i j (d5Tau E) (d5Tau E)),
        (0, d5PlaneVec i j (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E))} =
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) i ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) j := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨d5PlaneVec_mem i j 1 1,
      d5PlaneVec_mem i j (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2),
      d5PlaneVec_mem i j (d5Tau E) (d5Tau E),
      d5PlaneVec_mem i j (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)⟩
  · rw [sup_le_iff]
    constructor
    · intro v hv
      rw [mem_coordPlane] at hv
      obtain ⟨x, rfl⟩ := hv
      obtain ⟨a, b, hab⟩ := d5n_basis_tau E x
      have hnfix : unitaryInvolution K 2 f (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) =
          d5Tau E * unitaryInvolution K 2 f (d5Tau E) := by
        rw [map_mul, E.isUnitary.invol, mul_comm]
      obtain ⟨n, hn⟩ := E.exists_of_fix _ hnfix
      set P1 : (F × F) × (Fin 4 → K) := ((0 : F × F), d5PlaneVec i j 1 1) with hP1
      set P2 : (F × F) × (Fin 4 → K) := ((0 : F × F),
        d5PlaneVec i j (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) with hP2
      set P3 : (F × F) × (Fin 4 → K) :=
        ((0 : F × F), d5PlaneVec i j (d5Tau E) (d5Tau E)) with hP3
      set P4 : (F × F) × (Fin 4 → K) :=
        ((0 : F × F), d5PlaneVec i j (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) with hP4
      have vCD : P3 + P4 = ((0 : F × F), Pi.single i (1 : K)) := by
        apply Prod.ext
        · simp [hP3, hP4]
        · change d5PlaneVec i j (d5Tau E) (d5Tau E) +
              d5PlaneVec i j (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E) = Pi.single i (1 : K)
          exact d5n_fun_CD E i j
      have vBi : P3 + P2 + n • P1 = ((0 : F × F), Pi.single i (d5Tau E)) := by
        apply Prod.ext
        · simp [hP1, hP2, hP3]
        · change (d5PlaneVec i j (d5Tau E) (d5Tau E) +
              d5PlaneVec i j (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) +
                n • d5PlaneVec i j 1 1 = Pi.single i (d5Tau E)
          exact d5n_fun_B_nA_i E i j n hn
      have hcomb : ((0 : F × F), Pi.single i x) =
          a • (P3 + P4) + b • (P3 + P2 + n • P1) := by
        rw [vCD, vBi]
        apply Prod.ext
        · simp
        · simp only [Prod.snd_add, Prod.smul_snd]
          simp only [d5n_smul_single, mul_one, hab, Pi.single_add]
      rw [hcomb]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
      · exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp))
      · exact Submodule.add_mem _ (Submodule.add_mem _
          (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · intro v hv
      rw [mem_coordPlane] at hv
      obtain ⟨x, rfl⟩ := hv
      obtain ⟨a, b, hab⟩ := d5n_basis_tau E x
      have hnfix : unitaryInvolution K 2 f (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) =
          d5Tau E * unitaryInvolution K 2 f (d5Tau E) := by
        rw [map_mul, E.isUnitary.invol, mul_comm]
      obtain ⟨n, hn⟩ := E.exists_of_fix _ hnfix
      set P1 : (F × F) × (Fin 4 → K) := ((0 : F × F), d5PlaneVec i j 1 1) with hP1
      set P2 : (F × F) × (Fin 4 → K) := ((0 : F × F),
        d5PlaneVec i j (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)) with hP2
      set P3 : (F × F) × (Fin 4 → K) :=
        ((0 : F × F), d5PlaneVec i j (d5Tau E) (d5Tau E)) with hP3
      set P4 : (F × F) × (Fin 4 → K) :=
        ((0 : F × F), d5PlaneVec i j (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) with hP4
      have vAD : P1 + P3 + P4 = ((0 : F × F), Pi.single j (1 : K)) := by
        apply Prod.ext
        · simp [hP1, hP3, hP4]
        · change (d5PlaneVec i j 1 1 + d5PlaneVec i j (d5Tau E) (d5Tau E)) +
              d5PlaneVec i j (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E) =
                Pi.single j (1 : K)
          exact d5n_fun_AD E i j
      have vBj : P2 + n • P1 = ((0 : F × F), Pi.single j (d5Tau E)) := by
        apply Prod.ext
        · simp [hP1, hP2]
        · change d5PlaneVec i j (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2) +
              n • d5PlaneVec i j 1 1 = Pi.single j (d5Tau E)
          exact d5n_fun_B_nA_j E i j n hn
      have hcomb : ((0 : F × F), Pi.single j x) =
          a • (P1 + P3 + P4) + b • (P2 + n • P1) := by
        rw [vAD, vBj]
        apply Prod.ext
        · simp
        · simp only [Prod.snd_add, Prod.smul_snd]
          simp only [d5n_smul_single, mul_one, hab, Pi.single_add]
      rw [hcomb]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
      · exact Submodule.add_mem _ (Submodule.add_mem _
          (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)))
          (Submodule.subset_span (by simp))
      · exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem d5n_plusIncl_toLinearMap_plusVec {m n : ℕ} (σ : Fin m ↪ Fin n)
    (a : Fin m) (s : Bool) :
    (plusIncl (K := F) σ).toLinearMap (plusVec m F a s) = plusVec n F (σ a) s := by
  change plusIncl (K := F) σ (plusVec m F a s) = plusVec n F (σ a) s
  exact plusIncl_plusVec (K := F) σ a s

private theorem plusInclRange_eq_span {m n : ℕ} (σ : Fin m ↪ Fin n) :
    plusInclRange (K := F) σ =
      Submodule.span F (Set.range fun p : Fin m × Bool => plusVec n F (σ p.1) p.2) := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    have hu : u = ∑ a : Fin m, (u (Sum.inl a) • plusVec m F a true +
        u (Sum.inr a) • plusVec m F a false) := by
      conv_lhs => rw [← Finset.univ_sum_single u]
      rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [plusVec_true, plusVec_false]
      congr 1
      · rw [← Pi.single_smul, smul_eq_mul, mul_one]
      · rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hu]
    simp only [map_sum, map_add, map_smul, d5n_plusIncl_toLinearMap_plusVec]
    refine Submodule.sum_mem _ fun a _ => ?_
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, true), rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, false), rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨⟨a, s⟩, rfl⟩
    exact ⟨plusVec m F a s, plusIncl_plusVec σ a s⟩

private theorem map_d5Frame_plusInclRange {m : ℕ} (σ : Fin m ↪ Fin 5) :
    (plusInclRange (K := F) σ).map (d5Frame E).toLinearEquiv.toLinearMap =
      Submodule.span F (Set.range fun p : Fin m × Bool =>
        if p.2 then d5FrameVecE E (σ p.1) else d5FrameVecF E (σ p.1)) := by
  rw [plusInclRange_eq_span, Submodule.map_span, ← Set.range_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, by
      simp only [Function.comp_apply]
      exact (d5Frame_plusVec E (σ p.1) p.2).symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, by
      simp only [Function.comp_apply]
      exact d5Frame_plusVec E (σ p.1) p.2⟩

private theorem d5n_span_planeVecs_le_span {m : ℕ} (σ : Fin m ↪ Fin 5) {i j : Fin 4}
    (hij : i ≠ j)
    (pA : Fin m × Bool)
    (hA : (if pA.2 then d5FrameVecE E (σ pA.1) else d5FrameVecF E (σ pA.1)) =
      ((0 : F × F), d5PlaneVec i j 1 1))
    (pB : Fin m × Bool)
    (hB : (if pB.2 then d5FrameVecE E (σ pB.1) else d5FrameVecF E (σ pB.1)) =
      ((0 : F × F), d5PlaneVec i j (d5Tau E * unitaryInvolution K 2 f (d5Tau E))
        (d5Tau E ^ 2)))
    (pC : Fin m × Bool)
    (hC : (if pC.2 then d5FrameVecE E (σ pC.1) else d5FrameVecF E (σ pC.1)) =
      ((0 : F × F), d5PlaneVec i j (d5Tau E) (d5Tau E)))
    (pD : Fin m × Bool)
    (hD : (if pD.2 then d5FrameVecE E (σ pD.1) else d5FrameVecF E (σ pD.1)) =
      ((0 : F × F), d5PlaneVec i j (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E))) :
    coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) i ⊔
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) j ≤
      Submodule.span F (Set.range fun p : Fin m × Bool =>
        if p.2 then d5FrameVecE E (σ p.1) else d5FrameVecF E (σ p.1)) := by
  rw [← span_d5PlaneVecs E hij]
  apply Submodule.span_mono
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact ⟨pA, hA⟩
  · exact ⟨pB, hB⟩
  · exact ⟨pC, hC⟩
  · exact ⟨pD, hD⟩

private theorem d5n_mem_univ_sup_pure (a : Fin 4) (s : Bool) :
    (if s then d5FrameVecE E (Fin.castLEEmb (by norm_num : 4 ≤ 5) a)
      else d5FrameVecF E (Fin.castLEEmb (by norm_num : 4 ≤ 5) a)) ∈
      (Finset.univ : Finset (Fin 4)).sup
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K)))) := by
  have h01 : (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1) ≤
      (Finset.univ : Finset (Fin 4)).sup
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K)))) :=
    sup_le (Finset.le_sup (Finset.mem_univ 0)) (Finset.le_sup (Finset.mem_univ 1))
  have h23 : (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 2 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 3) ≤
      (Finset.univ : Finset (Fin 4)).sup
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K)))) :=
    sup_le (Finset.le_sup (Finset.mem_univ 2)) (Finset.le_sup (Finset.mem_univ 3))
  cases s
  · fin_cases a
    · exact h23 (d5PlaneVec_mem 2 3
        (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2))
    · exact h23 (d5PlaneVec_mem 2 3 (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E))
    · exact h01 (d5PlaneVec_mem 0 1 (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E))
    · exact h01 (d5PlaneVec_mem 0 1
        (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2))
  · fin_cases a
    · exact h23 (d5PlaneVec_mem 2 3 1 1)
    · exact h23 (d5PlaneVec_mem 2 3 (d5Tau E) (d5Tau E))
    · exact h01 (d5PlaneVec_mem 0 1 (d5Tau E) (d5Tau E))
    · exact h01 (d5PlaneVec_mem 0 1 1 1)

private theorem d5n_coordAnchor_le_span_anchor :
    coordAnchor (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) ≤
      Submodule.span F (Set.range fun p : Fin 3 × Bool =>
        if p.2 then d5FrameVecE E (d5EmbA p.1) else d5FrameVecF E (d5EmbA p.1)) := by
  intro v hv
  obtain ⟨r, hr⟩ := (mem_coordAnchor (ψ := LinearEquiv.refl F
    ((F × F) × (Fin 4 → K)))).mp hv
  rw [← hr]
  simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply]
  have hr2 : ((r, 0) : (F × F) × (Fin 4 → K)) =
      r.1 • (((1, 0) : F × F), 0) + r.2 • (((0, 1) : F × F), 0) := by
    ext <;> simp
  rw [hr2]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
  · exact Submodule.subset_span ⟨(2, true), by rfl⟩
  · exact Submodule.subset_span ⟨(2, false), by rfl⟩

private theorem d5n_mem_anchor (a : Fin 3) (s : Bool) :
    (if s then d5FrameVecE E (d5EmbA a) else d5FrameVecF E (d5EmbA a)) ∈
      coordAnchor (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) ⊔
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
          coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1) := by
  have hW : coordAnchor (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) ≤
      coordAnchor (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) ⊔
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
          coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1) := le_sup_left
  have h01 : (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1) ≤
      coordAnchor (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) ⊔
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
          coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1) := le_sup_right
  cases s
  · fin_cases a
    · exact h01 (d5PlaneVec_mem 0 1 (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E))
    · exact h01 (d5PlaneVec_mem 0 1
        (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2))
    · exact hW ((mem_coordAnchor (ψ := LinearEquiv.refl F
        ((F × F) × (Fin 4 → K)))).mpr ⟨(0, 1), by rfl⟩)
  · fin_cases a
    · exact h01 (d5PlaneVec_mem 0 1 (d5Tau E) (d5Tau E))
    · exact h01 (d5PlaneVec_mem 0 1 1 1)
    · exact hW ((mem_coordAnchor (ψ := LinearEquiv.refl F
        ((F × F) × (Fin 4 → K)))).mpr ⟨(1, 0), by rfl⟩)

private theorem d5n_hypH2_le_span_cross :
    hypH2 E ≤ Submodule.span F (Set.range fun p : Fin 3 × Bool =>
      if p.2 then d5FrameVecE E (Fin.castLEEmb (by norm_num : 3 ≤ 5) p.1)
      else d5FrameVecF E (Fin.castLEEmb (by norm_num : 3 ≤ 5) p.1)) := by
  rw [hypH2]
  apply Submodule.span_mono
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact ⟨(2, true), by rfl⟩
  · exact ⟨(2, false), by rfl⟩

private theorem d5n_mem_crossPure (a : Fin 3) (s : Bool) :
    (if s then d5FrameVecE E (Fin.castLEEmb (by norm_num : 3 ≤ 5) a)
      else d5FrameVecF E (Fin.castLEEmb (by norm_num : 3 ≤ 5) a)) ∈
      hypH2 E ⊔
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 2 ⊔
          coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 3) := by
  have hH2 : hypH2 E ≤ hypH2 E ⊔
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 2 ⊔
          coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 3) := le_sup_left
  have h23 : (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 2 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 3) ≤
      hypH2 E ⊔
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 2 ⊔
          coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 3) := le_sup_right
  cases s
  · fin_cases a
    · exact h23 (d5PlaneVec_mem 2 3
        (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2))
    · exact h23 (d5PlaneVec_mem 2 3 (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E))
    · refine hH2 ?_
      change d5FrameVecF E 2 ∈ hypH2 E
      exact Submodule.subset_span (Or.inr rfl)
  · fin_cases a
    · exact h23 (d5PlaneVec_mem 2 3 1 1)
    · exact h23 (d5PlaneVec_mem 2 3 (d5Tau E) (d5Tau E))
    · refine hH2 ?_
      change d5FrameVecE E 2 ∈ hypH2 E
      exact Submodule.subset_span (Or.inl rfl)

private theorem map_d5Frame_plusInclRange_pure :
    (plusInclRange (K := F) (Fin.castLEEmb (by norm_num : 4 ≤ 5))).map
        (d5Frame E).toLinearEquiv.toLinearMap =
      (Finset.univ : Finset (Fin 4)).sup
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K)))) := by
  rw [map_d5Frame_plusInclRange]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨⟨a, s⟩, rfl⟩
    exact d5n_mem_univ_sup_pure E a s
  · have h01 := d5n_span_planeVecs_le_span (E := E)
        (σ := Fin.castLEEmb (by norm_num : 4 ≤ 5))
        (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
        (3, true) (by rfl)
        (3, false) (by rfl)
        (2, true) (by rfl)
        (2, false) (by rfl)
    have h23 := d5n_span_planeVecs_le_span (E := E)
        (σ := Fin.castLEEmb (by norm_num : 4 ≤ 5))
        (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
        (0, true) (by rfl)
        (0, false) (by rfl)
        (1, true) (by rfl)
        (1, false) (by rfl)
    refine Finset.sup_le (fun i _ => ?_)
    fin_cases i
    · exact le_sup_left.trans h01
    · exact le_sup_right.trans h01
    · exact le_sup_left.trans h23
    · exact le_sup_right.trans h23

private theorem map_d5Frame_plusInclRange_anchor :
    (plusInclRange (K := F) d5EmbA).map (d5Frame E).toLinearEquiv.toLinearMap =
      coordSupport (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) {0, 1} := by
  rw [map_d5Frame_plusInclRange, coordSupport]
  have hsup : ({0, 1} : Finset (Fin 4)).sup
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K)))) =
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1 := by
    rw [Finset.sup_insert, Finset.sup_singleton]
  rw [hsup]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨⟨a, s⟩, rfl⟩
    exact d5n_mem_anchor E a s
  · have hW := d5n_coordAnchor_le_span_anchor E
    have h01 := d5n_span_planeVecs_le_span (E := E) (σ := d5EmbA)
        (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
        (1, true) (by rfl)
        (1, false) (by rfl)
        (0, true) (by rfl)
        (0, false) (by rfl)
    exact sup_le hW h01

private theorem map_d5Frame_plusInclRange_crossPure :
    (plusInclRange (K := F) (Fin.castLEEmb (by norm_num : 3 ≤ 5))).map
        (d5Frame E).toLinearEquiv.toLinearMap = crossPure E := by
  rw [map_d5Frame_plusInclRange, crossPure]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨⟨a, s⟩, rfl⟩
    exact d5n_mem_crossPure E a s
  · have hH2 := d5n_hypH2_le_span_cross E
    have h23 := d5n_span_planeVecs_le_span (E := E)
        (σ := Fin.castLEEmb (by norm_num : 3 ≤ 5))
        (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
        (0, true) (by rfl)
        (0, false) (by rfl)
        (1, true) (by rfl)
        (1, false) (by rfl)
    exact sup_le hH2 h23

private theorem d5n_hypH1_le :
    hypH1 E ≤
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1 := by
  unfold hypH1
  refine Submodule.span_le.mpr ?_
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact d5PlaneVec_mem (F := F) (K := K) 0 1 1 1
  · exact d5PlaneVec_mem (F := F) (K := K) 0 1
      (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2)

private theorem d5n_hypH2_le :
    hypH2 E ≤
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1 := by
  unfold hypH2
  refine Submodule.span_le.mpr ?_
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact d5PlaneVec_mem (F := F) (K := K) 0 1 (d5Tau E) (d5Tau E)
  · exact d5PlaneVec_mem (F := F) (K := K) 0 1 (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)

omit [Finite K] [CharP K 2] in
private theorem d5n_sup01_le_coordActive :
    coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1 ≤
      coordActive (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) := by
  refine sup_le ?_ ?_
  · exact le_iSup (fun i : Fin 4 =>
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) i) 0
  · exact le_iSup (fun i : Fin 4 =>
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) i) 1

omit [Finite K] [CharP K 2] in
private theorem d5n_sup23_le_coordActive :
    coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 2 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 3 ≤
      coordActive (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) := by
  refine sup_le ?_ ?_
  · exact le_iSup (fun i : Fin 4 =>
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) i) 2
  · exact le_iSup (fun i : Fin 4 =>
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) i) 3

private theorem d5n_hypH1_le_coordActive :
    hypH1 E ≤ coordActive (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) :=
  (d5n_hypH1_le E).trans d5n_sup01_le_coordActive

private theorem d5n_hypH2_le_coordActive :
    hypH2 E ≤ coordActive (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) :=
  (d5n_hypH2_le E).trans d5n_sup01_le_coordActive

private theorem d5n_orth_U01_U23 :
    CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep (normHypForm E 4)
      (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1)
      (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 2 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 3) := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
  have hψ := normHypForm_apply_coord E 4
  rw [polar_add_left, polar_add_right, polar_add_right]
  rw [polar_coordPlane_plane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) hψ
        (show (0 : Fin 4) ≠ 2 by decide) ha hc,
      polar_coordPlane_plane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) hψ
        (show (0 : Fin 4) ≠ 3 by decide) ha hd,
      polar_coordPlane_plane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) hψ
        (show (1 : Fin 4) ≠ 2 by decide) hb hc,
      polar_coordPlane_plane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) hψ
        (show (1 : Fin 4) ≠ 3 by decide) hb hd]
  ring

private theorem d5n_hypH1_orth :
    CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep (normHypForm E 4) (hypH1 E)
      (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 2 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 3) :=
  fun h hh u hu => d5n_orth_U01_U23 E h (d5n_hypH1_le E hh) u hu

private theorem d5n_hypH2_orth :
    CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep (normHypForm E 4) (hypH2 E)
      (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 2 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 3) :=
  fun h hh u hu => d5n_orth_U01_U23 E h (d5n_hypH2_le E hh) u hu

private theorem d5n_polar_zeroAnchor (w w' : Fin 4 → K) :
    polar (normHypForm E 4) ((0 : F × F), w) ((0 : F × F), w') =
      polar (Qn E 4) w w' := by
  change polar (CFSG.Timmesfeld.ClassicalOrders.hypSum (Qn E 4))
    ((0 : F × F), w) ((0 : F × F), w') = polar (Qn E 4) w w'
  rw [CFSG.Timmesfeld.ClassicalOrders.polar_hypSum]
  simp

private theorem d5n_algebraMap_polar_plane (a b c d : K) :
    algebraMap F K (polar (normHypForm E 4)
        ((0 : F × F), d5PlaneVec 0 1 a b)
        ((0 : F × F), d5PlaneVec 0 1 c d)) =
      (a * unitaryInvolution K 2 f c + b * unitaryInvolution K 2 f d) +
        unitaryInvolution K 2 f (a * unitaryInvolution K 2 f c +
          b * unitaryInvolution K 2 f d) := by
  rw [d5n_polar_zeroAnchor]
  rw [algebraMap_polar_Qn]
  have hsum : (∑ i : Fin 4, d5PlaneVec 0 1 a b i *
      unitaryInvolution K 2 f (d5PlaneVec 0 1 c d i)) =
      a * unitaryInvolution K 2 f c + b * unitaryInvolution K 2 f d := by
    rw [Fin.sum_univ_four]
    simp [d5PlaneVec]
  simp only [hsum]

private theorem d5n_polar_plane_eq_zero {a b c d : K}
    (h : a * unitaryInvolution K 2 f c + b * unitaryInvolution K 2 f d +
      unitaryInvolution K 2 f (a * unitaryInvolution K 2 f c +
        b * unitaryInvolution K 2 f d) = 0) :
    polar (normHypForm E 4) ((0 : F × F), d5PlaneVec 0 1 a b)
      ((0 : F × F), d5PlaneVec 0 1 c d) = 0 := by
  apply (algebraMap F K).injective
  rw [d5n_algebraMap_polar_plane, h, map_zero]

private theorem d5n_polar_e1_e2 :
    polar (normHypForm E 4) (hypPairH1 E).e (hypPairH2 E).e = 0 := by
  change polar (normHypForm E 4) ((0 : F × F), d5PlaneVec 0 1 1 1)
    ((0 : F × F), d5PlaneVec 0 1 (d5Tau E) (d5Tau E)) = 0
  refine d5n_polar_plane_eq_zero E ?_
  have h : (1 : K) * unitaryInvolution K 2 f (d5Tau E) +
      1 * unitaryInvolution K 2 f (d5Tau E) = 0 := by
    simp [CharTwo.add_self_eq_zero]
  simp only [h, map_zero, zero_add]

private theorem d5n_polar_e1_f2 :
    polar (normHypForm E 4) (hypPairH1 E).e (hypPairH2 E).f = 0 := by
  change polar (normHypForm E 4) ((0 : F × F), d5PlaneVec 0 1 1 1)
    ((0 : F × F), d5PlaneVec 0 1 (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) = 0
  refine d5n_polar_plane_eq_zero E ?_
  have h : (1 : K) * unitaryInvolution K 2 f (unitaryInvolution K 2 f (d5Tau E)) +
      1 * unitaryInvolution K 2 f (d5Tau E) = 1 := by
    simp only [one_mul, E.isUnitary.invol, d5Tau_add_sigma E]
  have h1 : unitaryInvolution K 2 f (1 : K) = 1 := by
    simp
  simp only [h, h1, CharTwo.add_self_eq_zero]

private theorem d5n_polar_f1_e2 :
    polar (normHypForm E 4) (hypPairH1 E).f (hypPairH2 E).e = 0 := by
  change polar (normHypForm E 4)
    ((0 : F × F), d5PlaneVec 0 1
      (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2))
    ((0 : F × F), d5PlaneVec 0 1 (d5Tau E) (d5Tau E)) = 0
  refine d5n_polar_plane_eq_zero E ?_
  have hbase : (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) *
        unitaryInvolution K 2 f (d5Tau E) +
        (d5Tau E) ^ 2 * unitaryInvolution K 2 f (d5Tau E) =
      d5Tau E * unitaryInvolution K 2 f (d5Tau E) := by
    have h1 : d5Tau E * unitaryInvolution K 2 f (d5Tau E) + (d5Tau E) ^ 2 =
        d5Tau E := by
      linear_combination (d5Tau E) * d5Tau_add_sigma E
    rw [← add_mul, h1]
  have hfix : unitaryInvolution K 2 f (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) =
      d5Tau E * unitaryInvolution K 2 f (d5Tau E) := by
    rw [map_mul, E.isUnitary.invol]
    ring
  simp only [hbase, hfix, CharTwo.add_self_eq_zero]

private theorem d5n_polar_f1_f2 :
    polar (normHypForm E 4) (hypPairH1 E).f (hypPairH2 E).f = 0 := by
  change polar (normHypForm E 4)
    ((0 : F × F), d5PlaneVec 0 1
      (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) (d5Tau E ^ 2))
    ((0 : F × F), d5PlaneVec 0 1 (unitaryInvolution K 2 f (d5Tau E)) (d5Tau E)) = 0
  refine d5n_polar_plane_eq_zero E ?_
  have hbase : (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) *
        unitaryInvolution K 2 f (unitaryInvolution K 2 f (d5Tau E)) +
        (d5Tau E) ^ 2 * unitaryInvolution K 2 f (d5Tau E) = 0 := by
    rw [E.isUnitary.invol]
    have h : (d5Tau E * unitaryInvolution K 2 f (d5Tau E)) * d5Tau E =
        (d5Tau E) ^ 2 * unitaryInvolution K 2 f (d5Tau E) := by ring
    rw [h, CharTwo.add_self_eq_zero]
  simp only [hbase, map_zero, zero_add]

private theorem nondegenerate_pureSupport (S : Finset (Fin 4)) :
    (polarBilin ((normHypForm E 4).comp
      (S.sup (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))))).subtype)).Nondegenerate := by
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  let ψ := LinearEquiv.refl F ((F × F) × (Fin 4 → K))
  have hψ := normHypForm_apply_coord E 4
  have hUpoly : ∀ i, PolarNondegOn (normHypForm E 4) (coordPlane ψ i) :=
    fun i => coordPlane_polarNondegOn ψ hψ (normQuad_polarBilin_nondegenerate E) i
  have hUorth : ∀ i j, i ≠ j → ∀ x ∈ coordPlane ψ i, ∀ y ∈ coordPlane ψ j,
      polar (normHypForm E 4) x y = 0 :=
    fun i j hij x hx y hy => polar_coordPlane_plane ψ hψ hij hx hy
  exact nondegenerate_finset_sup (coordPlane ψ) hUpoly hUorth S

theorem nondegenerate_crossAnchor :
    (polarBilin ((normHypForm E 4).comp (crossAnchor E).subtype)).Nondegenerate := by
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  let ψ := LinearEquiv.refl F ((F × F) × (Fin 4 → K))
  have hψ := normHypForm_apply_coord E 4
  have hQ := normHypForm_polarBilin_nondegenerate E 4
  have hQE := normQuad_polarBilin_nondegenerate E
  have hW : PolarNondegOn (normHypForm E 4) (coordAnchor ψ) :=
    polarNondegOn_of_nondegenerate (coordAnchor_nondegenerate ψ hψ hQ hQE)
  have hH1 : PolarNondegOn (normHypForm E 4) (hypH1 E) := by
    change PolarNondegOn (normHypForm E 4)
      (Submodule.span F {(hypPairH1 E).e, (hypPairH1 E).f})
    exact polarNondegOn_span_pair_of_polar_eq_one (hypPairH1 E).polar_ef
  have hsep : CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep (normHypForm E 4)
      (coordAnchor ψ) (hypH1 E) :=
    fun w hw h hh => polar_coordAnchor_active ψ hψ hw (d5n_hypH1_le_coordActive E hh)
  have hmain : PolarNondegOn (normHypForm E 4) (coordAnchor ψ ⊔ hypH1 E) :=
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hW hH1 hsep
  exact CFSG.LieType.SeitzGeneration.OrthBlk.nondegenerate_of_polarNondegOn hmain

theorem nondegenerate_crossPure :
    (polarBilin ((normHypForm E 4).comp (crossPure E).subtype)).Nondegenerate := by
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  let ψ := LinearEquiv.refl F ((F × F) × (Fin 4 → K))
  have hψ := normHypForm_apply_coord E 4
  have hQE := normQuad_polarBilin_nondegenerate E
  have hH2 : PolarNondegOn (normHypForm E 4) (hypH2 E) := by
    change PolarNondegOn (normHypForm E 4)
      (Submodule.span F {(hypPairH2 E).e, (hypPairH2 E).f})
    exact polarNondegOn_span_pair_of_polar_eq_one (hypPairH2 E).polar_ef
  have hU23 : PolarNondegOn (normHypForm E 4) (coordPlane ψ 2 ⊔ coordPlane ψ 3) :=
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup
      (coordPlane_polarNondegOn ψ hψ hQE 2)
      (coordPlane_polarNondegOn ψ hψ hQE 3)
      (fun x hx y hy => polar_coordPlane_plane ψ hψ (by decide : (2 : Fin 4) ≠ 3) hx hy)
  have hmain : PolarNondegOn (normHypForm E 4)
      (hypH2 E ⊔ (coordPlane ψ 2 ⊔ coordPlane ψ 3)) :=
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hH2 hU23 (d5n_hypH2_orth E)
  exact CFSG.LieType.SeitzGeneration.OrthBlk.nondegenerate_of_polarNondegOn hmain

theorem polar_crossAnchor_crossPure {x y : (F × F) × (Fin 4 → K)} (hx : x ∈ crossAnchor E)
    (hy : y ∈ crossPure E) : polar (normHypForm E 4) x y = 0 := by
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  let ψ := LinearEquiv.refl F ((F × F) × (Fin 4 → K))
  have hψ := normHypForm_apply_coord E 4
  change x ∈ coordAnchor ψ ⊔ hypH1 E at hx
  change y ∈ hypH2 E ⊔ (coordPlane ψ 2 ⊔ coordPlane ψ 3) at hy
  obtain ⟨w, hw, h1, hh1, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨h2, hh2, u, hu, rfl⟩ := Submodule.mem_sup.mp hy
  have hwh2 : polar (normHypForm E 4) w h2 = 0 :=
    polar_coordAnchor_active ψ hψ hw (d5n_hypH2_le_coordActive E hh2)
  have hwu : polar (normHypForm E 4) w u = 0 :=
    polar_coordAnchor_active ψ hψ hw (d5n_sup23_le_coordActive (F := F) (K := K) hu)
  have hh1h2 : polar (normHypForm E 4) h1 h2 = 0 := by
    obtain ⟨a1, b1, rfl⟩ := Submodule.mem_span_pair.mp hh1
    obtain ⟨a2, b2, rfl⟩ := Submodule.mem_span_pair.mp hh2
    simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
      d5n_polar_e1_e2 E, d5n_polar_e1_f2 E, d5n_polar_f1_e2 E, d5n_polar_f1_f2 E]
    ring
  have hh1u : polar (normHypForm E 4) h1 u = 0 := d5n_hypH1_orth E h1 hh1 u hu
  rw [polar_add_left, polar_add_right, polar_add_right, hwh2, hwu, hh1h2, hh1u]
  ring

private theorem map_range_plusIncl_d5Equiv {m : ℕ} (hm : 3 ≤ m) (σ : Fin m ↪ Fin 5) :
    (plusIncl (K := F) σ).spinGroupMap.range.map (d5Equiv E).toMonoidHom =
      (supportedDerived (normHypForm E 4)
        ((plusInclRange (K := F) σ).map (d5Frame E).toLinearEquiv.toLinearMap)).subgroupOf
        (normOmega E 4) := by
  have hF : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  exact @map_range_spinGroupMap_plusIncl _ _ _ _ _ _ _ _ hF (d5Frame E).symm (by norm_num)
    (two_eq_zero_of_quadExt E) hm σ

private theorem exists_ne_zero_ne_one_of_four_le (hq : 4 ≤ Nat.card F) :
    ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (fun b : Bool => if b then (1 : F) else 0) := by
    intro c
    by_cases hc : c = 0
    · exact ⟨false, by simp [hc]⟩
    · have hc1 : c = 1 := h c hc
      exact ⟨true, by simp [hc1]⟩
  have hle : Nat.card F ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
  have h2 : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  omega

private theorem map_longRoot_le_d5 (hK : ∃ c : F, c ≠ 0 ∧ c ≠ 1)
    {P : Submodule F ((F × F) × (Fin 4 → K))}
    (hP : (polarBilin ((normHypForm E 4).comp P.subtype)).Nondegenerate) {i j : Fin 5}
    (hij : i ≠ j) (s t : Bool) (hi : d5Frame E (plusVec 5 F i s) ∈ P)
    (hj : d5Frame E (plusVec 5 F j t) ∈ P) :
    ((plusFrame 5 F (by norm_num)).longRoot hij s t).range.map (d5Equiv E).toMonoidHom ≤
      (supportedDerived (normHypForm E 4) P).subgroupOf (normOmega E 4) := by
  exact map_longRoot_range_le_supportedDerived hK (d5Frame E).symm (by norm_num)
    (two_eq_zero_of_quadExt E) hP hij s t hi hj

private theorem map_spinTenRankOne_le_of_mem (hK : ∃ c : F, c ≠ 0 ∧ c ≠ 1)
    {P : Submodule F ((F × F) × (Fin 4 → K))}
    (hP : (polarBilin ((normHypForm E 4).comp P.subtype)).Nondegenerate) (k : Fin 5)
    (h : ∀ s, d5Frame E (plusVec 5 F (rootIdxD 5 k) s) ∈ P)
    (h' : ∀ t, d5Frame E (plusVec 5 F (rootIdxD' 5 k) t) ∈ P) :
    (spinTenRankOne F k).map (d5Equiv E).toMonoidHom ≤
      (supportedDerived (normHypForm E 4) P).subgroupOf (normOmega E 4) := by
  have hn : 3 ≤ 5 := by norm_num
  have hij : rootIdxD 5 k ≠ rootIdxD' 5 k := rootIdxD_ne 5 (by norm_num) k
  change (plusRootGroup 5 F hn (Pi.single k 1) ⊔ plusRootGroup 5 F hn (-Pi.single k 1)).map
      (d5Equiv E).toMonoidHom ≤ (supportedDerived (normHypForm E 4) P).subgroupOf (normOmega E 4)
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · have h1 : toStdD 5 (Pi.single k 1) =
        Pi.single (rootIdxD 5 k) (boolSign true) +
          Pi.single (rootIdxD' 5 k) (boolSign (rootSignD 5 k)) :=
      toStdD_single_eq (by norm_num) k
    rw [plusRootGroup_eq hn hij true (rootSignD 5 k) h1]
    exact map_longRoot_le_d5 E hK hP hij true (rootSignD 5 k)
      (h true) (h' (rootSignD 5 k))
  · have h2 : toStdD 5 (-Pi.single k 1) =
        Pi.single (rootIdxD' 5 k) (boolSign (!rootSignD 5 k)) +
          Pi.single (rootIdxD 5 k) (boolSign false) := by
      rw [toStdD_neg, toStdD_single_eq (by norm_num) k, boolSign_not, boolSign_false,
        boolSign_true, neg_add, ← Pi.single_neg, ← Pi.single_neg, add_comm]
    rw [plusRootGroup_eq hn hij.symm (!rootSignD 5 k) false h2]
    exact map_longRoot_le_d5 E hK hP hij.symm (!rootSignD 5 k) false
      (h' (!rootSignD 5 k)) (h false)

private theorem d5n_longRoot_range_congr {n : ℕ} (hn : 3 ≤ n) {i j i' j' : Fin n}
    {s t s' t' : Bool} (hi : i = i') (hj : j = j') (hs : s = s') (ht : t = t')
    (hij : i ≠ j) (hij' : i' ≠ j') :
    ((plusFrame n F hn).longRoot hij s t).range =
      ((plusFrame n F hn).longRoot hij' s' t').range := by
  subst hi; subst hj; subst hs; subst ht
  exact congrArg (fun h => ((plusFrame n F hn).longRoot h s t).range)
    (Subsingleton.elim hij hij')

private theorem d5n_map_rankOne_eq {m : ℕ} (hm : 3 ≤ m) (σ : Fin m ↪ Fin 5) (a : Fin m) :
    (rankOne (plusDatum m F hm).rootGroup a).map (plusIncl (K := F) σ).spinGroupMap =
      ((plusFrame 5 F (by norm_num)).longRoot
          (σ.injective.ne (rootIdxD_ne m (by omega) a)) true (rootSignD m a)).range ⊔
        ((plusFrame 5 F (by norm_num)).longRoot
          (σ.injective.ne (rootIdxD_ne m (by omega) a)).symm (!rootSignD m a) false).range := by
  rw [(show rankOne (plusDatum m F hm).rootGroup a =
        plusRootGroup m F hm (Pi.single a 1) ⊔ plusRootGroup m F hm (-Pi.single a 1)
      from rfl), Subgroup.map_sup]
  rw [plusRootGroup_single hm a, plusRootGroup_neg_single hm a, MonoidHom.map_range,
    MonoidHom.map_range]
  unfold rootD negRootD
  rw [spinGroupMap_plusIncl_comp_longRoot hm (by norm_num : 3 ≤ 5) σ _ true _,
    spinGroupMap_plusIncl_comp_longRoot hm (by norm_num : 3 ≤ 5) σ _ (!rootSignD m a) _]

private theorem map_rankOne_plusIncl_eq {m : ℕ} (hm : 3 ≤ m) (σ : Fin m ↪ Fin 5) (a : Fin m)
    (b : Fin 5) (h1 : rootIdxD 5 b = σ (rootIdxD m a)) (h2 : rootIdxD' 5 b = σ (rootIdxD' m a))
    (h3 : rootSignD 5 b = rootSignD m a) :
    (rankOne (plusDatum m F hm).rootGroup a).map (plusIncl (K := F) σ).spinGroupMap =
      spinTenRankOne F b := by
  rw [d5n_map_rankOne_eq hm σ a]
  rw [(show spinTenRankOne F b = plusRootGroup 5 F (by norm_num) (Pi.single b 1) ⊔
      plusRootGroup 5 F (by norm_num) (-Pi.single b 1) from rfl)]
  rw [plusRootGroup_single (by norm_num : 3 ≤ 5) b,
    plusRootGroup_neg_single (by norm_num : 3 ≤ 5) b]
  unfold rootD negRootD
  rw [d5n_longRoot_range_congr (by norm_num : 3 ≤ 5) h1.symm h2.symm rfl h3.symm
      (σ.injective.ne (rootIdxD_ne m (by omega) a)) (rootIdxD_ne 5 (by omega) b),
    d5n_longRoot_range_congr (by norm_num : 3 ≤ 5) h2.symm h1.symm
      (congrArg Bool.not h3.symm) rfl ((σ.injective.ne (rootIdxD_ne m (by omega) a)).symm)
      ((rootIdxD_ne 5 (by omega) b).symm)]

private theorem map_rankOne_three_plusIncl_pure :
    (rankOne (plusDatum 4 F (by norm_num)).rootGroup (3 : Fin 4)).map
        (plusIncl (K := F) (Fin.castLEEmb (by norm_num : 4 ≤ 5))).spinGroupMap =
      ((plusFrame 5 F (by norm_num)).longRoot (show (2 : Fin 5) ≠ 3 by decide) true true).range ⊔
        ((plusFrame 5 F (by norm_num)).longRoot (show (3 : Fin 5) ≠ 2 by decide) false
          false).range := by
  rw [d5n_map_rankOne_eq (m := 4) (by norm_num : 3 ≤ 4)
    (Fin.castLEEmb (by norm_num : 4 ≤ 5)) (3 : Fin 4)]
  rw [d5n_longRoot_range_congr (by norm_num : 3 ≤ 5)
    (show Fin.castLEEmb (by norm_num : 4 ≤ 5) (rootIdxD 4 3) = (2 : Fin 5) by
      rw [Fin.castLEEmb_apply]; exact Fin.ext rfl)
    (show Fin.castLEEmb (by norm_num : 4 ≤ 5) (rootIdxD' 4 3) = (3 : Fin 5) by
      rw [Fin.castLEEmb_apply]; exact Fin.ext rfl)
    rfl (show rootSignD 4 3 = true by decide)
    ((Fin.castLEEmb (by norm_num : 4 ≤ 5)).injective.ne (rootIdxD_ne 4 (by omega) (3 : Fin 4)))
    (show (2 : Fin 5) ≠ 3 by decide),
    d5n_longRoot_range_congr (by norm_num : 3 ≤ 5)
    (show Fin.castLEEmb (by norm_num : 4 ≤ 5) (rootIdxD' 4 3) = (3 : Fin 5) by
      rw [Fin.castLEEmb_apply]; exact Fin.ext rfl)
    (show Fin.castLEEmb (by norm_num : 4 ≤ 5) (rootIdxD 4 3) = (2 : Fin 5) by
      rw [Fin.castLEEmb_apply]; exact Fin.ext rfl)
    (show (!rootSignD 4 3) = false by decide) rfl
    (((Fin.castLEEmb (by norm_num : 4 ≤ 5)).injective.ne
      (rootIdxD_ne 4 (by omega) (3 : Fin 4))).symm)
    (show (3 : Fin 5) ≠ 2 by decide)]

omit [Finite K] [CharP K 2] in
private theorem d5n_pure01 :
    ({0, 1} : Finset (Fin 4)).sup
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K)))) =
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1 := by
  simp [Finset.sup_insert, Finset.sup_singleton]

private theorem d5n_frame_mem_pure01 (i : Fin 5) (s : Bool) (hi : i = 2 ∨ i = 3) :
    d5Frame E (plusVec 5 F i s) ∈
      ({0, 1} : Finset (Fin 4)).sup
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K)))) := by
  rcases hi with rfl | rfl
  · rw [d5Frame_plusVec]
    cases s <;> rw [d5n_pure01] <;> exact d5PlaneVec_mem 0 1 _ _
  · rw [d5Frame_plusVec]
    cases s <;> rw [d5n_pure01] <;> exact d5PlaneVec_mem 0 1 _ _

private theorem d5n_frame_mem_crossAnchor (i : Fin 5) (s : Bool) (hi : i = 3 ∨ i = 4) :
    d5Frame E (plusVec 5 F i s) ∈ crossAnchor E := by
  rcases hi with rfl | rfl
  · rw [d5Frame_plusVec]
    cases s
    · rw [if_neg (by decide)]
      exact Submodule.mem_sup_right (show d5FrameVecF E 3 ∈ hypH1 E from
        Submodule.subset_span (by simp [hypPairH1]))
    · rw [if_pos (by decide)]
      exact Submodule.mem_sup_right (show d5FrameVecE E 3 ∈ hypH1 E from
        Submodule.subset_span (by simp [hypPairH1]))
  · rw [d5Frame_plusVec]
    cases s
    · rw [if_neg (by decide)]
      exact Submodule.mem_sup_left (mem_coordAnchor.mpr ⟨(0, 1), rfl⟩)
    · rw [if_pos (by decide)]
      exact Submodule.mem_sup_left (mem_coordAnchor.mpr ⟨(1, 0), rfl⟩)

private theorem d5n_mem_range_d5EmbA {k : Fin 5} (hk : 2 ≤ k.val) :
    rootIdxD 5 k ∈ Set.range d5EmbA ∧ rootIdxD' 5 k ∈ Set.range d5EmbA := by
  fin_cases k
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact ⟨⟨(0 : Fin 3), by decide⟩, ⟨(1 : Fin 3), by decide⟩⟩
  · exact ⟨⟨(1 : Fin 3), by decide⟩, ⟨(2 : Fin 3), by decide⟩⟩
  · exact ⟨⟨(1 : Fin 3), by decide⟩, ⟨(2 : Fin 3), by decide⟩⟩

private theorem d5n_rootIdxD_embA (a : Fin 3) :
    rootIdxD 5 (d5EmbA a) = d5EmbA (rootIdxD 3 a) := by
  fin_cases a <;> rfl

private theorem d5n_rootIdxD'_embA (a : Fin 3) :
    rootIdxD' 5 (d5EmbA a) = d5EmbA (rootIdxD' 3 a) := by
  fin_cases a <;> rfl

private theorem d5n_rootSignD_embA (a : Fin 3) :
    rootSignD 5 (d5EmbA a) = rootSignD 3 a := by
  fin_cases a <;> rfl

private theorem d5n_rootIdxD_castLE_of_ne (a : Fin 4) (ha : a ≠ 3) :
    rootIdxD 5 (Fin.castLEEmb (by norm_num : 4 ≤ 5) a) =
      Fin.castLEEmb (by norm_num : 4 ≤ 5) (rootIdxD 4 a) := by
  fin_cases a
  · rfl
  · rfl
  · rfl
  · exact absurd rfl ha

private theorem d5n_rootIdxD'_castLE_of_ne (a : Fin 4) (ha : a ≠ 3) :
    rootIdxD' 5 (Fin.castLEEmb (by norm_num : 4 ≤ 5) a) =
      Fin.castLEEmb (by norm_num : 4 ≤ 5) (rootIdxD' 4 a) := by
  fin_cases a
  · rfl
  · rfl
  · rfl
  · exact absurd rfl ha

private theorem d5n_rootSignD_castLE_of_ne (a : Fin 4) (ha : a ≠ 3) :
    rootSignD 5 (Fin.castLEEmb (by norm_num : 4 ≤ 5) a) = rootSignD 4 a := by
  fin_cases a
  · rfl
  · rfl
  · rfl
  · exact absurd rfl ha

theorem map_spinTenRankOne_le_normPureBlock {k : Fin 5} (hk : k.val ≤ 2) :
    (spinTenRankOne F k).map (d5Equiv E).toMonoidHom ≤ normPureBlock E 4 Finset.univ := by
  have hkD : rootIdxD 5 k ∈ Set.range (Fin.castLEEmb (by norm_num : 4 ≤ 5)) := by
    rw [rootIdxD_of_lt (n := 5) (by omega : k.val + 1 < 5)]
    exact ⟨(⟨k.val, by omega⟩ : Fin 4), rfl⟩
  have hkD' : rootIdxD' 5 k ∈ Set.range (Fin.castLEEmb (by norm_num : 4 ≤ 5)) := by
    rw [rootIdxD'_of_lt (n := 5) (by omega : k.val + 1 < 5)]
    exact ⟨(⟨k.val + 1, by omega⟩ : Fin 4), rfl⟩
  have hmap : ((plusIncl (K := F) (Fin.castLEEmb (by norm_num : 4 ≤ 5))).spinGroupMap.range).map
      (d5Equiv E).toMonoidHom = normPureBlock E 4 Finset.univ := by
    have h := map_range_plusIncl_d5Equiv (E := E) (m := 4) (by norm_num : 3 ≤ 4)
      (Fin.castLEEmb (by norm_num : 4 ≤ 5))
    rw [map_d5Frame_plusInclRange_pure E] at h
    exact h
  rw [← hmap]
  exact Subgroup.map_mono (rankOne_le_range_spinGroupMap_plusIncl (K := F)
    (by norm_num : 3 ≤ 4) (by norm_num : 3 ≤ 5)
    (Fin.castLEEmb (by norm_num : 4 ≤ 5)) k hkD hkD')

theorem map_spinTenRankOne_le_normBlock {k : Fin 5} (hk : 2 ≤ k.val) :
    (spinTenRankOne F k).map (d5Equiv E).toMonoidHom ≤ normBlock E 4 {0, 1} := by
  obtain ⟨hkD, hkD'⟩ := d5n_mem_range_d5EmbA hk
  have hmap : ((plusIncl (K := F) d5EmbA).spinGroupMap.range).map (d5Equiv E).toMonoidHom =
      normBlock E 4 {0, 1} := by
    have h := map_range_plusIncl_d5Equiv (E := E) (m := 3) (by norm_num : 3 ≤ 3) d5EmbA
    rw [map_d5Frame_plusInclRange_anchor E] at h
    exact h
  rw [← hmap]
  exact Subgroup.map_mono (rankOne_le_range_spinGroupMap_plusIncl (K := F)
    (by norm_num : 3 ≤ 3) (by norm_num : 3 ≤ 5) d5EmbA k hkD hkD')

theorem map_spinTenRankOne_two_le (hq : 4 ≤ Nat.card F) :
    (spinTenRankOne F 2).map (d5Equiv E).toMonoidHom ≤ normPureBlock E 4 {0, 1} := by
  refine map_spinTenRankOne_le_of_mem (E := E) (exists_ne_zero_ne_one_of_four_le hq)
    (nondegenerate_pureSupport E {0, 1}) 2 ?_ ?_
  · intro s
    rw [rootIdxD_of_lt (n := 5) (by norm_num : (2 : Fin 5).val + 1 < 5), d5Frame_plusVec]
    cases s <;> rw [d5n_pure01] <;> exact d5PlaneVec_mem 0 1 _ _
  · intro t
    rw [rootIdxD'_of_lt (n := 5) (by norm_num : (2 : Fin 5).val + 1 < 5), d5Frame_plusVec]
    cases t <;> rw [d5n_pure01] <;> exact d5PlaneVec_mem 0 1 _ _

theorem normBlock_zero_one_le_iSup :
    normBlock E 4 {0, 1} ≤
      ⨆ (k : Fin 5) (_ : 2 ≤ k.val), (spinTenRankOne F k).map (d5Equiv E).toMonoidHom := by
  have hmap : ((plusIncl (K := F) d5EmbA).spinGroupMap.range).map (d5Equiv E).toMonoidHom =
      normBlock E 4 {0, 1} := by
    have h := map_range_plusIncl_d5Equiv (E := E) (m := 3) (by norm_num : 3 ≤ 3) d5EmbA
    rw [map_d5Frame_plusInclRange_anchor E] at h
    exact h
  rw [← hmap, range_spinGroupMap_plusIncl (K := F) (by norm_num : 3 ≤ 3) d5EmbA,
    Subgroup.map_iSup]
  refine iSup_le fun (a : Fin 3) => ?_
  rw [map_rankOne_plusIncl_eq (F := F) (m := 3) (by norm_num : 3 ≤ 3) d5EmbA a (d5EmbA a)
    (d5n_rootIdxD_embA a) (d5n_rootIdxD'_embA a) (d5n_rootSignD_embA a)]
  exact le_iSup₂_of_le (d5EmbA a)
    (by rw [show (d5EmbA a).val = a.val + 2 from rfl]; exact Nat.le_add_left 2 a.val) le_rfl

theorem normPureBlock_univ_le_iSup (hq : 4 ≤ Nat.card F) :
    normPureBlock E 4 Finset.univ ≤
      (⨆ (k : Fin 5) (_ : k.val ≤ 2), (spinTenRankOne F k).map (d5Equiv E).toMonoidHom) ⊔
        normPureBlock E 4 {0, 1} := by
  have hmap : ((plusIncl (K := F) (Fin.castLEEmb (by norm_num : 4 ≤ 5))).spinGroupMap.range).map
      (d5Equiv E).toMonoidHom = normPureBlock E 4 Finset.univ := by
    have h := map_range_plusIncl_d5Equiv (E := E) (m := 4) (by norm_num : 3 ≤ 4)
      (Fin.castLEEmb (by norm_num : 4 ≤ 5))
    rw [map_d5Frame_plusInclRange_pure E] at h
    exact h
  rw [← hmap, range_spinGroupMap_plusIncl (K := F) (by norm_num : 3 ≤ 4)
      (Fin.castLEEmb (by norm_num : 4 ≤ 5)), Subgroup.map_iSup]
  refine iSup_le fun (a : Fin 4) => ?_
  by_cases ha3 : a = 3
  · rw [ha3, map_rankOne_three_plusIncl_pure (F := F), Subgroup.map_sup]
    refine le_trans (sup_le ?_ ?_) le_sup_right
    · exact map_longRoot_le_d5 (E := E) (exists_ne_zero_ne_one_of_four_le hq)
        (nondegenerate_pureSupport E {0, 1}) (show (2 : Fin 5) ≠ 3 by decide) true true
        (d5n_frame_mem_pure01 E 2 true (Or.inl rfl))
        (d5n_frame_mem_pure01 E 3 true (Or.inr rfl))
    · exact map_longRoot_le_d5 (E := E) (exists_ne_zero_ne_one_of_four_le hq)
        (nondegenerate_pureSupport E {0, 1}) (show (3 : Fin 5) ≠ 2 by decide) false false
        (d5n_frame_mem_pure01 E 3 false (Or.inr rfl))
        (d5n_frame_mem_pure01 E 2 false (Or.inl rfl))
  · have ha : a.val ≤ 2 := by
      have hne : a.val ≠ 3 := fun h => ha3 (Fin.ext h)
      have := a.isLt
      omega
    rw [map_rankOne_plusIncl_eq (F := F) (m := 4) (by norm_num : 3 ≤ 4)
      (Fin.castLEEmb (by norm_num : 4 ≤ 5)) a (Fin.castLEEmb (by norm_num : 4 ≤ 5) a)
      (d5n_rootIdxD_castLE_of_ne a ha3) (d5n_rootIdxD'_castLE_of_ne a ha3)
      (d5n_rootSignD_castLE_of_ne a ha3)]
    exact le_trans (le_iSup₂_of_le (Fin.castLEEmb (by norm_num : 4 ≤ 5) a)
      (by rw [show (Fin.castLEEmb (by norm_num : 4 ≤ 5) a).val = a.val from rfl]; exact ha)
      le_rfl) le_sup_left

theorem map_spinTenRankOne_le_crossPure {k : Fin 5} (hk : k.val ≤ 1) :
    (spinTenRankOne F k).map (d5Equiv E).toMonoidHom ≤
      (supportedDerived (normHypForm E 4) (crossPure E)).subgroupOf (normOmega E 4) := by
  have hkD : rootIdxD 5 k ∈ Set.range (Fin.castLEEmb (by norm_num : 3 ≤ 5)) := by
    rw [rootIdxD_of_lt (n := 5) (by omega : k.val + 1 < 5)]
    exact ⟨(⟨k.val, by omega⟩ : Fin 3), rfl⟩
  have hkD' : rootIdxD' 5 k ∈ Set.range (Fin.castLEEmb (by norm_num : 3 ≤ 5)) := by
    rw [rootIdxD'_of_lt (n := 5) (by omega : k.val + 1 < 5)]
    exact ⟨(⟨k.val + 1, by omega⟩ : Fin 3), rfl⟩
  have hmap : ((plusIncl (K := F) (Fin.castLEEmb (by norm_num : 3 ≤ 5))).spinGroupMap.range).map
      (d5Equiv E).toMonoidHom
      = (supportedDerived (normHypForm E 4) (crossPure E)).subgroupOf (normOmega E 4) := by
    have h := map_range_plusIncl_d5Equiv (E := E) (m := 3) (by norm_num : 3 ≤ 3)
      (Fin.castLEEmb (by norm_num : 3 ≤ 5))
    rw [map_d5Frame_plusInclRange_crossPure E] at h
    exact h
  rw [← hmap]
  exact Subgroup.map_mono (rankOne_le_range_spinGroupMap_plusIncl (K := F)
    (by norm_num : 3 ≤ 3) (by norm_num : 3 ≤ 5)
    (Fin.castLEEmb (by norm_num : 3 ≤ 5)) k hkD hkD')

theorem map_spinTenRankOne_le_crossAnchor {k : Fin 5} (hk : 3 ≤ k.val) (hq : 4 ≤ Nat.card F) :
    (spinTenRankOne F k).map (d5Equiv E).toMonoidHom ≤
      (supportedDerived (normHypForm E 4) (crossAnchor E)).subgroupOf (normOmega E 4) := by
  have hk34 : k = 3 ∨ k = 4 := by
    have hlt := k.isLt
    have h : k.val = 3 ∨ k.val = 4 := by omega
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hk34 with rfl | rfl
  · refine map_spinTenRankOne_le_of_mem (E := E) (exists_ne_zero_ne_one_of_four_le hq)
      (nondegenerate_crossAnchor E) 3 ?_ ?_
    · intro s
      rw [show rootIdxD 5 (3 : Fin 5) = 3 by decide]
      exact d5n_frame_mem_crossAnchor E 3 s (Or.inl rfl)
    · intro t
      rw [show rootIdxD' 5 (3 : Fin 5) = 4 by decide]
      exact d5n_frame_mem_crossAnchor E 4 t (Or.inr rfl)
  · refine map_spinTenRankOne_le_of_mem (E := E) (exists_ne_zero_ne_one_of_four_le hq)
      (nondegenerate_crossAnchor E) 4 ?_ ?_
    · intro s
      rw [show rootIdxD 5 (4 : Fin 5) = 3 by decide]
      exact d5n_frame_mem_crossAnchor E 3 s (Or.inl rfl)
    · intro t
      rw [show rootIdxD' 5 (4 : Fin 5) = 4 by decide]
      exact d5n_frame_mem_crossAnchor E 4 t (Or.inr rfl)

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
