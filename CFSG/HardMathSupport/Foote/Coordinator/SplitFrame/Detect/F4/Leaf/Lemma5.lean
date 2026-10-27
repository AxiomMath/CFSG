module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.CaseData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Lemma1Main

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.StandardType.RootCentExc
open Heis
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false

section Matrices

variable {K : Type} [Field K]

@[expose] def l5lo (a b z : K) : SL(3, K) :=
  ⟨!![1, 0, 0; a, 1, 0; z, b, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def l5up (t : K) : SL(3, K) :=
  ⟨!![1, 0, t; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_l5lo (a b z : K) :
    (l5lo a b z : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; a, 1, 0; z, b, 1] := rfl

theorem coe_l5up (t : K) :
    (l5up t : Matrix (Fin 3) (Fin 3) K) = !![1, 0, t; 0, 1, 0; 0, 0, 1] := rfl

theorem l5lo_mul (a b z a' b' z' : K) :
    l5lo a b z * l5lo a' b' z' = l5lo (a + a') (b + b') (z + z' + b * a') := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_l5lo]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem l5lo_zero : l5lo (0 : K) 0 0 = 1 := by
  ext i j
  simp only [coe_l5lo]
  fin_cases i <;> fin_cases j <;> simp

theorem l5lo_inv (a b z : K) : (l5lo a b z)⁻¹ = l5lo (-a) (-b) (a * b - z) := by
  apply inv_eq_of_mul_eq_one_right
  rw [l5lo_mul, ← l5lo_zero]
  congr 1 <;> ring

theorem l5up_mul (t t' : K) : l5up t * l5up t' = l5up (t + t') := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_l5up]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem l5up_zero : l5up (0 : K) = 1 := by
  ext i j
  simp only [coe_l5up]
  fin_cases i <;> fin_cases j <;> simp

theorem l5up_inv (t : K) : (l5up t)⁻¹ = l5up (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [l5up_mul, add_neg_cancel, l5up_zero]

@[expose] def l5Lo (K : Type) [Field K] : Subgroup SL(3, K) where
  carrier := {M | ∃ a b z : K, M = l5lo a b z}
  mul_mem' := by
    rintro _ _ ⟨a, b, z, rfl⟩ ⟨a', b', z', rfl⟩
    exact ⟨_, _, _, l5lo_mul a b z a' b' z'⟩
  one_mem' := ⟨0, 0, 0, l5lo_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, z, rfl⟩
    exact ⟨_, _, _, l5lo_inv a b z⟩

theorem l5_transvection_10 (t : K) :
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t = l5lo t 0 0 := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.transvection_coe, coe_l5lo]
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

theorem l5_transvection_21 (t : K) :
    Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t = l5lo 0 t 0 := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.transvection_coe, coe_l5lo]
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

theorem l5_transvection_20 (t : K) :
    Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t = l5lo 0 0 t := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.transvection_coe, coe_l5lo]
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

theorem l5_transvection_02 (t : K) :
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t = l5up t := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.transvection_coe, coe_l5up]
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

end Matrices


section MatrixLemmas

variable {K : Type} [Field K]

theorem l5_two {a b z : K} (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) = 0)
    (h : l5lo a b z * l5lo a b z = 1) : False := by
  rw [l5lo_mul, ← l5lo_zero] at h
  have e := congrArg (fun Y : SL(3, K) => (Y : Matrix (Fin 3) (Fin 3) K) 2 0) h
  simp only [coe_l5lo] at e
  simp at e
  have : b * a = 0 := by linear_combination e - z * h2
  rcases mul_eq_zero.1 this with h0 | h0
  · exact hb h0
  · exact ha h0

theorem l5_not_commute {a b z : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ⁅l5up (1 : K), l5lo a b z⁆ * l5up (1 : K) = l5up (1 : K) * ⁅l5up (1 : K), l5lo a b z⁆) :
    False := by
  rw [commutatorElement_def, l5up_inv, l5lo_inv] at h
  have e1 := congrArg (fun Y : SL(3, K) => (Y : Matrix (Fin 3) (Fin 3) K) 1 2) h
  have e2 := congrArg (fun Y : SL(3, K) => (Y : Matrix (Fin 3) (Fin 3) K) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_l5lo, coe_l5up] at e1 e2
  simp [Matrix.mul_apply, Fin.sum_univ_three, -mul_eq_zero] at e1 e2
  have hz : b * z = 0 := by linear_combination e2
  have hz' : z = 0 := by
    rcases mul_eq_zero.1 hz with h0 | h0
    · exact absurd h0 hb
    · exact h0
  subst hz'
  have : a * a * b = 0 := by linear_combination e1
  rcases mul_eq_zero.1 this with h0 | h0
  · rcases mul_eq_zero.1 h0 with h1 | h1 <;> exact ha h1
  · exact hb h0

theorem l5_central {a b z : K} (ha : a ≠ 0) (hb : b ≠ 0) {M : SL(3, K)} (hMM : M * M = 1)
    (hM1 : M ≠ 1) (h1 : M * l5up 1 = l5up 1 * M) (h2 : M * l5lo a b z = l5lo a b z * M) :
    False := by
  have ent : ∀ (X Y : SL(3, K)) (i j : Fin 3), X = Y →
      (X : Matrix (Fin 3) (Fin 3) K) i j = (Y : Matrix (Fin 3) (Fin 3) K) i j :=
    fun X Y i j h => by rw [h]
  have u12 := ent _ _ 1 2 h1
  have u22 := ent _ _ 2 2 h1
  have u01 := ent _ _ 0 1 h1
  have u02 := ent _ _ 0 2 h1
  have l01 := ent _ _ 0 1 h2
  have l00 := ent _ _ 0 0 h2
  have l11 := ent _ _ 1 1 h2
  have l10 := ent _ _ 1 0 h2
  have m00 := ent _ _ 0 0 hMM
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_l5lo, coe_l5up,
    Matrix.SpecialLinearGroup.coe_one] at u12 u22 u01 u02 l01 l00 l11 l10 m00
  simp [Matrix.mul_apply, Fin.sum_univ_three, -mul_eq_zero] at u12 u22 u01 u02 l01 l00 l11 l10 m00
  set m : Matrix (Fin 3) (Fin 3) K := (M : Matrix (Fin 3) (Fin 3) K) with hm
  have e10 : m 1 0 = 0 := by linear_combination u12
  have e20 : m 2 0 = 0 := by linear_combination u22
  have e21 : m 2 1 = 0 := by linear_combination u01
  have e22 : m 2 2 = m 0 0 := by linear_combination -u02
  have e02 : m 0 2 = 0 := by
    have : m 0 2 * b = 0 := by linear_combination l01
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · exact absurd h0 hb
  have e01 : m 0 1 = 0 := by
    have : m 0 1 * a = 0 := by linear_combination l00 - z * e02
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · exact absurd h0 ha
  have e12 : m 1 2 = 0 := by
    have : m 1 2 * b = 0 := by linear_combination l11 + a * e01
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · exact absurd h0 hb
  have e11 : m 1 1 = m 0 0 := by
    have : (m 1 1 - m 0 0) * a = 0 := by linear_combination l10 - z * e12
    rcases mul_eq_zero.1 this with h0 | h0
    · exact sub_eq_zero.1 h0
    · exact absurd h0 ha
  have hsq : m 0 0 * m 0 0 = 1 := by linear_combination m00 - m 0 1 * e10 - m 0 2 * e20
  have hdet : m 0 0 * m 0 0 * m 0 0 = 1 := by
    have h := M.2
    rw [Matrix.det_fin_three] at h
    rw [← hm] at h
    rw [e10, e20, e21, e01, e02, e12, e11, e22] at h
    linear_combination h
  have h1' : m 0 0 = 1 := by linear_combination (-(m 0 0)) * hsq + hdet
  apply hM1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← hm, e10, e20, e21, e01, e02, e12, e11, e22, h1']

end MatrixLemmas


section Frame

open CFSG.RankThree.PartOne.KF4 CFSG.RankThree.E6 CFSG.RankThree.Lattice

theorem l5_sigma_values :
    f4LongV • chainRoot f4chainLong 1 0 = -alpha1 ∧
    f4LongV • chainRoot f4chainLong 2 1 = -root1342 ∧
    f4LongV • chainRoot f4chainLong 2 0 = -theta ∧
    f4LongV • chainRoot f4chainLong 0 2 = theta := by
  simp only [f4LongV_smul]
  decide +kernel

theorem l5_frame (K : Type) [Field K] :
    ∃ ψ : SL(3, K) →* ModGL Tag.F4 K, Function.Injective ψ ∧
      (∃ ε : Kˣ, ∀ t : K, ψ (l5lo t 0 0) = pinnedX Tag.F4 K (-alpha1) ((ε : K) * t)) ∧
      (∃ ε : Kˣ, ∀ t : K, ψ (l5lo 0 t 0) = pinnedX Tag.F4 K (-root1342) ((ε : K) * t)) ∧
      (∃ ε : Kˣ, ∀ t : K, ψ (l5lo 0 0 t) = pinnedX Tag.F4 K (-theta) ((ε : K) * t)) ∧
      (∃ ε : Kˣ, ∀ t : K, ψ (l5up t) = pinnedX Tag.F4 K theta ((ε : K) * t)) := by
  have hA := (f4Long_frame (L := K)).transport f4LongV
  obtain ⟨e10, e21, e20, e02⟩ := l5_sigma_values
  refine ⟨_, hA.injective, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ε, hε⟩ := hA.transv 1 0 (by decide)
    exact ⟨ε, fun t => by
      rw [← l5_transvection_10 t]
      exact (hε t).trans (congrArg (fun r => pinnedX Tag.F4 K r ((ε : K) * t)) e10)⟩
  · obtain ⟨ε, hε⟩ := hA.transv 2 1 (by decide)
    exact ⟨ε, fun t => by
      rw [← l5_transvection_21 t]
      exact (hε t).trans (congrArg (fun r => pinnedX Tag.F4 K r ((ε : K) * t)) e21)⟩
  · obtain ⟨ε, hε⟩ := hA.transv 2 0 (by decide)
    exact ⟨ε, fun t => by
      rw [← l5_transvection_20 t]
      exact (hε t).trans (congrArg (fun r => pinnedX Tag.F4 K r ((ε : K) * t)) e20)⟩
  · obtain ⟨ε, hε⟩ := hA.transv 0 2 (by decide)
    exact ⟨ε, fun t => by
      rw [← l5_transvection_02 t]
      exact (hε t).trans (congrArg (fun r => pinnedX Tag.F4 K r ((ε : K) * t)) e02)⟩

end Frame

section Helpers

variable (K : Type) [Field K]

theorem l5_mem_R1neg (ψ : SL(3, K) →* ModGL Tag.F4 K)
    (h1 : ∃ ε : Kˣ, ∀ t : K, ψ (l5lo t 0 0) = pinnedX Tag.F4 K (-alpha1) ((ε : K) * t))
    (h2 : ∃ ε : Kˣ, ∀ t : K, ψ (l5lo 0 t 0) = pinnedX Tag.F4 K (-root1342) ((ε : K) * t))
    (h3 : ∃ ε : Kˣ, ∀ t : K, ψ (l5lo 0 0 t) = pinnedX Tag.F4 K (-theta) ((ε : K) * t))
    {d : ModGL Tag.F4 K} (hd : d ∈ R1neg K) : ∃ a b z : K, ψ (l5lo a b z) = d := by
  have hle : R1neg K ≤ (l5Lo K).map ψ := by
    refine iSup₂_le fun α hα => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    simp only [R1negRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rcases hα with rfl | rfl | rfl
    · obtain ⟨ε, hε⟩ := h1
      exact ⟨l5lo (ε⁻¹ * c) 0 0, ⟨_, _, _, rfl⟩, by rw [hε]; simp⟩
    · obtain ⟨ε, hε⟩ := h2
      exact ⟨l5lo 0 (ε⁻¹ * c) 0, ⟨_, _, _, rfl⟩, by rw [hε]; simp⟩
    · obtain ⟨ε, hε⟩ := h3
      exact ⟨l5lo 0 0 (ε⁻¹ * c), ⟨_, _, _, rfl⟩, by rw [hε]; simp⟩
  obtain ⟨M, ⟨a, b, z, rfl⟩, hM⟩ := hle hd
  exact ⟨a, b, z, hM⟩

theorem l5_mem_pure1 (ψ : SL(3, K) →* ModGL Tag.F4 K)
    (h1 : ∃ ε : Kˣ, ∀ t : K, ψ (l5lo t 0 0) = pinnedX Tag.F4 K (-alpha1) ((ε : K) * t))
    (h3 : ∃ ε : Kˣ, ∀ t : K, ψ (l5lo 0 0 t) = pinnedX Tag.F4 K (-theta) ((ε : K) * t))
    (a z : K) : ψ (l5lo a 0 z) ∈ rootSpan Tag.F4 K pureNegRoots1 := by
  obtain ⟨ε1, hε1⟩ := h1
  obtain ⟨ε3, hε3⟩ := h3
  have e : l5lo a (0 : K) z = l5lo 0 0 z * l5lo a 0 0 := by
    rw [l5lo_mul]; simp
  rw [e, map_mul, hε3, hε1]
  exact mul_mem (pinnedX_mem_rootSpan (by simp [pureNegRoots1]) _)
    (pinnedX_mem_rootSpan (by simp [pureNegRoots1]) _)

theorem l5_mem_pure2 (ψ : SL(3, K) →* ModGL Tag.F4 K)
    (h2 : ∃ ε : Kˣ, ∀ t : K, ψ (l5lo 0 t 0) = pinnedX Tag.F4 K (-root1342) ((ε : K) * t))
    (h3 : ∃ ε : Kˣ, ∀ t : K, ψ (l5lo 0 0 t) = pinnedX Tag.F4 K (-theta) ((ε : K) * t))
    (b z : K) : ψ (l5lo 0 b z) ∈ rootSpan Tag.F4 K pureNegRoots2 := by
  obtain ⟨ε2, hε2⟩ := h2
  obtain ⟨ε3, hε3⟩ := h3
  have e : l5lo (0 : K) b z = l5lo 0 0 z * l5lo 0 b 0 := by
    rw [l5lo_mul]; simp
  rw [e, map_mul, hε3, hε2]
  exact mul_mem (pinnedX_mem_rootSpan (by simp [pureNegRoots2]) _)
    (pinnedX_mem_rootSpan (by simp [pureNegRoots2]) _)

theorem l5_conjSub_eq_of_mem_normalizer {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) : conjSub g A = A := by
  ext x
  rw [mem_conjSub_iff]
  have h := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) x).symm
  simpa using h

theorem l5_exists_factor {p : ModGL Tag.F4 K} (hp : p ∈ Pθ Tag.F4 K) :
    ∃ q ∈ Qθ Tag.F4 K, ∃ l ∈ Lθ Tag.F4 K, p = q * l := by
  obtain ⟨-, -, -, -, -, -, hfac, -⟩ := parabolic_root_radical_Levi_factors Tag.F4 K (Jθ Tag.F4)
  obtain ⟨⟨q, l⟩, ⟨hq, hl, hp'⟩, -⟩ := hfac p hp
  exact ⟨q, hq, l, hl, hp'⟩

theorem l5_Uθ_comm {u g : ModGL Tag.F4 K} (hu : u ∈ Uθ Tag.F4 K)
    (hg : g ∈ posUnipotent Tag.F4 K) : u * g = g * u := by
  obtain ⟨b, rfl⟩ := mem_rootSubgroup.1 hu
  exact (commute_of_mem_posUnipotent (isMaxHeight_highRoot Tag.F4) hg b).eq.symm

theorem l5_abelian {D : Subgroup (ModGL Tag.F4 K)} (hD : IsLongRootSubgroup Tag.F4 K D) :
    ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
  obtain ⟨g, -, rfl⟩ := hD
  intro x hx y hy
  obtain ⟨s, hs⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hx)
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hy)
  have h : (g⁻¹ * x * g) * (g⁻¹ * y * g) = (g⁻¹ * y * g) * (g⁻¹ * x * g) := by
    rw [← hs, ← ht, ← pinnedX_add, ← pinnedX_add, add_comm]
  calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
    _ = y * x := by group

open CFSG.LieType.Steinberg.Adjoint in
theorem l5_data : ∀ β ∈ rootFinset .F4, iform β β = iform theta theta → β 0 = -1 →
    theta ≠ β ∧ theta ≠ -β ∧
    ∀ q ∈ commCandidates, q ≠ (1, 1) → q.1 • theta + q.2 • β ∉ rootFinset .F4 := by
  decide +kernel

theorem l5_commPairs {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β)
    (hlong : IsLongRoot Tag.F4 β) (hd : β 0 = -1) :
    commPairs Tag.F4 theta β = [(1, 1)] := by
  have hβ' := mem_rootFinset.2 hβ
  obtain ⟨-, -, hrest⟩ := l5_data β hβ' hlong hd
  refine list_eq_singleton_of_forall_eq (fun q hq => ?_) (commPairs_nodup _ _) ?_
  · rw [mem_commPairs] at hq
    by_contra hne
    exact hrest q hq.1 hne (mem_rootFinset.2 hq.2)
  · rw [mem_commPairs]
    refine ⟨by decide, ?_⟩
    simpa using mem_rootFinset.1 (theta_add_deg_neg_one β hβ' hd)

theorem l5_comm_comm {p : ModGL Tag.F4 K} (hp : p ∈ Pθ Tag.F4 K) {β : Fin Tag.F4.rank → ℤ}
    (hβ : IsRoot Tag.F4 β) (hlong : IsLongRoot Tag.F4 β) (hd : -1 ≤ β 0) :
    ∀ u ∈ Uθ Tag.F4 K, ∀ d ∈ conjSub p (rootSubgroup Tag.F4 K β), ⁅u, d⁆ * u = u * ⁅u, d⁆ := by
  intro u hu d hd'
  have hb := deg_bounds β (mem_rootFinset.2 hβ)
  by_cases h01 : β 0 = 0 ∨ β 0 = 1
  · have hc := commute_Uθ_conjSub K hp hβ h01 u hu d hd'
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc, one_mul, mul_one]
  by_cases h2 : β 0 = 2
  · have hθ : β = theta := deg_eq_two β (mem_rootFinset.2 hβ) h2
    subst hθ
    have hD : conjSub p (rootSubgroup Tag.F4 K theta) = Uθ Tag.F4 K :=
      l5_conjSub_eq_of_mem_normalizer (Pθ_le_normalizer_Uθ Tag.F4 K hp)
    rw [hD] at hd'
    obtain ⟨s, rfl⟩ := mem_rootSubgroup.1 hu
    obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hd'
    have hc : pinnedX Tag.F4 K (highRoot Tag.F4) s * pinnedX Tag.F4 K (highRoot Tag.F4) t =
        pinnedX Tag.F4 K (highRoot Tag.F4) t * pinnedX Tag.F4 K (highRoot Tag.F4) s := by
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc, one_mul, mul_one]
  have h1 : β 0 = -1 := by omega
  have hpn := Pθ_le_normalizer_Uθ Tag.F4 K (inv_mem hp)
  have hu' : p⁻¹ * u * p ∈ Uθ Tag.F4 K := by
    have := (Subgroup.mem_normalizer_iff.1 hpn u).1 hu
    simpa using this
  obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hu'
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hd')
  have hs' : pinnedX Tag.F4 K theta s = p⁻¹ * u * p := hs
  obtain ⟨hne, hne', -⟩ := l5_data β (mem_rootFinset.2 hβ) hlong h1
  obtain ⟨-, -, -, -, hF⟩ := root_commutator_formula.{0} Tag.F4 isRoot_theta hβ hne hne'
  have hF' := hF K s t
  rw [l5_commPairs hβ hlong h1] at hF'
  obtain ⟨w, hw⟩ : ∃ w : K, pinnedX Tag.F4 K theta s * pinnedX Tag.F4 K β t *
      pinnedX Tag.F4 K theta (-s) * pinnedX Tag.F4 K β (-t) =
        pinnedX Tag.F4 K (theta + β) w := ⟨_, by simpa using hF'⟩
  have hβ2 : IsRoot Tag.F4 (theta + β) := mem_rootFinset.1 (theta_add_deg_neg_one β
    (mem_rootFinset.2 hβ) h1)
  have hdeg : (theta + β) 0 = 1 := by
    show theta 0 + β 0 = 1
    rw [h1]; rfl
  have hcomm : pinnedX Tag.F4 K (theta + β) w * pinnedX Tag.F4 K theta s =
      pinnedX Tag.F4 K theta s * pinnedX Tag.F4 K (theta + β) w :=
    (commute_Uθ_rootSubgroup K hβ2 (Or.inr hdeg) s w).symm.eq
  have hu_eq : u = p * pinnedX Tag.F4 K theta s * p⁻¹ := by rw [hs']; group
  have hd_eq : d = p * pinnedX Tag.F4 K β t * p⁻¹ := by rw [ht]; group
  have hcc : ⁅u, d⁆ = p * pinnedX Tag.F4 K (theta + β) w * p⁻¹ := by
    rw [← hw, commutatorElement_def, hu_eq, hd_eq, ← pinnedX_neg, ← pinnedX_neg]
    group
  rw [hcc, hu_eq]
  calc p * pinnedX Tag.F4 K (theta + β) w * p⁻¹ * (p * pinnedX Tag.F4 K theta s * p⁻¹)
      = p * (pinnedX Tag.F4 K (theta + β) w * pinnedX Tag.F4 K theta s) * p⁻¹ := by group
    _ = p * (pinnedX Tag.F4 K theta s * pinnedX Tag.F4 K (theta + β) w) * p⁻¹ := by rw [hcomm]
    _ = _ := by group

theorem l5_HSL_central (A : SL2 K) : HSL (-1 : Kˣ) * A = A * HSL (-1 : Kˣ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem l5_HSL_sq : HSL (-1 : Kˣ) * HSL (-1 : Kˣ) = (1 : SL2 K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem l5_HSL_ne_one (h2 : (2 : K) ≠ 0) : HSL (-1 : Kˣ) ≠ (1 : SL2 K) := by
  intro h
  have e := congrArg (fun Y : SL2 K => (Y : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [coe_HSL] at e
  apply h2
  linear_combination -e

theorem l5_central_involution (h2 : (2 : K) ≠ 0) {p : ModGL Tag.F4 K} (hp : p ∈ Pθ Tag.F4 K) :
    ∃ z₀ ∈ Uθ Tag.F4 K ⊔ conjSub p (Heis.Uneg Tag.F4 K), z₀ ≠ 1 ∧ z₀ * z₀ = 1 ∧
      (∀ x ∈ Uθ Tag.F4 K, z₀ * x = x * z₀) ∧
      (∀ x ∈ conjSub p (Heis.Uneg Tag.F4 K), z₀ * x = x * z₀) := by
  obtain ⟨q, hq, l, hl, rfl⟩ := l5_exists_factor K hp
  rw [conjSub_mul, l5_conjSub_eq_of_mem_normalizer (Lθ_le_normalizer_Uneg Tag.F4 K hl)]
  have hρinj : Function.Injective (rootSL2 Tag.F4 K theta) :=
    CFSG.RankThree.Chevalley.rootSL2_injective_of_field theta
  have hρrange : (rootSL2 Tag.F4 K theta).range =
      rootSubgroup Tag.F4 K theta ⊔ rootSubgroup Tag.F4 K (-theta) :=
    CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot isRoot_theta
  set c : ModGL Tag.F4 K := rootSL2 Tag.F4 K theta (HSL (-1 : Kˣ)) with hc
  have hUle : Uθ Tag.F4 K ≤ (rootSL2 Tag.F4 K theta).range := by
    rw [hρrange]; exact le_sup_left
  have hVle : Heis.Uneg Tag.F4 K ≤ (rootSL2 Tag.F4 K theta).range := by
    rw [hρrange]; exact le_sup_right
  have hc1 : ∀ y ∈ (rootSL2 Tag.F4 K theta).range, c * y = y * c := by
    rintro _ ⟨A, rfl⟩
    rw [hc, ← map_mul, ← map_mul, l5_HSL_central]
  have hc2 : c * c = 1 := by rw [hc, ← map_mul, l5_HSL_sq, map_one]
  have hc3 : c ≠ 1 := fun h => l5_HSL_ne_one K h2 (hρinj (by rw [map_one]; exact h))
  have hcmem : c ∈ Uθ Tag.F4 K ⊔ Heis.Uneg Tag.F4 K := by
    have : c ∈ (rootSL2 Tag.F4 K theta).range := ⟨_, rfl⟩
    rw [hρrange] at this
    exact this
  have hqP : q ∈ Pθ Tag.F4 K := (parabolic_root_radical_Levi_factors Tag.F4 K (Jθ Tag.F4)).1 hq
  have hqU : conjSub q (Uθ Tag.F4 K) = Uθ Tag.F4 K :=
    l5_conjSub_eq_of_mem_normalizer (Pθ_le_normalizer_Uθ Tag.F4 K hqP)
  have hqpos : q ∈ posUnipotent Tag.F4 K := parabolicRadical_le_posUnipotent (Jθ Tag.F4) hq
  refine ⟨q * c * q⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : q * c * q⁻¹ ∈ conjSub q (Uθ Tag.F4 K ⊔ Heis.Uneg Tag.F4 K) := by
      rw [mem_conjSub_iff]
      have e : q⁻¹ * (q * c * q⁻¹) * q = c := by group
      rw [e]
      exact hcmem
    have h2' : conjSub q (Uθ Tag.F4 K ⊔ Heis.Uneg Tag.F4 K) =
        conjSub q (Uθ Tag.F4 K) ⊔ conjSub q (Heis.Uneg Tag.F4 K) := by
      unfold conjSub
      rw [Subgroup.map_sup]
    rw [h2', hqU] at h1
    exact h1
  · intro h
    apply hc3
    have : c = q⁻¹ * (q * c * q⁻¹) * q := by group
    rw [this, h]
    group
  · calc q * c * q⁻¹ * (q * c * q⁻¹) = q * (c * c) * q⁻¹ := by group
      _ = 1 := by rw [hc2]; group
  · intro x hx
    have hxq : x * q = q * x := l5_Uθ_comm K hx hqpos
    have hcx : c * x = x * c := hc1 x (hUle hx)
    calc q * c * q⁻¹ * x = q * c * (q⁻¹ * x * q) * q⁻¹ := by group
      _ = q * (c * x) * q⁻¹ := by
        rw [show q⁻¹ * x * q = x by rw [mul_assoc, hxq, inv_mul_cancel_left]]; group
      _ = q * (x * c) * q⁻¹ := by rw [hcx]
      _ = (q * x) * c * q⁻¹ := by group
      _ = (x * q) * c * q⁻¹ := by rw [hxq]
      _ = x * (q * c * q⁻¹) := by group
  · intro x hx
    have hx' : q⁻¹ * x * q ∈ Heis.Uneg Tag.F4 K := mem_conjSub_iff.1 hx
    have hcx : c * (q⁻¹ * x * q) = (q⁻¹ * x * q) * c := hc1 _ (hVle hx')
    calc q * c * q⁻¹ * x = q * (c * (q⁻¹ * x * q)) * q⁻¹ := by group
      _ = q * ((q⁻¹ * x * q) * c) * q⁻¹ := by rw [hcx]
      _ = x * (q * c * q⁻¹) := by group

theorem l5_key {D : Subgroup (ModGL Tag.F4 K)} (hD : IsLongRootSubgroup Tag.F4 K D)
    {ψ : SL(3, K) →* ModGL Tag.F4 K} (hψ : Function.Injective ψ)
    (hup : ∃ ε : Kˣ, ∀ t : K, ψ (l5up t) = pinnedX Tag.F4 K theta ((ε : K) * t))
    (hDr : D ≤ ψ.range) {a b z : K} (ha : a ≠ 0) (hb : b ≠ 0) (hd : ψ (l5lo a b z) ∈ D) :
    False := by
  obtain ⟨ε, hε⟩ := hup
  have hu1 : ψ (l5up (1 : K)) ∈ Uθ Tag.F4 K := by
    rw [hε]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  have hUle : Uθ Tag.F4 K ≤ ψ.range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact ⟨l5up (ε⁻¹ * c), by rw [hε, Units.mul_inv_cancel_left]; rfl⟩
  obtain ⟨g, hg, hDg⟩ := hD
  have hd' : ψ (l5lo a b z) ∈ conjSub g (Uθ Tag.F4 K) := by rw [← hDg]; exact hd
  by_cases h2 : ringChar K = 2
  · have hp := pow_char_eq_one_of_mem_conjSub K hd'
    haveI : CharP K 2 := ringChar.of_eq h2
    have h20 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
    rw [h2, ← map_pow, ← map_one ψ] at hp
    have hp' := hψ hp
    rw [pow_two] at hp'
    exact l5_two ha hb h20 hp'
  · have h2' : (2 : K) ≠ 0 := Ring.two_ne_zero h2
    obtain ⟨p, hp, β, hβ, ⟨w, hw⟩, hgβ⟩ := Heis.exists_normalForm Tag.F4 K hg
    have hlong : IsLongRoot Tag.F4 β := by
      rw [hw]; exact Heis.isLongRoot_smul_highRoot Tag.F4 w
    have hd'' : ψ (l5lo a b z) ∈ conjSub p (rootSubgroup Tag.F4 K β) := by
      rw [← hgβ]; exact hd'
    have hb2 := deg_bounds β (mem_rootFinset.2 hβ)
    by_cases hdeg : -1 ≤ β 0
    · have hc := l5_comm_comm K hp hβ hlong hdeg _ hu1 _ hd''
      rw [← map_commutatorElement, ← map_mul, ← map_mul] at hc
      exact l5_not_commute ha hb (hψ hc)
    · have hβ0 : β 0 = -2 := by omega
      have hβe : β = -theta := deg_eq_neg_two β (mem_rootFinset.2 hβ) hβ0
      subst hβe
      obtain ⟨z₀, hz₀, hne, hsq, hU, hV⟩ := l5_central_involution K h2' hp
      have hDle : conjSub p (Heis.Uneg Tag.F4 K) ≤ ψ.range := by
        have := hDr
        rw [hDg, hgβ] at this
        exact this
      obtain ⟨M, hM⟩ := sup_le hUle hDle hz₀
      have hMM : M * M = 1 := hψ (by rw [map_mul, hM, hsq, map_one])
      have hM1 : M ≠ 1 := by
        rintro rfl
        exact hne (by rw [← hM, map_one])
      have hcU : M * l5up 1 = l5up 1 * M := hψ (by
        rw [map_mul, map_mul, hM]; exact hU _ hu1)
      have hcL : M * l5lo a b z = l5lo a b z * M := hψ (by
        rw [map_mul, map_mul, hM]; exact hV _ hd'')
      exact l5_central ha hb hMM hM1 hcU hcL

end Helpers

theorem lemma5_neg (K : Type) [Field K] [Finite K] {D : Subgroup (ModGL Tag.F4 K)}
    (hD : IsLongRootSubgroup Tag.F4 K D) (hle : D ≤ R1neg K) :
    D ≤ rootSpan Tag.F4 K pureNegRoots1 ∨ D ≤ rootSpan Tag.F4 K pureNegRoots2 := by
  classical
  obtain ⟨ψ, hψ, h21, h32, h31, h13⟩ := l5_frame K
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  obtain ⟨d1, hd1, hd1n⟩ := SetLike.not_le_iff_exists.1 hn1
  obtain ⟨d2, hd2, hd2n⟩ := SetLike.not_le_iff_exists.1 hn2
  have hDr : D ≤ ψ.range := by
    intro d hd
    obtain ⟨a, b, z, hz⟩ := l5_mem_R1neg K ψ h21 h32 h31 (hle hd)
    exact ⟨_, hz⟩
  obtain ⟨a1, b1, z1, rfl⟩ := l5_mem_R1neg K ψ h21 h32 h31 (hle hd1)
  obtain ⟨a2, b2, z2, rfl⟩ := l5_mem_R1neg K ψ h21 h32 h31 (hle hd2)
  have hb1 : b1 ≠ 0 := by
    rintro rfl
    exact hd1n (l5_mem_pure1 K ψ h21 h31 a1 z1)
  have ha2 : a2 ≠ 0 := by
    rintro rfl
    exact hd2n (l5_mem_pure2 K ψ h32 h31 b2 z2)
  have hcomm : l5lo a1 b1 z1 * l5lo a2 b2 z2 = l5lo a2 b2 z2 * l5lo a1 b1 z1 :=
    hψ (by rw [map_mul, map_mul]; exact l5_abelian K hD _ hd1 _ hd2)
  rw [l5lo_mul, l5lo_mul] at hcomm
  have e := congrArg (fun Y : SL(3, K) => (Y : Matrix (Fin 3) (Fin 3) K) 2 0) hcomm
  simp only [coe_l5lo] at e
  simp at e
  have hba : b1 * a2 = b2 * a1 := by linear_combination e
  have ha1 : a1 ≠ 0 := by
    rintro rfl
    apply mul_ne_zero hb1 ha2
    rw [hba, mul_zero]
  exact l5_key K hD hψ h13 hDr ha1 hb1 hd1

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
