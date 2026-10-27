module

public import CFSG.LieType.SeitzGeneration.RootPairOrthSplit
public import CFSG.ClassicalGroups.Orthogonal.RootCenters

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

namespace RootPairOrth

section Center

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : SplitCoord Q)

theorem SplitCoord.polar_single_right (a : Fin d) (x : Fin d → K) :
    polar Q x (Pi.single a 1) = x (S.star a) := by
  rw [polar_comm, S.polar_single]

theorem SplitCoord.eichler_coord {u v : Fin d} (huv : v ≠ S.star u) (x : Fin d → K) :
    eichler Q (Pi.single u 1) (Pi.single v 1) x =
      x + x (S.star u) • (Pi.single v 1 : Fin d → K) -
        x (S.star v) • (Pi.single u 1 : Fin d → K) := by
  have hpol : polar Q (Pi.single u 1 : Fin d → K) (Pi.single v 1) = 0 := by
    rw [S.polar_single_single]; simp [Ne.symm huv]
  rw [eichler_apply (S.Q_single u) hpol, S.polar_single_right, S.polar_single_right, S.Q_single]
  simp

include S in
theorem SplitCoord.nondegenerate : (polarBilin Q).Nondegenerate := by
  refine ⟨fun m hm => ?_, fun n hn => ?_⟩
  · funext a
    have := hm (Pi.single (S.star a) 1)
    rw [polarBilin_apply_apply, S.polar_single_right, S.star_star] at this
    simpa using this
  · funext a
    have := hn (Pi.single (S.star a) 1)
    rw [polarBilin_apply_apply, S.polar_single, S.star_star] at this
    simpa using this

variable {S} (H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)))

variable (Q) in
@[expose] def rootLine (p : Fin d) : Submodule K (Fin d → K) where
  carrier := {w | polar Q (Pi.single p 1 : Fin d → K) w = 0 ∧
    ∀ t : K, eichler Q (Pi.single p 1 : Fin d → K) (t • w) ∈ H}
  add_mem' := by
    rintro w w' ⟨hw, hHw⟩ ⟨hw', hHw'⟩
    refine ⟨by rw [polar_add_right, hw, hw', add_zero], fun t => ?_⟩
    have e1 : polar Q (Pi.single p 1 : Fin d → K) (t • w) = 0 := by
      rw [polar_smul_right_eq, hw, mul_zero]
    have e2 : polar Q (Pi.single p 1 : Fin d → K) (t • w') = 0 := by
      rw [polar_smul_right_eq, hw', mul_zero]
    rw [smul_add, ← eichler_mul e1 e2]
    exact H.mul_mem (hHw t) (hHw' t)
  zero_mem' := by
    refine ⟨polar_zero_right Q _, fun t => ?_⟩
    rw [smul_zero, eichler_zero_right]
    exact H.one_mem
  smul_mem' := by
    rintro c w ⟨hw, hHw⟩
    refine ⟨by rw [polar_smul_right_eq, hw, mul_zero], fun t => ?_⟩
    rw [smul_smul]
    exact hHw (t * c)

theorem rootLine_map (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {p : Fin d}
    {h : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hh : h ∈ H) (hp : h (Pi.single p 1) = Pi.single p 1)
    {w : Fin d → K} (hw : w ∈ rootLine Q H p) : h w ∈ rootLine Q H p := by
  obtain ⟨hw0, hHw⟩ := hw
  refine ⟨?_, fun t => ?_⟩
  · calc polar Q (Pi.single p 1 : Fin d → K) (h w)
        = polar Q (h (Pi.single p 1)) (h w) := by rw [hp]
      _ = polar Q (Pi.single p 1) w := polar_map_of_mem (hH hh) _ _
      _ = 0 := hw0
  · have := eichler_conj (hH hh) (Pi.single p 1 : Fin d → K) (t • w)
    rw [hp, map_smul] at this
    rw [← this]
    exact H.mul_mem (H.mul_mem hh (hHw t)) (H.inv_mem hh)

@[expose] def CoordEichler (S : SplitCoord Q) : Prop :=
  ∀ u v : Fin d, v ≠ S.star u → eichler Q (Pi.single u 1 : Fin d → K) (Pi.single v 1) ∈ H

theorem single_ne_zero (p : Fin d) : (Pi.single p 1 : Fin d → K) ≠ 0 := fun h => by
  have := congrFun h p
  simp at this

theorem single_mem_rootLine (S : SplitCoord Q) (p : Fin d) :
    (Pi.single p 1 : Fin d → K) ∈ rootLine Q H p := by
  refine ⟨polar_self_eq_zero (S.Q_single p), fun t => ?_⟩
  have := eichler_add_smul_self (S.Q_single p) (0 : Fin d → K) t
  rw [zero_add, eichler_zero_right] at this
  rw [this]
  exact H.one_mem

theorem SplitCoord.coord_mem_rootLine (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb : CoordEichler H S) {p q c : Fin d} (hq : q ≠ p) (hc2 : c ≠ S.star p)
    (hc3 : c ≠ q) (hc4 : c ≠ S.star q) (hqR : (Pi.single q 1 : Fin d → K) ∈ rootLine Q H p) :
    (Pi.single c 1 : Fin d → K) ∈ rootLine Q H p := by
  have hcond : c ≠ S.star (S.star q) := by rw [S.star_star]; exact hc3
  have hh := hb _ _ hcond
  have hp : eichler Q (Pi.single (S.star q) 1 : Fin d → K) (Pi.single c 1) (Pi.single p 1) =
      Pi.single p 1 := by
    rw [S.eichler_coord hcond, S.star_star]
    have e1 : (Pi.single p 1 : Fin d → K) q = 0 := by simp [hq]
    have e2 : (Pi.single p 1 : Fin d → K) (S.star c) = 0 := by
      have : S.star c ≠ p := fun h => hc2 (by rw [← h, S.star_star])
      simp [this]
    rw [e1, e2]
    simp
  have hq' : eichler Q (Pi.single (S.star q) 1 : Fin d → K) (Pi.single c 1) (Pi.single q 1) =
      Pi.single q 1 + Pi.single c 1 := by
    rw [S.eichler_coord hcond, S.star_star]
    have e1 : (Pi.single q 1 : Fin d → K) q = 1 := by simp
    have e2 : (Pi.single q 1 : Fin d → K) (S.star c) = 0 := by
      have : S.star c ≠ q := fun h => hc4 (by rw [← h, S.star_star])
      simp [this]
    rw [e1, e2]
    simp
  have h1 := rootLine_map H hH hh hp hqR
  rw [hq'] at h1
  have h2 := Submodule.sub_mem _ h1 hqR
  simpa using h2

theorem SplitCoord.rootLine_all (hd : 5 < d) (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb : CoordEichler H S) {p q : Fin d} (hqp : q ≠ p) (hqR : (Pi.single q 1 : Fin d → K) ∈
      rootLine Q H p) (c : Fin d) (hc : c ≠ S.star p) :
    (Pi.single c 1 : Fin d → K) ∈ rootLine Q H p := by
  by_cases hcp : c = p
  · subst hcp; exact single_mem_rootLine H S c
  by_cases hcq : c = q
  · subst hcq; exact hqR
  by_cases hcsq : c = S.star q
  · have hqs : q ≠ S.star p := fun h => by
      have := hqR.1
      rw [S.polar_single_single, h] at this
      simp at this
    obtain ⟨c', hc'⟩ := Fin.exists_notMem ({p, S.star p, q, S.star q} : Finset (Fin d))
      (lt_of_le_of_lt Finset.card_le_four (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'
    have hc'R := S.coord_mem_rootLine H hH hb hqp hc'.2.1 hc'.2.2.1 hc'.2.2.2 hqR
    subst hcsq
    refine S.coord_mem_rootLine H hH hb hc'.1 hc (fun h => hc'.2.2.2 h.symm) ?_ hc'R
    intro h
    have := congrArg S.star h
    rw [S.star_star, S.star_star] at this
    exact hc'.2.2.1 this.symm
  · exact S.coord_mem_rootLine H hH hb hqp hc hcq hcsq hqR

theorem SplitCoord.isRootCenter_coord (hd : 5 < d)
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hb : CoordEichler H S) {p q : Fin d}
    (hqp : q ≠ p) (hqR : (Pi.single q 1 : Fin d → K) ∈ rootLine Q H p) :
    IsRootCenter Q H (Pi.single p 1 : Fin d → K) := by
  refine ⟨single_ne_zero p, S.Q_single p, fun w hw => ?_⟩
  have hwR : w ∈ rootLine Q H p := by
    have hw0 : w (S.star p) = 0 := (S.polar_single p w).symm.trans hw
    have : w = ∑ c, w c • (Pi.single c 1 : Fin d → K) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    refine Submodule.sum_mem _ fun c _ => ?_
    by_cases hc : c = S.star p
    · subst hc; rw [hw0, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (S.rootLine_all H hd hH hb hqp hqR c hc)
  simpa using hwR.2 1

theorem SplitCoord.exists_move (hb : CoordEichler H S) {p j : Fin d} (hjp : j ≠ p)
    (hjs : j ≠ S.star p) : ∃ h ∈ H, h (Pi.single p 1 : Fin d → K) = Pi.single (S.star j) 1 := by
  have hsj : p ≠ S.star j := fun h => hjs (by rw [h, S.star_star])
  have hsj' : S.star j ≠ p := fun h => hsj h.symm
  have h1 : eichler Q (Pi.single (S.star p) 1 : Fin d → K) (Pi.single (S.star j) 1) ∈ H :=
    hb _ _ (by rw [S.star_star]; exact hsj')
  have h2 : eichler Q (Pi.single j 1 : Fin d → K) (Pi.single p 1) ∈ H := hb _ _ hsj
  refine ⟨(eichler Q (Pi.single j 1 : Fin d → K) (Pi.single p 1))⁻¹ *
    eichler Q (Pi.single (S.star p) 1 : Fin d → K) (Pi.single (S.star j) 1),
    H.mul_mem (H.inv_mem h2) h1, ?_⟩
  have e1 : eichler Q (Pi.single (S.star p) 1 : Fin d → K) (Pi.single (S.star j) 1)
      (Pi.single p 1) = Pi.single p 1 + Pi.single (S.star j) 1 := by
    rw [S.eichler_coord (by rw [S.star_star]; exact hsj'), S.star_star, S.star_star]
    have : (Pi.single p 1 : Fin d → K) j = 0 := by simp [hjp]
    simp [this]
  have e2 : eichler Q (Pi.single j 1 : Fin d → K) (Pi.single p 1) (Pi.single (S.star j) 1) =
      Pi.single p 1 + Pi.single (S.star j) 1 := by
    rw [S.eichler_coord hsj]
    have : (Pi.single (S.star j) 1 : Fin d → K) (S.star p) = 0 := by
      have : S.star p ≠ S.star j := fun h => hjp (by
        have h' := congrArg S.star h
        rw [S.star_star, S.star_star] at h'
        exact h'.symm)
      simp [this]
    simp [this]
    abel
  rw [LinearEquiv.mul_apply, e1, ← e2, ← LinearEquiv.mul_apply, inv_mul_cancel]
  rfl

theorem SplitCoord.elementaryGroup_le_of_rootLine (hd : 5 < d)
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hb : CoordEichler H S) {p q : Fin d}
    (hqp : q ≠ p) (hqR : (Pi.single q 1 : Fin d → K) ∈ rootLine Q H p) :
    elementaryGroup Q ≤ H := by
  have he := S.isRootCenter_coord H hd hH hb hqp hqR
  obtain ⟨j, hj⟩ := Fin.exists_notMem ({p, S.star p} : Finset (Fin d))
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  obtain ⟨h₁, hh₁, e₁⟩ := S.exists_move H hb hj.1 hj.2
  have hp1 : p ≠ S.star j := fun h => hj.2 (by rw [h, S.star_star])
  obtain ⟨h₂, hh₂, e₂⟩ := S.exists_move H hb (p := S.star j) (j := p) hp1
    (by rw [S.star_star]; exact fun h => hj.1 h.symm)
  have hf : IsRootCenter Q H (Pi.single (S.star p) 1 : Fin d → K) := by
    have := he.map hH (H.mul_mem hh₂ hh₁)
    rwa [LinearEquiv.mul_apply, e₁, e₂] at this
  have hpair : polar Q (Pi.single p 1 : Fin d → K) (Pi.single (S.star p) 1) = 1 := by
    rw [S.polar_single_single]; simp
  exact elementaryGroup_le_of_hypPair S.nondegenerate hH
    ⟨Pi.single p 1, Pi.single (S.star p) 1, S.Q_single p, S.Q_single _, hpair⟩ he hf

theorem SplitCoord.elementaryGroup_le_of_basic_line (hd : 5 < d)
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hb : CoordEichler H S) {x y : Fin d → K}
    (hxy : IsBasic S x y) (hne : x ≠ y) (hline : ∀ t : K, eichler Q x (t • y) ∈ H) :
    elementaryGroup Q ≤ H := by
  cases hxy with
  | single hb' =>
    rename_i a b
    have hab : b ≠ a := fun h => hne (by rw [h])
    refine S.elementaryGroup_le_of_rootLine H hd hH hb hab ?_
    refine ⟨?_, fun t => hline t⟩
    rw [S.polar_single_single]
    simp [Ne.symm hb']
  | plane hj hjs =>
    rename_i a j
    have haj : a ≠ S.star j := fun h => hjs (by rw [h, S.star_star])
    have hE : eichler Q (Pi.single j 1 : Fin d → K) (Pi.single a 1) ∈ H := hb _ _ haj
    have hjn : S.star a ≠ S.star j := fun h => hj (by
      have h' := congrArg S.star h
      rw [S.star_star, S.star_star] at h'
      exact h'.symm)
    have e1 : eichler Q (Pi.single j 1 : Fin d → K) (Pi.single a 1) (Pi.single (S.star j) 1) =
        Pi.single a 1 + Pi.single (S.star j) 1 := by
      rw [S.eichler_coord haj]
      have : (Pi.single (S.star j) 1 : Fin d → K) (S.star a) = 0 := by simp [hjn.symm]
      simp [this]
      abel
    have e2 : eichler Q (Pi.single j 1 : Fin d → K) (Pi.single a 1) (-Pi.single (S.star a) 1) =
        Pi.single j 1 - Pi.single (S.star a) 1 := by
      rw [map_neg, S.eichler_coord haj]
      have h1 : (Pi.single (S.star a) 1 : Fin d → K) (S.star j) = 0 := by simp [hjn]
      simp [h1]
    set E := eichler Q (Pi.single j 1 : Fin d → K) (Pi.single a 1) with hEdef
    have hx : E⁻¹ ((Pi.single a 1 : Fin d → K) + Pi.single (S.star j) 1) =
        Pi.single (S.star j) 1 := by
      rw [← e1, ← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    have hy : E⁻¹ (Pi.single j 1 - Pi.single (S.star a) 1 : Fin d → K) =
        -Pi.single (S.star a) 1 := by
      rw [← e2, ← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    have hline' : ∀ t : K, eichler Q (Pi.single (S.star j) 1 : Fin d → K)
        (t • Pi.single (S.star a) 1) ∈ H := by
      intro t
      have h3 := eichler_conj (hH (H.inv_mem hE))
        ((Pi.single a 1 : Fin d → K) + Pi.single (S.star j) 1)
        ((-t) • (Pi.single j 1 - Pi.single (S.star a) 1))
      have e4 : E⁻¹ ((-t) • (Pi.single j 1 - Pi.single (S.star a) 1 : Fin d → K)) =
          t • Pi.single (S.star a) 1 := by
        rw [map_smul, hy, smul_neg, neg_smul, neg_neg]
      rw [hx, e4] at h3
      rw [← h3]
      exact H.mul_mem (H.mul_mem (H.inv_mem hE) (hline (-t))) (H.inv_mem (H.inv_mem hE))
    refine S.elementaryGroup_le_of_rootLine H hd hH hb (p := S.star j) (q := S.star a) hjn ?_
    refine ⟨?_, fun t => hline' t⟩
    rw [S.polar_single_single, S.star_star]
    simp [hjs]

end Center

end RootPairOrth

end CFSG.LieType.SeitzGeneration
