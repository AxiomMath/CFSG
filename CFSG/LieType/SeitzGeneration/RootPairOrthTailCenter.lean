module

public import CFSG.LieType.SeitzGeneration.RootPairOrthTail
public import CFSG.LieType.SeitzGeneration.RootPairOrthCenter

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

namespace RootPairOrth

section Center

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : HypCoord Q)
  {k : Subfield K} (H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)))

theorem single_apply_ne {a b : Fin d} (h : b ≠ a) : (Pi.single a 1 : Fin d → K) b = 0 := by
  simp [h]

theorem HypCoord.eichler_coord_T {u v : Fin d} (hu : u ∈ S.hyp) (hv : S.star u ≠ v)
    (x : Fin d → K) :
    eichler Q (Pi.single u 1) (Pi.single v 1) x =
      x + x (S.star u) • (Pi.single v 1 : Fin d → K) -
        (polar Q x (Pi.single v 1) + Q (Pi.single v 1) * x (S.star u)) •
          (Pi.single u 1 : Fin d → K) := by
  have hpol : polar Q (Pi.single u 1 : Fin d → K) (Pi.single v 1) = 0 := by
    rw [S.polar_single_single hu]; simp [hv]
  rw [eichler_apply (S.Q_single u hu) hpol, S.polar_single_right hu]

@[expose] def CoordEichlerT (S : HypCoord Q) : Prop :=
  ∀ u ∈ S.hyp, ∀ v : Fin d, S.star u ≠ v →
    eichler Q (Pi.single u 1 : Fin d → K) (Pi.single v 1) ∈ H

theorem single_mem_rootLine_T {p : Fin d} (hp : p ∈ S.hyp) :
    (Pi.single p 1 : Fin d → K) ∈ rootLine Q H p := by
  refine ⟨polar_self_eq_zero (S.Q_single p hp), fun t => ?_⟩
  have := eichler_add_smul_self (S.Q_single p hp) (0 : Fin d → K) t
  rw [zero_add, eichler_zero_right] at this
  rw [this]
  exact H.one_mem

theorem HypCoord.coord_mem_rootLine_T (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb : CoordEichlerT H S) {p q c : Fin d} (hp : p ∈ S.hyp) (hq : q ∈ S.hyp) (hc : c ∈ S.hyp)
    (hqp : q ≠ p) (hc2 : c ≠ S.star p) (hc3 : c ≠ q) (hc4 : c ≠ S.star q)
    (hqR : (Pi.single q 1 : Fin d → K) ∈ rootLine Q H p) :
    (Pi.single c 1 : Fin d → K) ∈ rootLine Q H p := by
  have hsq := S.star_mem q hq
  have hcond : S.star (S.star q) ≠ c := by rw [S.star_star q hq]; exact Ne.symm hc3
  have hh := hb _ hsq c hcond
  have hp1 : eichler Q (Pi.single (S.star q) 1 : Fin d → K) (Pi.single c 1) (Pi.single p 1) =
      Pi.single p 1 := by
    rw [S.eichler_coord_T hsq hcond, S.star_star q hq, S.polar_single p hp, S.Q_single c hc]
    simp [single_apply_ne hqp, single_apply_ne (Ne.symm hc2)]
  have hq1 : eichler Q (Pi.single (S.star q) 1 : Fin d → K) (Pi.single c 1) (Pi.single q 1) =
      Pi.single q 1 + Pi.single c 1 := by
    rw [S.eichler_coord_T hsq hcond, S.star_star q hq, S.polar_single q hq, S.Q_single c hc]
    simp [single_apply_ne (Ne.symm hc4)]
  have h1 := rootLine_map H hH hh hp1 hqR
  rw [hq1] at h1
  have h2 := Submodule.sub_mem _ h1 hqR
  simpa using h2

theorem HypCoord.rootLine_all_T (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb : CoordEichlerT H S) {p q : Fin d} (hp : p ∈ S.hyp) (hq : q ∈ S.hyp) (hqp : q ≠ p)
    (hqR : (Pi.single q 1 : Fin d → K) ∈ rootLine Q H p) (c : Fin d) (hc : c ∈ S.hyp)
    (hcs : c ≠ S.star p) : (Pi.single c 1 : Fin d → K) ∈ rootLine Q H p := by
  by_cases hcp : c = p
  · subst hcp
    exact single_mem_rootLine_T S H hc
  by_cases hcq : c = q
  · subst hcq
    exact hqR
  by_cases hcsq : c = S.star q
  · obtain ⟨c', hc'mem, hc'⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({p, S.star p, q, S.star q} : Finset (Fin d))) (t := S.hyp)
      (lt_of_le_of_lt Finset.card_le_four (by have := S.card_hyp; omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'
    have hc'R := S.coord_mem_rootLine_T H hH hb hp hq hc'mem hqp hc'.2.1 hc'.2.2.1 hc'.2.2.2 hqR
    subst hcsq
    refine S.coord_mem_rootLine_T H hH hb hp hc'mem hc hc'.1 hcs (fun h => hc'.2.2.2 h.symm) ?_
      hc'R
    intro h
    exact hc'.2.2.1 (S.star_injective hq hc'mem h).symm
  · exact S.coord_mem_rootLine_T H hH hb hp hq hc hqp hcs hcq hcsq hqR

theorem HypCoord.tail_mem_rootLine_T (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb : CoordEichlerT H S) {p q t : Fin d} (hp : p ∈ S.hyp) (hq : q ∈ S.hyp) (ht : t ∉ S.hyp)
    (hqp : q ≠ p) (hqR : (Pi.single q 1 : Fin d → K) ∈ rootLine Q H p)
    (hallR : ∀ c ∈ S.hyp, c ≠ S.star p → (Pi.single c 1 : Fin d → K) ∈ rootLine Q H p) :
    (Pi.single t 1 : Fin d → K) ∈ rootLine Q H p := by
  have hsq := S.star_mem q hq
  have hcond : S.star (S.star q) ≠ t := by
    rw [S.star_star q hq]
    exact fun h => ht (h ▸ hq)
  have hh := hb _ hsq t hcond
  have hspt : S.star p ≠ t := fun h => ht (h ▸ S.star_mem p hp)
  have hp1 : eichler Q (Pi.single (S.star q) 1 : Fin d → K) (Pi.single t 1) (Pi.single p 1) =
      Pi.single p 1 := by
    rw [S.eichler_coord_T hsq hcond, S.star_star q hq, S.polar_single p hp]
    simp [single_apply_ne hqp, single_apply_ne hspt]
  have hq1 : eichler Q (Pi.single (S.star q) 1 : Fin d → K) (Pi.single t 1) (Pi.single q 1) =
      Pi.single q 1 + Pi.single t 1 - Q (Pi.single t 1) • Pi.single (S.star q) 1 := by
    rw [S.eichler_coord_T hsq hcond, S.star_star q hq, S.polar_single q hq]
    have : S.star q ≠ t := fun h => ht (h ▸ hsq)
    simp [single_apply_ne this]
  have h1 := rootLine_map H hH hh hp1 hqR
  rw [hq1] at h1
  have hsqR := hallR _ hsq (fun h => hqp (S.star_injective hq hp h))
  have h2 := Submodule.add_mem _ (Submodule.sub_mem _ h1 hqR)
    (Submodule.smul_mem _ (Q (Pi.single t 1 : Fin d → K)) hsqR)
  convert h2 using 1
  abel

theorem HypCoord.isRootCenter_coord_T (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hb : CoordEichlerT H S) {p q : Fin d} (hp : p ∈ S.hyp) (hq : q ∈ S.hyp) (hqp : q ≠ p)
    (hqR : (Pi.single q 1 : Fin d → K) ∈ rootLine Q H p) :
    IsRootCenter Q H (Pi.single p 1 : Fin d → K) := by
  refine ⟨single_ne_zero p, S.Q_single p hp, fun w hw => ?_⟩
  have hallR : ∀ c ∈ S.hyp, c ≠ S.star p → (Pi.single c 1 : Fin d → K) ∈ rootLine Q H p :=
    fun c hc hcs => S.rootLine_all_T H hH hb hp hq hqp hqR c hc hcs
  have hwR : w ∈ rootLine Q H p := by
    have hw0 : w (S.star p) = 0 := (S.polar_single p hp w).symm.trans hw
    have : w = ∑ c, w c • (Pi.single c 1 : Fin d → K) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    refine Submodule.sum_mem _ fun c _ => ?_
    by_cases hc : c = S.star p
    · subst hc
      rw [hw0, zero_smul]
      exact Submodule.zero_mem _
    · by_cases hch : c ∈ S.hyp
      · exact Submodule.smul_mem _ _ (hallR c hch hc)
      · exact Submodule.smul_mem _ _ (S.tail_mem_rootLine_T H hH hb hp hq hch hqp hqR hallR)
  simpa using hwR.2 1

theorem HypCoord.exists_move_T (hb : CoordEichlerT H S) {p j : Fin d} (hp : p ∈ S.hyp)
    (hj : j ∈ S.hyp) (hjp : j ≠ p) (hjs : j ≠ S.star p) :
    ∃ h ∈ H, h (Pi.single p 1 : Fin d → K) = Pi.single (S.star j) 1 := by
  have hsj : p ≠ S.star j := fun h => hjs (by rw [h, S.star_star j hj])
  have hsj' : S.star j ≠ p := fun h => hsj h.symm
  have hsp := S.star_mem p hp
  have hsjm := S.star_mem j hj
  have h1 : eichler Q (Pi.single (S.star p) 1 : Fin d → K) (Pi.single (S.star j) 1) ∈ H :=
    hb _ hsp _ (by rw [S.star_star p hp]; exact hsj)
  have h2 : eichler Q (Pi.single j 1 : Fin d → K) (Pi.single p 1) ∈ H := hb _ hj _ hsj'
  refine ⟨(eichler Q (Pi.single j 1 : Fin d → K) (Pi.single p 1))⁻¹ *
    eichler Q (Pi.single (S.star p) 1 : Fin d → K) (Pi.single (S.star j) 1),
    H.mul_mem (H.inv_mem h2) h1, ?_⟩
  have e1 : eichler Q (Pi.single (S.star p) 1 : Fin d → K) (Pi.single (S.star j) 1)
      (Pi.single p 1) = Pi.single p 1 + Pi.single (S.star j) 1 := by
    rw [S.eichler_coord_T hsp (by rw [S.star_star p hp]; exact hsj), S.star_star p hp,
      S.polar_single_right hsjm, S.star_star j hj, S.Q_single _ hsjm]
    have : (Pi.single p 1 : Fin d → K) j = 0 := single_apply_ne hjp
    simp [this]
  have e2 : eichler Q (Pi.single j 1 : Fin d → K) (Pi.single p 1) (Pi.single (S.star j) 1) =
      Pi.single p 1 + Pi.single (S.star j) 1 := by
    rw [S.eichler_coord_T hj hsj.symm, S.polar_single_right hp, S.Q_single p hp]
    have : (Pi.single (S.star j) 1 : Fin d → K) (S.star p) = 0 := by
      have hne : S.star p ≠ S.star j := fun h => hjp (S.star_injective hp hj h).symm
      exact single_apply_ne hne
    simp [this]
    abel
  rw [LinearEquiv.mul_apply, e1, ← e2, ← LinearEquiv.mul_apply, inv_mul_cancel]
  rfl

theorem HypCoord.elementaryGroup_le_of_rootLine_T (hnd : (polarBilin Q).Nondegenerate)
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hb : CoordEichlerT H S) {p q : Fin d}
    (hp : p ∈ S.hyp) (hq : q ∈ S.hyp) (hqp : q ≠ p)
    (hqR : (Pi.single q 1 : Fin d → K) ∈ rootLine Q H p) : elementaryGroup Q ≤ H := by
  have he := S.isRootCenter_coord_T H hH hb hp hq hqp hqR
  obtain ⟨j, -, hj, -, hjp, hjs, -, -, -, -⟩ := S.exists_three_T hp
  obtain ⟨h₁, hh₁, e₁⟩ := S.exists_move_T H hb hp hj hjp hjs
  have hsj := S.star_mem j hj
  have hp1 : p ≠ S.star j := fun h => hjs (by rw [h, S.star_star j hj])
  obtain ⟨h₂, hh₂, e₂⟩ := S.exists_move_T H hb (p := S.star j) (j := p) hsj hp hp1
    (by rw [S.star_star j hj]; exact fun h => hjp h.symm)
  have hf : IsRootCenter Q H (Pi.single (S.star p) 1 : Fin d → K) := by
    have := he.map hH (H.mul_mem hh₂ hh₁)
    rwa [LinearEquiv.mul_apply, e₁, e₂] at this
  have hpair : polar Q (Pi.single p 1 : Fin d → K) (Pi.single (S.star p) 1) = 1 := by
    rw [S.polar_single_single hp]; simp
  exact elementaryGroup_le_of_hypPair hnd hH
    ⟨Pi.single p 1, Pi.single (S.star p) 1, S.Q_single p hp, S.Q_single _ (S.star_mem p hp),
      hpair⟩ he hf

theorem HypCoord.elementaryGroup_le_of_basic_line_T (hnd : (polarBilin Q).Nondegenerate)
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hrat : ∀ u w : Fin d → K, IsRat k u → IsRat k w → Q u = 0 → polar Q u w = 0 →
      eichler Q u w ∈ H)
    {x y : Fin d → K} (hxy : IsBasicT S x y) (hne : x ≠ y)
    (hline : ∀ t : K, eichler Q x (t • y) ∈ H) : elementaryGroup Q ≤ H := by
  have hb : CoordEichlerT H S := fun u hu v hv => hrat _ _ (isRat_single k u) (isRat_single k v)
    (S.Q_single u hu) (by rw [S.polar_single_single hu]; simp [hv])
  cases hxy with
  | single ha hb' hbs =>
    rename_i a b
    have hab : b ≠ a := fun h => hne (by rw [h])
    refine S.elementaryGroup_le_of_rootLine_T H hnd hH hb ha hb' hab ⟨?_, fun t => hline t⟩
    rw [S.polar_single_single ha]
    simp [Ne.symm hbs]
  | plane ha hj hja hjs =>
    rename_i a j
    have hsj := S.star_mem j hj
    have haj : S.star j ≠ a := fun h => hjs (by rw [← h, S.star_star j hj])
    have hE : eichler Q (Pi.single j 1 : Fin d → K) (Pi.single a 1) ∈ H := hb j hj a haj
    have hjn : S.star a ≠ S.star j := fun h => hja (S.star_injective hj ha h.symm)
    have has := S.star_mem a ha
    have e1 : eichler Q (Pi.single j 1 : Fin d → K) (Pi.single a 1) (Pi.single (S.star j) 1) =
        Pi.single a 1 + Pi.single (S.star j) 1 := by
      rw [S.eichler_coord_T hj haj, S.polar_single_right ha, S.Q_single a ha]
      have : (Pi.single (S.star j) 1 : Fin d → K) (S.star a) = 0 := single_apply_ne hjn
      simp [this]
      abel
    have e2 : eichler Q (Pi.single j 1 : Fin d → K) (Pi.single a 1) (-Pi.single (S.star a) 1) =
        Pi.single j 1 - Pi.single (S.star a) 1 := by
      rw [map_neg, S.eichler_coord_T hj haj, S.polar_single_right ha, S.Q_single a ha]
      have h1 : (Pi.single (S.star a) 1 : Fin d → K) (S.star j) = 0 := single_apply_ne hjn.symm
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
    refine S.elementaryGroup_le_of_rootLine_T H hnd hH hb hsj has hjn ⟨?_, fun t => hline' t⟩
    rw [S.polar_single_single hsj, S.star_star j hj]
    simp [hjs]
  | tail1 ha hj hja hjs ht =>
    rename_i a j t
    have hsj := S.star_mem j hj
    have hcond : S.star (S.star j) ≠ t := by
      rw [S.star_star j hj]
      exact fun h => ht (h ▸ hj)
    have hE : eichler Q (Pi.single (S.star j) 1 : Fin d → K) (Pi.single t 1) ∈ H :=
      hb _ hsj t hcond
    have hspt : S.star a ≠ t := fun h => ht (h ▸ S.star_mem a ha)
    have hjt : S.star j ≠ t := fun h => ht (h ▸ hsj)
    have e1 : eichler Q (Pi.single (S.star j) 1 : Fin d → K) (Pi.single t 1) (Pi.single a 1) =
        Pi.single a 1 := by
      rw [S.eichler_coord_T hsj hcond, S.star_star j hj, S.polar_single a ha]
      simp [single_apply_ne hja, single_apply_ne hspt]
    have e2 : eichler Q (Pi.single (S.star j) 1 : Fin d → K) (Pi.single t 1) (Pi.single j 1) =
        Pi.single j 1 + Pi.single t 1 - Q (Pi.single t 1) • Pi.single (S.star j) 1 := by
      rw [S.eichler_coord_T hsj hcond, S.star_star j hj, S.polar_single j hj]
      simp [single_apply_ne hjt]
    set E := eichler Q (Pi.single (S.star j) 1 : Fin d → K) (Pi.single t 1) with hEdef
    have hx : E⁻¹ (Pi.single a 1 : Fin d → K) = Pi.single a 1 := by
      have h : E⁻¹ (E (Pi.single a 1 : Fin d → K)) = Pi.single a 1 := by
        rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
      rwa [e1] at h
    have hy : E⁻¹ ((Pi.single j 1 : Fin d → K) + Pi.single t 1 -
        Q (Pi.single t 1) • Pi.single (S.star j) 1) = Pi.single j 1 := by
      have h : E⁻¹ (E (Pi.single j 1 : Fin d → K)) = Pi.single j 1 := by
        rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
      rwa [e2] at h
    have hline' : ∀ t' : K, eichler Q (Pi.single a 1 : Fin d → K) (t' • Pi.single j 1) ∈ H := by
      intro t'
      have h3 := eichler_conj (hH (H.inv_mem hE)) (Pi.single a 1 : Fin d → K)
        (t' • ((Pi.single j 1 : Fin d → K) + Pi.single t 1 -
          Q (Pi.single t 1) • Pi.single (S.star j) 1))
      rw [hx, map_smul, hy] at h3
      rw [← h3]
      exact H.mul_mem (H.mul_mem (H.inv_mem hE) (hline t')) (H.inv_mem (H.inv_mem hE))
    refine S.elementaryGroup_le_of_rootLine_T H hnd hH hb ha hj hja ⟨?_, fun t' => hline' t'⟩
    rw [S.polar_single_single ha]
    simp [Ne.symm hjs]

end Center

end RootPairOrth

end CFSG.LieType.SeitzGeneration
