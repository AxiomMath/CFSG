module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootLeviBase

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

namespace LeviAux

local notation "ev" j => (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)

theorem roots_A3 :
    ((ev 2) + (ev 3) ∈ rootFinset TwistTag.E6.tag) ∧
    ((ev 3) + (ev 4) ∈ rootFinset TwistTag.E6.tag) ∧
    (-(ev 2) ≠ (ev 2) + (ev 3)) ∧ (-(ev 2) ≠ -((ev 2) + (ev 3))) ∧
    (-(ev 4) ≠ (ev 3) + (ev 4)) ∧ (-(ev 4) ≠ -((ev 3) + (ev 4))) ∧
    (-(ev 4) + ((ev 2) + (ev 3)) ∉ rootFinset TwistTag.E6.tag) ∧
      (-(ev 4) ≠ (ev 2) + (ev 3)) ∧ (-(ev 4) ≠ -((ev 2) + (ev 3))) ∧
    (-(ev 2) + ((ev 3) + (ev 4)) ∉ rootFinset TwistTag.E6.tag) ∧
      (-(ev 2) ≠ (ev 3) + (ev 4)) ∧ (-(ev 2) ≠ -((ev 3) + (ev 4))) ∧
    (-(ev 2) + (ev 3) ∉ rootFinset TwistTag.E6.tag) ∧ (-(ev 2) ≠ (ev 3)) ∧ (-(ev 2) ≠ -(ev 3)) ∧
    ((ev 2) + (ev 3) + (ev 3) ∉ rootFinset TwistTag.E6.tag) ∧ ((ev 2) + (ev 3) ≠ (ev 3)) ∧
      ((ev 2) + (ev 3) ≠ -(ev 3)) := by
  decide +kernel

theorem orbitWord_two :
    TwistTag.E6.orbitWord (2 : Fin TwistTag.E6.foldedTag.rank) = [3] := by
  decide +kernel

theorem reflect_three :
    reflect TwistTag.E6.tag 3 (ev 2) = (ev 2) + (ev 3) ∧
      reflect TwistTag.E6.tag 3 (ev 4) = (ev 3) + (ev 4) := by
  decide +kernel

theorem orbitMin_one : TwistTag.E6.orbitMin (1 : Fin TwistTag.E6.foldedTag.rank) = 2 := by
  decide +kernel

theorem orbitMin_two : TwistTag.E6.orbitMin (2 : Fin TwistTag.E6.foldedTag.rank) = 3 := by
  decide +kernel

theorem card_orbit_one' :
    (TwistTag.E6.orbit (1 : Fin TwistTag.E6.foldedTag.rank)).card = 2 := by
  decide

theorem card_orbit_two' :
    (TwistTag.E6.orbit (2 : Fin TwistTag.E6.foldedTag.rank)).card = 1 := by
  decide

theorem perm_two : TwistTag.E6.perm (2 : Fin TwistTag.E6.tag.rank) = 4 := by decide

theorem comm_mul_mul {G : Type*} [Group G] {u v W Z : G} (hvW : Commute v W)
    (huZ : Commute u Z) (hur : Commute u ⁅v, Z⁆) (hWr : Commute W ⁅v, Z⁆) :
    ⁅u * v, W * Z⁆ = ⁅u, W⁆ * ⁅v, Z⁆ := by
  have hr : v * Z * v⁻¹ = ⁅v, Z⁆ * Z := by simp only [commutatorElement_def]; group
  have hp : u * W * u⁻¹ = ⁅u, W⁆ * W := by simp only [commutatorElement_def]; group
  have hvW' : v * W * v⁻¹ = W := by rw [mul_inv_eq_iff_eq_mul]; exact hvW.eq
  have huZ' : u * Z * u⁻¹ = Z := by rw [mul_inv_eq_iff_eq_mul]; exact huZ.eq
  have hur' : u * ⁅v, Z⁆ * u⁻¹ = ⁅v, Z⁆ := by rw [mul_inv_eq_iff_eq_mul]; exact hur.eq
  have hWr' : W * ⁅v, Z⁆ * W⁻¹ = ⁅v, Z⁆ := by rw [mul_inv_eq_iff_eq_mul]; exact hWr.eq
  generalize ⁅v, Z⁆ = r at *
  generalize ⁅u, W⁆ = p at *
  simp only [commutatorElement_def]
  calc u * v * (W * Z) * (u * v)⁻¹ * (W * Z)⁻¹
      = u * (v * (W * Z) * v⁻¹) * u⁻¹ * (W * Z)⁻¹ := by group
    _ = u * ((v * W * v⁻¹) * (v * Z * v⁻¹)) * u⁻¹ * (W * Z)⁻¹ := by group
    _ = u * (W * (r * Z)) * u⁻¹ * (W * Z)⁻¹ := by rw [hvW', hr]
    _ = (u * W * u⁻¹) * (u * r * u⁻¹) * (u * Z * u⁻¹) * (W * Z)⁻¹ := by group
    _ = p * W * r * Z * (W * Z)⁻¹ := by rw [hp, hur', huZ']
    _ = p * (W * r * W⁻¹) := by group
    _ = p * r := by rw [hWr']

section Even


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

omit [Finite K] in
theorem commute_pinnedX {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : IsRoot TwistTag.E6.tag β) (hne : α ≠ β)
    (hne' : α ≠ -β) (hs : ¬ IsRoot TwistTag.E6.tag (α + β)) (c d : K) :
    Commute (pinnedX TwistTag.E6.tag K α c) (pinnedX TwistTag.E6.tag K β d) :=
  commute_of_not_isRoot_add hα hβ hne hne' hs (Subgroup.subset_closure ⟨c, rfl⟩)
    (Subgroup.subset_closure ⟨d, rfl⟩)

omit [Finite K] in
theorem comm_pinnedX_of_two (h2 : (2 : K) = 0) {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : IsRoot TwistTag.E6.tag β) (hne : α ≠ β)
    (hne' : α ≠ -β) (hs : IsRoot TwistTag.E6.tag (α + β)) (c d : K) :
    ⁅pinnedX TwistTag.E6.tag K α c, pinnedX TwistTag.E6.tag K β d⁆ =
      pinnedX TwistTag.E6.tag K (α + β) (c * d) := by
  obtain ⟨hε, hF⟩ :=
    (simply_laced_root_commutator_unit TwistTag.E6.tag TwistTag.E6.isSimplyLaced hα hβ hne hne').1
      hs
  rw [hF K c d]
  have h1 : ((commConst TwistTag.E6.tag α β (1, 1) : ℤ) : K) = 1 := by
    rcases hε with h | h
    · rw [h]; simp
    · rw [h]; push_cast; linear_combination (-1 : K) * h2
  rw [h1, one_mul]

omit [Finite K] in
theorem comm_A3 (h2 : (2 : K) = 0) (x y : K) :
    ⁅yUnit TwistTag.E6.tag K 2 x * yUnit TwistTag.E6.tag K 4 y,
      canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection 2) *
        (xUnit TwistTag.E6.tag K 2 1 * xUnit TwistTag.E6.tag K 4 1) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection 2))⁻¹⁆ =
      xUnit TwistTag.E6.tag K 3 (x + y) := by
  obtain ⟨hR1, hR2, hn1, hn2, hn3, hn4, hs5, hn5, hn6, hs7, hn7, hn8, hs9, hn9, hn10, hs11, hn11,
    hn12⟩ := roots_A3
  have hW : canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection 2) *
      xUnit TwistTag.E6.tag K 2 1 *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection 2))⁻¹ =
      pinnedX TwistTag.E6.tag K ((ev 2) + (ev 3)) 1 := by
    rw [← pinnedX_single, canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ (isRoot_single _ 2) 1,
      TwistTag.orbitReflection_smul, orbitWord_two, List.foldr_cons, List.foldr_nil,
      (reflect_three).1]
  have hZ : canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection 2) *
      xUnit TwistTag.E6.tag K 4 1 *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection 2))⁻¹ =
      pinnedX TwistTag.E6.tag K ((ev 3) + (ev 4)) 1 := by
    rw [← pinnedX_single, canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ (isRoot_single _ 4) 1,
      TwistTag.orbitReflection_smul, orbitWord_two, List.foldr_cons, List.foldr_nil,
      (reflect_three).2]
  have hB : canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection 2) *
      (xUnit TwistTag.E6.tag K 2 1 * xUnit TwistTag.E6.tag K 4 1) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection 2))⁻¹ =
      pinnedX TwistTag.E6.tag K ((ev 2) + (ev 3)) 1 *
        pinnedX TwistTag.E6.tag K ((ev 3) + (ev 4)) 1 := by
    rw [← hW, ← hZ]
    group
  have e1 : -(ev 2) + ((ev 2) + (ev 3)) = ev 3 := by abel
  have e2 : -(ev 4) + ((ev 3) + (ev 4)) = ev 3 := by abel
  have hp : ⁅pinnedX TwistTag.E6.tag K (-(ev 2)) x,
      pinnedX TwistTag.E6.tag K ((ev 2) + (ev 3)) 1⁆ = pinnedX TwistTag.E6.tag K (ev 3) x := by
    rw [comm_pinnedX_of_two h2 (isRoot_neg_single _ 2) (mem_rootFinset.1 hR1) hn1 hn2
      (by rw [e1]; exact isRoot_single _ 3), e1, mul_one]
  have hr : ⁅pinnedX TwistTag.E6.tag K (-(ev 4)) y,
      pinnedX TwistTag.E6.tag K ((ev 3) + (ev 4)) 1⁆ = pinnedX TwistTag.E6.tag K (ev 3) y := by
    rw [comm_pinnedX_of_two h2 (isRoot_neg_single _ 4) (mem_rootFinset.1 hR2) hn3 hn4
      (by rw [e2]; exact isRoot_single _ 3), e2, mul_one]
  rw [hB, ← pinnedX_neg_single, ← pinnedX_neg_single, comm_mul_mul, hp, hr, ← pinnedX_add,
    pinnedX_single]
  · exact commute_pinnedX (isRoot_neg_single _ 4) (mem_rootFinset.1 hR1) hn5 hn6
      (fun h => hs5 (mem_rootFinset.2 h)) y 1
  · exact commute_pinnedX (isRoot_neg_single _ 2) (mem_rootFinset.1 hR2) hn7 hn8
      (fun h => hs7 (mem_rootFinset.2 h)) x 1
  · rw [hr]
    exact commute_pinnedX (isRoot_neg_single _ 2) (isRoot_single _ 3) hn9 hn10
      (fun h => hs9 (mem_rootFinset.2 h)) x y
  · rw [hr]
    exact commute_pinnedX (mem_rootFinset.1 hR1) (isRoot_single _ 3) hn11 hn12
      (fun h => hs11 (mem_rootFinset.2 h)) 1 y

theorem coe_yG_one (c : orbitField TwistTag.E6 K σ.toRingHom 1) :
    ((yG σ 1 c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      yUnit TwistTag.E6.tag K 2 c * yUnit TwistTag.E6.tag K 4 (σ c) := by
  rw [coe_yG, coe_orbitY]
  simp [card_orbit_one', orbitMin_one, List.range_succ, perm_two]

theorem coe_xG_one (c : orbitField TwistTag.E6 K σ.toRingHom 1) :
    ((xG σ 1 c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K 2 c * xUnit TwistTag.E6.tag K 4 (σ c) := by
  rw [coe_xG, coe_orbitX]
  simp [card_orbit_one', orbitMin_one, List.range_succ, perm_two]

theorem coe_xG_two (c : orbitField TwistTag.E6 K σ.toRingHom 2) :
    ((xG σ 2 c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K 3 c := by
  rw [coe_xG, coe_orbitX]
  simp [card_orbit_two', orbitMin_two]

theorem xG_two_eq_commutator (h2 : (2 : K) = 0)
    (c₁ : orbitField TwistTag.E6 K σ.toRingHom 1) (c₀ : orbitField TwistTag.E6 K σ.toRingHom 2)
    (hc : (c₀ : K) = c₁ + σ c₁) :
    xG σ 2 c₀ = ⁅yG σ 1 c₁, nG σ 2 * xG σ 1 1 * (nG σ 2)⁻¹⁆ := by
  apply Subtype.ext
  rw [coe_xG_two, hc, ← comm_A3 h2 (c₁ : K) (σ c₁)]
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [coe_yG_one, coe_xG_one, coe_nG]
  simp

theorem xG_a2_mem_levi_of_two (h2 : (2 : K) = 0)
    (c₁ : orbitField TwistTag.E6 K σ.toRingHom 1) (c₀ : orbitField TwistTag.E6 K σ.toRingHom 2)
    (hc : (c₀ : K) = c₁ + σ c₁) :
    xG σ 2 c₀ ∈ twE6LongRootLevi (twE6RootSubgroup K σ e6HighestRoot)
      (twE6RootSubgroup K σ (-e6HighestRoot)) := by
  rw [xG_two_eq_commutator σ h2 c₁ c₀ hc]
  have h1 : (1 : Fin TwistTag.E6.foldedTag.rank) ≠ 3 := by decide
  have h2' : (2 : Fin TwistTag.E6.foldedTag.rank) ≠ 3 := by decide
  exact Subgroup.commutator_mem_commutator (yG_mem_centralizer σ h1 c₁)
    (mul_mem (mul_mem (nG_mem_centralizer σ h2') (xG_mem_centralizer σ h1 1))
      (inv_mem (nG_mem_centralizer σ h2')))

end Even

end LeviAux

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
