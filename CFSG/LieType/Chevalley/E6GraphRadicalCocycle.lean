module

public import CFSG.LieType.Chevalley.E6GraphRadicalDetector
public import CFSG.LieType.Chevalley.E6GraphLeviIntersections
public import CFSG.LieType.Chevalley.E6GraphRadicalCoords

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphRadical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphInvolution

@[expose] def fixedWords : List (List (Fin TwistTag.E6.tag.rank)) :=
  [([3] : List (Fin 6)), ([3, 2, 4] : List (Fin 6)), ([3, 2, 4, 3] : List (Fin 6)),
    ([3, 2, 4, 0, 5] : List (Fin 6)), ([3, 2, 4, 0, 5, 3] : List (Fin 6)),
    ([3, 2, 4, 0, 5, 3, 2, 4] : List (Fin 6)), ([3, 2, 4, 0, 5, 3, 2, 4, 3] : List (Fin 6)),
    ([] : List (Fin 6))]

@[expose] def negAlpha2Word : List (Fin TwistTag.E6.tag.rank) :=
  ([1, 3, 2, 4, 3, 0, 5, 2, 4, 3, 1] : List (Fin 6))

theorem fixedWords_smul : ∀ f ∈ fixedList, ∃ ω ∈ fixedWords,
    ω.foldr (reflect TwistTag.E6.tag) f = Pi.single (e6Idx 1) 1 := by
  decide +kernel

theorem fixedWords_perm : ∀ ω ∈ fixedWords,
    (radList.map fun α => ω.foldr (reflect TwistTag.E6.tag) α).Perm radList := by
  decide +kernel

theorem fixedWords_twist : ∀ ω ∈ fixedWords, ∀ i : Fin TwistTag.E6.tag.rank,
    (ω.map TwistTag.E6.perm).foldr (reflect TwistTag.E6.tag) (Pi.single i 1) =
      ω.foldr (reflect TwistTag.E6.tag) (Pi.single i 1) := by
  decide

theorem negAlpha2Word_smul :
    (coxeterSystem TwistTag.E6.tag).wordProd negAlpha2Word • e6HighestRoot =
      -Pi.single (e6Idx 1) 1 := by
  rw [wordProd_smul]
  decide

theorem weylTwist_negAlpha2Word :
    weylTwist TwistTag.E6 ((coxeterSystem TwistTag.E6.tag).wordProd negAlpha2Word) =
      (coxeterSystem TwistTag.E6.tag).wordProd negAlpha2Word :=
  weylTwist_wordProd_eq (by decide)

theorem degOneList_trichotomy : ∀ β ∈ degOneList,
    (β ∈ pairFirsts ∧ permLattice TwistTag.E6.perm.symm β ∉ pairFirsts ∧
        permLattice TwistTag.E6.perm.symm (permLattice TwistTag.E6.perm.symm β) = β) ∨
      (β ∉ pairFirsts ∧ permLattice TwistTag.E6.perm.symm β ∈ pairFirsts) ∨
      (β ∉ pairFirsts ∧ permLattice TwistTag.E6.perm.symm β = β ∧ β ∈ fixedList) := by
  decide +kernel

theorem fixedList_facts : ∀ f ∈ fixedList, f ∈ degOneList ∧ f ∉ pairFirsts ∧
    permLattice TwistTag.E6.perm.symm f = f := by
  decide +kernel

theorem degOneList_perm_symm : ∀ β ∈ degOneList,
    permLattice TwistTag.E6.perm.symm β ∈ degOneList := by
  decide +kernel

theorem radList_perm_perm : ∀ α ∈ radList,
    permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm α) = α := by
  decide +kernel

theorem theta_facts : e6HighestRoot ∉ pairFirsts ∧
    permLattice TwistTag.E6.perm.symm e6HighestRoot = e6HighestRoot := by
  decide

@[expose] def radPrefix : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  (pairFirsts.flatMap fun β => [β, permLattice TwistTag.E6.perm β]) ++ fixedList.dropLast

theorem radList_eq : radList = radPrefix ++ [Pi.single (e6Idx 1) 1, e6HighestRoot] := by
  decide

theorem radPrefix_facts : ∀ α ∈ radPrefix ++ [e6HighestRoot], α ∈ rootFinset TwistTag.E6.tag ∧
    0 < height α ∧ ∃ i : Fin TwistTag.E6.tag.rank, i ≠ e6Idx 1 ∧ α i ≠ 0 := by
  decide +kernel

section Coords

variable {E : Type} [Field E]

theorem exists_alpha2_split
    {a : ModGL TwistTag.E6.tag E}
    (ha : a ∈ parabolicRadical TwistTag.E6.tag E setA) :
    ∃ q ∈ parabolicRadical TwistTag.E6.tag E {e6Idx 1},
      a = q * xUnit TwistTag.E6.tag E (e6Idx 1) (radCoord a (Pi.single (e6Idx 1) 1)) := by
  have hJ : ∀ α ∈ radPrefix ++ [e6HighestRoot], ∀ t : E,
      pinnedX TwistTag.E6.tag E α t ∈ parabolicRadical TwistTag.E6.tag E {e6Idx 1} := by
    intro α hα t
    obtain ⟨h1, h2, i, hi, h3⟩ := radPrefix_facts α hα
    exact pinnedX_mem_rootSpan (mem_parabolicRadicalRoots_iff.2
      ⟨mem_rootFinset.1 h1, h2, i, hi, h3⟩) t
  have hα2 : (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ) ∈ radList := by
    rw [radList_eq]
    simp
  set c := radCoord a with hc
  refine ⟨(radPrefix.map fun α => pinnedX TwistTag.E6.tag E α (c α)).prod *
    pinnedX TwistTag.E6.tag E e6HighestRoot (c e6HighestRoot), mul_mem
      (Subgroup.list_prod_mem _ fun g hg => ?_)
      (hJ _ (List.mem_append_right _ (List.mem_singleton_self _)) _), ?_⟩
  · obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hg
    exact hJ α (List.mem_append_left _ hα) _
  · conv_lhs => rw [← radCoord_spec ha]
    rw [radList_eq, List.map_append, List.prod_append, List.map_cons, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_cons, List.prod_nil, mul_one, ← pinnedX_single,
      ← hc, mul_assoc, theta_mul_comm (pinnedX_mem_parabolicRadical hα2 _) (c e6HighestRoot)]

theorem diagramMap_mul_self' :
    diagramMap TwistTag.E6 E * diagramMap TwistTag.E6 E = 1 :=
  diagramMap_E6_mul_self

theorem sq_mul_diagramMap'
    (a : ModGL TwistTag.E6.tag E) :
    (a * diagramMap TwistTag.E6 E) ^ 2 =
      a * (diagramMap TwistTag.E6 E * a * (diagramMap TwistTag.E6 E)⁻¹) := by
  have hPinv : (diagramMap TwistTag.E6 E)⁻¹ = diagramMap TwistTag.E6 E :=
    (eq_inv_of_mul_eq_one_left diagramMap_mul_self').symm
  rw [sq, hPinv]
  calc a * diagramMap TwistTag.E6 E * (a * diagramMap TwistTag.E6 E) =
        a * (diagramMap TwistTag.E6 E * a * diagramMap TwistTag.E6 E) *
          (diagramMap TwistTag.E6 E * diagramMap TwistTag.E6 E) := by
        rw [diagramMap_mul_self', mul_one]
        group
    _ = _ := by rw [diagramMap_mul_self', mul_one]

theorem radCoord_invariant_of_sq
    (h2 : (2 : E) = 0) {a : ModGL TwistTag.E6.tag E}
    (ha : a ∈ parabolicRadical TwistTag.E6.tag E setA)
    (hsq : (a * diagramMap TwistTag.E6 E) ^ 2 = 1) :
    ∀ β ∈ degOneList, radCoord a (permLattice TwistTag.E6.perm.symm β) = radCoord a β := by
  rw [sq_mul_diagramMap'] at hsq
  obtain ⟨hP, hPc⟩ := radCoord_diagramMap_conj h2 ha
  intro β hβ
  have h := radCoord_mul h2 ha hP β hβ
  rw [hsq, radCoord_one β hβ, hPc β hβ] at h
  linear_combination -h - radCoord a β * h2

theorem radCoord_clear
    (h2 : (2 : E) = 0) {a x : ModGL TwistTag.E6.tag E}
    (ha : a ∈ parabolicRadical TwistTag.E6.tag E setA)
    (hx : x ∈ parabolicRadical TwistTag.E6.tag E setA) :
    x * a * (diagramMap TwistTag.E6 E * x * (diagramMap TwistTag.E6 E)⁻¹)⁻¹ ∈
        parabolicRadical TwistTag.E6.tag E setA ∧
      ∀ β ∈ degOneList,
        radCoord (x * a * (diagramMap TwistTag.E6 E * x * (diagramMap TwistTag.E6 E)⁻¹)⁻¹) β =
          radCoord x β + radCoord a β - radCoord x (permLattice TwistTag.E6.perm.symm β) := by
  obtain ⟨hP, hPc⟩ := radCoord_diagramMap_conj h2 hx
  refine ⟨mul_mem (mul_mem hx ha) (inv_mem hP), fun β hβ => ?_⟩
  rw [radCoord_mul h2 (mul_mem hx ha) (inv_mem hP) β hβ, radCoord_mul h2 hx ha β hβ,
    radCoord_inv h2 hP β hβ, hPc β hβ]
  ring

theorem conj_mul_diagramMap (a x : ModGL TwistTag.E6.tag E) :
    x * (a * diagramMap TwistTag.E6 E) * x⁻¹ =
      x * a * (diagramMap TwistTag.E6 E * x * (diagramMap TwistTag.E6 E)⁻¹)⁻¹ *
        diagramMap TwistTag.E6 E := by
  group

end Coords

section Clear

variable {E : Type} [Field E]

theorem exists_clear_ordinary
    (h2 : (2 : E) = 0) {a : ModGL TwistTag.E6.tag E}
    (ha : a ∈ parabolicRadical TwistTag.E6.tag E setA)
    (hsq : (a * diagramMap TwistTag.E6 E) ^ 2 = 1) :
    ∃ x ∈ parabolicRadical TwistTag.E6.tag E setA, ∀ β ∈ degOneList,
      radCoord (x * a * (diagramMap TwistTag.E6 E * x * (diagramMap TwistTag.E6 E)⁻¹)⁻¹) β =
        if β ∈ fixedList then radCoord a β else 0 := by
  classical
  set c := radCoord a with hc
  set D : (Fin TwistTag.E6.tag.rank → ℤ) → E := fun β => if β ∈ pairFirsts then c β else 0
    with hD
  set x := (radList.map fun α => pinnedX TwistTag.E6.tag E α (D α)).prod with hxdef
  have hx : x ∈ parabolicRadical TwistTag.E6.tag E setA :=
    list_prod_mem_parabolicRadical (List.Subset.refl _) D
  have hxc : ∀ β ∈ degOneList, radCoord x β = D β := fun β hβ =>
    (radCoord_eq_of_mul hx (by rw [pinnedX_zero, mul_one]) β hβ).symm
  have hinv := radCoord_invariant_of_sq h2 ha hsq
  refine ⟨x, hx, fun β hβ => ?_⟩
  rw [(radCoord_clear h2 ha hx).2 β hβ, hxc β hβ, hxc _ (degOneList_perm_symm β hβ)]
  rcases degOneList_trichotomy β hβ with ⟨h1, h2', -⟩ | ⟨h1, h2'⟩ | ⟨h1, h2', h3⟩
  · have hnf : β ∉ fixedList := fun h => (fixedList_facts β h).2.1 h1
    simp only [hD, h1, h2', hnf, ↓reduceIte]
    linear_combination c β * h2
  · have hnf : β ∉ fixedList := fun h => by
      have := (fixedList_facts β h).2
      rw [this.2] at h2'
      exact this.1 h2'
    simp only [hD, h1, h2', hnf, ↓reduceIte]
    have hinv' : c (permLattice TwistTag.E6.perm.symm β) = c β := hinv β hβ
    rw [hinv']
    ring
  · simp only [hD, h1, h2', h3, ↓reduceIte]
    ring

theorem twistHom_pinnedX_of_two
    (h2 : (2 : E) = 0) (σ : E →+* E)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (d : E) :
    twistHom TwistTag.E6 E σ (pinnedX TwistTag.E6.tag E α d) =
      pinnedX TwistTag.E6.tag E (permLattice TwistTag.E6.perm α) (σ d) := by
  rw [twistHom_apply, units_map_entrywiseHom_pinnedX', diagramMap_conj_pinnedX_of_two h2 hα]

theorem exists_fixed_lift
    (h2 : (2 : E) = 0) {σ : E →+* E} (hσσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ s, s + σ s = a) {D : (Fin TwistTag.E6.tag.rank → ℤ) → E}
    (hD : ∀ β ∈ degOneList, σ (D (permLattice TwistTag.E6.perm.symm β)) = D β)
    (hDθ : D e6HighestRoot = 0) :
    ∃ x ∈ parabolicRadical TwistTag.E6.tag E setA, twistHom TwistTag.E6 E σ x = x ∧
      ∀ β ∈ degOneList, radCoord x β = D β := by
  set xD := (radList.map fun α => pinnedX TwistTag.E6.tag E α (D α)).prod with hxD
  have hxDm : xD ∈ parabolicRadical TwistTag.E6.tag E setA :=
    list_prod_mem_parabolicRadical (List.Subset.refl _) D
  have hθr := (radList_pos (List.mem_append_right _ (List.mem_singleton_self e6HighestRoot))).1
  have hF1 : twistHom TwistTag.E6 E σ xD = (radList.map fun α =>
      pinnedX TwistTag.E6.tag E (permLattice TwistTag.E6.perm α) (σ (D α))).prod := by
    rw [hxD, map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun α hα => by
      simp only [Function.comp_apply]
      exact twistHom_pinnedX_of_two h2 σ (radList_pos hα).1 _)
  have hF2 : (radList.map fun α =>
      pinnedX TwistTag.E6.tag E (permLattice TwistTag.E6.perm α) (σ (D α))) =
      (radList.map (permLattice TwistTag.E6.perm)).map fun β =>
        pinnedX TwistTag.E6.tag E β (σ (D (permLattice TwistTag.E6.perm.symm β))) := by
    rw [List.map_map]
    exact List.map_congr_left fun α _ => by
      simp only [Function.comp_apply, permLattice_symm_permLattice]
  obtain ⟨e, he⟩ := list_prod_perm_eq_mul h2 radList_perm_permLattice
    (fun x hx => radList_perm_permLattice.subset hx)
    (fun β => σ (D (permLattice TwistTag.E6.perm.symm β)))
  have hcoef : (radList.map fun β =>
      pinnedX TwistTag.E6.tag E β (σ (D (permLattice TwistTag.E6.perm.symm β)))) =
      radList.map fun β => pinnedX TwistTag.E6.tag E β (D β) :=
    List.map_congr_left fun β hβ => by
      rcases List.mem_append.1 hβ with hβ' | hβ'
      · rw [hD β hβ']
      · rw [List.mem_singleton.1 hβ', theta_facts.2, hDθ, map_zero]
  have hFx : twistHom TwistTag.E6 E σ xD = xD * pinnedX TwistTag.E6.tag E e6HighestRoot e := by
    rw [hF1, hF2, he, hcoef]
  have hFF : ∀ y ∈ radList, ∀ d : E, twistHom TwistTag.E6 E σ
      (twistHom TwistTag.E6 E σ (pinnedX TwistTag.E6.tag E y d)) =
        pinnedX TwistTag.E6.tag E y d := fun y hy d => by
    rw [twistHom_pinnedX_of_two h2 σ (radList_pos hy).1, twistHom_pinnedX_of_two h2 σ
      ((radList_pos hy).1.permLattice TwistTag.E6.cartan_perm), radList_perm_perm y hy, hσσ]
  have hFFx : twistHom TwistTag.E6 E σ (twistHom TwistTag.E6 E σ xD) = xD := by
    rw [hxD, map_list_prod, map_list_prod, List.map_map, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun α hα => hFF α hα _)
  have hσe : σ e = e := by
    rw [hFx, map_mul, hFx, twistHom_pinnedX_of_two h2 σ hθr, permLattice_e6HighestRoot,
      mul_assoc, ← pinnedX_add] at hFFx
    have h1 : pinnedX TwistTag.E6.tag E e6HighestRoot (e + σ e) = 1 :=
      mul_left_cancel (hFFx.trans (mul_one xD).symm)
    have h0 := pinnedX_injective (τ := TwistTag.E6.tag) (R := E) e6HighestRoot
      (h1.trans (pinnedX_zero _ _ _).symm)
    linear_combination h0 - e * h2
  obtain ⟨s, hs⟩ := htr e hσe
  refine ⟨xD * pinnedX TwistTag.E6.tag E e6HighestRoot s,
    mul_mem hxDm (pinnedX_mem_parabolicRadical (List.mem_append_right _
      (List.mem_singleton_self _)) s), ?_, fun β hβ =>
      (radCoord_eq_of_mul (mul_mem hxDm (pinnedX_mem_parabolicRadical (List.mem_append_right _
        (List.mem_singleton_self _)) s)) rfl β hβ).symm⟩
  rw [map_mul, hFx, twistHom_pinnedX_of_two h2 σ hθr, permLattice_e6HighestRoot, mul_assoc,
    ← pinnedX_add]
  congr 2
  linear_combination -hs + σ s * h2

theorem exists_clear_twisted
    (h2 : (2 : E) = 0) {σ : E →+* E} (hσσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ s, s + σ s = a) {a : ModGL TwistTag.E6.tag E}
    (ha : a ∈ parabolicRadical TwistTag.E6.tag E setA) (hFa : twistHom TwistTag.E6 E σ a = a)
    (hsq : (a * diagramMap TwistTag.E6 E) ^ 2 = 1) :
    ∃ x ∈ parabolicRadical TwistTag.E6.tag E setA, twistHom TwistTag.E6 E σ x = x ∧
      ∀ β ∈ degOneList,
        radCoord (x * a * (diagramMap TwistTag.E6 E * x * (diagramMap TwistTag.E6 E)⁻¹)⁻¹) β =
          if β ∈ fixedList then radCoord a β else 0 := by
  classical
  have hinv := radCoord_invariant_of_sq h2 ha hsq
  have hFc : ∀ β ∈ degOneList,
      radCoord a β = σ (radCoord a (permLattice TwistTag.E6.perm.symm β)) := by
    intro β hβ
    have := (radCoord_twistHom h2 σ ha).2 β hβ
    rwa [hFa] at this
  have hfix : ∀ β ∈ degOneList, σ (radCoord a β) = radCoord a β := by
    intro β hβ
    calc σ (radCoord a β) = σ (radCoord a (permLattice TwistTag.E6.perm.symm β)) := by
          rw [hinv β hβ]
      _ = radCoord a β := (hFc β hβ).symm
  have hex : ∀ β, ∃ d : E, β ∈ degOneList → d + σ d = radCoord a β := by
    intro β
    by_cases hβ : β ∈ degOneList
    · obtain ⟨d, hd⟩ := htr _ (hfix β hβ)
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hβ⟩
  choose d₀ hd₀spec using hex
  set D : (Fin TwistTag.E6.tag.rank → ℤ) → E := fun β =>
    if β ∈ pairFirsts then d₀ β else
      if permLattice TwistTag.E6.perm.symm β ∈ pairFirsts then
        σ (d₀ (permLattice TwistTag.E6.perm.symm β)) else 0 with hD
  have hDσ : ∀ β ∈ degOneList, σ (D (permLattice TwistTag.E6.perm.symm β)) = D β := by
    intro β hβ
    rcases degOneList_trichotomy β hβ with ⟨h1, h2', h3⟩ | ⟨h1, h2'⟩ | ⟨h1, h2', -⟩
    · simp only [hD, h2', h3, h1, hσσ, ↓reduceIte]
    · simp only [hD, h2', h1, ↓reduceIte]
    · simp only [hD, h2', h1, map_zero, ↓reduceIte]
  have hDθ : D e6HighestRoot = 0 := by
    simp only [hD, theta_facts.1, theta_facts.2, ↓reduceIte]
  obtain ⟨x, hx, hFx, hxc⟩ := exists_fixed_lift h2 hσσ htr hDσ hDθ
  refine ⟨x, hx, hFx, fun β hβ => ?_⟩
  rw [(radCoord_clear h2 ha hx).2 β hβ, hxc β hβ, hxc _ (degOneList_perm_symm β hβ)]
  rcases degOneList_trichotomy β hβ with ⟨h1, h2', h3⟩ | ⟨h1, h2'⟩ | ⟨h1, h2', h3⟩
  · have hnf : β ∉ fixedList := fun h => (fixedList_facts β h).2.1 h1
    simp only [hD, h1, h2', h3, hnf, ↓reduceIte]
    have := hd₀spec β hβ
    linear_combination -this + d₀ β * h2
  · have hnf : β ∉ fixedList := fun h => by
      have := (fixedList_facts β h).2
      rw [this.2] at h2'
      exact this.1 h2'
    simp only [hD, h1, h2', hnf, ↓reduceIte]
    have := hd₀spec _ (degOneList_perm_symm β hβ)
    rw [← hinv β hβ]
    linear_combination -this + (σ (d₀ (permLattice TwistTag.E6.perm.symm β))) * h2
  · simp only [hD, h1, h2', h3, ↓reduceIte]
    ring

end Clear

section Cases

variable {E : Type} [Field E]

theorem twistHom_diagramMap' (σ : E →+* E) :
    twistHom TwistTag.E6 E σ (diagramMap TwistTag.E6 E) = diagramMap TwistTag.E6 E := by
  rw [twistHom_apply, units_map_entrywiseHom_diagramMap, mul_inv_cancel_right]

theorem twistHom_clear (σ : E →+* E) {a x : ModGL TwistTag.E6.tag E}
    (hFa : twistHom TwistTag.E6 E σ a = a) (hFx : twistHom TwistTag.E6 E σ x = x) :
    twistHom TwistTag.E6 E σ
        (x * a * (diagramMap TwistTag.E6 E * x * (diagramMap TwistTag.E6 E)⁻¹)⁻¹) =
      x * a * (diagramMap TwistTag.E6 E * x * (diagramMap TwistTag.E6 E)⁻¹)⁻¹ := by
  rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, twistHom_diagramMap', hFa, hFx]

theorem thetaRankOneGroup_le_adjointGroup
    {F₀ : Type} [Field F₀] (ι : F₀ →+* E) :
    thetaRankOneGroup ι ≤ adjointGroup TwistTag.E6.tag E :=
  sup_le ((Subgroup.closure_le _).2 (Set.range_subset_iff.2 fun _ =>
      pinnedX_mem_adjointGroup _ _))
    ((Subgroup.closure_le _).2 (Set.range_subset_iff.2 fun _ => pinnedX_mem_adjointGroup _ _))

theorem rootTorusSL2_conj_theta_mul_diagramMap
    (h2 : (2 : E) = 0) (b : Eˣ) {e : E}
    (hb : (b : E) ^ 2 * e = 1) :
    rootTorusSL2 TwistTag.E6.tag E e6HighestRoot b *
        (pinnedX TwistTag.E6.tag E e6HighestRoot e * diagramMap TwistTag.E6 E) *
        (rootTorusSL2 TwistTag.E6.tag E e6HighestRoot b)⁻¹ =
      pinnedX TwistTag.E6.tag E e6HighestRoot 1 * diagramMap TwistTag.E6 E := by
  have hP : diagramMap TwistTag.E6 E * rootTorusSL2 TwistTag.E6.tag E e6HighestRoot b *
      (diagramMap TwistTag.E6 E)⁻¹ = rootTorusSL2 TwistTag.E6.tag E e6HighestRoot b := by
    rw [← thetaTorusHom_apply, thetaTorusHom_eq_thetaSL2, diagramMap_conj_thetaSL2 h2]
  calc rootTorusSL2 TwistTag.E6.tag E e6HighestRoot b *
        (pinnedX TwistTag.E6.tag E e6HighestRoot e * diagramMap TwistTag.E6 E) *
        (rootTorusSL2 TwistTag.E6.tag E e6HighestRoot b)⁻¹ =
        (rootTorusSL2 TwistTag.E6.tag E e6HighestRoot b *
          pinnedX TwistTag.E6.tag E e6HighestRoot e *
          (rootTorusSL2 TwistTag.E6.tag E e6HighestRoot b)⁻¹) *
          ((diagramMap TwistTag.E6 E * rootTorusSL2 TwistTag.E6.tag E e6HighestRoot b *
            (diagramMap TwistTag.E6 E)⁻¹) *
              (rootTorusSL2 TwistTag.E6.tag E e6HighestRoot b)⁻¹)⁻¹ *
          diagramMap TwistTag.E6 E := by group
    _ = _ := by rw [hP, mul_inv_cancel, inv_one, mul_one, rootTorusSL2_conj_pinnedX h2, hb]

theorem theta_case
    (h2 : (2 : E) = 0) {F₀ : Type} [Field F₀] [Finite F₀] (ι : F₀ →+* E)
    (e : F₀) :
    e = 0 ∨ ∃ h ∈ thetaTorus ι,
      h * (pinnedX TwistTag.E6.tag E e6HighestRoot (ι e) * diagramMap TwistTag.E6 E) * h⁻¹ =
        pinnedX TwistTag.E6.tag E e6HighestRoot 1 * diagramMap TwistTag.E6 E := by
  by_cases he : e = 0
  · exact Or.inl he
  right
  have h2' : (2 : F₀) = 0 := (map_eq_zero_iff ι ι.injective).1 (by rw [map_ofNat]; exact h2)
  obtain ⟨b, hb⟩ := exists_sq_eq_of_two h2' (Units.mk0 e he)⁻¹
  refine ⟨rootTorusSL2 TwistTag.E6.tag E e6HighestRoot (Units.map ι.toMonoidHom b),
    (mem_thetaTorus ι).2 ⟨b, rfl⟩, rootTorusSL2_conj_theta_mul_diagramMap h2 _ ?_⟩
  have hb' : (b : F₀) ^ 2 * e = 1 := by
    have := congrArg (fun u : F₀ˣ => (u : F₀)) hb
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0] at this
    rw [this, inv_mul_cancel₀ he]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  rw [← map_pow, ← map_mul, hb', map_one]

theorem diagramMap_conj_yUnit_alpha2
    (h2 : (2 : E) = 0) (c : E) :
    diagramMap TwistTag.E6 E * yUnit TwistTag.E6.tag E (e6Idx 1) c *
        (diagramMap TwistTag.E6 E)⁻¹ = yUnit TwistTag.E6.tag E (e6Idx 1) c := by
  have hρ : permLattice TwistTag.E6.perm
      (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single (e6Idx 1) 1 := by
    decide
  rw [← pinnedX_neg_single, ← twistHom_id_eq, twistHom_id_pinnedX h2 (isRoot_neg_single _ _),
    permLattice_neg, hρ]

theorem wordElt_negAlpha2Word_conj
    (h2 : (2 : E) = 0) (c : E) :
    wordElt E negAlpha2Word * pinnedX TwistTag.E6.tag E e6HighestRoot c *
        (wordElt E negAlpha2Word)⁻¹ = yUnit TwistTag.E6.tag E (e6Idx 1) c := by
  rw [wordElt_conj_pinnedX h2 negAlpha2Word isRoot_e6HighestRoot, negAlpha2Word_smul,
    pinnedX_neg_single]

theorem detector_case
    (h2 : (2 : E) = 0) {F₀ : Type} [Field F₀] (ι : F₀ →+* E)
    {a : ModGL TwistTag.E6.tag E} (ha : a ∈ parabolicRadical TwistTag.E6.tag E setA)
    {f : Fin TwistTag.E6.tag.rank → ℤ} (hf : f ∈ fixedList) (hc : radCoord a f ≠ 0)
    {z j : ModGL TwistTag.E6.tag E} (hj : z * j * z⁻¹ = a * diagramMap TwistTag.E6 E) :
    ∃ ω ∈ fixedWords, ¬ IsPGroup 2 ↥((thetaRootGroup ι).map (MulAut.conj
        (z⁻¹ * (wordElt E ω)⁻¹ * wordElt E negAlpha2Word)).toMonoidHom ⊔
      ((thetaRootGroup ι).map (MulAut.conj
        (z⁻¹ * (wordElt E ω)⁻¹ * wordElt E negAlpha2Word)).toMonoidHom).map
          (MulAut.conj j).toMonoidHom) := by
  obtain ⟨ω, hω, hωf⟩ := fixedWords_smul f hf
  refine ⟨ω, hω, ?_⟩
  have hperm : (radList.map fun α =>
      (coxeterSystem TwistTag.E6.tag).wordProd ω • α).Perm radList := by
    simp only [wordProd_smul]
    exact fixedWords_perm ω hω
  obtain ⟨ha', hc'⟩ := radCoord_wordElt_conj h2 ω hperm ha
  have hα2 : (Pi.single (e6Idx 1) 1 : Fin TwistTag.E6.tag.rank → ℤ) ∈ degOneList := by decide
  have hcf : radCoord (wordElt E ω * a * (wordElt E ω)⁻¹) (Pi.single (e6Idx 1) 1) =
      radCoord a f := by
    rw [hc' _ hα2]
    congr 1
    rw [inv_smul_eq_iff, wordProd_smul, hωf]
  obtain ⟨q, hq, hqa⟩ := exists_alpha2_split ha'
  rw [hcf] at hqa
  have hnP : diagramMap TwistTag.E6 E * wordElt E ω * (diagramMap TwistTag.E6 E)⁻¹ =
      wordElt E ω :=
    diagramMap_conj_wordElt h2 (weylTwist_wordProd_eq (fixedWords_twist ω hω))
  have hnP' : (wordElt E ω)⁻¹ * diagramMap TwistTag.E6 E * wordElt E ω =
      diagramMap TwistTag.E6 E := by
    calc (wordElt E ω)⁻¹ * diagramMap TwistTag.E6 E * wordElt E ω =
          (wordElt E ω)⁻¹ * (diagramMap TwistTag.E6 E * wordElt E ω *
            (diagramMap TwistTag.E6 E)⁻¹) * diagramMap TwistTag.E6 E := by group
      _ = _ := by rw [hnP]; group
  have hj' : j = (wordElt E ω * z)⁻¹ * (wordElt E ω * a * (wordElt E ω)⁻¹ *
      diagramMap TwistTag.E6 E) * (wordElt E ω * z) := by
    calc j = z⁻¹ * (z * j * z⁻¹) * z := by group
      _ = z⁻¹ * (a * ((wordElt E ω)⁻¹ * diagramMap TwistTag.E6 E * wordElt E ω)) * z := by
          rw [hj, hnP']
      _ = _ := by group
  rw [hqa] at hj'
  have hr : (wordElt E ω * z)⁻¹ * yUnit TwistTag.E6.tag E (e6Idx 1) 1 * (wordElt E ω * z) ∈
      (thetaRootGroup ι).map (MulAut.conj
        (z⁻¹ * (wordElt E ω)⁻¹ * wordElt E negAlpha2Word)).toMonoidHom := by
    refine ⟨pinnedX TwistTag.E6.tag E e6HighestRoot (ι 1), (mem_thetaRootGroup ι).2 ⟨1, rfl⟩, ?_⟩
    rw [map_one, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← wordElt_negAlpha2Word_conj h2]
    group
  refine not_isPGroup_two_of_detector h2 hq hc (wordElt E ω * z) (Subgroup.mem_sup_left hr)
    (Subgroup.mem_sup_right ⟨_, hr, ?_⟩)
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hj']
  calc (wordElt E ω * z)⁻¹ * (q * xUnit TwistTag.E6.tag E (e6Idx 1) (radCoord a f) *
          diagramMap TwistTag.E6 E) * (wordElt E ω * z) *
        ((wordElt E ω * z)⁻¹ * yUnit TwistTag.E6.tag E (e6Idx 1) 1 * (wordElt E ω * z)) *
        ((wordElt E ω * z)⁻¹ * (q * xUnit TwistTag.E6.tag E (e6Idx 1) (radCoord a f) *
          diagramMap TwistTag.E6 E) * (wordElt E ω * z))⁻¹ =
        (wordElt E ω * z)⁻¹ * (q * xUnit TwistTag.E6.tag E (e6Idx 1) (radCoord a f) *
          (diagramMap TwistTag.E6 E * yUnit TwistTag.E6.tag E (e6Idx 1) 1 *
            (diagramMap TwistTag.E6 E)⁻¹) *
          (q * xUnit TwistTag.E6.tag E (e6Idx 1) (radCoord a f))⁻¹) * (wordElt E ω * z) := by
        group
    _ = _ := by rw [diagramMap_conj_yUnit_alpha2 h2]

end Cases

section Reduction

variable {k K : Type} [Field k] [Field K]

theorem ordinary_reduction
    [Finite k] (h2 : (2 : k) = 0) {a : ModGL TwistTag.E6.tag k}
    (ha : a ∈ parabolicRadical TwistTag.E6.tag k setA)
    (hsq : (a * diagramMap TwistTag.E6 k) ^ 2 = 1) :
    (∃ g ∈ adjointGroup TwistTag.E6.tag k,
        g * (a * diagramMap TwistTag.E6 k) * g⁻¹ = diagramMap TwistTag.E6 k) ∨
      (∃ g ∈ adjointGroup TwistTag.E6.tag k,
        g * (a * diagramMap TwistTag.E6 k) * g⁻¹ =
          pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k) ∨
      ∃ g ∈ adjointGroup TwistTag.E6.tag k,
        ¬ IsPGroup 2 ↥((thetaRootGroup (RingHom.id k)).map (MulAut.conj g).toMonoidHom ⊔
          ((thetaRootGroup (RingHom.id k)).map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj (a * diagramMap TwistTag.E6 k)).toMonoidHom) := by
  classical
  obtain ⟨x, hx, hxc⟩ := exists_clear_ordinary h2 ha hsq
  have hxG : x ∈ adjointGroup TwistTag.E6.tag k := rootSpan_le_adjointGroup k _ hx
  have hj := conj_mul_diagramMap a x
  have ha' := (radCoord_clear h2 ha hx).1
  by_cases hall : ∀ f ∈ fixedList, radCoord a f = 0
  · have h0 : ∀ β ∈ degOneList, radCoord
        (x * a * (diagramMap TwistTag.E6 k * x * (diagramMap TwistTag.E6 k)⁻¹)⁻¹) β = 0 := by
      intro β hβ
      rw [hxc β hβ]
      split_ifs with hβf
      · exact hall β hβf
      · rfl
    obtain ⟨e, he⟩ : ∃ e : k,
        x * a * (diagramMap TwistTag.E6 k * x * (diagramMap TwistTag.E6 k)⁻¹)⁻¹ =
          pinnedX TwistTag.E6.tag k e6HighestRoot e :=
      ⟨_, eq_pinnedX_theta_of_radCoord ha' h0⟩
    rw [he] at hj
    rcases theta_case h2 (RingHom.id k) e with he0 | ⟨h, hh, hhe⟩
    · refine Or.inl ⟨x, hxG, ?_⟩
      rw [hj, he0, pinnedX_zero, one_mul]
    · refine Or.inr (Or.inl ⟨h * x, mul_mem (thetaRankOneGroup_le_adjointGroup _
        (thetaTorus_le_thetaRankOneGroup h2 _ hh)) hxG, ?_⟩)
      rw [show h * x * (a * diagramMap TwistTag.E6 k) * (h * x)⁻¹ =
        h * (x * (a * diagramMap TwistTag.E6 k) * x⁻¹) * h⁻¹ by group, hj]
      exact hhe
  · push Not at hall
    obtain ⟨f, hf, hcf⟩ := hall
    have hcf' : radCoord
        (x * a * (diagramMap TwistTag.E6 k * x * (diagramMap TwistTag.E6 k)⁻¹)⁻¹) f ≠ 0 := by
      have := hxc f (fixedList_facts f hf).1
      simp only [hf, ↓reduceIte] at this
      rw [this]
      exact hcf
    obtain ⟨ω, -, hnot⟩ := detector_case h2 (RingHom.id k) ha' hf hcf' hj
    exact Or.inr (Or.inr ⟨_, mul_mem (mul_mem (inv_mem hxG)
      (inv_mem (wordElt_mem_adjointGroup ω))) (wordElt_mem_adjointGroup _), hnot⟩)

variable [Algebra k K]

theorem twisted_reduction
    [Finite k] (h2 : (2 : K) = 0) {σ : K →+* K}
    (hσk : ∀ c, σ c = c ^ Nat.card k) (hσσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ s, s + σ s = a) {a : ModGL TwistTag.E6.tag K}
    (ha : a ∈ parabolicRadical TwistTag.E6.tag K setA)
    (haG : a ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (hsq : (a * diagramMap TwistTag.E6 K) ^ 2 = 1) :
    (∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
        g * (a * diagramMap TwistTag.E6 K) * g⁻¹ = diagramMap TwistTag.E6 K) ∨
      (∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
        g * (a * diagramMap TwistTag.E6 K) * g⁻¹ =
          pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K) ∨
      ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
        ¬ IsPGroup 2 ↥((thetaRootGroup (algebraMap k K)).map (MulAut.conj g).toMonoidHom ⊔
          ((thetaRootGroup (algebraMap k K)).map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj (a * diagramMap TwistTag.E6 K)).toMonoidHom) := by
  classical
  have hFa : twistHom TwistTag.E6 K σ a = a :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ haG)).2
  obtain ⟨x, hx, hFx, hxc⟩ := exists_clear_twisted h2 hσσ htr ha hFa hsq
  have hxG : x ∈ graphFixedRootGroup TwistTag.E6 K σ :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2
      ⟨parabolicRadical_le_posUnipotent _ hx, (mem_twistedFixedGroup_iff_twistHom _ _ _).2
        ⟨rootSpan_le_adjointGroup K _ hx, hFx⟩⟩)
  have hj := conj_mul_diagramMap a x
  have ha' := (radCoord_clear h2 ha hx).1
  have hFa' := twistHom_clear σ hFa hFx
  by_cases hall : ∀ f ∈ fixedList, radCoord a f = 0
  · have h0 : ∀ β ∈ degOneList, radCoord
        (x * a * (diagramMap TwistTag.E6 K * x * (diagramMap TwistTag.E6 K)⁻¹)⁻¹) β = 0 := by
      intro β hβ
      rw [hxc β hβ]
      split_ifs with hβf
      · exact hall β hβf
      · rfl
    obtain ⟨e, he⟩ : ∃ e : K,
        x * a * (diagramMap TwistTag.E6 K * x * (diagramMap TwistTag.E6 K)⁻¹)⁻¹ =
          pinnedX TwistTag.E6.tag K e6HighestRoot e :=
      ⟨_, eq_pinnedX_theta_of_radCoord ha' h0⟩
    rw [he] at hj hFa'
    rw [twistHom_pinnedX_of_two h2 σ isRoot_e6HighestRoot, permLattice_e6HighestRoot] at hFa'
    have hσe : σ e = e := pinnedX_injective (τ := TwistTag.E6.tag) (R := K) e6HighestRoot hFa'
    obtain ⟨e', rfl⟩ := mem_range_algebraMap_of_pow_card_eq (k := k) (c := e)
      (by rw [← hσk]; exact hσe)
    rcases theta_case h2 (algebraMap k K) e' with he0 | ⟨h, hh, hhe⟩
    · refine Or.inl ⟨x, hxG, ?_⟩
      rw [hj, he0, map_zero, pinnedX_zero, one_mul]
    · refine Or.inr (Or.inl ⟨h * x, mul_mem (thetaRankOneGroup_le_graphFixedRootGroup h2 hσk
        (thetaTorus_le_thetaRankOneGroup h2 _ hh)) hxG, ?_⟩)
      rw [show h * x * (a * diagramMap TwistTag.E6 K) * (h * x)⁻¹ =
        h * (x * (a * diagramMap TwistTag.E6 K) * x⁻¹) * h⁻¹ by group, hj]
      exact hhe
  · push Not at hall
    obtain ⟨f, hf, hcf⟩ := hall
    have hcf' : radCoord
        (x * a * (diagramMap TwistTag.E6 K * x * (diagramMap TwistTag.E6 K)⁻¹)⁻¹) f ≠ 0 := by
      have := hxc f (fixedList_facts f hf).1
      simp only [hf, ↓reduceIte] at this
      rw [this]
      exact hcf
    obtain ⟨ω, hω, hnot⟩ := detector_case h2 (algebraMap k K) ha' hf hcf' hj
    exact Or.inr (Or.inr ⟨_, mul_mem (mul_mem (inv_mem hxG)
      (inv_mem (wordElt_mem_graphFixedRootGroup h2
        (weylTwist_wordProd_eq (fixedWords_twist ω hω)))))
      (wordElt_mem_graphFixedRootGroup h2 weylTwist_negAlpha2Word), hnot⟩)

end Reduction

theorem _root_.CFSG.LieType.Chevalley.even_E6_graph_radical_cocycle_reduction
    (f : ℕ)
    (hf : 1 ≤ f) (k K : Type) [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (∀ a ∈ parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k,
      (a * diagramMap TwistTag.E6 k) ^ 2 = 1 →
      (∃ g ∈ adjointGroup TwistTag.E6.tag k,
          g * (a * diagramMap TwistTag.E6 k) * g⁻¹ = diagramMap TwistTag.E6 k) ∨
        (∃ g ∈ adjointGroup TwistTag.E6.tag k,
          g * (a * diagramMap TwistTag.E6 k) * g⁻¹ =
            pinnedX TwistTag.E6.tag k e6HighestRoot 1 * diagramMap TwistTag.E6 k) ∨
        ∃ g ∈ adjointGroup TwistTag.E6.tag k,
          ¬ IsPGroup 2 ↥((thetaRootGroup (RingHom.id k)).map (MulAut.conj g).toMonoidHom ⊔
            ((thetaRootGroup (RingHom.id k)).map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj (a * diagramMap TwistTag.E6 k)).toMonoidHom)) ∧
    (∀ a ∈ parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ,
      (a * diagramMap TwistTag.E6 K) ^ 2 = 1 →
      (∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
          g * (a * diagramMap TwistTag.E6 K) * g⁻¹ = diagramMap TwistTag.E6 K) ∨
        (∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
          g * (a * diagramMap TwistTag.E6 K) * g⁻¹ =
            pinnedX TwistTag.E6.tag K e6HighestRoot 1 * diagramMap TwistTag.E6 K) ∨
        ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
          ¬ IsPGroup 2 ↥((thetaRootGroup (algebraMap k K)).map (MulAut.conj g).toMonoidHom ⊔
            ((thetaRootGroup (algebraMap k K)).map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj (a * diagramMap TwistTag.E6 K)).toMonoidHom)) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hK2
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ]
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
  have hσk : ∀ c, σ c = c ^ Nat.card k := fun c => by rw [hk]; exact hσ c
  have htr : ∀ a, σ a = a → ∃ s, s + σ s = a := fun a ha => by
    obtain ⟨s, hs⟩ := (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
      (p := 2) (f := f) hK).trace_surj a (by
        rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← hσ]
        exact ha)
    exact ⟨s, by rwa [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← hσ] at hs⟩
  refine ⟨fun a ha hsq => ordinary_reduction hk2 (Subgroup.mem_inf.1 ha).1 hsq,
    fun a ha hsq => twisted_reduction hK2 hσk hσσ htr (Subgroup.mem_inf.1 ha).1
      (Subgroup.mem_inf.1 ha).2 hsq⟩

end CFSG.LieType.Chevalley.E6GraphRadical
