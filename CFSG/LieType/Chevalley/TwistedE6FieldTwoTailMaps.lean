module

public import CFSG.LieType.Chevalley.TwistedE6FieldTwoRelativePairs
public import CFSG.LieType.Chevalley.E6GraphRadicalCocycle

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.RelativeRoots

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap
open scoped commutatorElement

@[expose] def tailA : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ)

@[expose] def tailB : Fin TwistTag.E6.tag.rank → ℤ := (![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ)

@[expose] def tailB' : Fin TwistTag.E6.tag.rank → ℤ := (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ)

@[expose] def tailC : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 1, 1, 0, 0] : Fin 6 → ℤ)

@[expose] def tailC' : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 0, 1, 1, 0] : Fin 6 → ℤ)

@[expose] def tailD : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ)

@[expose] def relA : Fin Tag.F4.rank → ℤ := (![1, 0, 0, 0] : Fin 4 → ℤ)

@[expose] def relB : Fin Tag.F4.rank → ℤ := (![0, 1, 1, 0] : Fin 4 → ℤ)

@[expose] def relU : Fin Tag.F4.rank → ℤ := (![1, 1, 1, 0] : Fin 4 → ℤ)

@[expose] def relD : Fin Tag.F4.rank → ℤ := (![1, 2, 2, 0] : Fin 4 → ℤ)

theorem relU_eq : relU = relA + relB := by
  decide +kernel

theorem relD_eq : relD = relA + 2 • relB := by
  decide +kernel

@[expose] def asE6 (v : Fin TwistTag.E6.tag.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  v

theorem isRoot_tail :
    IsRoot TwistTag.E6.tag tailA ∧ IsRoot TwistTag.E6.tag tailB ∧ IsRoot TwistTag.E6.tag tailB' ∧
      IsRoot TwistTag.E6.tag tailC ∧ IsRoot TwistTag.E6.tag tailC' ∧
      IsRoot TwistTag.E6.tag tailD := by
  have h : (∃ k : Fin 72, e6Root k = asE6 tailA) ∧ (∃ k : Fin 72, e6Root k = asE6 tailB) ∧
      (∃ k : Fin 72, e6Root k = asE6 tailB') ∧ (∃ k : Fin 72, e6Root k = asE6 tailC) ∧
      (∃ k : Fin 72, e6Root k = asE6 tailC') ∧ (∃ k : Fin 72, e6Root k = asE6 tailD) := by
    decide +kernel
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨isRoot_iff_exists_e6Root.2 h1, isRoot_iff_exists_e6Root.2 h2,
    isRoot_iff_exists_e6Root.2 h3, isRoot_iff_exists_e6Root.2 h4, isRoot_iff_exists_e6Root.2 h5,
    isRoot_iff_exists_e6Root.2 h6⟩

theorem tail_relations :
    tailA + tailB = tailC ∧ tailA + tailB' = tailC' ∧ tailB + tailC' = tailD ∧
      permLattice TwistTag.E6.perm tailA = tailA ∧ permLattice TwistTag.E6.perm tailB = tailB' ∧
      permLattice TwistTag.E6.perm tailB' = tailB ∧ permLattice TwistTag.E6.perm tailC = tailC' ∧
      permLattice TwistTag.E6.perm tailC' = tailC ∧ permLattice TwistTag.E6.perm tailD = tailD ∧
      relProj tailA = relA ∧ relProj tailB = relB ∧ relProj tailC = relU ∧
      relProj tailD = relD := by
  decide +kernel

theorem tail_nonroots :
    (∀ k : Fin 72, e6Root k ≠ asE6 (tailB + tailB')) ∧
      (∀ k : Fin 72, e6Root k ≠ asE6 (tailC + tailC')) ∧
      (∀ k : Fin 72, e6Root k ≠ asE6 (tailD + tailC')) ∧
      tailA ≠ tailB ∧ tailA ≠ -tailB ∧ tailA ≠ tailB' ∧ tailA ≠ -tailB' ∧ tailB ≠ tailC' ∧
      tailB ≠ -tailC' ∧ tailB ≠ tailB' ∧ tailB ≠ -tailB' ∧ tailC ≠ tailC' ∧ tailC ≠ -tailC' ∧
      tailD ≠ tailC' ∧ tailD ≠ -tailC' := by
  decide +kernel

theorem tail_pos :
    0 < height tailB ∧ 0 < height tailB' ∧ 0 < height tailC ∧ 0 < height tailC' := by
  decide +kernel

theorem not_isRoot_of_forall_ne {v : Fin TwistTag.E6.tag.rank → ℤ}
    (h : ∀ k : Fin 72, e6Root k ≠ asE6 v) : ¬IsRoot TwistTag.E6.tag v := fun hv => by
  obtain ⟨k, hk⟩ := isRoot_iff_exists_e6Root.1 hv
  exact h k hk

abbrev tX
    (ε : Fin TwistTag.E6.tag.rank → ℤ) (c : K) : ModGL TwistTag.E6.tag K :=
  pinnedX TwistTag.E6.tag K ε c

theorem two_eq_zero_K : (2 : K) = 0 :=
  CharTwo.two_eq_zero

theorem commutatorElement_tX
    {ε ζ : Fin TwistTag.E6.tag.rank → ℤ} (hε : IsRoot TwistTag.E6.tag ε)
    (hζ : IsRoot TwistTag.E6.tag ζ) (hne : ε ≠ ζ) (hne' : ε ≠ -ζ)
    (hεζ : IsRoot TwistTag.E6.tag (ε + ζ)) (c d : K) : ⁅tX ε c, tX ζ d⁆ = tX (ε + ζ) (c * d) := by
  obtain ⟨hC, h⟩ := (simply_laced_root_commutator_unit.{0} TwistTag.E6.tag
    (Or.inr (Or.inl rfl)) hε hζ hne hne').1 hεζ
  rw [h K c d]
  congr 1
  rcases hC with hC | hC <;> rw [hC]
  · simp
  · rw [Int.cast_neg, Int.cast_one, neg_K, one_mul]

theorem twistHom_tX
    {ε : Fin TwistTag.E6.tag.rank → ℤ} (hε : IsRoot TwistTag.E6.tag ε) (c : K) :
    twistHom TwistTag.E6 K barHom (tX ε c) = tX (permLattice TwistTag.E6.perm ε) (bar c) :=
  E6GraphRadical.twistHom_pinnedX_of_two two_eq_zero_K barHom hε c

theorem commute_tX
    {ε ζ : Fin TwistTag.E6.tag.rank → ℤ} (hε : IsRoot TwistTag.E6.tag ε)
    (hζ : IsRoot TwistTag.E6.tag ζ) (hne : ε ≠ ζ) (hne' : ε ≠ -ζ)
    (hεζ : ¬IsRoot TwistTag.E6.tag (ε + ζ)) (c d : K) : Commute (tX ε c) (tX ζ d) :=
  (simply_laced_root_commutator_unit.{0} TwistTag.E6.tag (Or.inr (Or.inl rfl)) hε hζ hne
    hne').2 hεζ K _ (Subgroup.subset_closure ⟨c, rfl⟩) _ (Subgroup.subset_closure ⟨d, rfl⟩)

theorem tail_commutator
    (y z : K) :
    ⁅tX tailA 1, tX tailB y * tX tailB' z⁆ = tX tailC y * tX tailC' z * tX tailD (y * z) := by
  obtain ⟨hA, hB, hB', hC, hC', hD⟩ := isRoot_tail
  obtain ⟨eC, eC', eD, -⟩ := tail_relations
  obtain ⟨-, -, nDC', hAB, hAB', hAB₂, hAB₂', hBC', hBC'', -, -, -, -, hDC', hDC''⟩ :=
    tail_nonroots
  have h1 : ⁅tX tailA 1, tX tailB y⁆ = tX tailC y := by
    rw [commutatorElement_tX hA hB hAB hAB' (eC ▸ hC), one_mul, eC]
  have h2 : ⁅tX tailA 1, tX tailB' z⁆ = tX tailC' z := by
    rw [commutatorElement_tX hA hB' hAB₂ hAB₂' (eC' ▸ hC'), one_mul, eC']
  have h3 : ⁅tX tailB y, tX tailC' z⁆ = tX tailD (y * z) := by
    rw [commutatorElement_tX hB hC' hBC' hBC'' (eD ▸ hD), eD]
  have h4 : Commute (tX tailD (y * z)) (tX tailC' z) :=
    commute_tX hD hC' hDC' hDC'' (not_isRoot_of_forall_ne nDC') _ _
  have e : ⁅tX tailA 1, tX tailB y * tX tailB' z⁆ =
      ⁅tX tailA 1, tX tailB y⁆ * (⁅tX tailB y, ⁅tX tailA 1, tX tailB' z⁆⁆ *
        ⁅tX tailA 1, tX tailB' z⁆) := by
    simp only [commutatorElement_def]
    group
  rw [e, h1, h2, h3, mul_assoc, h4.eq]

theorem relFibre_relA
    : relFibre relA = {tailA} := by
  obtain ⟨hA, -⟩ := isRoot_tail
  obtain ⟨-, -, -, hρA, -, -, -, -, -, pA, -⟩ := tail_relations
  rw [← pA, relFibre_relProj hA, diagramOrbit_eq_pair, hρA, Finset.pair_eq_singleton,
    Finset.coe_singleton]

theorem relFibre_relB
    : relFibre relB = {tailB, tailB'} := by
  obtain ⟨-, hB, -⟩ := isRoot_tail
  obtain ⟨-, -, -, -, hρB, -, -, -, -, -, pB, -⟩ := tail_relations
  rw [← pB, relFibre_relProj hB, diagramOrbit_eq_pair, hρB, Finset.coe_pair]

theorem relFibre_relU
    : relFibre relU = {tailC, tailC'} := by
  obtain ⟨-, -, -, hC, -⟩ := isRoot_tail
  obtain ⟨-, -, -, -, -, -, hρC, -, -, -, -, pC, -⟩ := tail_relations
  rw [← pC, relFibre_relProj hC, diagramOrbit_eq_pair, hρC, Finset.coe_pair]

theorem relFibre_relD
    : relFibre relD = {tailD} := by
  obtain ⟨-, -, -, -, -, hD⟩ := isRoot_tail
  obtain ⟨-, -, -, -, -, -, -, -, hρD, -, -, -, pD⟩ := tail_relations
  rw [← pD, relFibre_relProj hD, diagramOrbit_eq_pair, hρD, Finset.pair_eq_singleton,
    Finset.coe_singleton]

theorem rootSpan_singleton'
    (ε : Fin TwistTag.E6.tag.rank → ℤ) :
    rootSpan TwistTag.E6.tag K {ε} = rootSubgroup TwistTag.E6.tag K ε := by
  rw [rootSpan, iSup_singleton]

@[expose] def paramB
    (y : K) : ModGL TwistTag.E6.tag K :=
  tX tailB y * tX tailB' (bar y)

@[expose] def paramU
    (y : K) : ModGL TwistTag.E6.tag K :=
  tX tailC y * tX tailC' (bar y)

theorem param_mem
    {ε ε' : Fin TwistTag.E6.tag.rank → ℤ} (hε : IsRoot TwistTag.E6.tag ε)
    (hε' : IsRoot TwistTag.E6.tag ε') (hne : ε ≠ ε') (hne' : ε ≠ -ε')
    (hsum : ¬IsRoot TwistTag.E6.tag (ε + ε')) (hρ : permLattice TwistTag.E6.perm ε = ε')
    (hρ' : permLattice TwistTag.E6.perm ε' = ε) (y : K) :
    tX ε y * tX ε' (bar y) ∈ rootSpan TwistTag.E6.tag K {ε, ε'} ⊓
      twistedFixedGroup TwistTag.E6 K barHom := by
  have hmem : tX ε y * tX ε' (bar y) ∈ rootSpan TwistTag.E6.tag K {ε, ε'} :=
    mul_mem (pinnedX_mem_rootSpan (Set.mem_insert _ _) _)
      (pinnedX_mem_rootSpan (Set.mem_insert_of_mem _ (Set.mem_singleton _)) _)
  refine ⟨hmem, (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).2
    ⟨rootSpan_le_adjointGroup K _ hmem, ?_⟩⟩
  rw [map_mul, twistHom_tX hε, twistHom_tX hε', hρ, hρ', bar_bar]
  exact (commute_tX hε hε' hne hne' hsum y (bar y)).eq.symm

theorem param_add
    {ε ε' : Fin TwistTag.E6.tag.rank → ℤ} (hε : IsRoot TwistTag.E6.tag ε)
    (hε' : IsRoot TwistTag.E6.tag ε') (hne : ε ≠ ε') (hne' : ε ≠ -ε')
    (hsum : ¬IsRoot TwistTag.E6.tag (ε + ε')) (y y' : K) :
    tX ε (y + y') * tX ε' (bar (y + y')) = tX ε y * tX ε' (bar y) * (tX ε y' * tX ε' (bar y')) := by
  have hc := (commute_tX hε hε' hne hne' hsum y' (bar y)).eq
  simp only [tX] at hc ⊢
  rw [bar_add, pinnedX_add, pinnedX_add, mul_assoc, mul_assoc, ← mul_assoc (pinnedX _ _ ε y'), hc,
    mul_assoc]

theorem param_injective
    {ε ε' : Fin TwistTag.E6.tag.rank → ℤ} (hε : IsRoot TwistTag.E6.tag ε)
    (hε' : IsRoot TwistTag.E6.tag ε') (hp : 0 < height ε) (hp' : 0 < height ε') (hne : ε ≠ ε')
    {y y' : K} (h : tX ε y * tX ε' (bar y) = tX ε y' * tX ε' (bar y')) : y = y' := by
  have hinj := (positive_root_product_injectivity TwistTag.E6.tag K ![ε, ε']
    (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all [eq_comm])
    (fun i => by fin_cases i <;> simp [hε, hε', hp, hp'])).2
  have h' := @hinj ![y, bar y] ![y', bar y'] (by simpa [List.ofFn_succ] using h)
  exact congrFun h' 0

theorem card_relRootGroup_relB_relU :
    Nat.card (relRootGroup relB) = 4 ∧ Nat.card (relRootGroup relU) = 4 := by
  obtain ⟨-, hB, -, hC, -⟩ := isRoot_tail
  obtain ⟨-, -, -, -, -, -, -, -, -, -, pB, pC, -⟩ := tail_relations
  have hn : f4Euclid relB ⬝ᵥ f4Euclid relB ≠ 2 ∧ f4Euclid relU ⬝ᵥ f4Euclid relU ≠ 2 := by
    decide +kernel
  rw [card_relRootGroup (pB ▸ isRoot_relProj hB), card_relRootGroup (pC ▸ isRoot_relProj hC),
    ite_eq_right hn.1, ite_eq_right hn.2]
  exact ⟨rfl, rfl⟩

theorem card_K' : Nat.card K = 4 := by
  rw [Nat.card_eq_fintype_card, card_K]

theorem paramB_mem
    (y : K) : paramB y ∈ relRootGroup relB := by
  obtain ⟨-, hB, hB', -⟩ := isRoot_tail
  obtain ⟨-, -, -, -, hρB, hρB', -⟩ := tail_relations
  obtain ⟨nBB', -, -, -, -, -, -, -, -, hBB', hBB'', -⟩ := tail_nonroots
  rw [relRootGroup, relFibre_relB]
  exact param_mem hB hB' hBB' hBB'' (not_isRoot_of_forall_ne nBB') hρB hρB' y

theorem paramU_mem
    (y : K) : paramU y ∈ relRootGroup relU := by
  obtain ⟨-, -, -, hC, hC', -⟩ := isRoot_tail
  obtain ⟨-, -, -, -, -, -, hρC, hρC', -⟩ := tail_relations
  obtain ⟨-, nCC', -, -, -, -, -, -, -, -, -, hCC', hCC'', -⟩ := tail_nonroots
  rw [relRootGroup, relFibre_relU]
  exact param_mem hC hC' hCC' hCC'' (not_isRoot_of_forall_ne nCC') hρC hρC' y

@[expose] def paramBHom
    : Multiplicative K →* relRootGroup relB where
  toFun y := ⟨paramB y.toAdd, paramB_mem _⟩
  map_one' := Subtype.ext (by
    change pinnedX TwistTag.E6.tag K tailB 0 * pinnedX TwistTag.E6.tag K tailB' (bar 0) = 1
    rw [bar_zero, pinnedX_zero, pinnedX_zero, mul_one])
  map_mul' y y' := Subtype.ext (by
    obtain ⟨-, hB, hB', -⟩ := isRoot_tail
    obtain ⟨nBB', -, -, -, -, -, -, -, -, hBB', hBB'', -⟩ := tail_nonroots
    exact param_add hB hB' hBB' hBB'' (not_isRoot_of_forall_ne nBB') y.toAdd y'.toAdd)

@[expose] def paramUHom
    : Multiplicative K →* relRootGroup relU where
  toFun y := ⟨paramU y.toAdd, paramU_mem _⟩
  map_one' := Subtype.ext (by
    change pinnedX TwistTag.E6.tag K tailC 0 * pinnedX TwistTag.E6.tag K tailC' (bar 0) = 1
    rw [bar_zero, pinnedX_zero, pinnedX_zero, mul_one])
  map_mul' y y' := Subtype.ext (by
    obtain ⟨-, -, -, hC, hC', -⟩ := isRoot_tail
    obtain ⟨-, nCC', -, -, -, -, -, -, -, -, -, hCC', hCC'', -⟩ := tail_nonroots
    exact param_add hC hC' hCC' hCC'' (not_isRoot_of_forall_ne nCC') y.toAdd y'.toAdd)

theorem coe_paramBHom
    (y : Multiplicative K) :
    (paramBHom y : ModGL TwistTag.E6.tag K) = paramB y.toAdd :=
  rfl

theorem coe_paramUHom
    (y : Multiplicative K) :
    (paramUHom y : ModGL TwistTag.E6.tag K) = paramU y.toAdd :=
  rfl

theorem paramBHom_bijective :
    Function.Bijective paramBHom := by
  obtain ⟨-, hB, hB', -⟩ := isRoot_tail
  obtain ⟨hpB, hpB', -⟩ := tail_pos
  obtain ⟨-, -, -, -, -, -, -, -, -, hBB', -⟩ := tail_nonroots
  refine Function.Injective.bijective_of_nat_card_le (fun y y' h => ?_) ?_
  · have h' := congrArg Subtype.val h
    rw [coe_paramBHom, coe_paramBHom, paramB, paramB] at h'
    exact Multiplicative.toAdd.injective (param_injective hB hB' hpB hpB' hBB' h')
  · rw [card_relRootGroup_relB_relU.1, Nat.card_congr Multiplicative.toAdd, card_K']

theorem paramUHom_bijective :
    Function.Bijective paramUHom := by
  obtain ⟨-, -, -, hC, hC', -⟩ := isRoot_tail
  obtain ⟨-, -, hpC, hpC'⟩ := tail_pos
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hCC', -⟩ := tail_nonroots
  refine Function.Injective.bijective_of_nat_card_le (fun y y' h => ?_) ?_
  · have h' := congrArg Subtype.val h
    rw [coe_paramUHom, coe_paramUHom, paramU, paramU] at h'
    exact Multiplicative.toAdd.injective (param_injective hC hC' hpC hpC' hCC' h')
  · rw [card_relRootGroup_relB_relU.2, Nat.card_congr Multiplicative.toAdd, card_K']

@[expose] def paramBEquiv
    : Multiplicative K ≃* relRootGroup relB :=
  MulEquiv.ofBijective paramBHom paramBHom_bijective

@[expose] def paramUEquiv
    : Multiplicative K ≃* relRootGroup relU :=
  MulEquiv.ofBijective paramUHom paramUHom_bijective

theorem coe_paramBEquiv
    (y : Multiplicative K) :
    (paramBEquiv y : ModGL TwistTag.E6.tag K) = paramB y.toAdd :=
  rfl

theorem coe_paramUEquiv
    (y : Multiplicative K) :
    (paramUEquiv y : ModGL TwistTag.E6.tag K) = paramU y.toAdd :=
  rfl

theorem eq_tX_one_of_mem
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ relRootGroup relA)
    (hx1 : x ≠ 1) : x = tX tailA 1 := by
  obtain ⟨hA, -⟩ := isRoot_tail
  obtain ⟨-, -, -, hρA, -⟩ := tail_relations
  have hx₁ := hx.1
  rw [relFibre_relA, rootSpan_singleton'] at hx₁
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx₁
  have hfix := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).1 hx.2).2
  rw [twistHom_tX hA, hρA] at hfix
  have hc : c * c = c * 1 := by
    rw [mul_one, ← pow_two]
    exact pinnedX_injective TwistTag.E6.tag K tailA hfix
  have hc0 : c ≠ 0 := fun h => hx1 (by rw [h, pinnedX_zero])
  rw [mul_left_cancel₀ hc0 hc]

theorem tX_tailD_mem
    (y : K) : tX tailD (y * bar y) ∈ relRootGroup relD := by
  obtain ⟨-, -, -, -, -, hD⟩ := isRoot_tail
  obtain ⟨-, -, -, -, -, -, -, -, hρD, -⟩ := tail_relations
  refine ⟨?_, (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).2
    ⟨pinnedX_mem_adjointGroup _ _, ?_⟩⟩
  · rw [relFibre_relD]
    exact pinnedX_mem_rootSpan (Set.mem_singleton _) _
  · rw [twistHom_tX hD, hρD, bar_mul, bar_bar, mul_comm]

theorem exists_tail_equiv_rep
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ relRootGroup relA)
    (hx1 : x ≠ 1) : ∃ φ : relRootGroup relB ≃* relRootGroup relU,
      ∀ v : relRootGroup relB, ((φ v : ModGL TwistTag.E6.tag K))⁻¹ *
        ⁅x, (v : ModGL TwistTag.E6.tag K)⁆ ∈ relRootGroup relD := by
  rw [eq_tX_one_of_mem hx hx1]
  refine ⟨paramBEquiv.symm.trans paramUEquiv, fun v => ?_⟩
  obtain ⟨y, rfl⟩ := paramBEquiv.surjective v
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, coe_paramUEquiv, coe_paramBEquiv]
  have h := tail_commutator y.toAdd (bar y.toAdd)
  change (paramU y.toAdd)⁻¹ * ⁅tX tailA 1, paramB y.toAdd⁆ ∈ _
  rw [show ⁅tX tailA 1, paramB y.toAdd⁆ = paramU y.toAdd * tX tailD (y.toAdd * bar y.toAdd) from h,
    inv_mul_cancel_left]
  exact tX_tailD_mem _

theorem tail_invariants :
    f4Euclid relA ⬝ᵥ f4Euclid relA = 2 ∧ f4Euclid relB ⬝ᵥ f4Euclid relB = 1 ∧
      f4Euclid relA ⬝ᵥ f4Euclid relB = -1 ∧ relA ≠ relB ∧ relA ≠ -relB := by
  decide +kernel

theorem exists_tail_commutator_equiv
    {a b : Fin Tag.F4.rank → ℤ} (ha : IsRoot .F4 a)
    (hb : IsRoot .F4 b) (hal : f4Euclid a ⬝ᵥ f4Euclid a = 2)
    (hbs : f4Euclid b ⬝ᵥ f4Euclid b = 1) (hab : f4Euclid a ⬝ᵥ f4Euclid b = -1)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ relRootGroup a) (hx1 : x ≠ 1) :
    ∃ φ : relRootGroup b ≃* relRootGroup (a + b), ∀ v : relRootGroup b,
      ((φ v : ModGL TwistTag.E6.tag K))⁻¹ * ⁅x, (v : ModGL TwistTag.E6.tag K)⁆ ∈
        relRootGroup (a + 2 • b) := by
  obtain ⟨hA, hB, -⟩ := isRoot_tail
  obtain ⟨-, -, -, -, -, -, -, -, -, pA, pB, -⟩ := tail_relations
  obtain ⟨iA, iB, iAB, hne₀, hne₀'⟩ := tail_invariants
  have hrA : IsRoot .F4 relA := pA ▸ isRoot_relProj hA
  have hrB : IsRoot .F4 relB := pB ▸ isRoot_relProj hB
  have hne : a ≠ b := fun h => by
    rw [h, hbs] at hal
    norm_num at hal
  have hne' : a ≠ -b := fun h => by
    rw [h, f4Euclid_neg, neg_dotProduct, dotProduct_neg, neg_neg, hbs] at hal
    norm_num at hal
  obtain ⟨w, hwa, hwb, w', -, -, hmap⟩ := exists_pair_conj hrA hrB ha hb hne₀ hne₀' hne hne'
    (by rw [iA, hal]) (by rw [iB, hbs]) (by rw [iAB, hab])
  set c := (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w')).toMonoidHom
  have hcinj : Function.Injective c := (MulAut.conj _).injective
  have hu : w • relU = a + b := by rw [relU_eq, smul_add, hwa, hwb]
  have hd : w • relD = a + 2 • b := by rw [relD_eq, smul_add, smul_comm, hwa, hwb]
  have hxa : x ∈ (relRootGroup relA).map c := by
    rw [hmap, hwa]
    exact hx
  obtain ⟨x₀, hx₀, rfl⟩ := hxa
  have hx₀1 : x₀ ≠ 1 := fun h => hx1 (by rw [h, map_one])
  obtain ⟨φ₀, hφ₀⟩ := exists_tail_equiv_rep hx₀ hx₀1
  let eb : relRootGroup relB ≃* relRootGroup b :=
    ((relRootGroup relB).equivMapOfInjective c hcinj).trans
      (MulEquiv.subgroupCongr (by rw [hmap, hwb]))
  let eu : relRootGroup relU ≃* relRootGroup (a + b) :=
    ((relRootGroup relU).equivMapOfInjective c hcinj).trans
      (MulEquiv.subgroupCongr (by rw [hmap, hu]))
  refine ⟨eb.symm.trans (φ₀.trans eu), fun v => ?_⟩
  obtain ⟨v₀, rfl⟩ := eb.surjective v
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
  have h1 : ((eu (φ₀ v₀) : relRootGroup (a + b)) : ModGL TwistTag.E6.tag K) = c (φ₀ v₀) := rfl
  have h2 : ((eb v₀ : relRootGroup b) : ModGL TwistTag.E6.tag K) = c v₀ := rfl
  have hmem := Subgroup.mem_map_of_mem c (hφ₀ v₀)
  rw [hmap, hd] at hmem
  rw [h1, h2]
  rwa [map_mul, map_inv, map_commutatorElement] at hmem

theorem euclid_tail_data : ∀ i j : Fin 4, i < j →
    (Pi.single i 1 - Pi.single j 1 : Fin 4 → ℚ) ⬝ᵥ (Pi.single i 1 - Pi.single j 1) = 2 ∧
      (Pi.single j 1 : Fin 4 → ℚ) ⬝ᵥ Pi.single j 1 = 1 ∧
      (Pi.single i 1 - Pi.single j 1 : Fin 4 → ℚ) ⬝ᵥ Pi.single j 1 = -1 := by
  decide +kernel

theorem exists_tail_commutator_equiv_euclid
    {i j : Fin 4} (hij : i < j)
    {a b u d : Fin Tag.F4.rank → ℤ} (ha : IsRoot .F4 a) (hb : IsRoot .F4 b)
    (ea : f4Euclid a = Pi.single i 1 - Pi.single j 1) (eb : f4Euclid b = Pi.single j 1)
    (eu : f4Euclid u = Pi.single i 1) (ed : f4Euclid d = Pi.single i 1 + Pi.single j 1)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ relRootGroup a) (hx1 : x ≠ 1) :
    ∃ φ : relRootGroup b ≃* relRootGroup u, ∀ v : relRootGroup b,
      ((φ v : ModGL TwistTag.E6.tag K))⁻¹ * ⁅x, (v : ModGL TwistTag.E6.tag K)⁆ ∈
        relRootGroup d := by
  obtain ⟨h1, h2, h3⟩ := euclid_tail_data i j hij
  have hu : u = a + b := f4Euclid_injective (by rw [f4Euclid_add, ea, eb, eu, sub_add_cancel])
  have hd : d = a + 2 • b := f4Euclid_injective (by
    rw [two_nsmul, f4Euclid_add, f4Euclid_add, ea, eb, ed]
    abel)
  subst hu hd
  exact exists_tail_commutator_equiv ha hb (by rw [ea]; exact h1) (by rw [eb]; exact h2)
    (by rw [ea, eb]; exact h3) hx hx1

end CFSG.LieType.Chevalley.C2E6Std.RelativeRoots
