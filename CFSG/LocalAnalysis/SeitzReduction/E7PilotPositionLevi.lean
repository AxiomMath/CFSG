module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionB
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionOrder
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionAbstract

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.EvenSmallLie RootOps
open scoped commutatorElement

@[expose] def highRootD : Fin Tag.E7.rank → ℤ := ![0, 1, 1, 2, 2, 2, 1]

@[expose] def posPerpPred (β : Fin Tag.E7.rank → ℤ) : Prop :=
  0 < height β ∧ β (highNode .E7) = 0

instance : DecidablePred posPerpPred := fun β => by
  unfold posPerpPred
  infer_instance

@[expose] def posPerpRoots : Set (Fin Tag.E7.rank → ℤ) := {β | IsRoot .E7 β ∧ posPerpPred β}

theorem highRootD_eq : highRootD = e7RepPreHigh 0 := rfl


theorem posPerp_check :
    (Timmesfeld.ExceptionalOrders.rootList .E7).countP (fun v => decide (posPerpPred v)) = 30 ∧
      (Timmesfeld.ExceptionalOrders.rootList .E7).all (fun v =>
        !decide (posPerpPred v) || decide (v = highRootD) ||
          (List.finRange Tag.E7.rank).any fun j =>
            decide (j ≠ highNode .E7 ∧ coPair .E7 j v = -1)) ∧
      (Timmesfeld.ExceptionalOrders.rootList .E7).all (fun v =>
        !decide (posPerpPred v) || decide (height v ≤ height highRootD)) ∧
      (Timmesfeld.ExceptionalOrders.rootList .E7).all (fun v =>
        !decide (posPerpPred v) || decide (0 ≤ iform highRootD v)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem posPerpRoots_ncard : posPerpRoots.ncard = 30 := by
  rw [posPerpRoots, Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and]
  exact posPerp_check.1

theorem posPerpRoots_pos : ∀ β ∈ posPerpRoots, IsRoot .E7 β ∧ 0 < height β :=
  fun _ hβ => ⟨hβ.1, hβ.2.1⟩

theorem posPerpRoots_closed : ∀ α ∈ posPerpRoots, ∀ β ∈ posPerpRoots, ∀ a b : ℕ,
    1 ≤ a → 1 ≤ b → IsRoot .E7 (a • α + b • β) → a • α + b • β ∈ posPerpRoots := by
  rintro α ⟨-, hαh, hα0⟩ β ⟨-, hβh, hβ0⟩ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_, ?_⟩
  · rw [height_nsmul_add_nsmul]
    nlinarith
  · simp [hα0, hβ0]

theorem highRootD_mem_posPerpRoots : highRootD ∈ posPerpRoots :=
  ⟨e7RepPreHigh_isRoot 0, by decide, by decide⟩

theorem highRootD_mem_perpRoots : highRootD ∈ EPilot.perpRoots .E7 :=
  ⟨e7RepPreHigh_isRoot 0, by decide⟩

theorem exists_coPair_eq_neg_one_D {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ posPerpRoots)
    (hne : β ≠ highRootD) : ∃ j, j ≠ highNode .E7 ∧ coPair .E7 j β = -1 := by
  have h := List.all_eq_true.1 posPerp_check.2.1 β
    (Timmesfeld.ExceptionalOrders.mem_rootList.2 hβ.1)
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    decide_eq_true_eq, List.any_eq_true, List.mem_finRange, true_and] at h
  rcases h with (h | h) | ⟨j, hj⟩
  · exact absurd hβ.2 h
  · exact absurd h hne
  · exact ⟨j, hj⟩

theorem height_le_highRootD {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ posPerpRoots) :
    height β ≤ height highRootD := by
  have h := List.all_eq_true.1 posPerp_check.2.2.1 β
    (Timmesfeld.ExceptionalOrders.mem_rootList.2 hβ.1)
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd hβ.2 h
  · exact h

theorem iform_highRootD_nonneg {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ posPerpRoots) :
    0 ≤ iform highRootD β := by
  have h := List.all_eq_true.1 posPerp_check.2.2.2 β
    (Timmesfeld.ExceptionalOrders.mem_rootList.2 hβ.1)
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd hβ.2 h
  · exact h

section Centre


variable {K : Type} [Field K]

theorem mem_rootSubgroup_highRootD_of_commute [Finite K] {z : ModGL .E7 K}
    (hz : z ∈ rootSpan .E7 K posPerpRoots)
    (hc : ∀ j : Fin Tag.E7.rank, j ≠ highNode .E7 →
      z * pinnedX .E7 K (Pi.single j 1) 1 = pinnedX .E7 K (Pi.single j 1) 1 * z) :
    z ∈ rootSubgroup .E7 K highRootD := by
  classical
  have hτ : Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 := Or.inr (Or.inl rfl)
  obtain ⟨α, hα, hrange⟩ := exists_rootEnum (finite_of_forall_isRoot_pos posPerpRoots_pos)
  have hpos : ∀ l, α l ∈ posPerpRoots := fun l => by
    have h : α l ∈ Set.range α := ⟨l, rfl⟩
    rwa [hrange] at h
  obtain ⟨c, -, hcz⟩ :=
    (bijOn_prod_pinnedX K posPerpRoots_pos posPerpRoots_closed α hα hrange).surjOn hz
  have hcz' : (List.ofFn fun l => pinnedX .E7 K (α l) (c l)).prod = z := hcz
  have key : ∀ n : ℕ, ∀ l, height (α l) ≤ n → α l ≠ highRootD → c l = 0 := by
    intro n
    induction n with
    | zero =>
      intro l hl _
      have := (hpos l).2.1
      push_cast at hl
      omega
    | succ n ih =>
      intro i hi hir
      by_cases hle : height (α i) ≤ n
      · exact ih i hle hir
      obtain ⟨j, hj0, hj⟩ := exists_coPair_eq_neg_one_D (hpos i) hir
      have hγ' : IsRoot .E7 (α i + Pi.single j 1) :=
        reflect_eq_add_single hj ▸ IsRoot.reflect j (hpos i).1
      have hγ'p : IsRoot .E7 (α i + Pi.single j 1) ∧ 0 < height (α i + Pi.single j 1) :=
        ⟨hγ', by rw [height_add, height_single]; have := (hpos i).2.1; omega⟩
      have hlow : ∀ l, height (α l) < height (α i) → c l = 0 := fun l hl => ih l (by
        push_cast at hi
        omega) fun h => by
          have h1 := height_le_highRootD (hpos i)
          rw [← h] at h1
          omega
      set w := pinnedX .E7 K (Pi.single j 1) (1 : K) with hw_def
      have hfac : ∀ l, ⁅pinnedX .E7 K (α l) (c l), w⁆ ∈
            heightSeries .E7 K (height (α i + Pi.single j 1)) ∧
          rootCoord hγ'p ⁅pinnedX .E7 K (α l) (c l), w⁆ =
            if l = i then (commConst .E7 (α i) (Pi.single j 1) (1, 1) : K) * c i else 0 := by
        intro l
        by_cases hl : height (α l) < height (α i)
        · rw [hlow l hl, pinnedX_zero, commutatorElement_one_left, rootCoord_one,
            ite_eq_right (fun h => by subst h; exact lt_irrefl _ hl)]
          exact ⟨one_mem _, rfl⟩
        · obtain ⟨h1, h2⟩ := commutator_simple_mem_and_rootCoord hτ hj hγ'p (hpos l).1
            (hpos l).2.1 (not_lt.1 hl) (c l)
          refine ⟨h1, h2.trans ?_⟩
          by_cases hli : l = i
          · subst hli
            simp
          · rw [ite_eq_right (fun h => hli (hα h)), ite_eq_right hli]
      obtain ⟨-, hπ⟩ := commutator_prod_mem_and_coord (U := posUnipotent .E7 K)
        (M := heightSeries .E7 K (height (α i + Pi.single j 1)))
        (heightSeries_le_normalizer K _) (rootCoord hγ'p)
        (fun x hx y hy => rootCoord_mul hγ'p hx hy) (fun g hg x hx => rootCoord_conj hγ'p hg hx)
        (List.ofFn fun l => pinnedX .E7 K (α l) (c l)) [w]
        (fun x hx => by
          obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
          exact rootSubgroup_le_posUnipotent_of_height_pos (hpos l).1 (hpos l).2.1
            (mem_rootSubgroup.2 ⟨_, rfl⟩))
        (fun y hy => by
          rw [List.mem_singleton] at hy
          rw [hy]
          exact pinnedX_single_mem_posUnipotent j 1)
        (fun x hx y hy => by
          rw [List.mem_singleton] at hy
          obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
          rw [hy]
          exact (hfac l).1)
      rw [hcz', List.prod_singleton, commutatorElement_eq_one_iff_mul_comm.2 (hc j hj0),
        rootCoord_one, List.map_ofFn, List.sum_ofFn] at hπ
      simp only [Function.comp_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, (hfac _).2, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hπ
      obtain ⟨hε, -⟩ := (simply_laced_root_commutator_unit.{0} .E7 (Or.inr hτ) (hpos i).1
        (isRoot_single .E7 j) (fun h => by
          have h2 : coPair .E7 j (Pi.single j 1) = 2 := by
            rw [coPair, Finset.sum_eq_single j (fun l _ hl => by simp [hl])
              (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one,
              Tag.cartan_self]
          rw [← h, hj] at h2
          omega) (fun h => by
          have h1 := (hpos i).2.1
          rw [h, height_neg, height_single] at h1
          omega)).1 hγ'
      rcases hε with hε | hε
      · rw [hε] at hπ
        simpa using hπ.symm
      · rw [hε] at hπ
        simpa using hπ.symm
  rw [← hcz']
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
  by_cases hl : α l = highRootD
  · rw [hl]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  · rw [key (height (α l)).toNat l (Int.self_le_toNat _) hl, pinnedX_zero]
    exact one_mem _

theorem rootSpan_posPerpRoots_le_centralizer_highRootD (c : K) :
    rootSpan .E7 K posPerpRoots ≤ Subgroup.centralizer {pinnedX .E7 K highRootD c} := by
  refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨a, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  by_cases hβe : β = highRootD
  · subst hβe
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · have hne' : β ≠ -highRootD := by
      intro h
      have := hβ.2.1
      rw [h, height_neg] at this
      have h2 := highRootD_mem_posPerpRoots.2.1
      omega
    have hnr : ¬ IsRoot .E7 (β + highRootD) := by
      rw [add_comm]
      exact not_isRoot_add_of_iform_nonneg (e7RepPreHigh_isRoot 0) hβ.1
        (iform_highRootD_nonneg hβ)
    exact ((simply_laced_root_commutator_unit .E7 (Or.inr (Or.inr (Or.inl rfl))) hβ.1
      (e7RepPreHigh_isRoot 0) hβe hne').2 hnr K _ (mem_rootSubgroup.2 ⟨a, rfl⟩) _
      (mem_rootSubgroup.2 ⟨c, rfl⟩)).eq

end Centre

section Sylow


variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def posPerpU : Subgroup (adjointGroup .E7 K) :=
  (rootSpan .E7 K posPerpRoots).subgroupOf (adjointGroup .E7 K)

theorem posPerpU_le_perpLevi : posPerpU K ≤ EPilot.perpLevi .E7 K := fun _ hx =>
  mem_subgroupOf.2 ((iSup₂_le fun β hβ => le_iSup₂_of_le
    (f := fun δ (_ : δ ∈ EPilot.perpRoots .E7) => rootSubgroup .E7 K δ) β ⟨hβ.1, hβ.2.2⟩ le_rfl :
      rootSpan .E7 K posPerpRoots ≤ rootSpan .E7 K (EPilot.perpRoots .E7)) (mem_subgroupOf.1 hx))

theorem natCard_posPerpU [Finite K] : Nat.card (posPerpU K) = Nat.card K ^ 30 := by
  rw [posPerpU, Nat.card_congr (subgroupOfEquivOfLe (EPilot.rootSpan_le_adjointGroup' _)).toEquiv,
    card_rootSpan posPerpRoots_pos posPerpRoots_closed, posPerpRoots_ncard]

theorem radicalRoots_highRoot_pos :
    ∀ β ∈ EPilot.radicalRoots .E7 (highRoot .E7), IsRoot .E7 β ∧ 0 < height β := by
  rintro β ⟨hβ, hpos⟩
  refine ⟨hβ, (IsRoot.height_pos_iff hβ).2 ?_⟩
  rw [iform_comm, EPilot.iform_highRoot (Or.inr (Or.inl rfl))] at hpos
  rcases hβ.nonneg_or_nonpos with h | h
  · exact h
  · exact absurd (h (highNode .E7)) (not_le.2 hpos)

theorem radicalRoots_highRoot_closed : ∀ α ∈ EPilot.radicalRoots .E7 (highRoot .E7),
    ∀ β ∈ EPilot.radicalRoots .E7 (highRoot .E7), ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot .E7 (a • α + b • β) → a • α + b • β ∈ EPilot.radicalRoots .E7 (highRoot .E7) := by
  rintro α ⟨-, hα⟩ β ⟨-, hβ⟩ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_⟩
  rw [iform_add_left, ← Nat.cast_smul_eq_nsmul ℤ a α, ← Nat.cast_smul_eq_nsmul ℤ b β,
    iform_smul_left, iform_smul_left]
  nlinarith

theorem radicalRoots_highRoot_ncard : (EPilot.radicalRoots .E7 (highRoot .E7)).ncard = 33 := by
  rw [EPilot.radicalRoots, Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and]
  decide +kernel

theorem natCard_rootRadical_highRoot [Finite K] :
    Nat.card (EPilot.rootRadical .E7 K (highRoot .E7)) = Nat.card K ^ 33 := by
  rw [EPilot.rootRadical,
    Nat.card_congr (subgroupOfEquivOfLe (EPilot.rootSpan_le_adjointGroup' _)).toEquiv,
    card_rootSpan radicalRoots_highRoot_pos radicalRoots_highRoot_closed,
    radicalRoots_highRoot_ncard]

theorem rootPerpLevi_highRoot_eq : EPilot.rootPerpLevi .E7 K (highRoot .E7) =
    EPilot.perpLevi .E7 K := by
  rw [EPilot.rootPerpLevi, EPilot.rootPerp_highRoot (Or.inr (Or.inl rfl))]
  rfl

theorem exists_sylow_perpLevi_eq [Finite K] [CharP K 2] :
    ∃ S : Sylow 2 (EPilot.perpLevi .E7 K),
      (S : Subgroup (EPilot.perpLevi .E7 K)) = (posPerpU K).subgroupOf (EPilot.perpLevi .E7 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := EPilot.perpLevi .E7 K with hDdef
  obtain ⟨f, -, hK⟩ := exists_card_eq_two_pow_eClasses K
  have hUcard := natCard_posPerpU (K := K)
  have hUD2 : IsPGroup 2 ((posPerpU K).subgroupOf D) := by
    refine IsPGroup.of_card (n := f * 30) ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe posPerpU_le_perpLevi).toEquiv, hUcard, hK,
      ← pow_mul]
  obtain ⟨S, hS⟩ := hUD2.exists_le_sylow
  set S' : Subgroup (adjointGroup .E7 K) := (S : Subgroup D).map D.subtype with hS'def
  have hS'D : S' ≤ D := map_subtype_le _
  obtain ⟨hQ2, -, hQMb, hMN⟩ := EPilot.isTwoRadicalDecomp_root (K := K) (Or.inr (Or.inl rfl))
    (isRoot_highRoot .E7) (one_ne_zero (α := K))
  rw [rootPerpLevi_highRoot_eq] at hQMb hMN
  set Q := EPilot.rootRadical .E7 K (highRoot .E7) with hQdef
  have hS'N : S' ≤ normalizer (Q : Set (adjointGroup .E7 K)) := hS'D.trans hMN
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map _
  have hsup2 : IsPGroup 2 (S' ⊔ Q : Subgroup (adjointGroup .E7 K)) :=
    hS'2.to_sup_of_normal_right' hQ2 hS'N
  have hsupcard := natCard_le_of_isPGroup_E7 hsup2
  have hdisj : ∀ x ∈ S', x ∈ Q → x = 1 := fun x hxS hxQ => by
    have hx : x ∈ Q ⊓ D := mem_inf.2 ⟨hxQ, hS'D hxS⟩
    rw [hQMb, mem_bot] at hx
    exact hx
  let φ : S' × Q → (S' ⊔ Q : Subgroup (adjointGroup .E7 K)) := fun p =>
    ⟨(p.1 : adjointGroup .E7 K) * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hφ : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨x, hx⟩ := a
    obtain ⟨y, hy⟩ := b
    obtain ⟨x', hx'⟩ := a'
    obtain ⟨y', hy'⟩ := b'
    have h1 : x * y = x' * y' := congrArg Subtype.val h
    have h2 : x'⁻¹ * x = y' * y⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
        _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h1]
        _ = y' * y⁻¹ := by group
    have h3 : x'⁻¹ * x = 1 :=
      hdisj _ (mul_mem (inv_mem hx') hx) (h2 ▸ mul_mem hy' (inv_mem hy))
    have hxx : x = x' := by
      calc x = x' * (x'⁻¹ * x) := by group
        _ = x' := by rw [h3, mul_one]
    have h4 : y' * y⁻¹ = 1 := h2 ▸ h3
    have hyy : y = y' := by
      calc y = (y' * y⁻¹)⁻¹ * y' := by group
        _ = y' := by rw [h4, inv_one, one_mul]
    subst hxx
    subst hyy
    rfl
  have hprod : Nat.card S' * Nat.card Q ≤ Nat.card (S' ⊔ Q : Subgroup (adjointGroup .E7 K)) := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective φ hφ
  rw [natCard_rootRadical_highRoot] at hprod
  have hS'card : Nat.card S' ≤ Nat.card K ^ 30 := by
    have hpos : 0 < Nat.card K ^ 33 := pow_pos Nat.card_pos 33
    have h63 : Nat.card K ^ 63 = Nat.card K ^ 30 * Nat.card K ^ 33 := by rw [← pow_add]
    have := hprod.trans hsupcard
    rw [h63] at this
    exact Nat.le_of_mul_le_mul_right this hpos
  have hUS' : posPerpU K ≤ S' := fun x hx =>
    ⟨⟨x, posPerpU_le_perpLevi hx⟩, hS (mem_subgroupOf.2 hx), rfl⟩
  have heq : posPerpU K = S' := Subgroup.eq_of_le_of_card_ge hUS' (by rw [hUcard]; exact hS'card)
  refine ⟨S, ?_⟩
  rw [heq, hS'def]
  ext x
  rw [mem_subgroupOf]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

end Sylow

section RootSL2


variable {K : Type} [Field K]

theorem nSL_one_mul_uSL (c : K) : nSL (1 : Kˣ) * uSL c = vSL (-c) * nSL 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have h1 : ((nSL (1 : Kˣ) : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := by
    simp [nSL]
  have h2 : ((uSL c : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := rfl
  have h3 : ((vSL (-c) : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; -c, 1] := rfl
  rw [h1, h2, h3]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_mem_conj_pinnedX_highRootD [CharP K 2] :
    ∃ n ∈ rootSubgroup .E7 K highRootD ⊔ rootSubgroup .E7 K (-highRootD),
      ∀ c : K, n * pinnedX .E7 K highRootD c * n⁻¹ = pinnedX .E7 K (-highRootD) (-c) := by
  obtain ⟨-, hrange, -, huv, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps (τ := .E7) K
      (e7RepPreHigh_isRoot 0)
  rw [← highRootD_eq] at hrange huv
  refine ⟨rootSL2 .E7 K highRootD (nSL 1), hrange ▸ ⟨nSL 1, rfl⟩, fun c => ?_⟩
  rw [← (huv c).1, ← (huv (-c)).2, ← map_inv, ← map_mul, ← map_mul, nSL_one_mul_uSL,
    mul_inv_cancel_right]

theorem map_conj_rootSubgroup_highRootD {n : ModGL .E7 K}
    (hn : ∀ c : K, n * pinnedX .E7 K highRootD c * n⁻¹ = pinnedX .E7 K (-highRootD) (-c)) :
    (rootSubgroup .E7 K highRootD).map (MulAut.conj n).toMonoidHom =
      rootSubgroup .E7 K (-highRootD) := by
  ext y
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    exact mem_rootSubgroup.2 ⟨-c, (hn c).symm⟩
  · intro hy
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
    exact ⟨pinnedX .E7 K highRootD (-d), mem_rootSubgroup.2 ⟨-d, rfl⟩, by rw [hn, neg_neg]⟩

theorem isSimpleGroup_rootSL2_highRootD [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    IsSimpleGroup (rootSubgroup .E7 K highRootD ⊔ rootSubgroup .E7 K (-highRootD) :
      Subgroup (ModGL .E7 K)) ∧
      ¬ IsPGroup 2 (rootSubgroup .E7 K highRootD ⊔ rootSubgroup .E7 K (-highRootD) :
        Subgroup (ModGL .E7 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps (τ := .E7) K
      (e7RepPreHigh_isRoot 0)
  rw [← highRootD_eq] at h
  obtain ⟨hs, -, hnc⟩ := h ‹Finite K› hq
  have : Finite (rootSubgroup .E7 K highRootD ⊔ rootSubgroup .E7 K (-highRootD) :
      Subgroup (ModGL .E7 K)) := by
    have := finite_modGL (τ := .E7) (K := K)
    infer_instance
  refine ⟨hs, fun hp => ?_⟩
  have : Nontrivial (rootSubgroup .E7 K highRootD ⊔ rootSubgroup .E7 K (-highRootD) :
      Subgroup (ModGL .E7 K)) := hs.toNontrivial
  have hnt := hp.center_nontrivial
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
  · rw [h] at hnt
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt rfl
  · obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have ha : a ∈ Subgroup.center _ := by rw [h]; exact mem_top a
    exact (mem_center_iff.1 ha b).symm

end RootSL2

section D


variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def perpLeviHom : EPilot.perpLevi .E7 K →* ModGL .E7 K :=
  (adjointGroup .E7 K).subtype.comp (EPilot.perpLevi .E7 K).subtype

theorem perpLeviHom_injective : Function.Injective (perpLeviHom K) :=
  (adjointGroup .E7 K).subtype_injective.comp (EPilot.perpLevi .E7 K).subtype_injective

theorem map_perpLeviHom_subgroupOf {H : Subgroup (ModGL .E7 K)}
    (hH : H ≤ rootSpan .E7 K (EPilot.perpRoots .E7)) :
    ((H.subgroupOf (adjointGroup .E7 K)).subgroupOf (EPilot.perpLevi .E7 K)).map
      (perpLeviHom K) = H := by
  have hHC : H ≤ adjointGroup .E7 K := hH.trans (EPilot.rootSpan_le_adjointGroup' _)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_subgroupOf.1 (mem_subgroupOf.1 hy)
  · intro hx
    exact ⟨⟨⟨x, hHC hx⟩, mem_subgroupOf.2 (hH hx)⟩, mem_subgroupOf.2 (mem_subgroupOf.2 hx), rfl⟩

theorem rootSubgroup_highRootD_le_rootSpan_perpRoots :
    rootSubgroup .E7 K highRootD ≤ rootSpan .E7 K (EPilot.perpRoots .E7) ∧
      rootSubgroup .E7 K (-highRootD) ≤ rootSpan .E7 K (EPilot.perpRoots .E7) :=
  ⟨le_iSup₂_of_le (f := fun δ (_ : δ ∈ EPilot.perpRoots .E7) => rootSubgroup .E7 K δ) highRootD
      highRootD_mem_perpRoots le_rfl,
    le_iSup₂_of_le (f := fun δ (_ : δ ∈ EPilot.perpRoots .E7) => rootSubgroup .E7 K δ)
      (-highRootD) (EPilot.neg_mem_perpRoots highRootD_mem_perpRoots) le_rfl⟩

variable (K) in
@[expose] noncomputable def highRootDU : Subgroup (EPilot.perpLevi .E7 K) :=
  ((rootSubgroup .E7 K highRootD).subgroupOf (adjointGroup .E7 K)).subgroupOf
    (EPilot.perpLevi .E7 K)

variable (K) in
@[expose] noncomputable def highRootDJ : Subgroup (EPilot.perpLevi .E7 K) :=
  ((rootSubgroup .E7 K highRootD ⊔ rootSubgroup .E7 K (-highRootD)).subgroupOf
    (adjointGroup .E7 K)).subgroupOf (EPilot.perpLevi .E7 K)

theorem map_perpLeviHom_highRootDU :
    (highRootDU K).map (perpLeviHom K) = rootSubgroup .E7 K highRootD :=
  map_perpLeviHom_subgroupOf rootSubgroup_highRootD_le_rootSpan_perpRoots.1

theorem map_perpLeviHom_highRootDJ :
    (highRootDJ K).map (perpLeviHom K) =
      rootSubgroup .E7 K highRootD ⊔ rootSubgroup .E7 K (-highRootD) :=
  map_perpLeviHom_subgroupOf (sup_le rootSubgroup_highRootD_le_rootSpan_perpRoots.1
    rootSubgroup_highRootD_le_rootSpan_perpRoots.2)

theorem sylow_inf_centralizer_eq_highRootDU [Finite K] (S : Sylow 2 (EPilot.perpLevi .E7 K))
    (hS : (S : Subgroup (EPilot.perpLevi .E7 K)) =
      (posPerpU K).subgroupOf (EPilot.perpLevi .E7 K)) :
    (S : Subgroup (EPilot.perpLevi .E7 K)) ⊓
        centralizer ((S : Subgroup (EPilot.perpLevi .E7 K)) : Set (EPilot.perpLevi .E7 K)) =
      highRootDU K := by
  have hmemS : ∀ x : EPilot.perpLevi .E7 K, x ∈ (S : Subgroup (EPilot.perpLevi .E7 K)) ↔
      (((x : adjointGroup .E7 K)) : ModGL .E7 K) ∈ rootSpan .E7 K posPerpRoots := fun x => by
    rw [hS, mem_subgroupOf, posPerpU, mem_subgroupOf]
  ext x
  constructor
  · rintro ⟨hxS, hxc⟩
    rw [highRootDU, mem_subgroupOf, mem_subgroupOf]
    refine mem_rootSubgroup_highRootD_of_commute ((hmemS x).1 hxS) fun j hj => ?_
    have hjr : Pi.single j (1 : ℤ) ∈ posPerpRoots :=
      ⟨isRoot_single .E7 j, by rw [height_single]; omega, by simp [Ne.symm hj]⟩
    have hjm : pinnedX .E7 K (Pi.single j 1) 1 ∈ rootSpan .E7 K posPerpRoots :=
      pinnedX_mem_rootSpan hjr 1
    set y : EPilot.perpLevi .E7 K :=
      ⟨⟨pinnedX .E7 K (Pi.single j 1) 1, pinnedX_mem_adjointGroup _ _⟩,
        posPerpU_le_perpLevi (mem_subgroupOf.2 hjm)⟩ with hydef
    have hyS : y ∈ (S : Subgroup (EPilot.perpLevi .E7 K)) := (hmemS y).2 hjm
    have h := mem_centralizer_iff.1 hxc y hyS
    have h' := congrArg
      (fun z : EPilot.perpLevi .E7 K => ((z : adjointGroup .E7 K) : ModGL .E7 K)) h
    simp only [Subgroup.coe_mul] at h'
    exact h'.symm
  · intro hx
    rw [highRootDU, mem_subgroupOf, mem_subgroupOf] at hx
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hx
    refine ⟨(hmemS x).2 (hc ▸ pinnedX_mem_rootSpan highRootD_mem_posPerpRoots c),
      mem_centralizer_iff.2 fun y hy => ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.1
      (rootSpan_posPerpRoots_le_centralizer_highRootD c ((hmemS y).1 hy))
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hc]
    exact h

noncomputable def highRootDJEquiv :
    highRootDJ K ≃* (rootSubgroup .E7 K highRootD ⊔ rootSubgroup .E7 K (-highRootD) :
      Subgroup (ModGL .E7 K)) :=
  ((highRootDJ K).equivMapOfInjective _ perpLeviHom_injective).trans
    (MulEquiv.subgroupCongr map_perpLeviHom_highRootDJ)

theorem forall_normal_isPGroup_eq_bot_perpLevi [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ∀ N : Subgroup (EPilot.perpLevi .E7 K), N.Normal → IsPGroup 2 N → N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_perpLevi_eq (K := K)
  obtain ⟨hs, hnp⟩ := isSimpleGroup_rootSL2_highRootD (K := K) hq
  have hsJ : IsSimpleGroup (highRootDJ K) := by
    have := hs
    exact (highRootDJEquiv (K := K)).isSimpleGroup
  refine forall_normal_isPGroup_eq_bot_of_inf_centralizer_le S (J := highRootDJ K) ?_
    hsJ (fun hp => hnp (hp.of_equiv highRootDJEquiv))
  rw [sylow_inf_centralizer_eq_highRootDU S hS]
  intro x hx
  rw [highRootDU, mem_subgroupOf, mem_subgroupOf] at hx
  rw [highRootDJ, mem_subgroupOf, mem_subgroupOf]
  exact mem_sup_left hx

end D

section F5D


variable {K : Type} [Field K]

theorem exists_highRootDJ_eq_sup [CharP K 2] : ∃ nD : EPilot.perpLevi .E7 K,
    highRootDJ K = highRootDU K ⊔ (highRootDU K).map (MulAut.conj nD).toMonoidHom := by
  obtain ⟨n, hnJ, hn⟩ := exists_mem_conj_pinnedX_highRootD (K := K)
  have hnD : n ∈ rootSpan .E7 K (EPilot.perpRoots .E7) :=
    (sup_le rootSubgroup_highRootD_le_rootSpan_perpRoots.1
      rootSubgroup_highRootD_le_rootSpan_perpRoots.2) hnJ
  have hnC : n ∈ adjointGroup .E7 K := EPilot.rootSpan_le_adjointGroup' _ hnD
  refine ⟨⟨⟨n, hnC⟩, mem_subgroupOf.2 hnD⟩, ?_⟩
  apply map_injective perpLeviHom_injective
  rw [Subgroup.map_sup, map_perpLeviHom_highRootDJ, map_map_conj_eq, map_perpLeviHom_highRootDU]
  exact congrArg _ (map_conj_rootSubgroup_highRootD hn).symm

theorem rootSubgroup_highRootD_eq_map :
    rootSubgroup .E7 K highRootD = (rootSubgroup .E7 K (highRoot .E7)).map
      (MulAut.conj (e7RepConj K 0 : ModGL .E7 K)⁻¹).toMonoidHom := by
  have h := map_conj_e7RepConj_rootSubgroup (K := K) 0 (e7RepPreHigh_isRoot 0)
  rw [e7RepWeyl_smul_e7RepPreHigh] at h
  rw [← h, map_conj_map_conj, inv_mul_cancel, highRootD_eq]
  ext x
  simp

theorem exists_map_highRootDJ_eq [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (ι : EPilot.perpLevi .E7 K ≃* EPilot.perpLevi .E7 K) :
    ∃ c ∈ adjointGroup .E7 K, ((highRootDJ K).map ι.toMonoidHom).map (perpLeviHom K) =
      (EPilot.highRootSL2 .E7 K).map (MulAut.conj c).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_perpLevi_eq (K := K)
  obtain ⟨d, hd⟩ := exists_map_inf_centralizer_eq S ι
  rw [sylow_inf_centralizer_eq_highRootDU S hS] at hd
  obtain ⟨nD, hJ⟩ := exists_highRootDJ_eq_sup (K := K)
  have h := map_mulEquiv_sup_map_conj_eq (perpLeviHom K) ι (highRootDU K) nD d hd
  rw [← hJ, map_perpLeviHom_highRootDU, rootSubgroup_highRootD_eq_map, map_conj_map_conj,
    map_conj_map_conj] at h
  have hmemC : ∀ x : EPilot.perpLevi .E7 K, perpLeviHom K x ∈ adjointGroup .E7 K := fun x =>
    (x : adjointGroup .E7 K).2
  have hn₀ : ((e7RepConj K 0 : adjointGroup .E7 K) : ModGL .E7 K)⁻¹ ∈ adjointGroup .E7 K :=
    inv_mem (e7RepConj K 0).2
  rcases isPGroup_or_eq_conj_of_conj_highRoot 2 (mul_mem (hmemC d) hn₀)
      (mul_mem (hmemC (ι nD * d)) hn₀) with hp | ⟨c, hc, heq⟩
  · exfalso
    rw [← h] at hp
    obtain ⟨-, hnp⟩ := isSimpleGroup_rootSL2_highRootD (K := K) hq
    refine hnp ((hp.of_equiv ((((highRootDJ K).map ι.toMonoidHom).equivMapOfInjective _
      perpLeviHom_injective).symm.trans ((highRootDJ K).equivMapOfInjective _
        ι.injective).symm)).of_equiv highRootDJEquiv)
  · exact ⟨c, hc, h.trans heq⟩

end F5D

section Transport


variable {K : Type} [Field K]

theorem e7RepWeyl_zero_smul_highRoot : e7RepWeyl 0 • highRoot .E7 = rootXE7 := by
  have h := e7RepWeyl_smul_e7ASFrame 0
  simp only [e7ASFrame, e7RepFrames, Matrix.cons_val_zero, List.map_cons, List.map_nil] at h
  exact List.singleton_inj.1 h

theorem xLeviE7_eq_map : xLeviE7 K =
    (EPilot.perpLevi .E7 K).map (MulAut.conj (e7RepConj K 0)).toMonoidHom := by
  rw [xLeviE7, EPilot.rootPerpLevi, ← e7RepWeyl_zero_smul_highRoot,
    ← EPilot.map_conj_rootSpan_perpRoots (Or.inr (Or.inl rfl)) (e7RepWeyl 0), EPilot.perpLevi,
    CFSG.LieType.Chevalley.map_conj_subgroupOf (EPilot.rootSpan_le_adjointGroup' _)]
  rfl

variable (K) in
@[expose] noncomputable def perpLeviEquivXLevi : EPilot.perpLevi .E7 K ≃* xLeviE7 K :=
  ((EPilot.perpLevi .E7 K).equivMapOfInjective _ (MulAut.conj (e7RepConj K 0)).injective).trans
    (MulEquiv.subgroupCongr xLeviE7_eq_map.symm)

variable (K) in
@[expose] noncomputable def xLeviHom : xLeviE7 K →* ModGL .E7 K :=
  (adjointGroup .E7 K).subtype.comp (xLeviE7 K).subtype

theorem xLeviHom_injective : Function.Injective (xLeviHom K) :=
  (adjointGroup .E7 K).subtype_injective.comp (xLeviE7 K).subtype_injective

theorem xLeviHom_perpLeviEquivXLevi (x : EPilot.perpLevi .E7 K) :
    xLeviHom K (perpLeviEquivXLevi K x) =
      (e7RepConj K 0 : ModGL .E7 K) * perpLeviHom K x * (e7RepConj K 0 : ModGL .E7 K)⁻¹ := rfl

theorem map_xLeviHom_map_perpLeviEquivXLevi (H : Subgroup (EPilot.perpLevi .E7 K)) :
    (H.map (perpLeviEquivXLevi K).toMonoidHom).map (xLeviHom K) =
      (H.map (perpLeviHom K)).map (MulAut.conj (e7RepConj K 0 : ModGL .E7 K)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem factO2E7 [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) : FactO2E7 K :=
  EPilot.forall_normal_isPGroup_eq_bot_of_mulEquiv (perpLeviEquivXLevi K)
    (forall_normal_isPGroup_eq_bot_perpLevi hq)

theorem posJE7_subgroupOf_eq_map :
    (posJE7 K).subgroupOf (xLeviE7 K) = (highRootDJ K).map (perpLeviEquivXLevi K).toMonoidHom := by
  apply map_injective xLeviHom_injective
  rw [map_xLeviHom_map_perpLeviEquivXLevi, map_perpLeviHom_highRootDJ, highRootD_eq,
    map_conj_e7RepConj_rootSL2_preHigh 0]
  have hle : posJE7 K ≤ xLeviE7 K := posJE7_le_xLeviE7
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_subgroupOf.1 (mem_subgroupOf.1 hy)
  · intro hx
    have hxC : x ∈ adjointGroup .E7 K := EPilot.highRootSL2_le_adjointGroup hx
    exact ⟨⟨⟨x, hxC⟩, hle (mem_subgroupOf.2 hx)⟩, mem_subgroupOf.2 (mem_subgroupOf.2 hx), rfl⟩

theorem factF5E7 [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) : FactF5E7 K := by
  intro ι
  obtain ⟨c, hc, h⟩ := exists_map_highRootDJ_eq hq
    (((perpLeviEquivXLevi K).trans ι).trans (perpLeviEquivXLevi K).symm)
  refine ⟨e7RepConj K 0 * ⟨c, hc⟩, ?_⟩
  apply map_injective (adjointGroup .E7 K).subtype_injective
  have h2 := map_xLeviHom_map_perpLeviEquivXLevi ((highRootDJ K).map
    (((perpLeviEquivXLevi K).trans ι).trans (perpLeviEquivXLevi K).symm).toMonoidHom)
  rw [h, map_conj_map_conj, ← map_map_mulEquiv_conj, ← posJE7_subgroupOf_eq_map] at h2
  have hsub : (adjointGroup .E7 K).subtype (e7RepConj K 0 * ⟨c, hc⟩) =
      (e7RepConj K 0 : ModGL .E7 K) * c := by
    simp only [map_mul, Subgroup.coe_subtype]
  rw [Subgroup.map_map]
  refine h2.trans ?_
  rw [map_map_conj_eq, posJE7, subgroupOf_map_subtype,
    inf_eq_left.2 EPilot.highRootSL2_le_adjointGroup, hsub]

end Transport

end CFSG.SeitzReduction.E7Pilot
