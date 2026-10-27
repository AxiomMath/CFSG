module

public import CFSG.LieType.Ree.Duality
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley

section SignedSwap

variable {L R : Type*} [CommRing R] (p : L → Prop) [DecidablePred p] (σ : L ≃ L) (u : L → R)

@[expose] def signedSwap : Module.End R (L →₀ R) :=
  Finsupp.linearCombination R fun b => if p b then 0 else u b • Finsupp.single (σ b) 1

theorem signedSwap_single (b : L) :
    signedSwap p σ u (Finsupp.single b 1) = if p b then 0 else u b • Finsupp.single (σ b) 1 := by
  rw [signedSwap, Finsupp.linearCombination_single, one_smul]

theorem signedSwap_apply (x : L →₀ R) (a : L) :
    signedSwap p σ u x a = if p (σ.symm a) then 0 else u (σ.symm a) * x (σ.symm a) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply]
    split_ifs <;> ring
  | single b r =>
    rw [← Finsupp.smul_single_one, map_smul, signedSwap_single, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
    by_cases hb : σ b = a
    · subst hb
      simp only [Equiv.symm_apply_apply, Finsupp.single_eq_same, mul_one]
      split_ifs <;> simp [mul_comm]
    · have hb' : σ.symm a ≠ b := fun h => hb (by rw [← h, Equiv.apply_symm_apply])
      split_ifs <;> simp [hb, hb'.symm]

variable {p σ u}

theorem ker_signedSwap (hu : ∀ b, IsUnit (u b)) :
    LinearMap.ker (signedSwap p σ u) = Finsupp.supported R R {b | p b} := by
  ext x
  rw [LinearMap.mem_ker, Finsupp.mem_supported']
  constructor
  · intro h b hb
    have := DFunLike.congr_fun h (σ b)
    rw [signedSwap_apply, Equiv.symm_apply_apply, ite_eq_right (show ¬p b from hb),
      Finsupp.coe_zero, Pi.zero_apply] at this
    exact (hu b).mul_right_eq_zero.1 this
  · intro h
    ext a
    rw [signedSwap_apply, Finsupp.coe_zero, Pi.zero_apply]
    split_ifs with ha
    · rfl
    · rw [h _ (show σ.symm a ∉ {b | p b} from ha), mul_zero]

theorem range_signedSwap (hσ : ∀ b, p (σ b) ↔ ¬p b) (hu : ∀ b, u b * u b = 1) :
    LinearMap.range (signedSwap p σ u) = Finsupp.supported R R {b | p b} := by
  have hσ' : ∀ a, p a ↔ ¬p (σ.symm a) := fun a => by
    simpa using hσ (σ.symm a)
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [Finsupp.mem_supported']
    intro a ha
    have : p (σ.symm a) := by
      by_contra h
      exact ha ((hσ' a).2 h)
    rw [signedSwap_apply, ite_eq_left this]
  · rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨u (σ.symm a) • Finsupp.single (σ.symm a) 1, ?_⟩
    rw [map_smul, signedSwap_single, ite_eq_right ((hσ' a).1 ha), smul_smul, hu, one_smul,
      Equiv.apply_symm_apply]

theorem signedSwap_mul_self (hσ : ∀ b, p (σ b) ↔ ¬p b) (hu : ∀ b, u b * u b = 1) :
    signedSwap p σ u * signedSwap p σ u = 0 := by
  have hu' : ∀ b, IsUnit (u b) := fun b => IsUnit.of_mul_eq_one _ (hu b)
  refine LinearMap.ext fun x => ?_
  have : signedSwap p σ u x ∈ LinearMap.ker (signedSwap p σ u) := by
    rw [ker_signedSwap hu', ← range_signedSwap hσ hu]
    exact LinearMap.mem_range_self _ x
  exact this

end SignedSwap

namespace ReeTag

variable (t : ReeTag)

@[expose] def sign (α : Fin t.tag.rank → ℤ) : ℤ :=
  if t = G2 ∧ (List.ofFn α = [2, 3] ∨ List.ofFn α = [-2, -3]) then -1 else 1

theorem sign_mul_self (α : Fin t.tag.rank → ℤ) : t.sign α * t.sign α = 1 := by
  unfold sign
  split_ifs <;> norm_num

@[expose] def IsShortLabel : Label t.tag → Prop
  | .inl i => i ∉ t.longSet
  | .inr α => t.lengthParam α.1 = 1

instance : DecidablePred t.IsShortLabel := fun b =>
  match b with
  | .inl i => inferInstanceAs (Decidable (i ∉ t.longSet))
  | .inr α => inferInstanceAs (Decidable (t.lengthParam α.1 = 1))

@[expose] def shortLabels : Set (Label t.tag) :=
  {b | t.IsShortLabel b}

variable (R : Type*) [CommRing R]

@[expose] def shortModule : Submodule R (RootModule t.tag R) :=
  Submodule.span R ((fun i => hVec t.tag R i) '' {i | i ∉ t.longSet} ∪
    (fun α => rootVec t.tag R α) '' t.shortRoots)

open _root_.Classical in
@[expose] def lengthMap : Module.End R (RootModule t.tag R) :=
  Finsupp.linearCombination R fun b =>
    match b with
    | .inl i => if i ∈ t.longSet then hVec t.tag R (t.perm i) else 0
    | .inr α =>
      if α.1 ∈ t.longRoots then (t.sign α.1 : R) • rootVec t.tag R (t.dualRoot α.1) else 0

variable {t R}

theorem lengthMap_hVec_of_mem {i : Fin t.tag.rank} (hi : i ∈ t.longSet) :
    t.lengthMap R (hVec t.tag R i) = hVec t.tag R (t.perm i) := by
  change t.lengthMap R (Finsupp.single (Sum.inl i) 1) = _
  rw [lengthMap, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left hi

theorem lengthMap_hVec_of_notMem {i : Fin t.tag.rank} (hi : i ∉ t.longSet) :
    t.lengthMap R (hVec t.tag R i) = 0 := by
  change t.lengthMap R (Finsupp.single (Sum.inl i) 1) = _
  rw [lengthMap, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_right hi

theorem lengthMap_rootVec_of_mem_longRoots {α : Fin t.tag.rank → ℤ} (hα : α ∈ t.longRoots) :
    t.lengthMap R (rootVec t.tag R α) = (t.sign α : R) • rootVec t.tag R (t.dualRoot α) := by
  rw [rootVec, dite_eq_left hα.1, lengthMap, Finsupp.linearCombination_single, one_smul]
  exact ite_eq_left hα

theorem lengthMap_rootVec_of_mem_shortRoots {α : Fin t.tag.rank → ℤ} (hα : α ∈ t.shortRoots) :
    t.lengthMap R (rootVec t.tag R α) = 0 := by
  rw [rootVec, dite_eq_left hα.1, lengthMap, Finsupp.linearCombination_single, one_smul]
  refine ite_eq_right fun h => ?_
  exact (lengthParam_eq_one_iff_ne hα.1).1 hα.2 h.2

variable (t) in
theorem perm_perm (i : Fin t.tag.rank) : t.perm (t.perm i) = i := by
  cases t <;> revert i <;> decide

variable (t) in
@[expose] def dualLabelFun : Label t.tag → Label t.tag
  | .inl i => .inl (t.perm i)
  | .inr α => .inr ⟨t.dualRoot α.1, isRoot_dualRoot α.2⟩

theorem dualLabelFun_involutive : Function.Involutive t.dualLabelFun := by
  rintro (i | ⟨α, hα⟩)
  · simp [dualLabelFun, perm_perm]
  · simp [dualLabelFun, dualRoot_dualRoot hα]

variable (t) in
@[expose] def dualLabel : Equiv.Perm (Label t.tag) :=
  dualLabelFun_involutive.toPerm _

variable (t) in
@[expose] def labelSign : Label t.tag → ℤ
  | .inl _ => 1
  | .inr α => t.sign α.1

theorem labelSign_mul_self (b : Label t.tag) :
    ((t.labelSign b : ℤ) : R) * t.labelSign b = 1 := by
  rw [← Int.cast_mul]
  rcases b with i | α
  · simp [labelSign]
  · simp [labelSign, sign_mul_self]

theorem isShortLabel_dualLabel (b : Label t.tag) :
    t.IsShortLabel (t.dualLabel b) ↔ ¬t.IsShortLabel b := by
  rcases b with i | ⟨α, hα⟩
  · change t.perm i ∉ t.longSet ↔ ¬i ∉ t.longSet
    cases t <;> revert i <;> decide
  · exact lengthParam_dualRoot_eq_one_iff hα

theorem lengthMap_eq_signedSwap :
    t.lengthMap R = signedSwap t.IsShortLabel t.dualLabel fun b => (t.labelSign b : R) := by
  unfold lengthMap signedSwap
  congr 1
  funext b
  rcases b with i | ⟨α, hα⟩ <;> dsimp only
  · by_cases hi : i ∈ t.longSet
    · rw [ite_eq_left hi, ite_eq_right (show ¬t.IsShortLabel (.inl i) from not_not.2 hi)]
      simp [labelSign, dualLabel, dualLabelFun, hVec]
    · rw [ite_eq_right hi, ite_eq_left (show t.IsShortLabel (.inl i) from hi)]
  · by_cases hl : t.lengthParam α = t.prime
    · rw [ite_eq_left (show α ∈ t.longRoots from ⟨hα, hl⟩),
        ite_eq_right (show ¬t.IsShortLabel (.inr ⟨α, hα⟩) from
          fun h => (lengthParam_eq_one_iff_ne hα).1 h hl)]
      simp [labelSign, dualLabel, dualLabelFun, rootVec, isRoot_dualRoot hα]
    · rw [ite_eq_right (show α ∉ t.longRoots from fun h => hl h.2),
        ite_eq_left (show t.IsShortLabel (.inr ⟨α, hα⟩) from
          (lengthParam_eq_one_iff_ne hα).2 hl)]

variable (t R) in
theorem shortModule_eq_supported :
    t.shortModule R = Finsupp.supported R R t.shortLabels := by
  rw [Finsupp.supported_eq_span_single, shortModule]
  congr 1
  ext v
  simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, shortLabels]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨α, ⟨hα, hα1⟩, rfl⟩)
    · exact ⟨.inl i, hi, rfl⟩
    · exact ⟨.inr ⟨α, hα⟩, hα1, by rw [rootVec, dite_eq_left hα]⟩
  · rintro ⟨b, hb, rfl⟩
    rcases b with i | ⟨α, hα⟩
    · exact Or.inl ⟨i, hb, rfl⟩
    · exact Or.inr ⟨α, ⟨hα, hb⟩, by rw [rootVec, dite_eq_left hα]⟩

variable (t R) in
@[expose] def shortBasis : Module.Basis t.shortLabels R (t.shortModule R) :=
  (Finsupp.basisSingleOne.map (Finsupp.supportedEquivFinsupp t.shortLabels).symm).map
    (LinearEquiv.ofEq _ _ (t.shortModule_eq_supported R).symm)

theorem coe_shortBasis (b : t.shortLabels) :
    (t.shortBasis R b : RootModule t.tag R) = Finsupp.single b.1 1 := by
  simp [shortBasis]

variable (t) in
@[expose] def shortDim : ℕ :=
  match t with
  | G2 => 7
  | F4 => 26

variable (t) in
theorem card_shortLabels : Nat.card t.shortLabels = t.shortDim := by
  have h1 : Nat.card {i : Fin t.tag.rank // i ∉ t.longSet} = t.tag.rank - t.longSet.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
  have h2 : Nat.card {α : {v : Fin t.tag.rank → ℤ // IsRoot t.tag v} //
      t.lengthParam α.1 = 1} = t.halfRootCount := by
    rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun v => IsRoot t.tag v)
      (fun v => t.lengthParam v = 1)), ← ncard_shortRoots t]
    rfl
  rw [shortLabels, Set.coe_ofPred, Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
  change Nat.card {i : Fin t.tag.rank // i ∉ t.longSet} +
    Nat.card {α : {v : Fin t.tag.rank → ℤ // IsRoot t.tag v} // t.lengthParam α.1 = 1} = _
  rw [h1, h2]
  cases t <;> rfl

end ReeTag

end CFSG.LieType.Ree
