module

public import CFSG.LargeExtraspecial.A2ModPLc
public import CFSG.LargeExtraspecial.A2ModSLModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module Matrix CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

variable {k : ℕ}

noncomputable abbrev elemTv (i j : Fin k) : SpecialLinearGroup (Fin k) (ZMod 2) :=
  tv (Pi.single i 1) (Pi.single j 1)

theorem elemTv_eq_transvection {i j : Fin k} (hij : i ≠ j) :
    elemTv i j = SpecialLinearGroup.transvection hij 1 :=
  (transvection_eq_tv hij 1).symm

theorem single_dotProduct_single_of_ne {i j : Fin k} (hij : i ≠ j) :
    (Pi.single j (1 : ZMod 2) : Fin k → ZMod 2) ⬝ᵥ Pi.single i 1 = 0 := by
  rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hij.symm]

theorem elemTv_mem_transvectionSet {i j : Fin k} (hij : i ≠ j) :
    elemTv i j ∈ transvectionSet k (ZMod 2) :=
  tv_mem_transvectionSet (Pi.single_ne_zero_iff.mpr one_ne_zero)
    (Pi.single_ne_zero_iff.mpr one_ne_zero) (single_dotProduct_single_of_ne hij)

theorem elemTv_eq_commutator {i l j : Fin k} (hil : i ≠ l) (hlj : l ≠ j) (hij : i ≠ j) :
    elemTv i j = ⁅elemTv i l, elemTv l j⁆ := by
  rw [elemTv_eq_transvection hij, elemTv_eq_transvection hil, elemTv_eq_transvection hlj,
    SpecialLinearGroup.commutatorElement_transvection hil hlj hij, mul_one]

section Commute

variable {X : Type*} [Group X] (Ψ : SpecialLinearGroup (Fin k) (ZMod 2) →* X) {a : X}

theorem commute_commutatorElement {x y : X} (hx : Commute a x) (hy : Commute a y) :
    Commute a ⁅x, y⁆ := by
  rw [commutatorElement_def]
  exact ((hx.mul_right hy).mul_right hx.inv_right).mul_right hy.inv_right

theorem commute_elemTv_of_lt
    (h : ∀ i j : Fin k, j.val + 1 = i.val → Commute a (Ψ (elemTv i j))) :
    ∀ i j : Fin k, j < i → Commute a (Ψ (elemTv i j)) := by
  have key : ∀ d : ℕ, ∀ i j : Fin k, i.val = j.val + d + 1 → Commute a (Ψ (elemTv i j)) := by
    intro d
    induction d with
    | zero => exact fun i j hij => h i j (by omega)
    | succ d ih =>
      intro i j hij
      set l : Fin k := ⟨j.val + 1, by omega⟩ with hl
      have hil : i ≠ l := fun e => by have := congrArg Fin.val e; simp [hl] at this; omega
      have hlj : l ≠ j := fun e => by have := congrArg Fin.val e; simp [hl] at this
      have hij' : i ≠ j := fun e => by have := congrArg Fin.val e; omega
      rw [elemTv_eq_commutator hil hlj hij', map_commutatorElement]
      exact commute_commutatorElement (ih i l (by simp [hl]; omega)) (h l j (by simp [hl]))
  intro i j hij
  rw [Fin.lt_def] at hij
  exact key (i.val - j.val - 1) i j (by omega)

theorem commute_elemTv_of_lt'
    (h : ∀ i j : Fin k, i.val + 1 = j.val → Commute a (Ψ (elemTv i j))) :
    ∀ i j : Fin k, i < j → Commute a (Ψ (elemTv i j)) := by
  have key : ∀ d : ℕ, ∀ i j : Fin k, j.val = i.val + d + 1 → Commute a (Ψ (elemTv i j)) := by
    intro d
    induction d with
    | zero => exact fun i j hij => h i j (by omega)
    | succ d ih =>
      intro i j hij
      set l : Fin k := ⟨i.val + 1, by omega⟩ with hl
      have hil : i ≠ l := fun e => by have := congrArg Fin.val e; simp [hl] at this
      have hlj : l ≠ j := fun e => by have := congrArg Fin.val e; simp [hl] at this; omega
      have hij' : i ≠ j := fun e => by have := congrArg Fin.val e; omega
      rw [elemTv_eq_commutator hil hlj hij', map_commutatorElement]
      exact commute_commutatorElement (h i l (by simp [hl])) (ih l j (by simp [hl]; omega))
  intro i j hij
  rw [Fin.lt_def] at hij
  exact key (j.val - i.val - 1) i j (by omega)

end Commute

theorem isSimpleGroup_sl_zmodTwo (hk : 3 ≤ k) :
    IsSimpleGroup (SpecialLinearGroup (Fin k) (ZMod 2)) := by
  have hs : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin k) (ZMod 2)) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 k (by omega) (.inl (by omega)) (.inl (by omega))
  have hZ := sl_center_eq_bot_of_card_two (n := k) (F := ZMod 2) (Nat.card_zmod 2)
  exact MulEquiv.isSimpleGroup
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

theorem injective_of_map_ne_one {X : Type*} [Group X] (hk : 3 ≤ k)
    (Ψ : SpecialLinearGroup (Fin k) (ZMod 2) →* X) {g : SpecialLinearGroup (Fin k) (ZMod 2)}
    (hg : Ψ g ≠ 1) : Function.Injective Ψ := by
  have := isSimpleGroup_sl_zmodTwo hk
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Ψ.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff Ψ).mp h
  · exact absurd (Ψ.mem_ker.mp (h ▸ Subgroup.mem_top g)) hg

section Action

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem A2Action.comp (hA : A2Action D Q ρ) {Y : Type} [Group Y] {f : Y →* X}
    (hf : Function.Injective f) {D' : Set Y} (hD' : ∀ y ∈ D', f y ∈ D) :
    A2Action D' Q (ρ.comp f) :=
  ⟨hA.nondegenerate, hA.injective.comp hf, fun y v => hA.map_apply (f y) v,
    fun y hy => hA.isTypeA (hD' y hy)⟩

theorem A2Action.comp_sl (hA : A2Action D Q ρ) (hk : 3 ≤ k)
    {Ψ : SpecialLinearGroup (Fin k) (ZMod 2) →* X}
    (hΨ : ∀ g ∈ transvectionSet k (ZMod 2), Ψ g ∈ D) :
    Function.Injective Ψ ∧ A2Action (transvectionSet k (ZMod 2)) Q (ρ.comp Ψ) := by
  have h01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := fun h => by simp [Fin.ext_iff] at h
  have hinj := injective_of_map_ne_one hk Ψ (hA.ne_one (hΨ _ (elemTv_mem_transvectionSet h01)))
  exact ⟨hinj, hA.comp hinj hΨ⟩

end Action

section Map

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {X Y : Type*} [Group X]
  [Group Y] (ρ : X →* (V ≃ₗ[K] V)) (f : Y →* X)

theorem commSpaceOf_map (H : Subgroup Y) :
    commSpaceOf ρ (H.map f) = commSpaceOf (ρ.comp f) H := by
  refine le_antisymm ((commSpaceOf_le_iff ρ).mpr fun x hx => ?_)
    ((commSpaceOf_le_iff _).mpr fun y hy => commSpace_le_commSpaceOf ρ ⟨y, hy, rfl⟩)
  obtain ⟨y, hy, rfl⟩ := hx
  exact commSpace_le_commSpaceOf (ρ.comp f) hy

theorem commSpaceOf_range : commSpaceOf ρ f.range = commSpaceOf (ρ.comp f) ⊤ := by
  rw [MonoidHom.range_eq_map, commSpaceOf_map]

end Map

@[expose] def coordSpace (S : Set (Fin k)) : Submodule (ZMod 2) (Fin k → ZMod 2) :=
  Submodule.pi Sᶜ fun _ => ⊥

theorem mem_coordSpace {S : Set (Fin k)} {w : Fin k → ZMod 2} :
    w ∈ coordSpace S ↔ ∀ l, l ∉ S → w l = 0 := by
  simp [coordSpace, Submodule.mem_pi]

theorem single_mem_coordSpace {S : Set (Fin k)} {l : Fin k} (hl : l ∈ S) :
    Pi.single l (1 : ZMod 2) ∈ coordSpace S :=
  mem_coordSpace.mpr fun l' hl' => Pi.single_eq_of_ne (fun e : l' = l => hl' (e ▸ hl)) 1

theorem single_dotProduct_eq_zero_of_mem_coordSpace {S : Set (Fin k)} {w : Fin k → ZMod 2}
    (hw : w ∈ coordSpace S) {l : Fin k} (hl : l ∉ S) : Pi.single l (1 : ZMod 2) ⬝ᵥ w = 0 := by
  rw [single_dotProduct, one_mul, mem_coordSpace.mp hw l hl]

theorem dotProduct_single_eq_zero_of_mem_coordSpace {S : Set (Fin k)} {ψ : Fin k → ZMod 2}
    (hψ : ψ ∈ coordSpace S) {l : Fin k} (hl : l ∉ S) : ψ ⬝ᵥ Pi.single l (1 : ZMod 2) = 0 := by
  rw [dotProduct_single, mul_one, mem_coordSpace.mp hψ l hl]

theorem dotProduct_eq_zero_of_mem_coordSpace {S T : Set (Fin k)} (hST : Disjoint S T)
    {ψ w : Fin k → ZMod 2} (hψ : ψ ∈ coordSpace T) (hw : w ∈ coordSpace S) : ψ ⬝ᵥ w = 0 := by
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l ∈ S
  · rw [mem_coordSpace.mp hψ l (Set.disjoint_left.mp hST hl), zero_mul]
  · rw [mem_coordSpace.mp hw l hl, mul_zero]

theorem single_add_ne_zero_of_mem_coordSpace {S : Set (Fin k)} {w : Fin k → ZMod 2}
    (hw : w ∈ coordSpace S) {i : Fin k} (hi : i ∉ S) : Pi.single i (1 : ZMod 2) + w ≠ 0 := by
  intro h
  have := congrFun h i
  rw [Pi.add_apply, Pi.single_eq_same, mem_coordSpace.mp hw i hi, add_zero] at this
  exact one_ne_zero this

theorem coordSpace_le {S : Set (Fin k)} {T : Submodule (ZMod 2) (Fin k → ZMod 2)}
    (h : ∀ l ∈ S, Pi.single l 1 ∈ T) : coordSpace S ≤ T := by
  intro w hw
  rw [← Finset.univ_sum_single w]
  refine T.sum_mem fun l _ => ?_
  by_cases hl : l ∈ S
  · rcases zmodTwo_eq_zero_or_one (w l) with h0 | h1
    · rw [h0, Pi.single_zero]
      exact T.zero_mem
    · rw [h1]
      exact h l hl
  · rw [mem_coordSpace.mp hw l hl, Pi.single_zero]
    exact T.zero_mem

section CommuteGrid

variable {X : Type*} [Group X] (Ψ : SpecialLinearGroup (Fin k) (ZMod 2) →* X) {a : X}

private def commLeft (a : X) (i : Fin k) : Submodule (ZMod 2) (Fin k → ZMod 2) where
  carrier := {v | v i = 0 ∧ Commute a (Ψ (tv v (Pi.single i 1)))}
  add_mem' := by
    rintro v w ⟨hv, hcv⟩ ⟨hw, hcw⟩
    refine ⟨by rw [Pi.add_apply, hv, hw, add_zero], ?_⟩
    have h1 : (Pi.single i (1 : ZMod 2) : Fin k → ZMod 2) ⬝ᵥ v = 0 := by
      rw [single_dotProduct, one_mul, hv]
    have h2 : (Pi.single i (1 : ZMod 2) : Fin k → ZMod 2) ⬝ᵥ w = 0 := by
      rw [single_dotProduct, one_mul, hw]
    rw [← tv_mul_tv_right h1 h2, map_mul]
    exact hcv.mul_right hcw
  zero_mem' := ⟨rfl, by rw [tv_zero_left, map_one]; exact Commute.one_right a⟩
  smul_mem' := by
    rintro c v hv
    rcases zmodTwo_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul]
      exact ⟨rfl, by rw [tv_zero_left, map_one]; exact Commute.one_right a⟩
    · rwa [one_smul]

private def commRight (a : X) (j : Fin k) : Submodule (ZMod 2) (Fin k → ZMod 2) where
  carrier := {ψ | ψ j = 0 ∧ Commute a (Ψ (tv (Pi.single j 1) ψ))}
  add_mem' := by
    rintro φ ψ ⟨hφ, hcφ⟩ ⟨hψ, hcψ⟩
    refine ⟨by rw [Pi.add_apply, hφ, hψ, add_zero], ?_⟩
    have h1 : φ ⬝ᵥ (Pi.single j (1 : ZMod 2) : Fin k → ZMod 2) = 0 := by
      rw [dotProduct_single, mul_one, hφ]
    have h2 : ψ ⬝ᵥ (Pi.single j (1 : ZMod 2) : Fin k → ZMod 2) = 0 := by
      rw [dotProduct_single, mul_one, hψ]
    rw [← tv_mul_tv_left h1 h2, map_mul]
    exact hcφ.mul_right hcψ
  zero_mem' := ⟨rfl, by rw [tv_zero_right, map_one]; exact Commute.one_right a⟩
  smul_mem' := by
    rintro c ψ hψ
    rcases zmodTwo_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul]
      exact ⟨rfl, by rw [tv_zero_right, map_one]; exact Commute.one_right a⟩
    · rwa [one_smul]

theorem commute_tv_left_of_mem_coordSpace {i : Fin k} {S : Set (Fin k)} (hi : i ∉ S)
    (h : ∀ l ∈ S, Commute a (Ψ (elemTv l i))) {w : Fin k → ZMod 2} (hw : w ∈ coordSpace S) :
    Commute a (Ψ (tv w (Pi.single i 1))) :=
  (coordSpace_le (T := commLeft Ψ a i) (fun l hl =>
    ⟨Pi.single_eq_of_ne (fun e : i = l => hi (e ▸ hl)) 1, h l hl⟩) hw).2

theorem commute_tv_right_of_mem_coordSpace {j : Fin k} {S : Set (Fin k)} (hj : j ∉ S)
    (h : ∀ l ∈ S, Commute a (Ψ (elemTv j l))) {ψ : Fin k → ZMod 2} (hψ : ψ ∈ coordSpace S) :
    Commute a (Ψ (tv (Pi.single j 1) ψ)) :=
  (coordSpace_le (T := commRight Ψ a j) (fun l hl =>
    ⟨Pi.single_eq_of_ne (fun e : j = l => hj (e ▸ hl)) 1, h l hl⟩) hψ).2

end CommuteGrid

theorem conj_elemTv_eq {i j : Fin k} {S₁ S₂ : Set (Fin k)} (hi₁ : i ∉ S₁) (hj₁ : j ∉ S₁)
    (hi₂ : i ∉ S₂) (hj₂ : j ∉ S₂) (hS : Disjoint S₁ S₂) {w ψ : Fin k → ZMod 2}
    (hw : w ∈ coordSpace S₁) (hψ : ψ ∈ coordSpace S₂) :
    (tv w (Pi.single i 1) * tv (Pi.single j 1) ψ) * elemTv i j *
        (tv w (Pi.single i 1) * tv (Pi.single j 1) ψ)⁻¹ =
      tv (Pi.single i 1 + w) (Pi.single j 1 + ψ) := by
  have hwi : (Pi.single i (1 : ZMod 2) : Fin k → ZMod 2) ⬝ᵥ w = 0 :=
    single_dotProduct_eq_zero_of_mem_coordSpace hw hi₁
  have hψj : ψ ⬝ᵥ (Pi.single j (1 : ZMod 2) : Fin k → ZMod 2) = 0 :=
    dotProduct_single_eq_zero_of_mem_coordSpace hψ hj₂
  have hψi : ψ ⬝ᵥ (Pi.single i (1 : ZMod 2) : Fin k → ZMod 2) = 0 :=
    dotProduct_single_eq_zero_of_mem_coordSpace hψ hi₂
  have hwj : (Pi.single j (1 : ZMod 2) : Fin k → ZMod 2) ⬝ᵥ w = 0 :=
    single_dotProduct_eq_zero_of_mem_coordSpace hw hj₁
  have hψw : ψ ⬝ᵥ w = 0 := dotProduct_eq_zero_of_mem_coordSpace hS hψ hw
  rw [conj_tv, sl_mulVec_mul, tv_mulVec_of_dotProduct_eq_zero hψi, tv_mulVec hwi,
    single_dotProduct, one_mul, Pi.single_eq_same, one_smul, contra_mul,
    contra_tv hψj, single_dotProduct, one_mul, Pi.single_eq_same, one_smul,
    contra_tv_of_dotProduct_eq_zero (by rw [sub_dotProduct, hwj, hψw, sub_zero]),
    sub_eq_add_neg, ZModModule.neg_eq_self]

section PointMaps

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure IsPointMaps (ρ' : SpecialLinearGroup (Fin n) (ZMod 2) →* (V ≃ₗ[ZMod 2] V))
    (Q : QuadraticForm (ZMod 2) V) (P Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V) : Prop where
  injective : Function.Injective P
  injective_dual : Function.Injective Pd
  map_mulVec : ∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2),
    P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = ρ' g (P x)
  map_contra : ∀ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (φ : Fin n → ZMod 2),
    Pd (contra g φ) = ρ' g (Pd φ)
  commSpace_tv : ∀ v φ : Fin n → ZMod 2, v ≠ 0 → φ ≠ 0 → φ ⬝ᵥ v = 0 →
    commSpace (ρ' (tv v φ)) = Submodule.span (ZMod 2) {P v, Pd φ}
  range_inf_range : LinearMap.range P ⊓ LinearMap.range Pd = ⊥
  map_eq_zero : ∀ x, Q (P x) = 0
  map_eq_zero_dual : ∀ φ, Q (Pd φ) = 0
  commSpaceOf_top : commSpaceOf ρ' ⊤ = LinearMap.range P ⊔ LinearMap.range Pd

variable [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {ρ' : SpecialLinearGroup (Fin n) (ZMod 2) →* (V ≃ₗ[ZMod 2] V)}

theorem exists_isPointMaps (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ') (hn : 5 ≤ n) :
    ∃ P Pd, IsPointMaps ρ' Q P Pd := by
  obtain ⟨P, Pd, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := exists_pointMaps hA hn
  exact ⟨P, Pd, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem exists_isPointMaps_or_finrank_le (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ')
    (hn : 4 ≤ n) :
    (∃ P Pd, IsPointMaps ρ' Q P Pd) ∨ finrank (ZMod 2) (commSpaceOf ρ' ⊤) ≤ n + 3 := by
  rcases exists_pointMaps_or_finrank_le hA hn with
    ⟨P, Pd, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ | h
  · exact .inl ⟨P, Pd, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · exact .inr h

theorem IsPointMaps.finrank_commSpaceOf_top {P Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V}
    (h : IsPointMaps ρ' Q P Pd) : finrank (ZMod 2) (commSpaceOf ρ' ⊤) = 2 * n := by
  rw [h.commSpaceOf_top, finrank_range_sup_range_eq h.injective h.injective_dual
    h.range_inf_range]

end PointMaps

end CFSG.LargeExtraspecial.A2Mod
