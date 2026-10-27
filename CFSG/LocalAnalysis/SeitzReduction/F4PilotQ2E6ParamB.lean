module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelA
public import CFSG.Timmesfeld.LieEmbed.F4Edge
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RowEnd
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RowFamily

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open Matrix
open scoped commutatorElement
open CFSG.Timmesfeld.LieEmbed (exists_hom_of_steinbergRels isSign_eq_one exists_sl3ToF4 f4n c3ToF4
  c3ToF4_single)

local instance f4PilotQ2E6ParamBNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance f4PilotQ2E6ParamBNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def a2Pos13 (m : Fin (Tag.rank .E6)) : ℕ := (![2, 0, 2, 1, 2, 2] : Fin 6 → ℕ) m

@[expose] def a2Root13 (i j : Fin 3) : Fin (Tag.rank .E6) → ℤ := fun m =>
  if a2Pos13 m = 2 then 0 else
    (if i.val ≤ a2Pos13 m ∧ a2Pos13 m < j.val then 1 else 0) -
      (if j.val ≤ a2Pos13 m ∧ a2Pos13 m < i.val then 1 else 0)

@[expose] def a2Node13 (i : Fin 2) : Fin (Tag.rank .E6) := (![1, 3] : Fin 2 → Fin 6) i

set_option maxRecDepth 100000 in
theorem a2Root13_check : ∀ i j : Fin 3, i ≠ j → a2Root13 i j ∈ rootFinset .E6 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a2Root13_add_check : ∀ i j l : Fin 3, a2Root13 i j + a2Root13 j l = a2Root13 i l := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a2Root13_add_ne_zero_check : ∀ i j k l : Fin 3,
    (i ≠ j ∧ k ≠ l ∧ ¬ (k = j ∧ l = i)) → a2Root13 i j + a2Root13 k l ≠ 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem not_isRoot_a2Root13_add_check : ∀ i j k l : Fin 3,
    (i ≠ j ∧ k ≠ l ∧ ¬ (k = j ∧ l = i) ∧ j ≠ k ∧ i ≠ l) →
      ¬ (a2Root13 i j + a2Root13 k l ∈ rootFinset .E6) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a2Root13_castSucc_succ (i : Fin 2) :
    a2Root13 i.castSucc i.succ = Pi.single (a2Node13 i) 1 := by
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
theorem a2Root13_succ_castSucc (i : Fin 2) :
    a2Root13 i.succ i.castSucc = -Pi.single (a2Node13 i) 1 := by
  revert i
  decide +kernel

theorem a2Root13_zero_one : a2Root13 0 1 = Pi.single 1 1 := a2Root13_castSucc_succ 0

theorem a2Root13_one_zero : a2Root13 1 0 = -Pi.single 1 1 := a2Root13_succ_castSucc 0

theorem a2Root13_one_two : a2Root13 1 2 = Pi.single 3 1 := a2Root13_castSucc_succ 1

theorem a2Root13_two_one : a2Root13 2 1 = -Pi.single 3 1 := a2Root13_succ_castSucc 1

theorem exists_a2Node13_eq : ∀ j ∈ e6TwoA2Nodes, ∃ i : Fin 2, a2Node13 i = j := by
  decide

theorem a2Node13_mem : ∀ i : Fin 2, a2Node13 i ∈ e6TwoA2Nodes := by
  decide

theorem isRoot_a2Root13 {i j : Fin 3} (h : i ≠ j) : IsRoot .E6 (a2Root13 i j) :=
  mem_rootFinset.1 (a2Root13_check i j h)

theorem a2Root13_add (i j l : Fin 3) : a2Root13 i j + a2Root13 j l = a2Root13 i l :=
  a2Root13_add_check i j l

theorem a2Root13_add_ne_zero {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l)
    (hex : ¬ (k = j ∧ l = i)) : a2Root13 i j + a2Root13 k l ≠ 0 :=
  a2Root13_add_ne_zero_check i j k l ⟨hij, hkl, hex⟩

theorem not_isRoot_a2Root13_add {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l)
    (hex : ¬ (k = j ∧ l = i)) (hjk : j ≠ k) (hil : i ≠ l) :
    ¬ IsRoot .E6 (a2Root13 i j + a2Root13 k l) := fun h =>
  not_isRoot_a2Root13_add_check i j k l ⟨hij, hkl, hex, hjk, hil⟩ (mem_rootFinset.2 h)

section Hom

variable {k : Type} [Field k] [CharP k 2]


theorem a2Root13_commutator {i j k' l : Fin 3} (hij : i ≠ j) (hkl : k' ≠ l)
    (hex : ¬ (k' = j ∧ l = i)) (c d : k) :
    ⁅e6Data_valid.xm k (a2Root13 i j) c, e6Data_valid.xm k (a2Root13 k' l) d⁆ =
      if j = k' then e6Data_valid.xm k (a2Root13 i l) (c * d)
      else if i = l then e6Data_valid.xm k (a2Root13 k' j) (-(c * d)) else 1 := by
  obtain ⟨hroot, hnot⟩ := e6Data_valid.commutator_xm k (isRoot_a2Root13 hij)
    (isRoot_a2Root13 hkl) (a2Root13_add_ne_zero hij hkl hex)
  by_cases hjk : j = k'
  · subst hjk
    have hil : i ≠ l := fun h => hex ⟨rfl, h.symm⟩
    rw [ite_eq_left rfl]
    have hs : a2Root13 i j + a2Root13 j l = a2Root13 i l := a2Root13_add i j l
    obtain ⟨σ, hσ, h⟩ := hroot (hs ▸ isRoot_a2Root13 hil)
    rw [h, isSign_eq_one hσ, one_mul, hs]
  · rw [ite_eq_right hjk]
    by_cases hil : i = l
    · subst hil
      rw [ite_eq_left rfl]
      have hkj : k' ≠ j := fun h => hjk h.symm
      have hs : a2Root13 i j + a2Root13 k' i = a2Root13 k' j := by
        rw [add_comm, a2Root13_add]
      obtain ⟨σ, hσ, h⟩ := hroot (hs ▸ isRoot_a2Root13 hkj)
      rw [h, isSign_eq_one hσ, one_mul, hs, CharTwo.neg_eq]
    · rw [ite_eq_right hil]
      exact hnot (not_isRoot_a2Root13_add hij hkl hex hjk hil) c d

variable [Finite k]

theorem exists_sl3ToE6Sc13 : ∃ φ : SpecialLinearGroup (Fin 3) k →* e6Data_valid.minGroup k,
    ∀ (i j : Fin 3) (hij : i ≠ j) (c : k),
      φ (SpecialLinearGroup.transvection hij c) = e6Data_valid.xm k (a2Root13 i j) c :=
  exists_hom_of_steinbergRels (m := 2) le_rfl
    (x := fun i j c => e6Data_valid.xm k (a2Root13 i j) c)
    (fun _ _ _ c d => (e6Data_valid.xm_add k _ c d).symm) fun _ _ _ _ hij hkl hex c d =>
      a2Root13_commutator hij hkl hex c d

variable (k) in
@[expose] noncomputable def sl3ToE6Sc13 : SpecialLinearGroup (Fin 3) k →* e6Data_valid.minGroup k :=
  (exists_sl3ToE6Sc13 (k := k)).choose

theorem sl3ToE6Sc13_transvection {i j : Fin 3} (hij : i ≠ j) (c : k) :
    sl3ToE6Sc13 k (SpecialLinearGroup.transvection hij c) = e6Data_valid.xm k (a2Root13 i j) c :=
  (exists_sl3ToE6Sc13 (k := k)).choose_spec i j hij c

theorem range_sl3ToE6Sc13 : (sl3ToE6Sc13 k).range = e6ScLevi k e6TwoA2Nodes := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map,
      ← CFSG.LieType.Universal.SpecialLinear.iSup_fundamentalRootSubgroup_eq_top (m := 2)
        (F := k), Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    rintro _ ⟨g, hg, rfl⟩
    have hrank : CFSG.LieType.CurtisTits.rankOne (e6Datum k).rootGroup (a2Node13 i) ≤
        e6ScLevi k e6TwoA2Nodes := CFSG.LieType.CurtisTits.rankOne_le_levi _ (a2Node13_mem i)
    cases s
    · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ g).1 hg
      refine hrank (mem_sup_right ?_)
      rw [sl3ToE6Sc13_transvection, a2Root13_succ_castSucc]
      exact e6Data_valid.xm_mem_rootGroup k _ c
    · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ g).1 hg
      refine hrank (mem_sup_left ?_)
      rw [sl3ToE6Sc13_transvection, a2Root13_castSucc_succ]
      exact e6Data_valid.xm_mem_rootGroup k _ c
  · refine iSup₂_le fun j hj => sup_le ?_ ?_
    · obtain ⟨i, rfl⟩ := exists_a2Node13_eq j hj
      intro g hg
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hg
      refine ⟨SpecialLinearGroup.transvection (show i.castSucc ≠ i.succ from
        Fin.castSucc_lt_succ.ne) c, ?_⟩
      rw [sl3ToE6Sc13_transvection, a2Root13_castSucc_succ]
    · obtain ⟨i, rfl⟩ := exists_a2Node13_eq j hj
      intro g hg
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hg
      refine ⟨SpecialLinearGroup.transvection (show i.succ ≠ i.castSucc from
        Fin.castSucc_lt_succ.ne') c, ?_⟩
      rw [sl3ToE6Sc13_transvection, a2Root13_succ_castSucc]

theorem sl3ToE6Sc13_injective (hk : Nat.card k = 2) : Function.Injective (sl3ToE6Sc13 k) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hnt : ∃ g, sl3ToE6Sc13 k g ≠ 1 := by
    refine ⟨SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1, ?_⟩
    rw [sl3ToE6Sc13_transvection]
    intro h
    have h0 : e6Data_valid.xm k (a2Root13 0 1) 0 = 1 := e6Data_valid.xm_zero k _
    exact one_ne_zero (e6Data_valid.xm_injective k (isRoot_a2Root13 (by decide))
      (h.trans h0.symm))
  have hker : g ∈ center (SpecialLinearGroup (Fin 3) k) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 k le_rfl) hnt hg
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hker
  have := Fintype.ofFinite k
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Fintype.card_fin, zero_pow (by norm_num)] at hr
    exact zero_ne_one hr
  have hr1 : r = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one r hr0
    rwa [← Nat.card_eq_fintype_card, hk, show 2 - 1 = 1 from rfl, pow_one] at h
  apply Subtype.ext
  rw [← hrg, hr1, map_one]
  rfl

variable (k) in
@[expose] noncomputable def sl3EquivA2 (hk : Nat.card k = 2) :
    SpecialLinearGroup (Fin 3) k ≃* e6ScLevi k e6TwoA2Nodes :=
  (MonoidHom.ofInjective (sl3ToE6Sc13_injective hk)).trans
    (MulEquiv.subgroupCongr range_sl3ToE6Sc13)

theorem coe_sl3EquivA2 (hk : Nat.card k = 2) (g : SpecialLinearGroup (Fin 3) k) :
    ((sl3EquivA2 k hk g : e6ScLevi k e6TwoA2Nodes) : e6Data_valid.minGroup k) =
      sl3ToE6Sc13 k g :=
  rfl

end Hom

section HomExt

variable {k : Type} [Field k]

theorem e6ScLevi_hom_ext {H : Type*} [Group H] {J : Finset (Fin (Tag.rank .E6))}
    {f₁ f₂ : e6ScLevi k J →* H}
    (h : ∀ j ∈ J, ∀ γ : Fin (Tag.rank .E6) → ℤ, (γ = Pi.single j 1 ∨ γ = -Pi.single j 1) →
      ∀ (c : k) (hx : e6Data_valid.xm k γ c ∈ e6ScLevi k J), f₁ ⟨_, hx⟩ = f₂ ⟨_, hx⟩) :
    f₁ = f₂ := by
  have hle : e6ScLevi k J ≤ (MonoidHom.eqLocus f₁ f₂).map (e6ScLevi k J).subtype := by
    refine iSup₂_le fun j hj => sup_le ?_ ?_ <;> intro y hy
    · have hyS : y ∈ e6ScLevi k J :=
        CFSG.LieType.CurtisTits.rankOne_le_levi _ hj (mem_sup_left hy)
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hy
      exact ⟨⟨_, hyS⟩, h j hj _ (Or.inl rfl) c hyS, rfl⟩
    · have hyS : y ∈ e6ScLevi k J :=
        CFSG.LieType.CurtisTits.rankOne_le_levi _ hj (mem_sup_right hy)
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hy
      exact ⟨⟨_, hyS⟩, h j hj _ (Or.inr rfl) c hyS, rfl⟩
  refine MonoidHom.ext fun y => ?_
  obtain ⟨y', hy', hyy'⟩ := hle y.2
  have : y' = y := Subtype.ext hyy'
  rw [← this]
  exact hy'

theorem e6ScLevi_map_mem {H : Type*} [Group H] {J : Finset (Fin (Tag.rank .E6))}
    (f : e6ScLevi k J →* H) (M : Subgroup H)
    (h : ∀ j ∈ J, ∀ γ : Fin (Tag.rank .E6) → ℤ, (γ = Pi.single j 1 ∨ γ = -Pi.single j 1) →
      ∀ (c : k) (hx : e6Data_valid.xm k γ c ∈ e6ScLevi k J), f ⟨_, hx⟩ ∈ M)
    (x : e6ScLevi k J) : f x ∈ M := by
  have hle : e6ScLevi k J ≤ (M.comap f).map (e6ScLevi k J).subtype := by
    refine iSup₂_le fun j hj => sup_le ?_ ?_ <;> intro y hy
    · have hyS : y ∈ e6ScLevi k J :=
        CFSG.LieType.CurtisTits.rankOne_le_levi _ hj (mem_sup_left hy)
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hy
      exact ⟨⟨_, hyS⟩, h j hj _ (Or.inl rfl) c hyS, rfl⟩
    · have hyS : y ∈ e6ScLevi k J :=
        CFSG.LieType.CurtisTits.rankOne_le_levi _ hj (mem_sup_right hy)
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hy
      exact ⟨⟨_, hyS⟩, h j hj _ (Or.inr rfl) c hyS, rfl⟩
  obtain ⟨y', hy', hyy'⟩ := hle x.2
  have : y' = x := Subtype.ext hyy'
  rw [← this]
  exact hy'

theorem xm_mem_e6ScLevi {J : Finset (Fin (Tag.rank .E6))} {j : Fin (Tag.rank .E6)} (hj : j ∈ J)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ = Pi.single j 1 ∨ γ = -Pi.single j 1) (c : k) :
    e6Data_valid.xm k γ c ∈ e6ScLevi k J := by
  refine CFSG.LieType.CurtisTits.rankOne_le_levi _ hj ?_
  rcases hγ with rfl | rfl
  · exact mem_sup_left (e6Data_valid.xm_mem_rootGroup k _ c)
  · exact mem_sup_right (e6Data_valid.xm_mem_rootGroup k _ c)

end HomExt

section Model

variable {k : Type} [Field k] [Finite k] [CharP k 2]


variable (k) in
@[expose] noncomputable def sl3ToF4Long : SpecialLinearGroup (Fin 3) k →* adjointGroup .F4 k :=
  (exists_sl3ToF4 (K := k)).choose

theorem sl3ToF4Long_zero_one (c : k) :
    sl3ToF4Long k (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c) =
      Adjoint.f4Par k (Pi.single 0 1) c := by
  have h := ((exists_sl3ToF4 (K := k)).choose_spec.2 c).1
  rw [CFSG.Timmesfeld.tv_of_ne (show (0 : Fin 3) ≠ 1 by decide)] at h
  exact h

theorem sl3ToF4Long_one_zero (c : k) :
    sl3ToF4Long k (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c) =
      Adjoint.f4Par k (-Pi.single 0 1) c := by
  have h := ((exists_sl3ToF4 (K := k)).choose_spec.2 c).2.1
  rw [CFSG.Timmesfeld.tv_of_ne (show (1 : Fin 3) ≠ 0 by decide)] at h
  exact h

theorem sl3ToF4Long_one_two (c : k) :
    sl3ToF4Long k (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c) =
      Adjoint.f4Par k (Pi.single 1 1) c := by
  have h := ((exists_sl3ToF4 (K := k)).choose_spec.2 c).2.2.1
  rw [CFSG.Timmesfeld.tv_of_ne (show (1 : Fin 3) ≠ 2 by decide)] at h
  exact h

theorem sl3ToF4Long_two_one (c : k) :
    sl3ToF4Long k (SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c) =
      Adjoint.f4Par k (-Pi.single 1 1) c := by
  have h := ((exists_sl3ToF4 (K := k)).choose_spec.2 c).2.2.2.1
  rw [CFSG.Timmesfeld.tv_of_ne (show (2 : Fin 3) ≠ 1 by decide)] at h
  exact h

variable (k) in
@[expose] noncomputable def longA2Model (hk : Nat.card k = 2) :
    e6ScLevi k e6TwoA2Nodes →* adjointGroup .F4 k :=
  (sl3ToF4Long k).comp (sl3EquivA2 k hk).symm.toMonoidHom

theorem longA2Model_transvection (hk : Nat.card k = 2) {i j : Fin 3} (hij : i ≠ j) (c : k)
    (h : e6Data_valid.xm k (a2Root13 i j) c ∈ e6ScLevi k e6TwoA2Nodes) :
    longA2Model k hk ⟨e6Data_valid.xm k (a2Root13 i j) c, h⟩ =
      sl3ToF4Long k (SpecialLinearGroup.transvection hij c) := by
  have e1 : (sl3EquivA2 k hk).symm ⟨e6Data_valid.xm k (a2Root13 i j) c, h⟩ =
      SpecialLinearGroup.transvection hij c := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [coe_sl3EquivA2, sl3ToE6Sc13_transvection]
  rw [longA2Model, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e1]

theorem longA2Model_xm_one (hk : Nat.card k = 2) (c : k)
    (h : e6Data_valid.xm k (Pi.single 1 1) c ∈ e6ScLevi k e6TwoA2Nodes) :
    longA2Model k hk ⟨_, h⟩ = Adjoint.f4Par k (Pi.single 0 1) c := by
  have h' : e6Data_valid.xm k (a2Root13 0 1) c ∈ e6ScLevi k e6TwoA2Nodes := by
    rwa [a2Root13_zero_one]
  have e1 : (⟨e6Data_valid.xm k (Pi.single 1 1) c, h⟩ : e6ScLevi k e6TwoA2Nodes) = ⟨_, h'⟩ :=
    Subtype.ext (show e6Data_valid.xm k (Pi.single 1 1) c =
      e6Data_valid.xm k (a2Root13 0 1) c by rw [a2Root13_zero_one])
  rw [e1, longA2Model_transvection hk (show (0 : Fin 3) ≠ 1 by decide), sl3ToF4Long_zero_one]

theorem longA2Model_xm_neg_one (hk : Nat.card k = 2) (c : k)
    (h : e6Data_valid.xm k (-Pi.single 1 1) c ∈ e6ScLevi k e6TwoA2Nodes) :
    longA2Model k hk ⟨_, h⟩ = Adjoint.f4Par k (-Pi.single 0 1) c := by
  have h' : e6Data_valid.xm k (a2Root13 1 0) c ∈ e6ScLevi k e6TwoA2Nodes := by
    rwa [a2Root13_one_zero]
  have e1 : (⟨e6Data_valid.xm k (-Pi.single 1 1) c, h⟩ : e6ScLevi k e6TwoA2Nodes) = ⟨_, h'⟩ :=
    Subtype.ext (show e6Data_valid.xm k (-Pi.single 1 1) c =
      e6Data_valid.xm k (a2Root13 1 0) c by rw [a2Root13_one_zero])
  rw [e1, longA2Model_transvection hk (show (1 : Fin 3) ≠ 0 by decide), sl3ToF4Long_one_zero]

theorem longA2Model_xm_three (hk : Nat.card k = 2) (c : k)
    (h : e6Data_valid.xm k (Pi.single 3 1) c ∈ e6ScLevi k e6TwoA2Nodes) :
    longA2Model k hk ⟨_, h⟩ = Adjoint.f4Par k (Pi.single 1 1) c := by
  have h' : e6Data_valid.xm k (a2Root13 1 2) c ∈ e6ScLevi k e6TwoA2Nodes := by
    rwa [a2Root13_one_two]
  have e1 : (⟨e6Data_valid.xm k (Pi.single 3 1) c, h⟩ : e6ScLevi k e6TwoA2Nodes) = ⟨_, h'⟩ :=
    Subtype.ext (show e6Data_valid.xm k (Pi.single 3 1) c =
      e6Data_valid.xm k (a2Root13 1 2) c by rw [a2Root13_one_two])
  rw [e1, longA2Model_transvection hk (show (1 : Fin 3) ≠ 2 by decide), sl3ToF4Long_one_two]

theorem longA2Model_xm_neg_three (hk : Nat.card k = 2) (c : k)
    (h : e6Data_valid.xm k (-Pi.single 3 1) c ∈ e6ScLevi k e6TwoA2Nodes) :
    longA2Model k hk ⟨_, h⟩ = Adjoint.f4Par k (-Pi.single 1 1) c := by
  have h' : e6Data_valid.xm k (a2Root13 2 1) c ∈ e6ScLevi k e6TwoA2Nodes := by
    rwa [a2Root13_two_one]
  have e1 : (⟨e6Data_valid.xm k (-Pi.single 3 1) c, h⟩ : e6ScLevi k e6TwoA2Nodes) = ⟨_, h'⟩ :=
    Subtype.ext (show e6Data_valid.xm k (-Pi.single 3 1) c =
      e6Data_valid.xm k (a2Root13 2 1) c by rw [a2Root13_two_one])
  rw [e1, longA2Model_transvection hk (show (2 : Fin 3) ≠ 1 by decide), sl3ToF4Long_two_one]

end Model

section Param

variable {k : Type} [Field k] [Finite k] [CharP k 2]


variable {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def twoE6ParamB (e : L ≃* adjointGroup .F4 k) (hk : Nat.card k = 2) :
    e6ScLevi k e6TwoA2Nodes →* G :=
  L.subtype.comp (e.symm.toMonoidHom.comp (longA2Model k hk))

theorem twoE6ParamB_apply (e : L ≃* adjointGroup .F4 k) (hk : Nat.card k = 2)
    (x : e6ScLevi k e6TwoA2Nodes) :
    twoE6ParamB e hk x = ((e.symm (longA2Model k hk x) : L) : G) :=
  rfl

theorem range_twoE6ParamB_le (e : L ≃* adjointGroup .F4 k) (hk : Nat.card k = 2) :
    (twoE6ParamB e hk).range ≤ L := by
  rintro _ ⟨x, rfl⟩
  exact (e.symm (longA2Model k hk x)).2

theorem levi6Hom_refl_x (e : L ≃* adjointGroup .F4 k) (γ : Fin 3 → ℤ) (c : k) :
    levi6Hom e (RingEquiv.refl k) (Sp.x 3 k γ c) =
      ((e.symm (Adjoint.f4Par k (c3ToF4 γ) c) : L) : G) := by
  simp only [levi6Hom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, statedSpCongr_x,
    RingEquiv.refl_apply, Subgroup.coe_subtype]
  rw [c3LeviEquiv_x]

theorem agree_twoE6ParamB (e : L ≃* adjointGroup .F4 k) (hk : Nat.card k = 2)
    {ΦA : e6ScLevi k e6A5Nodes →* G} (hn : IsLeviNormalizedA e ΦA) :
    ∀ x : e6ScLevi k {3}, scLeviRestrict ΦA three_subset_e6A5Nodes x =
      scLeviRestrict (twoE6ParamB e hk) three_subset_e6TwoA2Nodes x := by
  have hext : scLeviRestrict ΦA three_subset_e6A5Nodes =
      scLeviRestrict (twoE6ParamB e hk) three_subset_e6TwoA2Nodes := by
    refine e6ScLevi_hom_ext fun j hj γ hγ c hx => ?_
    rw [Finset.mem_singleton] at hj
    subst hj
    rw [scLeviRestrict_apply, scLeviRestrict_apply, twoE6ParamB_apply]
    rcases hγ with rfl | rfl
    · have hA : ∀ hx' : e6Data_valid.xm k (Pi.single 3 1) c ∈ e6ScLevi k e6A5Nodes,
          (⟨_, hx'⟩ : e6ScLevi k e6A5Nodes) =
            graphParamEquiv k (RingEquiv.refl k) (sp6ToSL6 (Sp.x 3 k (Pi.single 2 1) c)) :=
        fun hx' => Subtype.ext (by rw [coe_graphParamEquiv, graphParamHom_sp6ToSL6_x_single_two])
      rw [hA, hn, levi6Hom_refl_x, longA2Model_xm_three, c3ToF4_single]
      rfl
    · have hA : ∀ hx' : e6Data_valid.xm k (-Pi.single 3 1) c ∈ e6ScLevi k e6A5Nodes,
          (⟨_, hx'⟩ : e6ScLevi k e6A5Nodes) =
            graphParamEquiv k (RingEquiv.refl k) (sp6ToSL6 (Sp.x 3 k (-Pi.single 2 1) c)) :=
        fun hx' => Subtype.ext (by
          rw [coe_graphParamEquiv, graphParamHom_sp6ToSL6_x_neg_single_two])
      rw [hA, hn, levi6Hom_refl_x, longA2Model_xm_neg_three, map_neg, c3ToF4_single]
      rfl
  exact fun x => DFunLike.congr_fun hext x

theorem le_sup_range_twoE6ParamB (e : L ≃* adjointGroup .F4 k) (hk : Nat.card k = 2) :
    L ≤ subgroupToG e (C3Levi k) ⊔ (twoE6ParamB e hk).range := by
  have hct := CFSG.LieType.Steinberg.Adjoint.f4_isCTGroupDatum k
  have hgen : ⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum k).leviAmalgam J = ⊤ :=
    CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
      (CFSG.LieType.RootSystem.isCTRootSystem
        (CFSG.LieType.Steinberg.Adjoint.f4Datum k).isFiniteType
        (CFSG.LieType.Steinberg.Adjoint.f4Datum k).divisible) hct
  set φ : adjointGroup .F4 k →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have h1 : (1 : Fin (Tag.rank .E6)) ∈ e6TwoA2Nodes := by decide
  have hone : ∀ j : Fin (Tag.rank .F4),
      (CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup j).map φ ≤
        subgroupToG e (C3Levi k) ⊔ (twoE6ParamB e hk).range := by
    intro j
    by_cases h0 : j = 0
    · subst h0
      refine le_sup_of_le_right ?_
      rw [CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨g, hg, rfl⟩
        obtain ⟨c, rfl⟩ := (Adjoint.mem_rootGroup_iff (isRoot_single _ 0) g).1 hg
        refine ⟨⟨_, xm_mem_e6ScLevi h1 (Or.inl rfl) c⟩, ?_⟩
        rw [twoE6ParamB_apply, longA2Model_xm_one]
        rfl
      · rintro _ ⟨g, hg, rfl⟩
        obtain ⟨c, rfl⟩ := (Adjoint.mem_rootGroup_iff (isRoot_neg_single _ 0) g).1 hg
        refine ⟨⟨_, xm_mem_e6ScLevi h1 (Or.inr rfl) c⟩, ?_⟩
        rw [twoE6ParamB_apply, longA2Model_xm_neg_one]
        rfl
    · refine le_sup_of_le_left ?_
      have hj0 : (⟨0, by decide⟩ : Fin (Tag.rank .F4)) ≠ j := fun h => h0 (h.symm.trans rfl)
      have hle : CFSG.LieType.CurtisTits.rankOne
          (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup j ≤ C3Levi k := by
        rw [CFSG.LieType.CurtisTits.rankOne]
        refine sup_le (rootGroup_le_C3Levi ⟨isRoot_single _ j, Pi.single_eq_of_ne hj0 1⟩)
          (rootGroup_le_C3Levi ⟨isRoot_neg_single _ j, ?_⟩)
        rw [Pi.neg_apply, Pi.single_eq_of_ne hj0, neg_zero]
      calc _ ≤ (C3Levi k).map φ := map_mono hle
        _ = subgroupToG e (C3Levi k) := by
          rw [hφdef, ← Subgroup.map_map]
          rfl
  have hle : (⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum k).leviAmalgam J).map φ ≤
      subgroupToG e (C3Levi k) ⊔ (twoE6ParamB e hk).range := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun J => ?_
    change (⨆ j ∈ J.1, CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup j).map φ ≤ _
    rw [Subgroup.map_iSup]
    refine iSup_le fun j => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun _ => hone j
  intro l hl
  have hmem : e ⟨l, hl⟩ ∈ ⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum k).leviAmalgam J :=
    hgen ▸ mem_top _
  have hφl : φ (e ⟨l, hl⟩) = l := by
    rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  rw [← hφl]
  exact hle (mem_map_of_mem φ hmem)

theorem sup_range_twoE6ParamB (e : L ≃* adjointGroup .F4 k) (hk : Nat.card k = 2)
    {X₀ : Subgroup (adjointGroup .F4 k)} {ΦA : e6ScLevi k e6A5Nodes →* G}
    (hA : ΦA.range = centralizerPerfectCore (subgroupToG e X₀))
    (hD : subgroupToG e (C3Levi k) ≤ centralizerPerfectCore (subgroupToG e X₀)) :
    ΦA.range ⊔ (twoE6ParamB e hk).range = twoE6Span e X₀ := by
  rw [hA, twoE6Span]
  refine le_antisymm (sup_le le_sup_left ((range_twoE6ParamB_le e hk).trans le_sup_right))
    (sup_le le_sup_left ?_)
  exact (le_sup_range_twoE6ParamB e hk).trans (sup_le (hD.trans le_sup_left) le_sup_right)

theorem twoE6ParamB_one_mem (e : L ≃* adjointGroup .F4 k) (hk : Nat.card k = 2)
    (a : e6ScLevi k {1}) :
    scLeviRestrict (twoE6ParamB e hk) one_subset_e6TwoA2Nodes a ∈
      subgroupToG e (CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Steinberg.Adjoint.f4Datum k).rootGroup 0) := by
  refine e6ScLevi_map_mem _ _ (fun j hj γ hγ c hx => ?_) a
  rw [Finset.mem_singleton] at hj
  subst hj
  rw [scLeviRestrict_apply, twoE6ParamB_apply]
  rcases hγ with rfl | rfl
  · rw [longA2Model_xm_one]
    exact ⟨_, ⟨_, mem_sup_left (Adjoint.xPar_mem (isRoot_single _ 0) c), rfl⟩, rfl⟩
  · rw [longA2Model_xm_neg_one]
    exact ⟨_, ⟨_, mem_sup_right (Adjoint.xPar_mem (isRoot_neg_single _ 0) c), rfl⟩, rfl⟩

end Param

end CFSG.SeitzReduction.F4Pilot
