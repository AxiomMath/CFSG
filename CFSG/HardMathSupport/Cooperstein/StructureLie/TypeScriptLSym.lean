module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLHeart
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLModels

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.ComponentClassification.OutcomeLocal CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open scoped commutatorElement

section Faithful

variable {m : ℕ}

theorem single_add_single_eq_one {i k j : Fin m} (h : (Pi.single i (1 : ZMod 2) +
    Pi.single k (1 : ZMod 2) : Fin m → ZMod 2) j = 1) : j = i ∨ j = k := by
  by_contra hcon
  push Not at hcon
  simp [hcon.1, hcon.2] at h

theorem perm_eq_one_of_pair_fixed (hm : 3 ≤ m) (σ : Equiv.Perm (Fin m))
    (h : ∀ i k : Fin m, i ≠ k → permCoord σ (Pi.single i 1 + Pi.single k 1) =
      Pi.single i 1 + Pi.single k 1) : σ = 1 := by
  refine Equiv.ext fun i => ?_
  have hone : ∀ k : Fin m, k ≠ i → σ i = i ∨ σ i = k := by
    intro k hki
    have := congrFun (h i k hki.symm) (σ i)
    rw [permCoord_apply, show σ⁻¹ (σ i) = i by simp] at this
    apply single_add_single_eq_one (i := i) (k := k)
    rw [← this]
    simp [Pi.single_eq_of_ne hki.symm]
  have hcard : 1 < (Finset.univ.erase i : Finset (Fin m)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  have ha' := hone a (Finset.ne_of_mem_erase ha)
  have hb' := hone b (Finset.ne_of_mem_erase hb)
  simp only [Equiv.Perm.coe_one, id_eq]
  rcases ha' with h1 | h1
  · exact h1
  · rcases hb' with h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hab

theorem sumZeroRep_injective (hm : 3 ≤ m) : Function.Injective (sumZeroRep m) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine perm_eq_one_of_pair_fixed hm σ fun i k _ => ?_
  have hx := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m) =>
    (g : sumZero m →ₗ[ZMod 2] sumZero m) (pairVec i k)) hσ
  simp only [sumZeroRep_apply, Units.val_one, Module.End.one_apply] at hx
  have := congrArg (fun y : sumZero m => (y : Fin m → ZMod 2)) hx
  simpa only [coe_sumZeroEquiv, coe_pairVec] using this

theorem heartRep_injective (hm : 5 ≤ m) : Function.Injective (heartRep m) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine perm_eq_one_of_pair_fixed (by omega) σ fun i k hik => ?_
  have hx := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m ⧸ onesLine m) =>
    (g : (sumZero m ⧸ onesLine m) →ₗ[ZMod 2] (sumZero m ⧸ onesLine m))
      (Submodule.Quotient.mk (pairVec i k))) hσ
  simp only [heartRep_apply_mk, Units.val_one, Module.End.one_apply] at hx
  rw [Submodule.Quotient.eq] at hx
  obtain ⟨c, hc⟩ := mem_onesLine.mp hx
  have hc' : ∀ j, permCoord σ (Pi.single i 1 + Pi.single k 1) j -
      (Pi.single i 1 + Pi.single k 1 : Fin m → ZMod 2) j = c := by
    intro j
    have := congrFun hc j
    simpa only [Submodule.coe_sub, Pi.sub_apply, coe_sumZeroEquiv, coe_pairVec] using this
  have hc0 : c = 0 := by
    classical
    obtain ⟨j, hj⟩ : ∃ j : Fin m, j ∉ ({σ i, σ k, i, k} : Finset (Fin m)) := by
      by_contra hall
      push Not at hall
      have hsub : (Finset.univ : Finset (Fin m)) ⊆ {σ i, σ k, i, k} := fun j _ => hall j
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_le_four (a := σ i) (b := σ k) (c := i) (d := k)
      rw [Finset.card_univ, Fintype.card_fin] at h1
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    obtain ⟨h1, h2, h3, h4⟩ := hj
    rw [← hc' j, permCoord_apply]
    have e1 : σ⁻¹ j ≠ i := fun h => h1 (by rw [← h]; simp)
    have e2 : σ⁻¹ j ≠ k := fun h => h2 (by rw [← h]; simp)
    simp only [Pi.add_apply, Pi.single_eq_of_ne e1, Pi.single_eq_of_ne e2,
      Pi.single_eq_of_ne h3, Pi.single_eq_of_ne h4]
    simp
  funext j
  have := hc' j
  rw [hc0, sub_eq_zero] at this
  exact this

end Faithful

section Model

variable {m : ℕ}

theorem mem_evenWeight_iff_sum {x : Fin m → ZMod 2} : x ∈ evenWeight m ↔ ∑ i, x i = 0 := by
  simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]

@[expose] def sumZeroEquivEvenWeight (m : ℕ) : sumZero m ≃+ evenWeight m where
  toFun x := ⟨x.1, mem_evenWeight_iff_sum.mpr x.2⟩
  invFun y := ⟨y.1, mem_evenWeight_iff_sum.mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem sumZeroEquivEvenWeight_sumZeroEquiv (σ : Equiv.Perm (Fin m)) (u : sumZero m) :
    sumZeroEquivEvenWeight m (sumZeroEquiv σ u) = evenWeightPerm σ (sumZeroEquivEvenWeight m u) :=
  rfl

theorem exists_const_iff_mem_zmultiples (f : Fin m → ZMod 2) :
    (∃ c : ZMod 2, f = fun _ => c) ↔ f ∈ AddSubgroup.zmultiples (allOnes m) := by
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨(c.val : ℤ), by funext j; simp [allOnes]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(k : ZMod 2), by funext j; simp [allOnes]⟩

theorem map_onesLine_eq_evenWeightOnes (m : ℕ) :
    (onesLine m).toAddSubgroup.map (sumZeroEquivEvenWeight m).toAddMonoidHom =
      evenWeightOnes m := by
  ext y
  rw [AddSubgroup.mem_map_equiv, evenWeightOnes, AddSubgroup.mem_addSubgroupOf,
    Submodule.mem_toAddSubgroup, mem_onesLine]
  exact exists_const_iff_mem_zmultiples _

@[expose] def heartEquivAltHeart (m : ℕ) : (sumZero m ⧸ onesLine m) ≃+ altHeart m :=
  QuotientAddGroup.congr (onesLine m).toAddSubgroup (evenWeightOnes m)
    (sumZeroEquivEvenWeight m) (map_onesLine_eq_evenWeightOnes m)

theorem heartEquivAltHeart_mk (u : sumZero m) :
    heartEquivAltHeart m (Submodule.Quotient.mk u) =
      ((sumZeroEquivEvenWeight m u : evenWeight m) : altHeart m) :=
  rfl

@[expose] def sumZeroEquivAltHeart (m : ℕ) (hm : Odd m) : sumZero m ≃+ altHeart m :=
  (sumZeroEquivEvenWeight m).trans
    ((QuotientAddGroup.quotientBot (G := evenWeight m)).symm.trans
      (QuotientAddGroup.quotientAddEquivOfEq (by
        rw [← map_onesLine_eq_evenWeightOnes m, onesLine_eq_bot hm]
        simp)))

section Generic

variable {W V : Type} [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup V] [Module (ZMod 2) V]

theorem isAltModel_of_rep (hm : 5 ≤ m)
    (ρ : Equiv.Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) V)
    (hinj : Function.Injective ρ) (mk : sumZero m → V) (q : V ≃+ altHeart m)
    (hq : ∀ u, q (mk u) = ((sumZeroEquivEvenWeight m u : evenWeight m) : altHeart m))
    (hρ : ∀ σ u, (ρ σ : V →ₗ[ZMod 2] V) (mk u) = mk (sumZeroEquiv σ u))
    (β : W ≃ₗ[ZMod 2] V) {H T : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)}
    (hH : H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom = ρ.range)
    (hT : T = ⁅H, H⁆) : IsAltModel T m := by
  set c := LinearMap.GeneralLinearGroup.congrLinearEquiv β with hc
  have h5 : 5 ≤ Nat.card (Fin m) := by simpa using hm
  have hTc : T.map c.toMonoidHom = (alternatingGroup (Fin m)).map ρ := by
    have h : ⁅(⊤ : Subgroup (Equiv.Perm (Fin m))), ⊤⁆ = alternatingGroup (Fin m) := by
      rw [← _root_.commutator_def]
      exact alternatingGroup.commutator_perm_eq h5
    rw [hT, Subgroup.map_commutator, hH, MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]
  let ψ : alternatingGroup (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) W :=
    c.symm.toMonoidHom.comp (ρ.comp (alternatingGroup (Fin m)).subtype)
  have hψT : ∀ a, ψ a ∈ T := by
    intro a
    have : ρ a ∈ T.map c.toMonoidHom := by
      rw [hTc]; exact ⟨a, a.2, rfl⟩
    obtain ⟨t, ht, hta⟩ := this
    have : ψ a = t := by
      change c.symm (ρ a) = t
      rw [← hta]; exact c.symm_apply_apply t
    rw [this]; exact ht
  let θ' : alternatingGroup (Fin m) →* T := ψ.codRestrict T hψT
  have hθ'inj : Function.Injective θ' := by
    intro a b hab
    have : ψ a = ψ b := congrArg Subtype.val hab
    have h2 : ρ a = ρ b := c.symm.injective this
    exact Subtype.ext (hinj h2)
  have hθ'surj : Function.Surjective θ' := by
    intro g
    have : c g.1 ∈ (alternatingGroup (Fin m)).map ρ := by
      rw [← hTc]; exact ⟨g.1, g.2, rfl⟩
    obtain ⟨a, ha, hag⟩ := this
    refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
    change c.symm (ρ a) = g.1
    rw [hag]; exact c.symm_apply_apply g.1
  let θ : T ≃* alternatingGroup (Fin m) :=
    (MulEquiv.ofBijective θ' ⟨hθ'inj, hθ'surj⟩).symm
  have hθ : ∀ g : T, ρ (θ g : Equiv.Perm (Fin m)) = c g.1 := by
    intro g
    have h1 : θ' (θ g) = g := (MulEquiv.ofBijective θ' ⟨hθ'inj, hθ'surj⟩).apply_symm_apply g
    have h2 : c.symm (ρ (θ g : Equiv.Perm (Fin m))) = g.1 := congrArg Subtype.val h1
    rw [← h2]; exact (c.apply_symm_apply _).symm
  refine ⟨β.toAddEquiv.trans q, θ, ?_⟩
  intro g w x hx
  obtain ⟨u, rfl⟩ := (sumZeroEquivEvenWeight m).surjective x
  have hβw : β w = mk u := by
    apply q.injective
    rw [hq]
    exact hx
  have hcg : β (((g.1 : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w) =
      ((c g.1 : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) (β w) := by
    rw [hc, LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]
    simp
  show q (β (((g.1 : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w)) = _
  rw [hcg, ← hθ g, hβw, hρ, hq]
  rfl

end Generic

theorem isAltModel_of_sumZero {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {m : ℕ}
    (hm : 5 ≤ m) (hodd : Odd m) (β : W ≃ₗ[ZMod 2] sumZero m)
    {H T : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)}
    (hH : H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
      (sumZeroRep m).range)
    (hT : T = ⁅H, H⁆) : IsAltModel T m :=
  isAltModel_of_rep hm (sumZeroRep m) (sumZeroRep_injective (by omega)) id
    (sumZeroEquivAltHeart m hodd) (fun _ => rfl) (fun _ _ => rfl) β hH hT

theorem isAltModel_of_heart {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {m : ℕ}
    (hm : 5 ≤ m) (β : W ≃ₗ[ZMod 2] (sumZero m ⧸ onesLine m))
    {H T : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)}
    (hH : H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
      (heartRep m).range)
    (hT : T = ⁅H, H⁆) : IsAltModel T m :=
  isAltModel_of_rep hm (heartRep m) (heartRep_injective hm) Submodule.Quotient.mk
    (heartEquivAltHeart m) (fun _ => rfl) (fun _ _ => rfl) β hH hT

end Model

end CFSG.HardMathSupport.Cooperstein.StructureLie
