module

public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.Open.SteinbergPresentationMilestoneDefs
import all CFSG.LieType.Universal.SpecialLinearRoots

public section

namespace CFSG.LieType.Steinberg.SL

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.RootSystem
open scoped commutatorElement

variable {m : ℕ} {F : Type} [Field F]

@[expose] noncomputable def stGen (s : Fin (m + 1) × Fin (m + 1) × F) :
    SpecialLinearGroup (Fin (m + 1)) F :=
  if h : s.1 ≠ s.2.1 then SpecialLinearGroup.transvection h s.2.2 else 1

theorem stGen_of_ne {i j : Fin (m + 1)} (hij : i ≠ j) (c : F) :
    stGen (i, j, c) = SpecialLinearGroup.transvection hij c :=
  dite_eq_left hij

theorem stGen_self (i : Fin (m + 1)) (c : F) : stGen (i, i, c) = 1 :=
  dite_eq_right (not_not.2 rfl)

theorem x_eq_stGen (γ : Fin m → ℤ) (c : F) :
    x m F γ c = stGen ((pairOf m γ).1, (pairOf m γ).2, c) :=
  rfl

private theorem transvection_inv' {i j : Fin (m + 1)} (hij : i ≠ j) (c : F) :
    (SpecialLinearGroup.transvection hij c)⁻¹ = SpecialLinearGroup.transvection hij (-c) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← SpecialLinearGroup.transvection_add, neg_add_cancel,
    SpecialLinearGroup.transvection_coeff_zero]

theorem commutatorElement_stGen {i j k l : Fin (m + 1)} (hij : i ≠ j) (hkl : k ≠ l)
    (hnot : ¬ (k = j ∧ l = i)) (c d : F) :
    ⁅stGen (i, j, c), stGen (k, l, d)⁆ =
      if j = k then stGen (i, l, c * d) else if i = l then stGen (k, j, -(c * d)) else 1 := by
  rw [stGen_of_ne hij, stGen_of_ne hkl]
  by_cases hjk : j = k
  · subst hjk
    have hil : i ≠ l := fun e => hnot ⟨rfl, e.symm⟩
    rw [ite_eq_left rfl, stGen_of_ne hil]
    exact SpecialLinearGroup.commutatorElement_transvection hij hkl hil c d
  · rw [ite_eq_right hjk]
    by_cases hil : i = l
    · subst hil
      have hkj : k ≠ j := fun e => hjk e.symm
      rw [ite_eq_left rfl, stGen_of_ne hkj, ← commutatorElement_inv,
        SpecialLinearGroup.commutatorElement_transvection hkl hij hkj d c, transvection_inv',
        mul_comm d c]
    · rw [ite_eq_right hil, commutatorElement_eq_one_iff_commute]
      exact SpecialLinearGroup.commute_transvection hij hkl hjk (fun e => hil e.symm) c d

theorem stGen_rels :
    ∀ r ∈ CFSG.Open.steinbergSLRels (m + 1) F, FreeGroup.lift stGen r = 1 := by
  rintro r ((⟨i, c, rfl⟩ | ⟨i, j, c, d, hij, rfl⟩) | ⟨i, j, k, l, c, d, hij, hkl, hnot, rfl⟩)
  · rw [FreeGroup.lift_apply_of, stGen_self]
  · rw [map_mul, map_mul, map_inv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, stGen_of_ne hij, stGen_of_ne hij, stGen_of_ne hij,
      SpecialLinearGroup.transvection_add, mul_inv_cancel]
  · have h := commutatorElement_stGen hij hkl hnot c d
    rw [commutatorElement_def] at h
    have hite : FreeGroup.lift stGen
        (if j = k then FreeGroup.of (i, l, c * d)
          else if i = l then FreeGroup.of (k, j, -(c * d)) else 1) =
        if j = k then stGen (i, l, c * d) else if i = l then stGen (k, j, -(c * d)) else 1 := by
      split_ifs <;> simp [FreeGroup.lift_apply_of]
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, hite, ← h, mul_inv_cancel]

@[expose] noncomputable def stHom :
    PresentedGroup (CFSG.Open.steinbergSLRels (m + 1) F) →* SpecialLinearGroup (Fin (m + 1)) F :=
  PresentedGroup.toGroup stGen_rels

theorem stHom_of (s : Fin (m + 1) × Fin (m + 1) × F) :
    stHom (PresentedGroup.of s) = stGen s :=
  PresentedGroup.toGroup.of _

private theorem mk_eq_one_of_mem {r : FreeGroup (Fin (m + 1) × Fin (m + 1) × F)}
    (hr : r ∈ CFSG.Open.steinbergSLRels (m + 1) F) :
    (QuotientGroup.mk r : PresentedGroup (CFSG.Open.steinbergSLRels (m + 1) F)) = 1 :=
  (QuotientGroup.eq_one_iff r).2 (Subgroup.subset_normalClosure hr)

@[expose] noncomputable def symbolOf (g : ChevGen (Φ (m := m) (F := F)) F) :
    Fin (m + 1) × Fin (m + 1) × F :=
  ((pairOf m g.1.1).1, (pairOf m g.1.1).2, g.2)

private theorem lift_symbolOf (w : FreeGroup (ChevGen (Φ (m := m) (F := F)) F)) :
    FreeGroup.lift (fun g => (PresentedGroup.of (symbolOf g) :
      PresentedGroup (CFSG.Open.steinbergSLRels (m + 1) F))) w =
      QuotientGroup.mk (FreeGroup.map symbolOf w) := by
  have h : FreeGroup.lift (fun g => (PresentedGroup.of (symbolOf g) :
      PresentedGroup (CFSG.Open.steinbergSLRels (m + 1) F))) =
      (PresentedGroup.mk (CFSG.Open.steinbergSLRels (m + 1) F)).comp (FreeGroup.map symbolOf) := by
    ext g
    rfl
  rw [h]
  rfl

private theorem map_chevOf {γ : Fin m → ℤ} (hγ : γ ∈ (Φ (m := m) (F := F)).roots) (c : F) :
    FreeGroup.map symbolOf (chevOf (Φ := Φ (m := m) (F := F)) γ c) =
      FreeGroup.of ((pairOf m γ).1, (pairOf m γ).2, c) := by
  rw [chevOf, dite_eq_left hγ, FreeGroup.map.of]
  rfl

private theorem list_eq_singleton' {l : List (ℕ × ℕ)} (hl : l.Nodup)
    (h : ∀ p, p ∈ l ↔ p = (1, 1)) : l = [(1, 1)] :=
  List.perm_singleton.1 ((List.perm_ext_iff_of_nodup hl (List.nodup_singleton _)).2
    fun p => by rw [h, List.mem_singleton])

theorem symbolOf_rels (O : CommOrder (Φ (m := m) (F := F))) :
    ∀ r ∈ relA (Φ (m := m) (F := F)) F ∪ relB (Φ (m := m) (F := F)) F O (commC (m := m)),
      FreeGroup.lift (fun g => (PresentedGroup.of (symbolOf g) :
        PresentedGroup (CFSG.Open.steinbergSLRels (m + 1) F))) r = 1 := by
  rintro r (⟨γ, hγ, c, d, rfl⟩ | ⟨α, hα, β, hβ, hαβ, c, d, rfl⟩)
  · rw [lift_symbolOf]
    refine mk_eq_one_of_mem (Or.inl (Or.inr ⟨_, _, c, d, (pairOf_spec (m := m) hγ).1, ?_⟩))
    rw [map_mul, map_mul, map_inv, map_chevOf hγ, map_chevOf hγ, map_chevOf hγ]
  · rw [lift_symbolOf]
    obtain ⟨hij, hα'⟩ := pairOf_spec (m := m) hα
    obtain ⟨hkl, hβ'⟩ := pairOf_spec (m := m) hβ
    set i := (pairOf m α).1
    set j := (pairOf m α).2
    set k := (pairOf m β).1
    set l := (pairOf m β).2
    have hnopp : ¬ (k = j ∧ l = i) := by
      rintro ⟨e1, e2⟩
      apply hαβ
      apply toStd_injective m
      rw [toStd_add, hα', hβ', ← e1, ← e2, toStd_zero]
      abel
    have hmem := fun p => (O.mem_iff α hα β hβ hαβ p).trans (mem_expPairs_iff hα hβ hαβ p)
    refine mk_eq_one_of_mem (Or.inr ⟨i, j, k, l, c, d, hij, hkl, hnopp, ?_⟩)
    rw [map_mul, map_inv, map_commutatorElement, map_chevOf hα, map_chevOf hβ,
      commutatorElement_def]
    by_cases hc : Chain α β
    · have hl : O.list α β = [(1, 1)] :=
        list_eq_singleton' (O.nodup α β) fun p => (hmem p).trans (and_iff_left hc)
      rw [hl, List.map_singleton, List.prod_singleton, one_smul, one_smul, pow_one, pow_one]
      rcases hc with hc | hc
      ·
        change j = k at hc
        have hil : i ≠ l := fun e => hnopp ⟨hc.symm, e.symm⟩
        have hsum : toStd m (α + β) = Pi.single i 1 - Pi.single l 1 := by
          rw [toStd_add, hα', hβ', hc]
          abel
        have hroot : α + β ∈ (Φ (m := m) (F := F)).roots := by
          rw [Φ_roots, roots_eq]
          exact ⟨i, l, hil, hsum⟩
        rw [map_chevOf hroot, pairOf_eq hil hsum, commC_of_eq hc, ite_eq_left hc, Int.cast_one,
          one_mul]
      ·
        change l = i at hc
        have hjk : j ≠ k := fun e => hnopp ⟨e.symm, hc⟩
        have hkj : k ≠ j := fun e => hjk e.symm
        have hsum : toStd m (α + β) = Pi.single k 1 - Pi.single j 1 := by
          rw [toStd_add, hα', hβ', hc]
          abel
        have hroot : α + β ∈ (Φ (m := m) (F := F)).roots := by
          rw [Φ_roots, roots_eq]
          exact ⟨k, j, hkj, hsum⟩
        rw [map_chevOf hroot, pairOf_eq hkj hsum, commC_of_ne hjk, ite_eq_right hjk,
          ite_eq_left hc.symm, show ((-1 : ℤ) : F) * c * d = -(c * d) by push_cast; ring]
    · have hl : O.list α β = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp =>
        hc ((hmem p).1 hp).2
      have hjk : ¬ j = k := fun e => hc (Or.inl e)
      have hil : ¬ i = l := fun e => hc (Or.inr e.symm)
      rw [hl, List.map_nil, List.prod_nil, map_one, ite_eq_right hjk, ite_eq_right hil]

private theorem exists_root {i j : Fin (m + 1)} (hij : i ≠ j) :
    ∃ γ ∈ (Φ (m := m) (F := F)).roots, toStd m γ = Pi.single i 1 - Pi.single j 1 := by
  obtain ⟨w, k, hw⟩ := exists_weylAction_single m hij
  refine ⟨_, ?_, hw⟩
  rw [Φ_roots, roots_eq]
  exact ⟨i, j, hij, hw⟩

theorem stHom_bijective [Finite F] (hm : 2 ≤ m) : Function.Bijective (stHom (m := m) (F := F)) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (rootDatum m F).isFiniteType
    (show (rootDatum m F).divisible = ∅ from rfl)
  obtain ⟨h, hbij⟩ := (presentationB (F := F) hm O).2 (commC (m := m)) (commutatorFormula O)
  set e := MulEquiv.ofBijective (PresentedGroup.toGroup h) hbij
  set ψ := PresentedGroup.toGroup (symbolOf_rels (F := F) O)
  have hcomp : stHom.comp ψ = PresentedGroup.toGroup h := by
    refine PresentedGroup.ext fun g => ?_
    rw [MonoidHom.comp_apply, PresentedGroup.toGroup.of, PresentedGroup.toGroup.of, stHom_of]
    rfl
  have hleft : (ψ.comp e.symm.toMonoidHom).comp stHom = MonoidHom.id _ := by
    refine PresentedGroup.ext fun s => ?_
    obtain ⟨i, j, c⟩ := s
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, stHom_of, MonoidHom.id_apply]
    by_cases hij : i = j
    · subst hij
      rw [stGen_self, MulEquiv.coe_toMonoidHom, map_one, map_one]
      exact (mk_eq_one_of_mem (Or.inl (Or.inl ⟨i, c, rfl⟩))).symm
    · obtain ⟨γ, hγ, hst⟩ := exists_root (F := F) hij
      have hx : stGen (i, j, c) = x m F γ c := by
        rw [stGen_of_ne hij, x_eq hij hst]
      have he : e.symm (x m F γ c) = PresentedGroup.of (⟨γ, hγ⟩, c) := by
        rw [MulEquiv.symm_apply_eq]
        change x m F γ c = PresentedGroup.toGroup h (PresentedGroup.of (⟨γ, hγ⟩, c))
        rw [PresentedGroup.toGroup.of]
        rfl
      rw [hx, MulEquiv.coe_toMonoidHom, he, PresentedGroup.toGroup.of]
      change PresentedGroup.of ((pairOf m γ).1, (pairOf m γ).2, c) = PresentedGroup.of (i, j, c)
      rw [pairOf_eq hij hst]
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · have := congrArg (ψ.comp e.symm.toMonoidHom) hab
    simpa only [← MonoidHom.comp_apply, hleft, MonoidHom.id_apply] using this
  · refine ⟨ψ (e.symm y), ?_⟩
    rw [← MonoidHom.comp_apply, hcomp]
    exact e.apply_symm_apply y

theorem exists_steinbergSLRels_equiv [Finite F] (hm : 2 ≤ m) :
    ∃ φ : PresentedGroup (CFSG.Open.steinbergSLRels (m + 1) F) ≃*
        SpecialLinearGroup (Fin (m + 1)) F,
      ∀ (i j : Fin (m + 1)) (c : F), i ≠ j →
        ((φ (PresentedGroup.of (i, j, c)) : SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.transvection i j c := by
  refine ⟨MulEquiv.ofBijective _ (stHom_bijective hm), fun i j c hij => ?_⟩
  rw [MulEquiv.ofBijective_apply, stHom_of, stGen_of_ne hij]
  exact SpecialLinearGroup.transvection_coe hij c

end CFSG.LieType.Steinberg.SL
