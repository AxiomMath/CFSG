module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLift
public import CFSG.Timmesfeld.LieEmbed.SLE6

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Subgroup Matrix
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {m : ℕ}

noncomputable def stT (hm : 2 ≤ m) (i j : Fin (m + 1)) (c : F) :
    SpecialLinearGroup (Fin (m + 1)) F :=
  (Classical.choose (CFSG.LieType.Steinberg.SL.exists_steinbergSLRels_equiv (m := m) (F := F) hm))
    (PresentedGroup.of (i, j, c))

theorem stT_spec (hm : 2 ≤ m) :
    ∃ φ : PresentedGroup (CFSG.Open.steinbergSLRels (m + 1) F) ≃*
        SpecialLinearGroup (Fin (m + 1)) F,
      (∀ i j c, stT hm i j c = φ (PresentedGroup.of (i, j, c))) ∧
      ∀ (i j : Fin (m + 1)) (c : F), i ≠ j →
        ((φ (PresentedGroup.of (i, j, c)) : SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.transvection i j c :=
  ⟨_, fun _ _ _ => rfl,
    Classical.choose_spec (CFSG.LieType.Steinberg.SL.exists_steinbergSLRels_equiv hm)⟩

theorem stT_eq_transvection (hm : 2 ≤ m) {i j : Fin (m + 1)} (hij : i ≠ j) (c : F) :
    stT hm i j c = SpecialLinearGroup.transvection hij c := by
  obtain ⟨φ, hφ, hφt⟩ := stT_spec (F := F) hm
  apply Subtype.ext
  rw [hφ, hφt i j c hij, SpecialLinearGroup.transvection_coe]
  rfl

omit [Finite F] in
theorem mk_of_eq (x : Fin (m + 1) × Fin (m + 1) × F) :
    PresentedGroup.mk (CFSG.Open.steinbergSLRels (m + 1) F) (FreeGroup.of x) =
      PresentedGroup.of x := rfl

theorem stT_diag (hm : 2 ≤ m) (i : Fin (m + 1)) (c : F) : stT hm i i c = 1 := by
  obtain ⟨φ, hφ, -⟩ := stT_spec (F := F) hm
  have hmem : FreeGroup.of (i, i, c) ∈ CFSG.Open.steinbergSLRels (m + 1) F :=
    Or.inl (Or.inl ⟨i, c, rfl⟩)
  rw [hφ, ← mk_of_eq, PresentedGroup.one_of_mem hmem, map_one]

theorem stT_add (hm : 2 ≤ m) {i j : Fin (m + 1)} (hij : i ≠ j) (c d : F) :
    stT hm i j c * stT hm i j d = stT hm i j (c + d) := by
  obtain ⟨φ, hφ, -⟩ := stT_spec (F := F) hm
  have hmem : FreeGroup.of (i, j, c) * FreeGroup.of (i, j, d) * (FreeGroup.of (i, j, c + d))⁻¹ ∈
      CFSG.Open.steinbergSLRels (m + 1) F := Or.inl (Or.inr ⟨i, j, c, d, hij, rfl⟩)
  have h := PresentedGroup.one_of_mem hmem
  simp only [map_mul, map_inv, mk_of_eq, mul_inv_eq_one] at h
  rw [hφ, hφ, hφ, ← map_mul, h]

theorem stT_comm (hm : 2 ≤ m) {i j k l : Fin (m + 1)} (hij : i ≠ j) (hkl : k ≠ l)
    (hex : ¬ (k = j ∧ l = i)) (c d : F) :
    ⁅stT hm i j c, stT hm k l d⁆ =
      if j = k then stT hm i l (c * d) else if i = l then stT hm k j (-(c * d)) else 1 := by
  obtain ⟨φ, hφ, -⟩ := stT_spec (F := F) hm
  have hmem : FreeGroup.of (i, j, c) * FreeGroup.of (k, l, d) * (FreeGroup.of (i, j, c))⁻¹ *
        (FreeGroup.of (k, l, d))⁻¹ *
        (if j = k then FreeGroup.of (i, l, c * d)
          else if i = l then FreeGroup.of (k, j, -(c * d)) else 1)⁻¹ ∈
      CFSG.Open.steinbergSLRels (m + 1) F := Or.inr ⟨i, j, k, l, c, d, hij, hkl, hex, rfl⟩
  have h := PresentedGroup.one_of_mem hmem
  simp only [map_mul, map_inv, mk_of_eq, mul_inv_eq_one] at h
  rw [commutatorElement_def, hφ, hφ, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h]
  split_ifs <;> simp [hφ, mk_of_eq]

theorem stT_comm_eq_one (hm : 2 ≤ m) {i j k l : Fin (m + 1)} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hil : i ≠ l) (c d : F) : Commute (stT hm i j c) (stT hm k l d) := by
  have h := stT_comm hm hij hkl (fun h => hjk h.1.symm) c d
  simp only [hjk, hil, ↓reduceIte] at h
  exact commutatorElement_eq_one_iff_commute.mp h

theorem stT_zero (hm : 2 ≤ m) (i j : Fin (m + 1)) : stT hm i j (0 : F) = 1 := by
  by_cases hij : i = j
  · subst hij; exact stT_diag hm i 0
  · have h := stT_add hm hij (0 : F) 0
    rw [add_zero] at h
    exact mul_eq_left.mp h

theorem stT_mul_self [CharP F 2] (hm : 2 ≤ m) (i j : Fin (m + 1)) (c : F) :
    stT hm i j c * stT hm i j c = 1 := by
  by_cases hij : i = j
  · subst hij; rw [stT_diag, mul_one]
  · rw [stT_add hm hij, CharTwo.add_self_eq_zero, stT_zero]

theorem closure_stT (hm : 2 ≤ m) :
    closure (Set.range fun p : Fin (m + 1) × Fin (m + 1) × F => stT hm p.1 p.2.1 p.2.2) = ⊤ := by
  obtain ⟨φ, hφ, -⟩ := stT_spec (F := F) hm
  have h := PresentedGroup.closure_range_of (CFSG.Open.steinbergSLRels (m + 1) F)
  have h2 := congrArg (Subgroup.map φ.toMonoidHom) h
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ φ.surjective] at h2
  rw [← h2]
  congr 1
  ext g
  simp [hφ]

section Lift

variable {Γ : Type*} [Group Γ] {M : Type*} [Group M]

theorem exists_hom_comp_eq_of_odd_center [CharP F 2] (hm : 2 ≤ m) (f : Γ →* M)
    (hZc : f.ker ≤ center Γ) (hZo : Odd (Nat.card f.ker))
    (ρ : SpecialLinearGroup (Fin (m + 1)) F →* M)
    (hρ : ∀ i j : Fin (m + 1), i ≠ j → ∀ c : F, ρ (stT hm i j c) ∈ f.range) :
    ∃ ψ : SpecialLinearGroup (Fin (m + 1)) F →* Γ, f.comp ψ = ρ := by
  have hpre : ∀ i j c, ∃ γ, f γ = ρ (stT hm i j c) := by
    intro i j c
    by_cases hij : i = j
    · subst hij; exact ⟨1, by rw [stT_diag, map_one, map_one]⟩
    · exact hρ i j hij c
  choose γ hγ using hpre
  have hsq : ∀ i j c, γ i j c ^ 2 ^ 1 ∈ f.ker := fun i j c => by
    rw [MonoidHom.mem_ker, map_pow, hγ, ← map_pow, pow_one, sq, stT_mul_self, map_one]
  choose w hwZ hw using fun i j c => exists_isTwoElt_mul hZc hZo (hsq i j c)
  set x : Fin (m + 1) → Fin (m + 1) → F → Γ := fun i j c => γ i j c * w i j c with hx
  have hfx : ∀ i j c, f (x i j c) = ρ (stT hm i j c) := fun i j c => by
    rw [hx, map_mul, hγ, (MonoidHom.mem_ker).mp (hwZ i j c), mul_one]
  have htwo : ∀ i j c, IsTwoElt (x i j c) := fun i j c => ⟨1, hw i j c⟩
  have hcomm_of : ∀ {a b : Γ} {s s' : SpecialLinearGroup (Fin (m + 1)) F}, IsTwoElt a →
      IsTwoElt b → f a = ρ s → f b = ρ s' → Commute s s' → Commute a b := by
    intro a b s s' ha hb hfa hfb hss
    refine commute_of_isTwoElt hZc hZo ha hb ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hfa, hfb, ← map_commutatorElement,
      commutatorElement_eq_one_iff_commute.mpr hss, map_one]
  have heq_of : ∀ {a b : Γ}, IsTwoElt a → IsTwoElt b → f a = f b → a = b := by
    intro a b ha hb hab
    refine eq_of_isTwoElt hZc hZo ha hb ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  have hadd : ∀ i j : Fin (m + 1), i ≠ j → ∀ c d : F, x i j c * x i j d = x i j (c + d) := by
    intro i j hij c d
    have hst : Commute (stT hm i j c) (stT hm i j d) := by
      rw [Commute, SemiconjBy, stT_add hm hij, stT_add hm hij, add_comm c d]
    have hc := hcomm_of (htwo i j c) (htwo i j d) (hfx i j c) (hfx i j d) hst
    refine heq_of ((htwo i j c).mul_of_commute (htwo i j d) hc) (htwo i j (c + d)) ?_
    rw [map_mul, hfx, hfx, ← map_mul, stT_add hm hij, hfx]
  have hcomm : ∀ i j k l : Fin (m + 1), i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → ∀ c d : F,
      ⁅x i j c, x k l d⁆ =
        if j = k then x i l (c * d) else if i = l then x k j (-(c * d)) else 1 := by
    intro i j k l hij hkl hex c d
    have hr2 : IsTwoElt
        (if j = k then x i l (c * d) else if i = l then x k j (-(c * d)) else (1 : Γ)) := by
      split_ifs
      exacts [htwo _ _ _, htwo _ _ _, isTwoElt_one]
    have hfr : f (if j = k then x i l (c * d) else if i = l then x k j (-(c * d)) else 1) =
        ρ (if j = k then stT hm i l (c * d) else if i = l then stT hm k j (-(c * d)) else 1) := by
      split_ifs
      · exact hfx _ _ _
      · exact hfx _ _ _
      · rw [map_one, map_one]
    have hrc : Commute
        (if j = k then x i l (c * d) else if i = l then x k j (-(c * d)) else 1) (x k l d) := by
      split_ifs with h1 h2
      · subst h1
        have hil : i ≠ l := fun h => hex ⟨rfl, h.symm⟩
        exact hcomm_of (htwo _ _ _) (htwo _ _ _) (hfx _ _ _) (hfx _ _ _)
          (stT_comm_eq_one hm hil hkl hkl.symm hil _ _)
      · subst h2
        have hkj : k ≠ j := fun h => h1 h.symm
        exact hcomm_of (htwo _ _ _) (htwo _ _ _) (hfx _ _ _) (hfx _ _ _)
          (stT_comm_eq_one hm hkj hkl h1 hkl _ _)
      · exact Commute.one_left _
    refine commutatorElement_eq_of_isTwoElt hZc hZo (htwo i j c) (htwo k l d) hr2 hrc ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_commutatorElement, hfx, hfx, hfr,
      ← map_commutatorElement, stT_comm hm hij hkl hex, inv_mul_cancel]
  obtain ⟨ψ, hψ⟩ := CFSG.Timmesfeld.LieEmbed.exists_hom_of_steinbergRels hm hadd hcomm
  refine ⟨ψ, MonoidHom.eq_of_eqOn_dense (closure_stT (F := F) hm) ?_⟩
  rintro _ ⟨⟨i, j, c⟩, rfl⟩
  by_cases hij : i = j
  · subst hij
    simp only [stT_diag, map_one]
  · simp only [MonoidHom.comp_apply]
    rw [stT_eq_transvection hm hij, hψ, ← stT_eq_transvection hm hij, hfx]

end Lift

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
