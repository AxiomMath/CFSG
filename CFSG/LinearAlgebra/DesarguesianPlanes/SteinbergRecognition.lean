module

public import CFSG.LieType.Steinberg.Classical.SpecialLinearSteinberg
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
public import CFSG.Assembly.OrderReductions.PermutationReduction

public section

namespace CFSG.DesarguesianPlanes

open Matrix
open scoped commutatorElement MatrixGroups

variable {F : Type} [Field F] {G : Type*} [Group G]

structure IsSteinbergFamily (x : Fin 3 → Fin 3 → F → G) : Prop where
  add : ∀ i j : Fin 3, i ≠ j → ∀ c d : F, x i j c * x i j d = x i j (c + d)
  comm : ∀ i j k l : Fin 3, i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → ∀ c d : F,
    ⁅x i j c, x k l d⁆ = if j = k then x i l (c * d) else if i = l then x k j (-(c * d)) else 1

@[expose] def steinbergGen (x : Fin 3 → Fin 3 → F → G) (s : Fin 3 × Fin 3 × F) : G :=
  if s.1 = s.2.1 then 1 else x s.1 s.2.1 s.2.2

omit [Field F] in
theorem steinbergGen_of_ne (x : Fin 3 → Fin 3 → F → G) {i j : Fin 3} (hij : i ≠ j) (c : F) :
    steinbergGen x (i, j, c) = x i j c := by
  simp [steinbergGen, hij]

theorem steinbergGen_rels {x : Fin 3 → Fin 3 → F → G} (hx : IsSteinbergFamily x) :
    ∀ r ∈ CFSG.Open.steinbergSLRels 3 F, FreeGroup.lift (steinbergGen x) r = 1 := by
  rintro r ((⟨i, c, rfl⟩ | ⟨i, j, c, d, hij, rfl⟩) | ⟨i, j, k, l, c, d, hij, hkl, hex, rfl⟩)
  · simp [steinbergGen]
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, steinbergGen_of_ne x hij]
    rw [hx.add i j hij c d, mul_inv_cancel]
  · have hcomm := hx.comm i j k l hij hkl hex c d
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, steinbergGen_of_ne x hij,
      steinbergGen_of_ne x hkl]
    by_cases hjk : j = k
    · subst hjk
      have hil : i ≠ l := fun h => hex ⟨rfl, h.symm⟩
      rw [ite_eq_left rfl] at hcomm ⊢
      rw [FreeGroup.lift_apply_of, steinbergGen_of_ne x hil, ← hcomm, commutatorElement_def,
        mul_inv_cancel]
    · rw [ite_eq_right hjk] at hcomm ⊢
      by_cases hil : i = l
      · subst hil
        rw [ite_eq_left rfl] at hcomm ⊢
        have hkj : k ≠ j := fun h => hjk h.symm
        rw [FreeGroup.lift_apply_of, steinbergGen_of_ne x hkj, ← hcomm, commutatorElement_def,
          mul_inv_cancel]
      · rw [ite_eq_right hil] at hcomm ⊢
        rw [map_one, inv_one, mul_one, ← commutatorElement_def, hcomm]

theorem exists_hom_of_steinbergFamily [Finite F] {x : Fin 3 → Fin 3 → F → G}
    (hx : IsSteinbergFamily x) :
    ∃ ρ : SL(3, F) →* G, ∀ (i j : Fin 3) (c : F) (A : SL(3, F)), i ≠ j →
      (A : Matrix (Fin 3) (Fin 3) F) = Matrix.transvection i j c → ρ A = x i j c := by
  obtain ⟨φ, hφ⟩ := CFSG.LieType.Steinberg.SL.exists_steinbergSLRels_equiv (m := 2) (F := F)
    (le_refl 2)
  let ψ : PresentedGroup (CFSG.Open.steinbergSLRels 3 F) →* G :=
    PresentedGroup.toGroup (steinbergGen_rels hx)
  refine ⟨ψ.comp φ.symm.toMonoidHom, ?_⟩
  intro i j c A hij hA
  have hAφ : A = φ (PresentedGroup.of (i, j, c)) := by
    apply Subtype.ext
    rw [hA, hφ i j c hij]
  rw [MonoidHom.comp_apply, hAφ, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  change PresentedGroup.toGroup (steinbergGen_rels hx) (PresentedGroup.of (i, j, c)) = x i j c
  rw [PresentedGroup.toGroup.of, steinbergGen_of_ne x hij]

theorem card_center_SL3_le [Finite F] : Nat.card (Subgroup.center (SL(3, F))) ≤ 3 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv]
  simpa using card_rootsOfUnity (R := F) (Fintype.card (Fin 3))

theorem nonempty_mulEquiv_psl_of_steinbergFamily [Finite F] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {x : Fin 3 → Fin 3 → F → G} (hx : IsSteinbergFamily x)
    {i₀ j₀ : Fin 3} {c₀ : F} (hij₀ : i₀ ≠ j₀) (hne : x i₀ j₀ c₀ ≠ 1)
    (hcard : Nat.card G ≤ Nat.card (SL(3, F))) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := by
  obtain ⟨ρ, hρ⟩ := exists_hom_of_steinbergFamily hx
  let A₀ : SL(3, F) := ⟨Matrix.transvection i₀ j₀ c₀, Matrix.det_transvection_of_ne _ _ hij₀ _⟩
  have hA₀ : ρ A₀ ≠ 1 := by
    rw [hρ i₀ j₀ c₀ A₀ hij₀ rfl]
    exact hne
  have hquasi : CFSG.Open.IsQuasisimple (SL(3, F)) :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 F
        (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num)))
  have hker : ρ.ker ≤ Subgroup.center (SL(3, F)) := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hquasi ρ.ker with
      h | h
    · exact h
    · exact absurd (h ▸ Subgroup.mem_top A₀ : A₀ ∈ ρ.ker) hA₀
  have hnoncomm : ¬ IsMulCommutative G := by
    rintro ⟨hc⟩
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (hc.comm a b)
  have hsurj : Function.Surjective ρ := by
    rw [← MonoidHom.range_eq_top]
    by_contra hproper
    have h5 :=
      CFSG.OrderReductions.PermutationReduction.simple_noncommutative_proper_subgroup_index_ge_five
        G hnoncomm ρ.range hproper
    have hfin : Finite (SL(3, F)) := inferInstance
    have hrange : Nat.card ρ.range * Nat.card ρ.ker = Nat.card (SL(3, F)) := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv,
        ← Subgroup.index_eq_card, Subgroup.index_mul_card]
    have hkercard : Nat.card ρ.ker ≤ 3 :=
      (Subgroup.card_le_of_le hker).trans card_center_SL3_le
    have hidx : ρ.range.index * Nat.card ρ.range = Nat.card G := ρ.range.index_mul_card
    have hpos : 0 < Nat.card ρ.range := Nat.card_pos
    nlinarith
  have hcenter : Subgroup.center (SL(3, F)) ≤ ρ.ker := by
    have hnormal : ((Subgroup.center (SL(3, F))).map ρ).Normal :=
      Subgroup.Normal.map inferInstance ρ hsurj
    rcases hnormal.eq_bot_or_eq_top with hbot | htop
    · rwa [← Subgroup.map_eq_bot_iff]
    · exfalso
      apply hnoncomm
      refine ⟨⟨fun a b => ?_⟩⟩
      have ha : a ∈ (Subgroup.center (SL(3, F))).map ρ := htop ▸ Subgroup.mem_top a
      obtain ⟨z, hz, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hsurj b
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz y).symm]
  have hkereq : ρ.ker = Subgroup.center (SL(3, F)) := le_antisymm hker hcenter
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective ρ hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hkereq))⟩

end CFSG.DesarguesianPlanes
