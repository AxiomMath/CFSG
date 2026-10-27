module

public import CFSG.ClassicalInvolution.Q3.Q3AMTriT01A
public import CFSG.ClassicalInvolution.Q3.Q3AMBadConj
public import CFSG.ClassicalInvolution.Q3.Q3T6FusM
public import CFSG.ClassicalInvolution.Q3.Q3MTLarge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.MuTab
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3CP
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3MT
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Dispatch



variable {ι : Type} {Z : Type} [Group Z] [Finite Z] {Φ : Set (Subgroup Z)}

theorem table_dispatch (D : LieSystemData3 ι Z Φ) (hconj : ConjInvariant Φ)
    (hO : classicalInvolutionOddCore Z = ⊥) (hnc : ∀ L ∈ Φ, ¬ Commutes L L)
    {J₁ J₂ : Subgroup Z} (h₁ : J₁ ∈ Φ) (h₂ : J₂ ∈ Φ) (hne : J₁ ≠ J₂) (hc : Commutes J₁ J₂)
    {a b zb : Z} (ha : IsUniqueInvolution J₁ a) (hb : IsUniqueInvolution J₂ b)
    (hab : a * b = zb) (hzb : zb ≠ 1) (hcen : ∀ y, y * zb = zb * y) :
    ShapeTriple Φ ∨ ShapeDouble D zb ∨ ShapeSingle D (CompData.model .PSp 2) zb ∨
      ShapeSingle D (CompData.model .PSL 4) zb ∨ ShapeSingle D (CompData.model .PSU 4) zb ∨
      ShapeSingle D (CompData.model .POmegaOdd 3) zb ∨
      ShapeSingle D (CompData.model .POmegaMinus 4) zb := by
  classical
  have hMFZ : RouteD.Gaps.FundNoncentral 3 := RouteD.Gaps.fundNoncentral 3
  obtain ⟨i₁, R₁, hR₁, hJ₁⟩ := D.fundamental J₁ h₁
  obtain ⟨i₂, R₂, hR₂, hJ₂⟩ := D.fundamental J₂ h₂
  have hle₁ : J₁ ≤ (D.hom i₁).range := hJ₁ ▸ Subgroup.map_le_range _ _
  have hle₂ : J₂ ≤ (D.hom i₂).range := hJ₂ ▸ Subgroup.map_le_range _ _
  obtain ⟨r₁, hr₁R, hr₁⟩ : ∃ r ∈ R₁, D.hom i₁ r = a := by
    have : a ∈ R₁.map (D.hom i₁) := hJ₁ ▸ ha.mem
    exact this
  obtain ⟨r₂, hr₂R, hr₂⟩ : ∃ r ∈ R₂, D.hom i₂ r = b := by
    have : b ∈ R₂.map (D.hom i₂) := hJ₂ ▸ hb.mem
    exact this
  have hcross : ∀ {i j : ι}, i ≠ j → ∀ x ∈ (D.hom i).range, ∀ y ∈ (D.hom j).range,
      x * y = y * x := by
    rintro i j hij _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact D.commute i j hij x y
  have hdiff : ∀ {i j : ι} {A B : Subgroup Z}, i ≠ j → A ≤ (D.hom i).range →
      B ≤ (D.hom j).range → A ∈ Φ → A ≠ B ∧ Commutes A B := by
    intro i j A B hij hA hB hAΦ
    have hcom : Commutes A B := fun x hx y hy => hcross hij x (hA hx) y (hB hy)
    refine ⟨fun hAB => hnc A hAΦ ?_, hcom⟩
    rw [hAB] at hcom ⊢
    exact hcom
  have hmeet : ∀ i : ι, ∃ A ∈ Φ, A ≤ (D.hom i).range := fun i => by
    obtain ⟨R, -, hR⟩ := D.meets i
    exact ⟨_, hR, Subgroup.map_le_range _ _⟩
  by_cases h3 : ∃ i j k : ι, i ≠ j ∧ i ≠ k ∧ j ≠ k
  ·
    left
    obtain ⟨i, j, k, hij, hik, hjk⟩ := h3
    obtain ⟨A, hA, hAi⟩ := hmeet i
    obtain ⟨B, hB, hBj⟩ := hmeet j
    obtain ⟨C, hC, hCk⟩ := hmeet k
    obtain ⟨hAB, cAB⟩ := hdiff hij hAi hBj hA
    obtain ⟨hAC, cAC⟩ := hdiff hik hAi hCk hA
    obtain ⟨hBC, cBC⟩ := hdiff hjk hBj hCk hB
    exact shapeTriple_of_three hA hB hC hAB hAC hBC cAB cAC cBC
  push Not at h3
  by_cases h12 : i₁ = i₂
  · subst h12
    by_cases hj : ∃ j : ι, j ≠ i₁
    ·
      left
      obtain ⟨j, hj⟩ := hj
      obtain ⟨B, hB, hBj⟩ := hmeet j
      obtain ⟨hJ₁B, cJ₁B⟩ := hdiff hj.symm hle₁ hBj h₁
      obtain ⟨hJ₂B, cJ₂B⟩ := hdiff hj.symm hle₂ hBj h₂
      exact shapeTriple_of_three h₁ h₂ hB hne hJ₁B hJ₂B hc cJ₁B cJ₂B
    ·
      push Not at hj
      have hsub : Subsingleton ι := ⟨fun x y => (hj x).trans (hj y).symm⟩
      by_cases hk : D.kind i₁ = CompData.sl23
      ·
        exfalso
        apply hne
        have e1 : J₁ = (D.hom i₁).range := by
          rw [hJ₁, Q3Y.eq_top_of_mem_fund_sl23 hk hR₁, Subgroup.map_top]
        have e2 : J₂ = (D.hom i₁).range := by
          rw [hJ₂, Q3Y.eq_top_of_mem_fund_sl23 hk hR₂, Subgroup.map_top]
        rw [e1, e2]
      obtain ⟨f, hfc, hfz⟩ : ∃ f ∈ Subgroup.center (D.kind i₁).G, D.hom i₁ f = zb := by
        refine ⟨r₁ * r₂, ?_, by rw [map_mul, hr₁, hr₂, hab]⟩
        refine Q3YS.zTwo_of_valid (D.kind i₁) (D.valid i₁) hk _ (fun m => D.ker_le_center i₁ ?_)
        rw [MonoidHom.mem_ker, map_commutatorElement, map_mul, hr₁, hr₂, hab,
          commutatorElement_eq_one_iff_mul_comm]
        exact (hcen _).symm
      have hnt : Nontrivial Z := ⟨⟨zb, 1, hzb⟩⟩
      have hΦne : Φ.Nonempty := ⟨J₁, h₁⟩
      have hsimple_false : IsSimpleGroup Z → False := by
        intro hs
        have hz : zb ∈ Subgroup.center Z := Subgroup.mem_center_iff.mpr hcen
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Z) with h | h
        · exact hzb (Subgroup.mem_bot.mp (h ▸ hz))
        · apply hnc J₁ h₁
          intro x hx y hy
          exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x
      rcases D.valid i₁ with ⟨t, n, hft, hadm, hkind⟩ | hsl | hm
      · let D' : LieSystemDataU 3 1 ι Z Φ := lieSystemDataU_of_q3 D
        have hkind' : D'.kind i₁ = compModel 3 1 t n := hkind
        let M : Ih8Model 3 1 Φ t n 1 :=
          Q3T6.ih8ModelOfSystemU D' i₁ hconj hft hadm (Or.inl rfl) hkind'
        rcases muKind_cases3 false t n with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hlarge
        ·
          exact (hsimple_false (Q3T6.isSimpleGroup_of_systemU (by norm_num) D' i₁ hconj
            (Or.inl ⟨rfl, rfl⟩) hft hadm (Or.inl rfl) hkind' hO)).elim
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i₁, hj, hkind, f, hfc, hfz⟩)))
        ·
          exact (hzb (by rw [← hfz, eq_one_of_mem_center_of_eq_psl5 hkind hfc, map_one])).elim
        ·
          exact (hsimple_false (Q3T6.isSimpleGroup_of_systemU (by norm_num) D' i₁ hconj
            (Or.inr (Or.inl ⟨rfl, rfl⟩)) hft hadm (Or.inl rfl) hkind' hO)).elim
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i₁, hj, hkind, f, hfc, hfz⟩))))
        ·
          exact (hzb (by rw [← hfz, eq_one_of_mem_center_of_eq_psu5 hadm hkind hfc,
            map_one])).elim
        ·
          exact Or.inr (Or.inr (Or.inl ⟨i₁, hj, hkind, f, hfc, hfz⟩))
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i₁, hj, hkind, f, hfc, hfz⟩)))))
        ·
          exact Or.inl (shapeTriple_of_plus4 M hΦne)
        ·
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i₁, hj, hkind, f, hfc, hfz⟩)))))
        ·
          exact (hsimple_false (Q3T6.isSimpleGroup_of_systemU (by norm_num) D' i₁ hconj
            (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hft hadm (Or.inl rfl) hkind' hO)).elim
        ·
          exact (hsimple_false (Q3T6.isSimpleGroup_of_systemU (by norm_num) D' i₁ hconj
            (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) hft hadm (Or.inl rfl) hkind' hO)).elim
        ·
          have hG2 : t ≠ .G2 := by
            rintro rfl
            obtain ⟨rfl, -⟩ := hadm.2.2
            simp [muKind] at hlarge
          have hD4 : t ≠ .trialityD4 := by
            rintro rfl
            obtain rfl : n = 0 := hadm.2.2
            simp [muKind] at hlarge
          have hnpsl : ¬ (t = .PSL ∧ n = 2) := by
            rintro ⟨rfl, rfl⟩
            exact hadm.2.2.2.2 (by simp)
          exact Or.inl (shapeTriple_of_datum3 M hΦne hG2 hD4
            (threeOrth_of_large (π := false) M.isFundTag M.admissible hnpsl hlarge))
      · exact absurd hsl hk
      · exact (hzb (by rw [← hfz, eq_one_of_mem_center_of_eq_m11 hm hfc, map_one])).elim
  ·
    right
    left
    have hall : ∀ k : ι, k = i₁ ∨ k = i₂ := by
      intro k
      by_cases hk1 : k = i₁
      · exact Or.inl hk1
      · by_cases hk2 : k = i₂
        · exact Or.inr hk2
        · exact absurd (h3 i₁ i₂ k h12 (Ne.symm hk1)).symm hk2
    have hacen : ∀ g : Z, g * a = a * g := by
      refine Q3YS.central_of_central_in_range D (i := i₁) (x := a) (hle₁ ha.mem) ?_
      intro y hy
      have hyb : y * b = b * y := hcross h12 y hy b (hle₂ hb.mem)
      have h1 : y * a * b = a * y * b := by
        calc y * a * b = y * (a * b) := mul_assoc _ _ _
          _ = y * zb := by rw [hab]
          _ = zb * y := hcen y
          _ = (a * b) * y := by rw [hab]
          _ = a * (b * y) := mul_assoc _ _ _
          _ = a * (y * b) := by rw [hyb]
          _ = a * y * b := (mul_assoc _ _ _).symm
      exact mul_right_cancel h1
    have hbcen : ∀ g : Z, g * b = b * g := by
      refine Q3YS.central_of_central_in_range D (i := i₂) (x := b) (hle₂ hb.mem) ?_
      intro y hy
      have hay : a * y = y * a := hcross h12 a (hle₁ ha.mem) y hy
      have h1 : a * (y * b) = a * (b * y) := by
        calc a * (y * b) = (a * y) * b := (mul_assoc _ _ _).symm
          _ = (y * a) * b := by rw [hay]
          _ = y * (a * b) := mul_assoc _ _ _
          _ = y * zb := by rw [hab]
          _ = zb * y := hcen y
          _ = (a * b) * y := by rw [hab]
          _ = a * (b * y) := mul_assoc _ _ _
      exact mul_left_cancel h1
    have hk₁ : D.kind i₁ = CompData.sl23 := by
      by_contra hk
      have hr1 : r₁ = 1 := Q3W.eq_one_of_central_comp3 hMFZ (D.kind i₁) (D.valid i₁) hk
        (D.hom i₁) (D.ker_le_center i₁) hR₁ hr₁R
        (fun y => by rw [hr₁]; exact (hacen (D.hom i₁ y)).symm)
      exact ha.ne_one (by rw [← hr₁, hr1, map_one])
    have hk₂ : D.kind i₂ = CompData.sl23 := by
      by_contra hk
      have hr2 : r₂ = 1 := Q3W.eq_one_of_central_comp3 hMFZ (D.kind i₂) (D.valid i₂) hk
        (D.hom i₂) (D.ker_le_center i₂) hR₂ hr₂R
        (fun y => by rw [hr₂]; exact (hbcen (D.hom i₂ y)).symm)
      exact hb.ne_one (by rw [← hr₂, hr2, map_one])
    have hJ₁r : J₁ = (D.hom i₁).range := by
      rw [hJ₁, Q3Y.eq_top_of_mem_fund_sl23 hk₁ hR₁, Subgroup.map_top]
    have hJ₂r : J₂ = (D.hom i₂).range := by
      rw [hJ₂, Q3Y.eq_top_of_mem_fund_sl23 hk₂ hR₂, Subgroup.map_top]
    have hab_ne : a ≠ b := fun h => hzb (by rw [← hab, h]; exact hb.sq)
    exact ⟨i₁, i₂, h12, hall, hk₁, hk₂, a, b, hle₁ ha.mem, hle₂ hb.mem, hab_ne, ha.sq, hb.sq,
      ha.ne_one, hb.ne_one, hacen, hbcen, fun u hu hu2 => ha.unique u (hJ₁r ▸ hu) hu2,
      fun u hu hu2 => hb.unique u (hJ₂r ▸ hu) hu2, hab.symm⟩

end Dispatch

end CFSG.ClassicalInvolution.Q3.Q3AM
