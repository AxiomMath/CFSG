module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Preimages
public import CFSG.LocalAnalysis.ComponentClassification.CommutingComponentFamily

public section

open CFSG.Open

namespace CFSG.ComponentClassification.AschbacherTheorem5

theorem semisimple_perfect {Q : Type*} [Group Q] (X : Subgroup Q)
    (hsemisimple : aschbacherThm5IsSemisimple X) : Group.IsPerfect X := by
  obtain ⟨k, K, _, hK, _, hgen⟩ := hsemisimple
  have hperfect : Group.IsPerfect (CommutingComponentFamily.generated (Set.range K)) := by
    apply CommutingComponentFamily.perfect
    rintro factor ⟨i, rfl⟩
    exact ⟨(hK i).2.1⟩
  rw [CommutingComponentFamily.generated, sSup_range, hgen] at hperfect
  exact hperfect

theorem semisimple_ne_bot {Q : Type*} [Group Q] (X : Subgroup Q)
    (hsemisimple : aschbacherThm5IsSemisimple X) : X ≠ ⊥ := by
  obtain ⟨k, K, hk, hK, _, _⟩ := hsemisimple
  let i : Fin k := ⟨0, hk⟩
  have hnontrivial := (K i).nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial (hK i).2)
  intro hbot
  exact hnontrivial (le_bot_iff.mp (hbot ▸ (hK i).1))

theorem semisimple_nontrivial {Q : Type*} [Group Q] (X : Subgroup Q)
    (hsemisimple : aschbacherThm5IsSemisimple X) : Nontrivial X :=
  X.nontrivial_iff_ne_bot.mpr (semisimple_ne_bot X hsemisimple)

theorem commuting_factors_normal {Q Index : Type*} [Group Q]
    (Abar : Index → Subgroup Q)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x)
    (hgen : ⨆ i, Abar i = ⊤) (i : Index) : (Abar i).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  apply iSup_le
  intro j
  by_cases hji : j = i
  · subst j
    exact Subgroup.le_normalizer
  · apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact (hcomm j i hji x hx y hy).symm

theorem quasisimple_factors_injective {Q Index : Type*} [Group Q]
    (K : Index → Subgroup Q) (hK : ∀ i, IsQuasisimple (K i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) :
    Function.Injective K := by
  intro i j heq
  by_contra hij
  have hcentral : K i ≤ Subgroup.centralizer (K i : Set Q) := by
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact (hcomm i j hij x hx y (heq ▸ hy)).symm
  let : Group.IsPerfect (K i) := ⟨(hK i).1⟩
  have hbot := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral
  rw [Subgroup.commutator_eq_self] at hbot
  exact ((K i).nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial (hK i))) hbot

theorem semisimple_component_presentation {Q : Type*} [Group Q] [Finite Q]
    (X : Subgroup Q) (hsemisimple : aschbacherThm5IsSemisimple X) :
    ∃ (k : ℕ) (K : Fin k → Subgroup Q), 0 < k ∧ Function.Injective K ∧
      (⨆ i, K i = X) ∧
      (∀ i, IsComponentOf ((K i).subgroupOf X) ⊤) ∧
      ∀ component : Subgroup Q, component ≤ X →
        (IsComponentOf (component.subgroupOf X) ⊤ ↔ ∃ i, K i = component) := by
  obtain ⟨k, K, hk, hK, hcomm, hgen⟩ := hsemisimple
  let family := Set.range K
  have hfamily : CommutingComponentFamily.generated family = X := by
    simpa only [CommutingComponentFamily.generated, family, sSup_range] using hgen
  have hquasisimple : ∀ factor ∈ family, IsQuasisimple factor := by
    rintro factor ⟨i, rfl⟩
    exact (hK i).2
  have hcommutes : ∀ first ∈ family, ∀ second ∈ family,
      first ≠ second → ⁅first, second⁆ = ⊥ := by
    rintro first ⟨i, rfl⟩ second ⟨j, rfl⟩ hij
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact (hcomm i j (fun heq => hij (congrArg K heq)) x hx y hy).symm
  refine ⟨k, K, hk, quasisimple_factors_injective K (fun i => (hK i).2) hcomm,
    hgen, ?_, ?_⟩
  · intro i
    rw [← hfamily]
    exact CommutingComponentFamily.factor_component family hcommutes hquasisimple (K i) ⟨i, rfl⟩
  · intro component hle
    rw [← hfamily] at hle ⊢
    exact CommutingComponentFamily.components_exact family hcommutes hquasisimple component hle

theorem quotient_perfect_of_semisimple_factors {Q Index : Type*} [Group Q]
    (Abar : Index → Subgroup Q) (hsemisimple : ∀ i, aschbacherThm5IsSemisimple (Abar i))
    (hgen : ⨆ i, Abar i = ⊤) : Group.IsPerfect Q := by
  apply Group.IsPerfect.top_iff.mp
  have hperfect : Group.IsPerfect (CommutingComponentFamily.generated (Set.range Abar)) := by
    apply CommutingComponentFamily.perfect
    rintro factor ⟨i, rfl⟩
    exact semisimple_perfect (Abar i) (hsemisimple i)
  rw [CommutingComponentFamily.generated, sSup_range, hgen] at hperfect
  exact hperfect

theorem canonical_preimage_normal {G Index : Type*} [Group G]
    (D : Subgroup G) (Abar : Index → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x)
    (hgen : ⨆ i, Abar i = ⊤) (i : Index) :
    ((aschbacherThm5Preimage D (Abar i)).subgroupOf D).Normal := by
  let : (Abar i).Normal := commuting_factors_normal Abar hcomm hgen i
  exact preimage_normal D (Abar i)

theorem canonical_two_factor_product {G : Type*} [Group G]
    (D : Subgroup G) (Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x)
    (hgen : ⨆ i, Abar i = ⊤) (i j : Fin 2) (hij : i ≠ j) :
    ∀ d ∈ D, ∃ a ∈ aschbacherThm5Preimage D (Abar i),
      ∃ b ∈ aschbacherThm5Preimage D (Abar j), d = a * b := by
  let : (Abar i).Normal := commuting_factors_normal Abar hcomm hgen i
  apply two_factor_product
  have hfull : (⨆ l, Abar l) = Abar i ⊔ Abar j := by
    apply le_antisymm
    · apply iSup_le
      intro l
      have heq : l = i ∨ l = j := by
        have hil := i.isLt
        have hjl := j.isLt
        have hll := l.isLt
        have hne : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
        have hval : l.val = i.val ∨ l.val = j.val := by omega
        exact hval.imp Fin.ext Fin.ext
      rcases heq with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup Abar i) (le_iSup Abar j)
  exact hfull.symm.trans hgen

end CFSG.ComponentClassification.AschbacherTheorem5
