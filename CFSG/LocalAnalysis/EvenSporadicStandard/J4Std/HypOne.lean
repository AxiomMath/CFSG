module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.HypOneA
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.HypOneB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4FinkOut
public import CFSG.Sporadic.Schreier.J4SOutOdd
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup CFSG.ComponentClassification.M12Cover CFSG.EvenSporadicStandard.HypOne

theorem noNormalFour_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : NoNormalFour A) : NoNormalFour B := by
  intro N hN
  have hN' : (N.comap e.toMonoidHom).Normal := hN.comap _
  have eN : N.comap e.toMonoidHom ≃* N :=
    (e.subgroupMap _).trans
      (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective e.surjective N))
  obtain ⟨h1, h2⟩ := h _ hN'
  exact ⟨⟨fun f => h1.false (eN.trans f)⟩, ⟨fun f => h2.false (eN.trans f)⟩⟩

@[expose] def centralizerEquivConj {Y : Type*} [Group Y] (y g : Y) :
    centralizer ({y} : Set Y) ≃* centralizer ({g * y * g⁻¹} : Set Y) where
  toFun c := ⟨g * c * g⁻¹, by
    rw [mem_centralizer_singleton_iff]
    have hc := mem_centralizer_singleton_iff.1 c.2
    calc g * c * g⁻¹ * (g * y * g⁻¹) = g * (c * y) * g⁻¹ := by group
      _ = g * (y * c) * g⁻¹ := by rw [hc]
      _ = g * y * g⁻¹ * (g * c * g⁻¹) := by group⟩
  invFun c := ⟨g⁻¹ * c * g, by
    rw [mem_centralizer_singleton_iff]
    have hc := mem_centralizer_singleton_iff.1 c.2
    calc g⁻¹ * c * g * y = g⁻¹ * (c * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * c) * g := by rw [hc]
      _ = y * (g⁻¹ * c * g) := by group⟩
  left_inv c := Subtype.ext (by show g⁻¹ * (g * (c : Y) * g⁻¹) * g = (c : Y); group)
  right_inv c := Subtype.ext (by show g * (g⁻¹ * (c : Y) * g) * g⁻¹ = (c : Y); group)
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

theorem noNormalFour_centralizer_of_isConj {Y : Type*} [Group Y] {y y' : Y} (h : IsConj y y')
    (hy : NoNormalFour (centralizer ({y} : Set Y))) :
    NoNormalFour (centralizer ({y'} : Set Y)) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  subst hg
  exact noNormalFour_of_mulEquiv (centralizerEquivConj y g) hy

theorem generalizedFitting_eq_top_of_simple {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] :
    CFSG.generalizedFitting X = ⊤ :=
  CFSG.Adapters.generalizedFitting_eq_top_of_isSimpleGroup X

theorem noNormalFour_centralizer_of_cover {Y : Type*} [Group Y] (a b : Y)
    (hcov : ∀ y : Y, y * y = 1 → y ≠ 1 → IsConj a y ∨ IsConj b y)
    (ha : NoNormalFour (centralizer ({a} : Set Y))) (hb : NoNormalFour (centralizer ({b} : Set Y)))
    {y : Y} (hy : y * y = 1) (hne : y ≠ 1) : NoNormalFour (centralizer ({y} : Set Y)) :=
  (hcov y hy hne).elim (fun h => noNormalFour_centralizer_of_isConj h ha)
    (fun h => noNormalFour_centralizer_of_isConj h hb)

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.ComponentClassification.RankTwoSporadic.J4Fink in
theorem noNormalFour_centralizer_J
    {y : J} (hy : y * y = 1) (hne : y ≠ 1) : NoNormalFour (centralizer ({y} : Set J)) := by
  refine noNormalFour_centralizer_of_cover (eta uJ 11 1) (eta uJ 11 1131) ?_
    noNormalFour_centralizer_eta_one noNormalFour_centralizer_eta_1131 hy hne
  intro r hr hr1
  rcases inv_conj_root j4Facts hr hr1 with h | h
  · exact Or.inl h
  · obtain ⟨g, -, hg⟩ := exists_conj_eta_three_of_mem_zMasks (c := 1131) mem_zMasks_1131
    have h1 : IsConj (eta uJ 11 3) (eta uJ 11 1131) := isConj_iff.2 ⟨g, hg⟩
    exact Or.inr (h1.symm.trans h)

noncomputable def generalizedFittingEquiv (X : Type*) [Group X] [Finite X] [IsSimpleGroup X] :
    CFSG.generalizedFitting X ≃* X :=
  (MulEquiv.subgroupCongr generalizedFitting_eq_top_of_simple).trans Subgroup.topEquiv

theorem isSimpleGroup_generalizedFitting (X : Type*) [Group X] [Finite X] [IsSimpleGroup X] :
    IsSimpleGroup (CFSG.generalizedFitting X) :=
  MulEquiv.isSimpleGroup (generalizedFittingEquiv X)

theorem center_eq_bot_of_simple_nonabelian {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (mem_center_iff.1 (h ▸ mem_top b) a)

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
  CFSG.ComponentClassification.RankTwoSporadic.J4Fink in
theorem J_nonabelian : ∃ a b : J, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have : IsSimpleGroup J := isSimpleGroup_J j4Facts
  let _ : CommGroup J := { (inferInstance : Group J) with mul_comm := hcomm }
  have hp := IsSimpleGroup.prime_card (α := J)
  rw [card_J j4Facts] at hp
  norm_num at hp

open CFSG.Sporadic.J4 in
theorem center_J_eq_bot : center J = ⊥ := by
  have : IsSimpleGroup J := isSimpleGroup_J j4Facts
  exact center_eq_bot_of_simple_nonabelian J_nonabelian

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
  CFSG.ComponentClassification.RankTwoSporadic.J4Fink in
theorem oddCore_centralizer_J
    {y : J} (hy : orderOf y = 2) :
    CFSG.Assembly.oddCore (centralizer ({y} : Set J)) = ⊥ := by
  have : IsSimpleGroup J := isSimpleGroup_J j4Facts
  have hsimple : IsSimpleGroup (CFSG.generalizedFitting J) := isSimpleGroup_generalizedFitting J
  let ψ : CFSG.generalizedFitting J ≃* J := generalizedFittingEquiv J
  have hnab : ∃ a b : CFSG.generalizedFitting J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := J_nonabelian
    exact ⟨ψ.symm a, ψ.symm b, fun h => hab (by
      have := congrArg ψ h
      simpa using this)⟩
  exact CTU_J4_full_group_involution_odd_core hsimple hnab ψ y hy

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
  CFSG.ComponentClassification.RankTwoSporadic.J4Fink in
theorem hypothesisOne_J :
    CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.HypothesisOne J := by
  refine hypothesisOne_of_inner (conj_injective_of_center_eq_bot center_J_eq_bot)
    (fun α => exists_eq_conj_J α) (fun y hy => ?_)
  have hsq : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  have hne : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hy; exact absurd hy (by decide)
  exact SmallNormalFree.of_noNormalFour (oddCore_centralizer_J hy)
    (noNormalFour_centralizer_J hsq hne)

end CFSG.EvenSporadicStandard.J4Std
