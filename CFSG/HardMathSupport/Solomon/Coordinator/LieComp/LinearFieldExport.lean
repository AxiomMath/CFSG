module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SLFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearAut
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearTwo
public import CFSG.GH74.GLS.IVK.L2.Fixed
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CentralQuotient
import CFSG.GH74.Generic.GKFCover
import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.IVK (fixedField fixedField_card_pow mem_fixedField_iff)

section Helpers

variable {n : ℕ} {k : Type} [Field k]

open Matrix in
private theorem injective_map_subtype (k₀ : Subfield k) :
    Function.Injective (SpecialLinearGroup.map k₀.subtype :
      SpecialLinearGroup (Fin n) k₀ →* SpecialLinearGroup (Fin n) k) := by
  intro g g' hgg'
  refine Subtype.ext (Matrix.ext fun a b => Subtype.val_injective ?_)
  have h1 := congrArg (fun x : SpecialLinearGroup (Fin n) k =>
    (x : Matrix (Fin n) (Fin n) k) a b) hgg'
  simpa [SpecialLinearGroup.map_apply_coe] using h1

open Matrix in
private theorem fixSubgroup_slFieldAut_eq_range {k₀ : Subfield k} {σ : k ≃+* k}
    (hk : ∀ x, x ∈ k₀ ↔ σ x = x) :
    fixSubgroup (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
        (Fin n) k σ) =
      (SpecialLinearGroup.map k₀.subtype :
        SpecialLinearGroup (Fin n) k₀ →* SpecialLinearGroup (Fin n) k).range := by
  ext g
  rw [mem_fixSubgroup]
  constructor
  · intro hg
    have hent : ∀ a b, σ ((g : Matrix (Fin n) (Fin n) k) a b) =
        (g : Matrix (Fin n) (Fin n) k) a b := fun a b =>
      congrArg (fun x : SpecialLinearGroup (Fin n) k => (x : Matrix (Fin n) (Fin n) k) a b) hg
    let g₀ : Matrix (Fin n) (Fin n) k₀ := Matrix.of fun a b => ⟨_, (hk _).2 (hent a b)⟩
    have hg₀ : g₀.map k₀.subtype = g := Matrix.ext fun _ _ => rfl
    have hdet : g₀.det = 1 := Subtype.val_injective (by
      change k₀.subtype g₀.det = k₀.subtype 1
      rw [RingHom.map_det, map_one]
      change (g₀.map k₀.subtype).det = 1
      rw [hg₀]
      exact g.2)
    exact ⟨⟨g₀, hdet⟩, Subtype.ext hg₀⟩
  · rintro ⟨g₀, rfl⟩
    refine Subtype.ext (Matrix.ext fun a b => ?_)
    exact (hk _).1 ((g₀ : Matrix (Fin n) (Fin n) k₀) a b).2

private theorem exists_surjective_ker_le_center_map_proj {G : Type*} [Group G]
    {S : Subgroup (Matrix.SpecialLinearGroup (Fin n) k)} (e : G ≃* S) :
    ∃ f : G →* ↥(S.map (LinearFlag.proj n k)), Function.Surjective f ∧
      f.ker ≤ Subgroup.center G := by
  refine ⟨((LinearFlag.proj n k).subgroupMap S).comp e.toMonoidHom,
    (MonoidHom.subgroupMap_surjective _ S).comp e.surjective, fun g hg => ?_⟩
  have h1 : LinearFlag.proj n k (e g : Matrix.SpecialLinearGroup (Fin n) k) = 1 :=
    congrArg Subtype.val hg
  have h2 : (e g : Matrix.SpecialLinearGroup (Fin n) k) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) k) :=
    LinearFlag.scalars_le_center n k (LinearFlag.proj_eq_one_iff.1 h1)
  rw [Subgroup.mem_center_iff]
  intro y
  apply e.injective
  rw [map_mul, map_mul]
  exact Subtype.ext (Subgroup.mem_center_iff.1 h2 (e y))

end Helpers

private theorem isSolvable_SL_of_not_perfect {n : ℕ} (hn : 2 ≤ n) {k₀ : Type} [Field k₀]
    [Finite k₀] (h : ¬ (3 ≤ n ∨ 4 ≤ Nat.card k₀)) :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin n) k₀) := by
  obtain rfl : n = 2 := by omega
  have hcard : Nat.card k₀ = 2 ∨ Nat.card k₀ = 3 := by
    have : 1 < Nat.card k₀ := Finite.one_lt_card
    omega
  haveI : Group.IsSolvable (GL (Fin 2) k₀) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable k₀ hcard
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) k₀ →* _))
    Matrix.SpecialLinearGroup.toGL_injective

theorem linearFieldAut_components {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Finite k]
    (σ : k ≃+* k) (K : Subgroup (LinearFlag.projectiveSL n k))
    (hK : IsComponentOf K (fixSubgroup (LinearFlag.fieldAut n k σ))) :
    (3 ≤ n ∨ 4 ≤ Nat.card (fixedField σ)) ∧
      ∃ f : Matrix.SpecialLinearGroup (Fin n) (fixedField σ) →* ↥K,
        Function.Surjective f ∧ f.ker ≤ Subgroup.center _ := by
  have hk : ∀ x, x ∈ fixedField σ ↔ σ x = x := mem_fixedField_iff σ
  set α := CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin n) k σ
  have hC := fixSubgroup_slFieldAut_eq_range (n := n) hk
  let e : Matrix.SpecialLinearGroup (Fin n) (fixedField σ) ≃* ↥(fixSubgroup α) :=
    (MonoidHom.ofInjective (injective_map_subtype (fixedField σ))).trans
      (MulEquiv.subgroupCongr hC.symm)
  have hαβ : ∀ x, LinearFlag.proj n k (α x) =
      LinearFlag.fieldAut n k σ (LinearFlag.proj n k x) :=
    fun x => (LinearFlag.descendAut_proj n k α x).symm
  have hker : (LinearFlag.proj n k).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) k) := by
    rw [LinearFlag.ker_proj]
    exact LinearFlag.scalars_le_center n k
  by_cases hperf : 3 ≤ n ∨ 4 ≤ Nat.card (fixedField σ)
  · refine ⟨hperf, ?_⟩
    have hq : CFSG.IsQuasisimple ↥(fixSubgroup α) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e
        (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le hn hperf)
    obtain ⟨-, hKi⟩ := components_of_centralQuotient (LinearFlag.proj n k)
      (LinearFlag.proj_surjective n k) hker α _ hαβ (fun _ : Unit => fixSubgroup α)
      (fun _ => le_rfl)
      (fun _ c hc g hg => (fixSubgroup α).mul_mem ((fixSubgroup α).mul_mem hc hg)
        ((fixSubgroup α).inv_mem hc))
      (fun _ => hq) (1 : ↥(fixSubgroup α) →* Unit)
      (fun x _ => Subgroup.mem_iSup_of_mem (ι := Unit) () x.2) K hK
    obtain ⟨f, hf, hfk⟩ := exists_surjective_ker_le_center_map_proj (n := n) (k := k) e
    rw [hKi]
    exact ⟨f, hf, hfk⟩
  · exfalso
    haveI := isSolvable_SL_of_not_perfect hn hperf
    haveI : Group.IsSolvable ↥(fixSubgroup α) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    obtain ⟨i, -⟩ := components_of_centralQuotient (LinearFlag.proj n k)
      (LinearFlag.proj_surjective n k) hker α _ hαβ (fun i : Empty => i.elim)
      (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (MonoidHom.id ↥(fixSubgroup α))
      (fun x hx => by
        have hx1 : x = 1 := hx
        rw [hx1]
        exact Subgroup.one_mem _) K hK
    exact i.elim

theorem linearFieldAut_lieFactorData (hSL : SLFactorFacts) {n : ℕ} (hn : 2 ≤ n) {k : Type}
    [Field k] [Finite k] (σ : k ≃+* k) (hperf : 3 ≤ n ∨ 4 ≤ Nat.card (fixedField σ)) :
    LieFactorData (ringChar k) (Matrix.SpecialLinearGroup (Fin n) (fixedField σ)) := by
  haveI : Fintype ↥(fixedField σ) := Fintype.ofFinite _
  have h := hSL (fixedField σ) n hn (fun h2 => by
    rcases hperf with h3 | h4
    · omega
    · rwa [Fintype.card_eq_nat_card])
  rwa [Algebra.ringChar_eq (fixedField σ) k] at h

private theorem noThreeCover_projectiveSL_two
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = 729) :
    NoThreeCover (LinearFlag.projectiveSL 2 k) := by
  intro Y _ _ hY ⟨e⟩ h3
  haveI := Fintype.ofFinite k
  have hk' : Fintype.card k = 729 := by rw [Fintype.card_eq_nat_card]; exact hk
  obtain ⟨-, ⟨m⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier
    (k := k) (by omega) (by omega)
  have hY' : CFSG.IsQuasisimple Y :=
    ⟨⟨hY.1⟩, hY.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY⟩
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hY'
    (e.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 k).symm)
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k)) = 2 := by
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
      Nat.card_congr m.toEquiv]
    simp [hk']
  rw [hcard] at hdvd
  have := Nat.le_of_dvd (by norm_num) (h3.trans hdvd)
  omega

theorem lieCompExport_fieldAut
    (hSL : SLFactorFacts) (hA6 : SLAltSixFacts) {n : ℕ} (hn : 2 ≤ n)
    {k : Type} [Field k] [Finite k] (σ : k ≃+* k) (hσ : orderOf σ = 3) :
    LieCompExport (ringChar k) (LinearFlag.fieldAut n k σ) := by
  haveI : Fintype ↥(fixedField σ) := Fintype.ofFinite _
  refine ⟨?_, fun K hK => ?_, ?_⟩
  · rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      exact LieSemisimple.perfectInLayer_fieldAut_two σ
    · exact LieSemisimple.perfectInLayer_fieldAut h Nat.prime_three (by norm_num) σ hσ
  · obtain ⟨hperf, f, hf, hfk⟩ := linearFieldAut_components hn σ K hK
    exact ⟨_, inferInstance, inferInstance, linearFieldAut_lieFactorData hSL hn σ hperf, f, hf,
      hfk⟩
  · rintro ⟨K, hK, ⟨a⟩⟩
    obtain ⟨hperf, f, hf, hfk⟩ := linearFieldAut_components hn σ K hK
    have hX := linearFieldAut_lieFactorData hSL hn σ hperf
    obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hX.perfect f hf hfk
    obtain ⟨rfl, h9⟩ := hA6 (fixedField σ) n hn ⟨e.trans a⟩
    have h9' : Nat.card ↥(fixedField σ) = 9 := by rw [← Fintype.card_eq_nat_card]; exact h9
    have hk729 : Nat.card k = 729 := by
      rw [← fixedField_card_pow σ, hσ, h9']
      norm_num
    exact noThreeCover_projectiveSL_two hk729

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
