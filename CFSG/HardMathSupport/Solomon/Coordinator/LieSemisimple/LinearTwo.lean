module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearInner
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2OrderThree
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.LocalAnalysis.ComponentInitial CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {K : Type} [Field K] [Finite K]

noncomputable abbrev psl2Equiv (K : Type) [Field K] : PSL2 K ≃* LinearFlag.projectiveSL 2 K :=
  LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K

theorem congr_pglAction_mk (A : GL (Fin 2) K) :
    MulAut.congr (psl2Equiv K) (pglAction K (QuotientGroup.mk A)) = LinearFlag.conjAut 2 K A := by
  change MulAut.congr (psl2Equiv K) (pglAction K (Matrix.ProjGenLinGroup.mk A)) = _
  ext y
  obtain ⟨x, rfl⟩ := (psl2Equiv K).surjective y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) x
  have h1 : pglAction K (Matrix.ProjGenLinGroup.mk A) (QuotientGroup.mk' (Subgroup.center _) g) =
      QuotientGroup.mk' (Subgroup.center _)
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 K A g) := by
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [toPGL_pglAction]
    change Matrix.ProjGenLinGroup.mk A *
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL g) *
      (Matrix.ProjGenLinGroup.mk A)⁻¹ =
        Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 2 K A g))
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul,
      map_mul, map_inv]
  show psl2Equiv K (pglAction K (Matrix.ProjGenLinGroup.mk A)
    ((psl2Equiv K).symm (psl2Equiv K (QuotientGroup.mk' (Subgroup.center _) g)))) = _
  rw [MulEquiv.symm_apply_apply, h1]
  exact (LinearFlag.conjAut_proj A g).symm

theorem congr_psl2FieldAut (σ : K ≃+* K) :
    MulAut.congr (psl2Equiv K) (psl2FieldAut K σ) = LinearFlag.fieldAut 2 K σ := by
  ext y
  obtain ⟨x, rfl⟩ := (psl2Equiv K).surjective y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) x
  show psl2Equiv K (psl2FieldAut K σ ((psl2Equiv K).symm
    (psl2Equiv K (QuotientGroup.mk' (Subgroup.center _) g)))) = _
  rw [MulEquiv.symm_apply_apply, psl2FieldAut_apply, psl2RingEquiv_mk]
  exact (LinearFlag.fieldAut_proj σ g).symm

open Matrix in
private theorem injective_map_subtype (k : Subfield K) :
    Function.Injective (SpecialLinearGroup.map k.subtype :
      SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 2) K) := by
  intro g g' hgg'
  refine Subtype.ext (Matrix.ext fun a b => Subtype.val_injective ?_)
  have h1 := congrArg (fun x : SpecialLinearGroup (Fin 2) K =>
    (x : Matrix (Fin 2) (Fin 2) K) a b) hgg'
  simpa [SpecialLinearGroup.map_apply_coe] using h1

open Matrix in
private theorem fixSubgroup_slFieldAut_eq_range {k : Subfield K} {σ : K ≃+* K}
    (hk : ∀ x, x ∈ k ↔ σ x = x) :
    fixSubgroup (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 2) K σ) =
      (SpecialLinearGroup.map k.subtype :
        SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 2) K).range := by
  ext g
  rw [mem_fixSubgroup]
  constructor
  · intro hg
    have hent : ∀ a b, σ ((g : Matrix (Fin 2) (Fin 2) K) a b) =
        (g : Matrix (Fin 2) (Fin 2) K) a b := fun a b =>
      congrArg (fun x : SpecialLinearGroup (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K) a b) hg
    let g₀ : Matrix (Fin 2) (Fin 2) k := Matrix.of fun a b => ⟨_, (hk _).2 (hent a b)⟩
    have hg₀ : g₀.map k.subtype = g := Matrix.ext fun _ _ => rfl
    have hdet : g₀.det = 1 := Subtype.val_injective (by
      change k.subtype g₀.det = k.subtype 1
      rw [RingHom.map_det, map_one]
      change (g₀.map k.subtype).det = 1
      rw [hg₀]
      exact g.2)
    exact ⟨⟨g₀, hdet⟩, Subtype.ext hg₀⟩
  · rintro ⟨g₀, rfl⟩
    refine Subtype.ext (Matrix.ext fun a b => ?_)
    exact (hk _).1 ((g₀ : Matrix (Fin 2) (Fin 2) k) a b).2

theorem perfectInLayer_fieldAut_two (σ : K ≃+* K) :
    PerfectInLayer (LinearFlag.fieldAut 2 K σ) := by
  set k : Subfield K := (σ : K →+* K).eqLocusField (RingHom.id K)
  have hk : ∀ x, x ∈ k ↔ σ x = x := fun x => Iff.rfl
  set α := CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 2) K σ
  have hC := fixSubgroup_slFieldAut_eq_range (k := k) (σ := σ) hk
  let e : Matrix.SpecialLinearGroup (Fin 2) k ≃* ↥(fixSubgroup α) :=
    (MonoidHom.ofInjective (injective_map_subtype k)).trans (MulEquiv.subgroupCongr hC.symm)
  have hαβ : ∀ x, LinearFlag.proj 2 K (α x) =
      LinearFlag.fieldAut 2 K σ (LinearFlag.proj 2 K x) :=
    fun x => (LinearFlag.descendAut_proj 2 K α x).symm
  have hker : (LinearFlag.proj 2 K).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [LinearFlag.ker_proj]
    exact LinearFlag.scalars_le_center 2 K
  by_cases h4 : 4 ≤ Nat.card k
  · have hq : CFSG.IsQuasisimple ↥(fixSubgroup α) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e
        (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le le_rfl h4)
    exact perfectInLayer_of_centralQuotient (LinearFlag.proj 2 K) (LinearFlag.proj_surjective 2 K)
      hker α _ hαβ (fun _ : Unit => fixSubgroup α) (fun _ => le_rfl)
      (fun _ c hc g hg => (fixSubgroup α).mul_mem ((fixSubgroup α).mul_mem hc hg)
        ((fixSubgroup α).inv_mem hc))
      (fun _ => hq) (1 : ↥(fixSubgroup α) →* Unit)
      (fun x _ => Subgroup.mem_iSup_of_mem (ι := Unit) () x.2)
  · have hcard : Nat.card k = 2 ∨ Nat.card k = 3 := by
      have : 1 < Nat.card k := Finite.one_lt_card
      omega
    haveI : Group.IsSolvable (GL (Fin 2) k) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable k hcard
    haveI : Group.IsSolvable ↥(fixSubgroup α) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Matrix.SpecialLinearGroup.toGL.comp e.symm.toMonoidHom)
        (Matrix.SpecialLinearGroup.toGL_injective.comp e.symm.injective)
    exact perfectInLayer_of_centralQuotient (LinearFlag.proj 2 K) (LinearFlag.proj_surjective 2 K)
      hker α _ hαβ (fun i : Empty => i.elim) (fun i => i.elim) (fun i => i.elim)
      (fun i => i.elim) (MonoidHom.id ↥(fixSubgroup α)) (fun x hx => by
        have hx1 : x = 1 := hx
        rw [hx1]
        exact Subgroup.one_mem _)

theorem perfectInLayer_projectiveSL_two {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (β : MulAut (LinearFlag.projectiveSL 2 K)) (hβ : β ^ p = 1) : PerfectInLayer β := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨β₀, hββ₀⟩ : ∃ β₀ : MulAut (PSL2 K), MulAut.congr (psl2Equiv K) β₀ = β :=
    ⟨(MulAut.congr (psl2Equiv K)).symm β, (MulAut.congr (psl2Equiv K)).apply_symm_apply β⟩
  have hβ₀p : β₀ ^ p = 1 :=
    (MulAut.congr (psl2Equiv K)).injective (by rw [map_pow, hββ₀, hβ, map_one])
  have hcongr : ∀ A : GL (Fin 2) K, MulAut.congr (psl2Equiv K)
      (pglAction K (Matrix.ProjGenLinGroup.mk A)) = LinearFlag.conjAut 2 K A :=
    fun A => congr_pglAction_mk A
  by_cases hD : β₀ ∈ (pglAction K).range
  · obtain ⟨g, hg⟩ := hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hβA : β = LinearFlag.conjAut 2 K A := by
      rw [← hββ₀, ← hg]
      exact hcongr A
    have hAp : A ^ p ∈ Subgroup.center (GL (Fin 2) K) := by
      have h1 : pglAction K (Matrix.ProjGenLinGroup.mk (A ^ p)) = pglAction K 1 := by
        rw [map_pow, map_pow, hg, hβ₀p, map_one]
      exact Matrix.ProjGenLinGroup.mk_eq_one.1
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K h1)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hAp
    obtain ⟨c, hc⟩ := hAp
    rw [hβA]
    exact perfectInLayer_conjAut hpK hc.symm
  · have hne : β₀ ≠ 1 := fun h => hD ⟨1, by rw [map_one, h]⟩
    have hord : orderOf β₀ = p := orderOf_eq_prime hβ₀p hne
    obtain ⟨σ, -, g, hgσ⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent hp β₀ hord hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hβ' : β = LinearFlag.conjAut 2 K A * LinearFlag.fieldAut 2 K σ *
        (LinearFlag.conjAut 2 K A)⁻¹ := by
      rw [← hββ₀, hgσ, map_mul, map_mul, map_inv, hcongr, congr_psl2FieldAut]
    rw [hβ']
    exact perfectInLayer_conj _ _ (perfectInLayer_fieldAut_two σ)

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
