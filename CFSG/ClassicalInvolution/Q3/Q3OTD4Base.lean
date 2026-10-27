module

public import CFSG.ClassicalInvolution.Q3.Q3OTBase
public import CFSG.ClassicalInvolution.Q3.Q3OTInn
public import CFSG.ClassicalInvolution.Q3.Q3OTKlein
public import CFSG.ClassicalInvolution.Q3.Q3TLKD4Fix
public import CFSG.ClassicalInvolution.Q3.Q3TD3R4Ord
public import CFSG.ClassicalInvolution.Q3.Q3TJD4
public import CFSG.ClassicalInvolution.Q3.Q3TSetup
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.Q3.Q3TIRed

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.ModelFacts.Orth15
open CFSG.ClassicalInvolution.G2D4Models.Twin (LiftSimFr PreservesFund)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)


section Facts

theorem oddCoreFree_plus4 (X : Type) [Group X] [Finite X] (ψ : spinGroup Q₄ →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center (spinGroup Q₄)) (x : X)
    (hx : orderOf x = 2) : CFSG.Assembly.Dichotomy.involutionOddCore x = ⊥ := by
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have key : ∀ M : LieUniversal, M = ⟨spinGroup Q₄, plusDatum 4 𝔽₃ (by norm_num)⟩ →
      (∀ (X : Type) [Group X] [Finite X] (ψ : M.K →* X), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center M.K → ∀ x : X, orderOf x = 2 →
          CFSG.Assembly.Dichotomy.involutionOddCore x = ⊥) →
      ∀ (X : Type) [Group X] [Finite X] (ψ : spinGroup Q₄ →* X), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center (spinGroup Q₄) → ∀ x : X, orderOf x = 2 →
          CFSG.Assembly.Dichotomy.involutionOddCore x = ⊥ := by
    intro M hM h
    subst hM
    exact h
  exact key _ (RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) (by norm_num))
    (fun X _ _ ψ hψ hk x hx => Q3.modelOddCentralizerFree3_proved .POmegaPlus 4
      Nat.prime_three trivial hadm X ψ hψ hk x hx) X ψ hψ hker x hx

theorem fundSingleClass_plus4 : ∀ R ∈ fundamentalSubgroups .POmegaPlus
    (plusDatum 4 𝔽₃ (by norm_num)), ∃ g : spinGroup Q₄, R = conjSub g (Q3T.d4R0 𝔽₃) := by
  intro R hR
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hR₀ : Q3T.d4R0 (GaloisField 3 1) ∈ Generic.fundamentalSubgroups .POmegaPlus
      (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D :=
    RouteD.rankOne_mem_fundamentalSubgroups_plusDatum Q3T.three_le_four 0
  obtain ⟨g, hg⟩ := ModelFacts.fundamentalSingleClass .POmegaPlus 4 3 1 Nat.prime_three
    trivial hadm (by decide) (by decide) _ hR₀ R hR
  exact ⟨g, hg⟩

theorem fundNoncentral_plus4 : ∀ R ∈ fundamentalSubgroups .POmegaPlus
    (plusDatum 4 𝔽₃ (by norm_num)), ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q₄) → r = 1 := by
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have key : ∀ M : LieUniversal, M = ⟨spinGroup Q₄, plusDatum 4 𝔽₃ (by norm_num)⟩ →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ r ∈ R, r ∈ Subgroup.center M.K → r = 1) →
      ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)),
        ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q₄) → r = 1 := by
    intro M hM h
    subst hM
    exact h
  exact key _ (RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) (by norm_num))
    (fund_noncentral_modelUniv (p := 3) (e := 1) (t := .POmegaPlus) (n := 4) trivial hadm
      (by simp))

end Facts

section Sq

variable {H : Type} [Group H]

theorem exists_ordinary_data_plus4 (ψ : spinGroup Q₄ →* H) {R R' : Subgroup (spinGroup Q₄)}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (hne : R ≠ R') (hc : Commutes R R') (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v) :
    ∃ (σ : spinGroup Q₄ ≃* spinGroup Q₄) (fr : OFrame Q₄), PreservesFund 3 1 σ ∧
      (R.map σ.toMonoidHom).map (spinAction Q₄) = fr.La.range ∧
      (R'.map σ.toMonoidHom).map (spinAction Q₄) = fr.swap.La.range ∧
      ∀ s : spinGroup Q₄, spinAction Q₄ s ∈ fr.La.range ⊔ fr.swap.La.range →
        ∀ g : ↥ψ.range, (v : MulAut ↥ψ.range) ((ψ.rangeRestrict.comp σ.symm.toMonoidHom) s * g *
          ((ψ.rangeRestrict.comp σ.symm.toMonoidHom) s)⁻¹) =
          (ψ.rangeRestrict.comp σ.symm.toMonoidHom) s * (v : MulAut ↥ψ.range) g *
            ((ψ.rangeRestrict.comp σ.symm.toMonoidHom) s)⁻¹ := by
  classical
  have : Group.IsPerfect (spinGroup Q₄) := isPerfect_spinGroup_quadPlus (by norm_num)
  obtain ⟨σ, fr, hσ, hσ', h1, h2⟩ := Q3TD.exists_ordinary_pair3 hR hR' hne hc
  have hθs : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hθ's : Function.Surjective (ψ.rangeRestrict.comp σ.symm.toMonoidHom) :=
    hθs.comp σ.symm.surjective
  have hθ'σ : ∀ s, (ψ.rangeRestrict.comp σ.symm.toMonoidHom) (σ.toMonoidHom s) =
      ψ.rangeRestrict s := fun s => by
    show ψ.rangeRestrict (σ.symm (σ s)) = _
    rw [MulEquiv.symm_apply_apply]
  have hinn : ∀ r, ((FrameVertex.innerHom ψ r : ↥(inducedAutOn ψ.range)) : MulAut ↥ψ.range) =
      MulAut.conj (ψ.rangeRestrict r) := fun r => by
    ext y
    rfl
  have hcomm : ∀ r, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v →
      ∀ g : ↥ψ.range, (v : MulAut ↥ψ.range) (ψ.rangeRestrict r * g * (ψ.rangeRestrict r)⁻¹) =
        ψ.rangeRestrict r * (v : MulAut ↥ψ.range) g * (ψ.rangeRestrict r)⁻¹ := by
    intro r hr
    have h3 := congrArg Subtype.val hr
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hinn] at h3
    exact pointwise_of_comm_conj _ _ h3
  refine ⟨σ, fr, hσ, h1, h2, ?_⟩
  intro s hs
  rw [← h1, ← h2, ← Subgroup.map_sup] at hs
  obtain ⟨w, hw, hws⟩ := hs
  have hwc : w⁻¹ * s ∈ Subgroup.center (spinGroup Q₄) :=
    ker_spinAction_le_center Q₄ (by rw [MonoidHom.mem_ker, map_mul, map_inv, hws, inv_mul_cancel])
  refine commute_conj_of_mem_sup (ψ.rangeRestrict.comp σ.symm.toMonoidHom) hθ's (v : MulAut _)
    (R₁ := R.map σ.toMonoidHom) (R₂ := R'.map σ.toMonoidHom) ?_ ?_ hw hwc
  · rintro _ ⟨r, hr, rfl⟩ g
    rw [hθ'σ]
    exact hcomm r (hvR r hr) g
  · rintro _ ⟨r, hr, rfl⟩ g
    rw [hθ'σ]
    exact hcomm r (hvR' r hr) g

theorem sq_mem_inn_plus4 (ψ : spinGroup Q₄ →* H)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q₄)) {R R' : Subgroup (spinGroup Q₄)}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (hne : R ≠ R') (hc : Commutes R R') (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v) :
    (v : MulAut ↥ψ.range) * (v : MulAut ↥ψ.range) ∈ innSubgroup ↥ψ.range := by
  classical
  have hodd := ModelFacts.TG3.odd_natCard_galoisField_three
  have hF3 := ModelFacts.TG3.natCard_galoisField_three
  have hn3 : 3 ≤ 4 := by norm_num
  have : Group.IsPerfect (spinGroup Q₄) := isPerfect_spinGroup_quadPlus hn3
  have hZ3 := Q3TLK.center_plus4_no_three
  have hdim : 7 ≤ Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    norm_num
  obtain ⟨σ, fr, hσ, h1, h2, hα⟩ := exists_ordinary_data_plus4 ψ hR hR' hne hc v hvR hvR'
  have hθs : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hθk : ψ.rangeRestrict.ker ≤ Subgroup.center (spinGroup Q₄) := ker_rangeRestrict_le ψ hψ
  have hθ's : Function.Surjective (ψ.rangeRestrict.comp σ.symm.toMonoidHom) :=
    hθs.comp σ.symm.surjective
  have hθ'k := ker_comp_symm_le_center ψ.rangeRestrict hθk σ
  exact sq_mem_inn_abs hodd hF3 (nondegenerate_polarBilin_quadPlus 4 _)
    (range_spinAction_quadPlus hn3) hZ3 hdim fr hθ's hθ'k (v : MulAut ↥ψ.range)
    (Q3TLK.liftSimFr3_plus4 _ hθ'k) hα

end Sq

end CFSG.ClassicalInvolution.Q3.Q3OT
