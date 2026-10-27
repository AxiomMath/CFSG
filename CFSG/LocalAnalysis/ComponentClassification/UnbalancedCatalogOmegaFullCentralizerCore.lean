module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaOddCoreLemmas
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaTriality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLGraphCoset

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped Pointwise

namespace OmegaRadical

variable {K : Type} [Field K] {d : ℕ}

@[expose] def SemilinearInvolutionOddCore (Q : QuadraticForm K (Fin d → K)) : Prop :=
  ∀ H : Subgroup (MulAut (matrixProjectiveDerived Q)), inner (matrixProjectiveDerived Q) ≤ H →
    H ≤ matrixProjectiveImage Q → ∀ α ∈ H, orderOf α = 2 →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥

@[expose] def FullInvolutionOddCore (Q : QuadraticForm K (Fin d → K)) : Prop :=
  ∀ H : Subgroup (MulAut (matrixProjectiveDerived Q)), inner (matrixProjectiveDerived Q) ≤ H →
    ∀ α ∈ H, orderOf α = 2 → CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥

theorem fullInvolutionOddCore_of_image_eq_top {Q : QuadraticForm K (Fin d → K)}
    (htop : matrixProjectiveImage Q = ⊤) (h : SemilinearInvolutionOddCore Q) :
    FullInvolutionOddCore Q := fun H hInn α hα h2 =>
  h H hInn (htop ▸ le_top) α hα h2

theorem fullInvolutionOddCore_plus_four (G : Type) [Group G] {f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 2 f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (hsemi : SemilinearInvolutionOddCore (coordinateQuadPlus 4 K)) :
    FullInvolutionOddCore (coordinateQuadPlus 4 K) := by
  have := finite_mulAut_matrixProjectiveDerived (coordinateQuadPlus 4 K)
  obtain ⟨himage, htri, -⟩ := d4_triality_full_involution_centralizer_obstruction
    G f h K hK e
  obtain ⟨hconj, horb⟩ :=
    CatalogueBOrthogonalInvolutionConjugacy.plus_four_conjugacy (K := K)
  intro H hInn α hαH hα2
  have hαα : α * α = 1 := by
    have h2 := pow_orderOf_eq_one α
    rw [hα2] at h2
    rw [← pow_two]
    exact h2
  obtain ⟨β, hβ⟩ := hconj α hαα
  rw [← himage] at hβ
  apply oddCore_centralizer_of_conj H α β
  set H' := H.map (MulAut.conj β⁻¹).toMonoidHom with hH'
  set α' := β⁻¹ * α * β with hα'
  have hα'H' : α' ∈ H' := ⟨α, hαH, by
    change β⁻¹ * α * β⁻¹⁻¹ = α'
    rw [inv_inv]⟩
  have hα'2 : orderOf α' = 2 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj β⁻¹) α
    rw [MulAut.conj_apply, inv_inv] at h1
    rw [hα', h1]
    exact hα2
  have hInn' : inner (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤ H' := by
    intro ι hι
    refine ⟨β * ι * β⁻¹, hInn (inner_conj_mem β hι), ?_⟩
    change β⁻¹ * (β * ι * β⁻¹) * β⁻¹⁻¹ = ι
    group
  have hstab : MulAction.stabilizer (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
      (projectivePointFamily (coordinateQuadPlus 4 K)) =
        matrixProjectiveImage (coordinateQuadPlus 4 K) := himage.symm
  refine oddCore_eq_bot_of_orbit_le_three (y₀ := projectivePointFamily (coordinateQuadPlus 4 K))
    (by rcases horb with h1 | h3 <;> omega)
    (N := inner (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ⊓
      Subgroup.centralizer {α'})
    (inf_le_inf_right _ hInn') ?_ ?_ ?_ ?_
  ·
    intro c hc n hn
    obtain ⟨hnI, hnC⟩ := Subgroup.mem_inf.mp hn
    obtain ⟨-, hcC⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨inner_conj_mem c hnI, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcC hnC) (Subgroup.inv_mem _ hcC)
  ·
    rw [hstab]
    exact inf_le_left.trans (matrixProjective_inner_le_image _)
  ·
    rw [hstab, inf_right_comm]
    exact hsemi _ (le_inf hInn' (matrixProjective_inner_le_image _)) inf_le_right α'
      (Subgroup.mem_inf.mpr ⟨hα'H', hβ⟩) hα'2
  ·
    intro η _ hη3 hηN
    rw [hstab]
    exact (htri α' hβ hα'2 η hη3 hηN).1

@[expose] def EvenOrthogonalModelFullCentralizer (G : Type) [Group G] (t : StatedLieTag)
    (n f : ℕ) : Prop :=
  match t with
  | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
      ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)),
        FullInvolutionOddCore (coordinateQuadPlus n K)
  | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
      ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)),
        FullInvolutionOddCore (coordinateQuadMinus n K hn b c)
  | _ => False

theorem oddCore_centralizer_of_full {X : Type} [Group X] [Finite X]
    [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) {P : Type} [Group P]
    (θ : CFSG.generalizedFitting X ≃* P)
    (hfull : ∀ H : Subgroup (MulAut P), inner P ≤ H → ∀ α ∈ H, orderOf α = 2 →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥)
    (z : X) (hz : orderOf z = 2) : CFSG.oddCore ↥(Subgroup.centralizer {z}) = ⊥ := by
  set F := CFSG.generalizedFitting X with hF
  set ρ := EvenLinearSL.conjModel θ with hρ
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (F : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun φ : MulAut P => φ (θ ⟨y, hy⟩)) hx
      simp only [MulAut.one_apply] at h1
      rw [hρ, EvenLinearSL.conjModel_apply] at h1
      have h2 := congrArg Subtype.val (θ.injective h1)
      simp only at h2
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    have hxF : x ∈ F := CFSG.centralizer_generalizedFitting_le X hxC
    have hcen : (⟨x, hxF⟩ : F) ∈ Subgroup.center F := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    rw [EvenLinearSL.center_eq_bot_of_simple hnonab, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hinner : inner P ≤ ρ.range := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨y, rfl⟩ := θ.surjective p
    exact ⟨y, EvenLinearSL.conjModel_of_mem θ y⟩
  have hρz : orderOf (ρ z) = 2 := by rw [orderOf_injective ρ hinj z, hz]
  have h1 := hfull ρ.range hinner (ρ z) ⟨z, rfl⟩ hρz
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv (EvenCatalog.centralizerMapEquiv hinj z).symm h1

theorem almost_simple_oddCore_of_modelFull {X : Type} [Group X] [Finite X]
    [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) (t : StatedLieTag)
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {n f : ℕ}
    (hmodel : StatedClassicalModel (CFSG.generalizedFitting X) t n 2 f)
    (hfull : EvenOrthogonalModelFullCentralizer (CFSG.generalizedFitting X) t n f) :
    ∀ z : X, orderOf z = 2 → CFSG.oddCore ↥(Subgroup.centralizer {z}) = ⊥ := by
  intro z hz
  rcases ht with rfl | rfl
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel.2
    exact oddCore_centralizer_of_full hnonab (coordinatePlusWitnessEquiv K e) (hfull K hK e) z hz
  · obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hmodel.2
    have hn : 1 ≤ n := by
      have := hmodel.1.2.2
      omega
    exact oddCore_centralizer_of_full hnonab (coordinateMinusWitnessEquiv K hn b c e)
      (hfull hn K hK b c hirr e) z hz

end OmegaRadical

end CFSG.ComponentClassification.UnbalancedCatalog
