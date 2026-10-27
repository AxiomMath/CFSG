module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUUnit
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUBlockElem
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUBlockFactor

public noncomputable section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG Subgroup Module CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatLeafProof.X10Lin (centralModel_GL_component_two_le)
open CFSG.ComponentClassification.CatLeafProof.X10Sp (CentralModel centralModel_of_component_equiv)

theorem sesqCentralizer_block {p f : ℕ} {E : Type} [Field E]
    (h : UnitaryFieldData p f E) (hp : p ≠ 2) {V : Type} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2)
    {M : Subgroup (Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B)))} (hM : IsComponent M) :
    (∃ k f' : ℕ, CentralModel p .PSL k f' M) ∨
      ∃ d : ℕ, 3 ≤ d ∧ CentralModel p .PSU d f M ∧ ∀ ζ : E, h.norm ζ = 1 → ζ ^ d = 1 →
        ∃ w : M, w ∈ center M ∧ ∃ P Q : Submodule E V,
          ActsAsBlock (unitaryOp ((w : Subgroup.centralizer ({A} : Set (sesqUnitaryGroup B))) :
            sesqUnitaryGroup B)) ζ P Q := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨l, -, -, hN, hP, hMm, hcompl, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hA
  have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
    ⟨fun x y => hB.eq (x : V) (y : V)⟩
  have hP' := Submodule.one_le_finrank_iff.mpr hP
  have hM' := Submodule.one_le_finrank_iff.mpr hMm
  rcases hN with hN | hN
  ·
    obtain ⟨-, hlP, hlM, e, hres⟩ := hsplit hN
    have hMe := LocalCores.isComponent_map_mulEquiv e hM
    rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
        hMe with h2' | h1'
    ·
      have h2'' : ∀ x ∈ M, (e x).2 = 1 := fun x hx => h2' _ ⟨x, hx, rfl⟩
      obtain ⟨ρ, hρi, hρc, hρe⟩ := OddClassSelector.restrict_component e hM h2''
      rcases unitaryFactor_component_model h hp hP' (hsymm _) hlP ρ hρi hρc with
        ⟨-, hm⟩ | ⟨h3, hm⟩
      · exact Or.inl ⟨2, f, hm⟩
      · refine Or.inr ⟨_, h3, hm, fun ζ hζ hζk => ?_⟩
        obtain ⟨x, hxc, hx⟩ := exists_scalar_of_component h hp hP' (hsymm _) hlP ρ hρi hρc hζ hζk
        refine ⟨x, hxc, _, _, ActsAsBlock.of_comp_subtype hcompl hP hMm (hres x).1 (hres x).2 ?_ ?_⟩
        · rw [← hρe x]
          exact hx
        · rw [h2'' x x.2]
          rfl
    ·
      have h1'' : ∀ x ∈ M, (e x).1 = 1 := fun x hx => h1' _ ⟨x, hx, rfl⟩
      let e' := e.trans MulEquiv.prodComm
      have h2'' : ∀ x ∈ M, (e' x).2 = 1 := fun x hx => h1'' x hx
      obtain ⟨ρ, hρi, hρc, hρe⟩ := OddClassSelector.restrict_component e' hM h2''
      rcases unitaryFactor_component_model h hp hM' (hsymm _) hlM ρ hρi hρc with
        ⟨-, hm⟩ | ⟨h3, hm⟩
      · exact Or.inl ⟨2, f, hm⟩
      · refine Or.inr ⟨_, h3, hm, fun ζ hζ hζk => ?_⟩
        obtain ⟨x, hxc, hx⟩ := exists_scalar_of_component h hp hM' (hsymm _) hlM ρ hρi hρc hζ hζk
        refine ⟨x, hxc, _, _, ActsAsBlock.of_comp_subtype hcompl.symm hMm hP (hres x).2 (hres x).1
          ?_ ?_⟩
        · have h3 : ρ x = (e x).2 := hρe x
          rw [← h3]
          exact hx
        · rw [h1'' x x.2]
          rfl
  ·
    obtain ⟨-, -, -, hdim2, -, -, e, -⟩ := hpaired hN
    refine Or.inl ⟨finrank E (eigenPlus l (unitaryOp A)), 2 * f, ?_⟩
    refine centralModel_of_component_equiv (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
      (Module.finBasis E (eigenPlus l (unitaryOp A)))).toMulEquiv)) (fun N hN' => ?_) hM
    rcases Nat.lt_or_ge (finrank E (eigenPlus l (unitaryOp A))) 2 with h1 | h2'
    · exfalso
      have := CatalogueBGeneralLinear.generalLinear_small_solvable
        (finrank E (eigenPlus l (unitaryOp A))) E (Or.inl (by omega))
      exact OddInner.not_isComponent_of_isSolvable N hN'
    · have h9 : 9 ≤ p ^ (2 * f) := by
        rw [pow_mul']
        exact Nat.pow_le_pow_left (OddInner.three_le_pow h.prime hp h.one_le) 2
      exact centralModel_GL_component_two_le h.prime hp (by have := h.one_le; omega) h.card h2'
        (Or.inr (by rw [h.card]; omega)) hN'

end CFSG.OddStandard.HigherRank.LinUnit
