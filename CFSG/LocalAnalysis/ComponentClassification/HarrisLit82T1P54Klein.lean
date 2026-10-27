module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Central
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthHigh

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.Klein

open CFSG Subgroup Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

theorem mem_center_of_forall_commutator_mem_center {P : Type*} [Group P]
    [hP : Group.IsPerfect P] {y : P} (h : ∀ g, ⁅y, g⁆ ∈ center P) : y ∈ center P := by
  let _ : CommGroup (center P) :=
    { (inferInstance : Group (center P)) with
      mul_comm := fun a b => Subtype.ext (mem_center_iff.mp b.2 a) }
  let φ : P →* center P :=
    { toFun := fun g => ⟨⁅y, g⁆, h g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change ⁅y, a * b⁆ = ⁅y, a⁆ * ⁅y, b⁆
        have hb := mem_center_iff.mp (h b) a
        have e : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e, hb, mul_inv_cancel_right]) }
  have hker : commutator P ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hP.commutator_eq_top] at hker
  refine mem_center_iff.mpr fun g => ?_
  have h2 : ⁅y, g⁆ = 1 := congrArg Subtype.val (hker (mem_top g))
  rw [commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2.symm

section Six

variable {k W : Type} [Field k] [Finite k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]

theorem isQuasisimple_commutator_orthogonalSix (hodd : Odd (Nat.card k))
    (Q₀ : QuadraticForm k W) (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (hdim : Module.finrank k W = 6) :
    IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀)) := by
  by_cases hT : ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0
  · obtain ⟨T, hT3, hTQ⟩ := hT
    exact CatalogueBOrthogonal.derived_quasisimple Q₀
      (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card k hodd) hQ₀ hT3.ge hTQ
  · obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
      LocalAnalysis.ComponentInitial.orthogonal_nonsplit_six_derived hodd Q₀ hQ₀ hdim hT
    exact hq

theorem lieModel_of_orthogonalSix_cover {J : Type} [Group J] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hk : Nat.card k = p ^ f) (Q₀ : QuadraticForm k W)
    (hQ₀ : Q₀.polarBilin.Nondegenerate) (hdim : Module.finrank k W = 6) (hJ : IsQuasisimple J)
    (φ : J →* commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀)) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ center J) :
    ((∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0) →
      Blueprint.LieModel (J ⧸ center J) .PSL 4 p f) ∧
    ((¬ ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0) →
      Blueprint.LieModel (J ⧸ center J) .PSU 4 p f) := by
  have hodd : Odd (Nat.card k) := hk ▸ (hp.odd_of_ne_two hp2).pow
  have hM : IsComponent (commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀)) :=
    ⟨isQuasisimple_commutator_orthogonalSix hodd Q₀ hQ₀ hdim,
      Subgroup.Normal.isSubnormal inferInstance⟩
  obtain ⟨e⟩ := nonempty_center_quot_equiv hJ hφ hker
  exact ⟨fun hT => LieType.CurtisTits.lieModel_of_mulEquiv e.symm
      (CatLeafProof.X10Lin.centralModel_orthogonal_split_six hp hp2 hf hk Q₀ hQ₀ hdim hT hM).2,
    fun hno => LieType.CurtisTits.lieModel_of_mulEquiv e.symm
      (CatLeafProof.X10Lin.centralModel_orthogonal_nonsplit_six hp hp2 hf hk Q₀ hQ₀ hdim hno
        hM).2⟩

@[expose] def commutatorEquiv (Q₀ : QuadraticForm k W) :
    commutator (TauCeti.QuadraticMap.orthogonalGroup Q₀) ≃*
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₀, TauCeti.QuadraticMap.orthogonalGroup Q₀⁆ :=
  ((commutator _).equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _))

theorem lieModel_of_orthogonalSix_cover' {J : Type} [Group J] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hk : Nat.card k = p ^ f) (Q₀ : QuadraticForm k W)
    (hQ₀ : Q₀.polarBilin.Nondegenerate) (hdim : Module.finrank k W = 6) (hJ : IsQuasisimple J)
    (φ : J →* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
      TauCeti.QuadraticMap.orthogonalGroup Q₀⁆)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center J) :
    ((∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0) →
      Blueprint.LieModel (J ⧸ center J) .PSL 4 p f) ∧
    ((¬ ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0) →
      Blueprint.LieModel (J ⧸ center J) .PSU 4 p f) := by
  refine lieModel_of_orthogonalSix_cover hp hp2 hf hk Q₀ hQ₀ hdim hJ
    ((commutatorEquiv Q₀).symm.toMonoidHom.comp φ) ((commutatorEquiv Q₀).symm.surjective.comp hφ)
    fun x hx => hker ?_
  rw [MonoidHom.mem_ker] at hx ⊢
  simpa using hx

theorem exists_lieModel_of_orthogonalSix_cover' {J : Type} [Group J] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hk : Nat.card k = p ^ f) (Q₀ : QuadraticForm k W)
    (hQ₀ : Q₀.polarBilin.Nondegenerate) (hdim : Module.finrank k W = 6) (hJ : IsQuasisimple J)
    (φ : J →* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
      TauCeti.QuadraticMap.orthogonalGroup Q₀⁆)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center J) :
    ∃ (τ' : StatedLieTag) (n' : ℕ), Blueprint.LieModel (J ⧸ center J) τ' n' p f := by
  have h := lieModel_of_orthogonalSix_cover' hp hp2 hf hk Q₀ hQ₀ hdim hJ φ hφ hker
  by_cases hT : ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0
  · exact ⟨.PSL, 4, h.1 hT⟩
  · exact ⟨.PSU, 4, h.2 hT⟩

end Six

end CFSG.ComponentClassification.HarrisLit.T1.P54.Klein
