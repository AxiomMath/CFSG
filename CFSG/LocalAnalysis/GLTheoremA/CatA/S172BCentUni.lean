module

public import CFSG.RankThree.CentralLift.DefiningUnitary
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.Adapters.CatalogueFieldBridges.UnitarySU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Types
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockQuasisimple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

open Module CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.ComponentInitial

theorem open_isQuasisimple_of {X : Type*} [Group X] (h : CFSG.IsQuasisimple X) :
    CFSG.Open.IsQuasisimple X :=
  ⟨@Group.IsPerfect.commutator_eq_top _ _ h.1, h.2.1⟩

theorem catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA {ℓ f : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ f E) (hℓf : ℓ ^ f = 2) {M : Type} [AddCommGroup M] [Module E M]
    [FiniteDimensional E M] {B : M →ₛₗ[hE.bar] M →ₗ[E] E} (hBs : B.IsSymm) (hBl : B.SeparatingLeft)
    {k : ℕ} (hk : 4 ≤ k) (hdim : finrank E M = k) :
    catalogIs (PSimple 3 (sesqSpecialUnitaryGroup B)) (isUnA k 2) := by
  classical
  haveI : Finite E := hE.finite
  haveI : Finite M := Module.finite_of_finite E
  have hq : CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroup B) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_sesqSpecialUnitaryGroup_of_three_le hE hBs hBl
      (by omega) (by rw [hdim, hℓf]; intro h; simp at h; omega)
  have hord := (CFSG.LinearGroups.unitary_full_group_order hE hBs hBl hdim (by omega)).2.1
  rw [hℓf] at hord
  have h3 : 3 ∣ Nat.card ↥(sesqSpecialUnitaryGroup B) := by
    have hprod : (3 : ℤ) ∣ ∏ i ∈ Finset.Icc 2 k, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) := by
      have := Finset.dvd_prod_of_mem (fun i : ℕ => (((2 : ℕ) : ℤ) ^ i - (-1) ^ i))
        (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩ : 2 ∈ Finset.Icc 2 k)
      simpa using this
    have : (3 : ℤ) ∣ (Nat.card ↥(sesqSpecialUnitaryGroup B) : ℤ) := by
      rw [hord]
      exact Dvd.dvd.mul_left hprod _
    exact_mod_cast this
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hBs hBl
  let e' : Module.Basis (Fin k) E M := e.reindex (finCongr hdim)
  have he' : ∀ i j, B (e' i) (e' j) = ((1 : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) i j := by
    intro i j
    simp only [e', Module.Basis.reindex_apply, he, Units.val_one, Matrix.one_apply,
      (finCongr hdim).symm.injective.eq_iff]
  obtain ⟨φ₁⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE e' he'
  have hS := CFSG.ComponentClassification.Burgoyne.U.statedSU_eq_gramSU hE (n := k)
  let ψ : ↥(StatedSU k (ℓ ^ f) E) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MulEquiv.subgroupCongr hS).trans φ₁.symm
  let ψq : ↥(StatedSU k (ℓ ^ f) E) ⧸ Subgroup.center ↥(StatedSU k (ℓ ^ f) E) ≃*
      ↥(sesqSpecialUnitaryGroup B) ⧸ Subgroup.center ↥(sesqSpecialUnitaryGroup B) :=
    QuotientGroup.congr _ _ ψ (Subgroup.map_center_eq ψ)
  haveI : Fintype E := Fintype.ofFinite E
  have hcardE : Fintype.card E = (ℓ ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hE.card, ← pow_mul, mul_comm]
  obtain ⟨q', hv, -, hq'c, ⟨χ⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
      (K := E) (m := k) (q := ℓ ^ f) hcardE (by omega) (by rw [hℓf]; intro h; simp at h; omega)
  have hJ := H81Orth.centerQuotEquivPSimple_of_dvd_card Nat.prime_three (open_isQuasisimple_of hq) h3
  refine ⟨.lie ⟨.twistedA (k - 1) q', hv⟩, ?_, ⟨hJ.symm.trans (ψq.symm.trans χ)⟩⟩
  refine Or.inl ?_
  show (k - 1) + 1 = k ∧ q'.card = 2
  exact ⟨by omega, by rw [hq'c, hℓf]⟩

end CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

end
