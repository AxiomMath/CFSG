module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSpAdapted
public import CFSG.LieType.HighestRoot.CentChevalleySLThree

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CH

open CFSG.ClassicalInvolution.Q3 CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups

section Model

variable {F : Type} [Field F] [Finite F] [hF3 : Fact (Nat.card F = 3)]

theorem nonempty_suid_two_equiv : Nonempty (SUid (gaussSigma (F := F)) 2 ≃* SL(2, ZMod 3)) := by
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.Models.nonempty_sl2_mulEquiv_su_two
    (K := GaussField F) (p := 3) (f := 1) card_gaussField_sq
  have hfix : Nat.card (CFSG.LieType.Steinberg.fixedSubfield (GaussField F) 3 1) = 3 := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield card_gaussField_sq, pow_one]
  exact ⟨e.symm.trans (CFSG.LieType.HighestRoot.slEquivSL23 hfix)⟩

theorem mat_gComplex_mul_self : mat 2 F (gComplex 2) * mat 2 F (gComplex 2) = -1 := by
  have h : mat 2 F (gComplex 2) = Matrix.fromBlocks 0 (-1) 1 0 := mat_ofSymplecticMat _ _
  rw [h, Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]

noncomputable def negOne : SUid (gaussSigma (F := F)) 2 :=
  mkSU (-1) (by simp [Matrix.det_neg]) (by
    have h1 : (-1 : Matrix (Fin 2) (Fin 2) (GaussField F)) =
        Matrix.scalar (Fin 2) (-1 : GaussField F) := by rw [map_neg, map_one]
    rw [h1, conjTr_scalar, ← map_mul, map_neg, map_one, neg_mul_neg, one_mul, map_one])

theorem mat_suToSp_negOne : mat 2 F (suToSp 2 (negOne (F := F))) = -1 := by
  rw [mat_suToSp]
  show gaussBlocks 2 (-1 : Matrix (Fin 2) (Fin 2) (GaussField F)) = -1
  rw [map_neg, map_one]

theorem gComplex_mul_self : gComplex (F := F) 2 * gComplex 2 = suToSp 2 negOne := by
  apply mat_injective
  rw [map_mul, mat_gComplex_mul_self, mat_suToSp_negOne]

theorem exists_layer0 (u : StatedSp 2 F) (hu : mat 2 F u * mat 2 F u = -1) :
    ∃ L0 : Subgroup (StatedSp 2 F), L0 ≤ Subgroup.centralizer ({u} : Set (StatedSp 2 F)) ∧
      (∀ x ∈ Subgroup.centralizer ({u} : Set (StatedSp 2 F)), ∀ y ∈ L0, x * y * x⁻¹ ∈ L0) ∧
      u * u ∈ L0 ∧ Nonempty (L0 ≃* SL(2, ZMod 3)) := by
  obtain ⟨Q, hQ⟩ := exists_conj_gComplex u hu
  have hu' : u = Q * gComplex 2 * Q⁻¹ := by rw [← hQ]; group
  set R0 : Subgroup (StatedSp 2 F) := (suToSp (F := F) 2).range with hR0
  have hc : Function.Injective (MulAut.conj Q).toMonoidHom := (MulAut.conj Q).injective
  have hmem : ∀ y, y ∈ R0.map (MulAut.conj Q).toMonoidHom ↔ Q⁻¹ * y * Q ∈ R0 := by
    intro y
    constructor
    · rintro ⟨r, hr, rfl⟩
      have e : Q⁻¹ * (MulAut.conj Q).toMonoidHom r * Q = r := by
        show Q⁻¹ * (Q * r * Q⁻¹) * Q = r
        group
      rw [e]
      exact hr
    · intro hy
      exact ⟨Q⁻¹ * y * Q, hy, by simp [MulAut.conj_apply]; group⟩
  have hcentR : ∀ r ∈ R0, r * gComplex 2 = gComplex 2 * r := by
    rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (suToSp_mem_centralizer A)
  refine ⟨R0.map (MulAut.conj Q).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [hmem] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hcentR _ hy
    have e1 : u * y = Q * (gComplex 2 * (Q⁻¹ * y * Q)) * Q⁻¹ := by rw [hu']; group
    have e2 : y * u = Q * ((Q⁻¹ * y * Q) * gComplex 2) * Q⁻¹ := by rw [hu']; group
    rw [e1, e2, h1]
  · intro x hx y hy
    rw [hmem] at hy ⊢
    have hx1 : Q⁻¹ * x * Q ∈ Subgroup.centralizer ({gComplex 2} : Set (StatedSp 2 F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hx
      have e1 : gComplex (F := F) 2 = Q⁻¹ * u * Q := by rw [hu']; group
      rw [e1]
      calc Q⁻¹ * x * Q * (Q⁻¹ * u * Q) = Q⁻¹ * (x * u) * Q := by group
        _ = Q⁻¹ * (u * x) * Q := by rw [h1]
        _ = (Q⁻¹ * u * Q) * (Q⁻¹ * x * Q) := by group
    have := conj_mem_range_suToSp hx1 hy
    have e : Q⁻¹ * (x * y * x⁻¹) * Q = (Q⁻¹ * x * Q) * (Q⁻¹ * y * Q) * (Q⁻¹ * x * Q)⁻¹ := by
      group
    rw [e]
    exact this
  · rw [hmem]
    have e : Q⁻¹ * (u * u) * Q = gComplex 2 * gComplex 2 := by rw [hu']; group
    rw [e, gComplex_mul_self]
    exact ⟨_, rfl⟩
  · obtain ⟨e1⟩ := nonempty_suid_two_equiv (F := F)
    exact ⟨(Subgroup.equivMapOfInjective R0 (MulAut.conj Q).toMonoidHom hc).symm.trans
      ((MonoidHom.ofInjective suToSp_injective).symm.trans e1)⟩

theorem mat_eq_neg_one_of_center {g : StatedSp 2 F} (hg : g ∈ Subgroup.center (StatedSp 2 F))
    (hne : g ≠ 1) : mat 2 F g = -1 := by
  have hex : ∃ r : F, mat 2 F g = r • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F, Subgroup.mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range] at hg
    obtain ⟨r, hr⟩ := hg
    refine ⟨r, ?_⟩
    rw [mat_apply, ← hr, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
  obtain ⟨r, hmat⟩ := hex
  have hsymp := mat_transpose_mul_gram_mul g
  rw [hmat] at hsymp
  have hr2 : r * r = 1 := by
    have h1 := congrFun (congrFun hsymp (Sum.inl 0)) (Sum.inr 0)
    simpa [gram, Matrix.mul_apply, Matrix.fromBlocks, Matrix.smul_apply, smul_eq_mul] using h1
  rcases mul_self_eq_one_iff.mp hr2 with h | h
  · exact absurd (mat_injective (by rw [hmat, h, one_smul, map_one])) hne
  · rw [hmat, h, neg_one_smul]

theorem exists_layer_bar {Xb : Type*} [Group Xb] (ψ : StatedSp 2 F →* Xb)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    {f : StatedSp 2 F} (hf : f ∈ Subgroup.center (StatedSp 2 F)) (hfz : ψ f ≠ 1)
    {ub : Xb} (hub : ub * ub = ψ f) :
    ∃ Lb : Subgroup Xb, Lb ≤ Subgroup.centralizer ({ub} : Set Xb) ∧
      (∀ x ∈ Subgroup.centralizer ({ub} : Set Xb), ∀ y ∈ Lb, x * y * x⁻¹ ∈ Lb) ∧ ub * ub ∈ Lb ∧
      Nonempty (Lb ≃* SL(2, ZMod 3)) := by
  have hf1 : f ≠ 1 := fun h => hfz (by rw [h, map_one])
  have hfm := mat_eq_neg_one_of_center hf hf1
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hx1
    have hxm := mat_eq_neg_one_of_center (hker (MonoidHom.mem_ker.mpr hx)) hx1
    have hxf : x = f := mat_injective (hxm.trans hfm.symm)
    exact hfz (by rw [← hxf]; exact hx)
  obtain ⟨u0, rfl⟩ := hψ ub
  have hu0 : u0 * u0 = f := hinj (by rw [map_mul, hub])
  have hmat : mat 2 F u0 * mat 2 F u0 = -1 := by rw [← map_mul, hu0, hfm]
  obtain ⟨L0, hL0c, hL0n, hu0L, ⟨e0⟩⟩ := exists_layer0 u0 hmat
  refine ⟨L0.map ψ, ?_, ?_, ?_, ⟨(Subgroup.equivMapOfInjective L0 ψ hinj).symm.trans e0⟩⟩
  · rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hL0c hl)]
  · rintro xb hxb _ ⟨l, hl, rfl⟩
    obtain ⟨x, rfl⟩ := hψ xb
    have hx : x ∈ Subgroup.centralizer ({u0} : Set (StatedSp 2 F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hinj
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hxb
    exact ⟨x * l * x⁻¹, hL0n x hx l hl, by simp⟩
  · exact ⟨u0 * u0, hu0L, by rw [map_mul]⟩

end Model

end CFSG.ClassicalInvolution.Q3.Q3CH
