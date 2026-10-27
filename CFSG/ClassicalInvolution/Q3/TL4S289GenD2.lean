module

public import CFSG.ClassicalInvolution.Q3.TL4S289GenD1
public import CFSG.ClassicalInvolution.Q3.TL4SecIdMu
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LShape
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LOdd01
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LMin01

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.S289G

section Pkg

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

theorem starFrameGenAll_of_pkg {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    {c : CompData} (hpkg : Q3AM.S4L.ModelPkg c) (hR : TypeRFam 3 Φ) (h : SecIdQ8Shape c Φ)
    (h284 : ∀ M ∈ Φ, ∀ N ∈ omegaNbr Φ M, ∀ m n : X, IsUniqueInvolution M m →
      IsUniqueInvolution N n → m * n ∈ Subgroup.center X) :
    ∀ L ∈ Φ, StarFrameGenAll Φ L := by
  obtain ⟨-, hperf, hsingle, -, V, _, _, _, Q, θ, z₀, D, hV, -⟩ := hpkg
  obtain ⟨ψ, hs, hker, hfund⟩ := h
  obtain ⟨Ra, Rb, -, a, b, u, -, hRa, hRb, -, hUa, hUb, -, hu, hu4, huu, hau, -, -, hnc, hgen⟩ :=
    Q3AM.S4L.exists_kframe ModelFacts.TG3.odd_natCard_galoisField_three D hV
  have hZ : ∀ {R : Subgroup c.G} {r : c.G}, R ∈ c.fund → IsUniqueInvolution R r →
      r ∈ Subgroup.center c.G → b * a⁻¹ ∈ Subgroup.center c.G := by
    intro R r hR hr hrZ
    have key : ∀ {R' : Subgroup c.G} {r' : c.G}, R' ∈ c.fund → IsUniqueInvolution R' r' →
        r' = r := by
      intro R' r' hR' hr'
      obtain ⟨g, hg⟩ := hsingle R hR R' hR'
      have h1 : IsUniqueInvolution R' (g * r * g⁻¹) := hg ▸ hr.conj g
      rw [hr'.eq h1, mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_center_iff.mp hrZ g
    rw [key hRb hUb, key hRa hUa, mul_inv_cancel]
    exact Subgroup.one_mem _
  refine starFrameGenAll_of_kframe hs hker hperf hfund (fun R hR' R' hR'' => ?_) hRa hRb hUa hUb
    (fun h => hnc (hZ hRa hUa h)) (fun h => hnc (hZ hRb hUb h)) hu hu4 huu hau hnc hgen hR h284
  obtain ⟨g, hg⟩ := hsingle R hR' R' hR''
  exact ⟨ψ g, by rw [hg, Q3AM.S4L.map_conjSub]⟩

end Pkg


section Odd

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.ModelFacts.TG3 CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic (conjSub)
open scoped MatrixGroups

theorem modelPkg_odd3 : Q3AM.S4L.ModelPkg (CompData.model .POmegaOdd 3) := by
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_three
  have hM : modelUniv .POmegaOdd 3 3 1 Nat.prime_three =
      ⟨spinGroup (quadOdd 3 (GaloisField 3 1)), oddDatum 3 (GaloisField 3 1)⟩ := rfl
  have hsingle : FundamentalSingleClass .POmegaOdd (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).D :=
    fundamentalSingleClass .POmegaOdd 3 3 1 Nat.prime_three trivial hadm (by decide) (by decide)
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .POmegaOdd) trivial hadm (by decide)
      (by decide) hR
  have hfin : Finite (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).K :=
    finite_modelUniv (t := .POmegaOdd) hp2 Nat.prime_three trivial hadm
  have hconj : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).D,
      ∀ g : (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).K, conjSub g R ∈
        fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).D :=
    fun R hR g => Q3AM.S4L.conjSub_mem_fundamentalSubgroups _ hR g
  show Q3AM.S4L.ModelPkg ⟨(modelUniv .POmegaOdd 3 3 1 Nat.prime_three).K,
    fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 3 1 Nat.prime_three).D⟩
  generalize modelUniv .POmegaOdd 3 3 1 Nat.prime_three = M at hM hsingle hsl2 hfin hconj ⊢
  subst hM
  have hdim : Module.finrank (GaloisField 3 1) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField 3 1) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField 3 1))) :=
    isPerfect_spinGroup_quadOdd h2 le_rfl
  exact Q3AM.S4L.modelPkg_of_spin (quadOdd 3 (GaloisField 3 1)) _
    (nondegenerate_polarBilin_quadOdd 3 _ h2) (by rw [hdim]) this
    (range_spinAction_quadOdd h2 le_rfl) (Q3TWY.centralQuot3_odd le_rfl) hconj hsingle hsl2
    (fun F₁ F₂ h => hproj_odd F₁ F₂ h)

end Odd

section Minus

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted QuadraticMap
open scoped MatrixGroups

theorem modelPkg_minus4 : Q3AM.S4L.ModelPkg (CompData.model .POmegaMinus 4) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨hp, le_rfl, le_rfl⟩
  have hirr := minusCoeffs_irr 3 1
  have hn4 : 4 ≤ 4 := le_rfl
  have hM : modelUniv .POmegaMinus 4 3 1 hp =
      ⟨spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        minusDatum 4 (minusCoeffs_irr 3 1)⟩ := rfl
  have hsingle : ModelFacts.FundamentalSingleClass .POmegaMinus
      (modelUniv .POmegaMinus 4 3 1 hp).D :=
    ModelFacts.fundamentalSingleClass .POmegaMinus 4 3 1 hp trivial hadm (by decide) (by decide)
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 3 1 hp).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaMinus)
      trivial hadm (by decide) (by decide) hR
  have hfin : Finite (modelUniv .POmegaMinus 4 3 1 hp).K :=
    ModelFacts.finite_modelUniv (t := .POmegaMinus) (by norm_num) hp trivial hadm
  show Q3AM.S4L.ModelPkg ⟨(modelUniv .POmegaMinus 4 3 1 hp).K,
    fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 3 1 hp).D⟩
  generalize modelUniv .POmegaMinus 4 3 1 hp = M at hM hsingle hsl2 hfin ⊢
  subst hM
  have : Finite (spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) := hfin
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 3 1) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have hconj : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1)),
      ∀ g : spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        conjSub g R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1)) := by
    rintro R ⟨g₀, γ, hγ, rfl⟩ g
    refine ⟨g * g₀, γ, hγ, ?_⟩
    change Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.map (MulAut.conj g₀).toMonoidHom _) =
      _
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  exact Q3AM.S4L.modelPkg_of_spin _ _
    (nondegenerate_polarBilin_quadMinus_of_finite 4 (GaloisField 3 1) hirr)
    (by rw [hdim]; omega) (isPerfect_spinGroup_quadMinus hn4 hirr)
    (range_spinAction_quadMinus hn4 hirr) (Q3TY.centralQuot3_minus hadm) hconj hsingle hsl2
    (fun F₁ F₂ h => ModelFacts.TG3.hproj_minus hirr hn4 F₁ F₂ h)

end Minus

end CFSG.ClassicalInvolution.Q3.TL4.S289G
