module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovL4U4O8Core
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovL4U4Lin
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthFamily
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Neg

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Cov

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
open CFSG.ComponentClassification.OddClassSelector

theorem lieModel_psl2_of_card {X : Type} [Group X] {F : Type} [Field F] [Finite F] {p n : ℕ}
    (hp : p.Prime) (h4 : 4 ≤ p ^ n) (hF : Nat.card F = p ^ n)
    (e : X ≃* GorensteinWalter.PSL2 F) : LieModel X .PSL 2 p n := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h4
  have hadm : StatedLieAdmissible .PSL 2 p n := by
    refine ⟨hp, Nat.one_le_iff_ne_zero.mpr hn, le_rfl, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
  exact .inl ⟨by decide, hadm, F, inferInstance, inferInstance, hF,
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 _)⟩⟩

variable {K : Type} [Field K] [Finite K]

theorem orth_socle_minus8 {A : Type} [Group A] {W : Subgroup A} [W.Normal]
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    (hstd : CFSG.IsStandardSubgroup L) (hs : SmallSource L) {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ e) {d : ℕ} (hd : d = 8)
    {Q : QuadraticForm K (Fin d → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hnoU : ¬ ∃ U : Submodule K (Fin d → K), finrank K U = 4 ∧ ∀ x ∈ U, Q x = 0)
    (hrep : SemilinearRepresentation Q) (θ : W ≃* matrixProjectiveDerived Q) :
    ∃ (E' : Type) (_ : Field E') (_ : Finite E'), Nat.card E' = Nat.card K ^ 4 ∧
      Nonempty (↥L ⧸ center ↥L ≃* GorensteinWalter.PSL2 E') := by
  have : IsSimpleGroup (matrixProjectiveDerived Q) := θ.symm.isSimpleGroup
  have hnab : ∃ x y : matrixProjectiveDerived Q, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hWnab
    refine ⟨θ x, θ y, fun h => hxy (θ.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have hZ := OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨ρ, X, hinj, hinn, hX, hLX, ⟨eLX⟩⟩ := fixed_component_of_socle hCW θ hZ hLCW
  have hW := noTightWitness_of_isStandardSubgroup hinj hinn (OddClassSelector.conj_injective hZ)
    hstd hLX
  have hαα : ρ a * ρ a = 1 := by
    rw [← map_mul, ← pow_two, ← ha, pow_orderOf_eq_one, map_one]
  have hα1 : ρ a ≠ 1 := by
    intro h
    have h1 : orderOf (ρ a) = orderOf a := orderOf_injective ρ hinj a
    rw [h, orderOf_one, ha] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨β, g, hβg, hσ2, ⟨c, hc⟩, hlin, -⟩ := hrep.2 (ρ a) hαα hα1
  have hX₁ := isComponentOf_map_symm β hX
  rw [hβg] at hX₁
  let eL := eLX.trans (X.equivMapOfInjective β.symm.toMonoidHom β.symm.injective)
  obtain ⟨E', _, _, hE', ⟨eE⟩⟩ := orth_core_minus8 hℓ hℓ2 he hK hd hQ hnoU g hσ2 c hc hlin hX₁
    (smallSource_of_mulEquiv eL hs) (hW.map β.symm)
  exact ⟨E', inferInstance, inferInstance, hE',
    ⟨(QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans eE⟩⟩

theorem orth_minus8_family {A : Type} [Group A] {W : Subgroup A} [W.Normal]
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hstd : CFSG.IsStandardSubgroup L) (hs : SmallSource L) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hW : StatedClassicalModel W .POmegaMinus 4 p f) :
    LieModel (↥L ⧸ center ↥L) .PSL 2 p (4 * f) := by
  classical
  have hLCW := LocalAnalysis.ComponentInitial.isComponentOf_of_le hL (le_inf hLW hL.1)
    inf_le_right
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id hW
  obtain ⟨-, hnd, -⟩ := coordinate_model_witness_minus hW K hK b c hirr e
  obtain ⟨E', _, _, hE', ⟨eE⟩⟩ := orth_socle_minus8 hWs hWnab hCW ha hLCW hstd hs hp hp2 hf hK
    (d := 2 * 4) (by norm_num) hnd
    (fun ⟨U, hU, hUQ⟩ => Catalog7Std.Om8.not_isPlusType_coordinateQuadMinus 4 (by norm_num) hirr
      ⟨U, by rw [hU, Module.finrank_fin_fun], hUQ⟩)
    (odd_orthogonal_involution_semilinear_representation .POmegaMinus (Or.inr (Or.inr rfl)) hW
      (by norm_num) K hK b c hirr e)
    (coordinateMinusWitnessEquiv K (by norm_num) b c e)
  have hE : Nat.card E' = p ^ (4 * f) := by
    rw [hE', hK, ← pow_mul, mul_comm]
  have h4 : 4 ≤ p ^ (4 * f) := by
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    calc 4 ≤ 3 ^ 4 := by norm_num
      _ ≤ p ^ 4 := Nat.pow_le_pow_left h3 4
      _ ≤ p ^ (4 * f) := Nat.pow_le_pow_right hp.pos (by omega)
  exact lieModel_psl2_of_card hp h4 hE eE

theorem nonabelian_of_inn_component {N : Type} [Group N] {G : Subgroup (MulAut N)}
    {J C : Subgroup G} (hJN : J ≤ (MulAut.conj : N →* MulAut N).range.subgroupOf G)
    (hL : CFSG.Assembly.IsComponentOf J C) : ∃ x y : N, x * y ≠ y * x := by
  by_contra hc
  push Not at hc
  obtain ⟨-, -, -, hsimp⟩ := hL
  have h1 : ∀ x : J, x = 1 := fun x => by
    obtain ⟨n, hn⟩ := mem_subgroupOf.mp (hJN x.2)
    apply Subtype.ext
    apply Subtype.ext
    rw [← hn]
    refine MulEquiv.ext fun y => ?_
    change n * y * n⁻¹ = y
    rw [hc n y, mul_inv_cancel_right]
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥J ⧸ center ↥J)
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  rw [h1 a', h1 b'] at hab
  exact hab rfl

theorem smallSource_of_small {A : Type} [Group A] {J : Subgroup A}
    (hodd : Odd (Nat.card (center J)))
    (hsmall : Nonempty (J ⧸ center J ≃* alternatingGroup (Fin 7)) ∨
      ∃ s t : ℕ, s.Prime ∧ s ≠ 2 ∧ 1 ≤ t ∧ 5 ≤ s ^ t ∧
        LieModel (J ⧸ center J) .PSL 2 s t) : SmallSource J := by
  rcases hsmall with h7 | ⟨s, t, hs, hs2, ht, hst, hm⟩
  · exact Or.inr (Or.inl ⟨h7, hodd⟩)
  · exact Or.inl ⟨s, t, hs, hs2, ht, hst, hm, hodd⟩

theorem cf23L4U4O8Comp_minus8 {N : Type} [Group N] [Finite N] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hN : LieModel N .POmegaMinus 4 p e)
    (G : Subgroup (MulAut N)) (hInn : (MulAut.conj : N →* MulAut N).range ≤ G) (α : G)
    (J : Subgroup G) (hα : orderOf α = 2)
    (hJN : J ≤ (MulAut.conj : N →* MulAut N).range.subgroupOf G)
    (hJc : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G))))
    (hstd : IsStandardSubgroup J) (hodd : Odd (Nat.card (center J)))
    (hsmall : Nonempty (J ⧸ center J ≃* alternatingGroup (Fin 7)) ∨
      ∃ s t : ℕ, s.Prime ∧ s ≠ 2 ∧ 1 ≤ t ∧ 5 ≤ s ^ t ∧
        LieModel (J ⧸ center J) .PSL 2 s t) :
    LieModel (J ⧸ center J) .PSL 2 p (2 * (2 * e)) := by
  have hM := statedClassicalModel_of_lieModel hN (by simp [chevalleyExceptionalTags])
    (by simp [reeTitsTags]) (by decide)
  have : IsSimpleGroup N :=
    (ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus N 4 p e hM).2
  have hL : CFSG.Assembly.IsComponentOf J (centralizer ({α} : Set G)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJc).2 hJ
  have hZ := OutcomeLocal.center_eq_bot_of_isSimpleGroup (nonabelian_of_inn_component hJN hL)
  obtain ⟨hWs, hWnab⟩ := innIn_simple_nonabelian G hZ hInn
  have hCW := centralizer_innIn G hZ hInn
  obtain ⟨hadm, K, _, _, hK, b, c, hirr, ⟨eN⟩⟩ := id hM
  have hW : StatedClassicalModel (innIn G) .POmegaMinus 4 p e :=
    ⟨hadm, K, inferInstance, inferInstance, hK, b, c, hirr, ⟨(innInEquiv G hZ hInn).trans eN⟩⟩
  have h := orth_minus8_family hWs hWnab hCW hα hJN hL hstd (smallSource_of_small hodd hsmall)
    hp hp2 he hW
  rwa [show 2 * (2 * e) = 4 * e by ring]

end CFSG.ComponentClassification.GSThmB.Cov
