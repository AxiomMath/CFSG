module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianStatements
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCFOddLinearTwoSocleCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCFSp6ActionParameters
public import CFSG.LieType.CurtisTits.Conclusion
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.SteinbergCF

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem oddCore_eq_bot_of_even {G : Type} [Group G] [Finite G] (hGs : IsSimpleGroup G)
    {C : Subgroup G} (hC : Even (Nat.card C)) : CFSG.oddCore G = ⊥ := by
  rw [CFSG.oddCore, sSup_eq_bot]
  rintro N ⟨hNn, hNodd⟩
  have := hGs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    rw [h] at hNodd
    have h1 : Nat.card C ∣ Nat.card (⊤ : Subgroup G) := Subgroup.card_dvd_of_le le_top
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hNodd h1)) hC

theorem not_normal_of_isStandardSubgroup {G : Type} [Group G] [Finite G] (hGs : IsSimpleGroup G)
    (hGn : ∃ x y : G, x * y ≠ y * x) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) : ¬ L.Normal :=
  CFSG.Open.standardComponentIsStandard.not_normal hL hGs hGn

theorem standard_binary_symplectic_six_elementary_lagrangian_odd_linear_two_ambient_exclusion
    (hF : Sp6LagrangianFullOddCoreStmt) {G : Type} [Group G] [Finite G] (hGs : IsSimpleGroup G)
    (hGn : ∃ x y : G, x * y ≠ y * x) (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {L : Subgroup G} (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hcore : ∀ t : G, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel (L ⧸ center L) .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (he : IsSymplecticBasis b e)
    (hfull : conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G)) :
    (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype = zpowers z ∧
      z ∈ centralizer (L : Set G) ∧ L ⊔ zpowers z = centralizer ({z} : Set G) ∧
      L ⊓ zpowers z = ⊥ ∧
      (∃! E : Subgroup G, (E : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E ∧ Nat.card E = 512) ∧
      IsElementaryAbelian 2 (sp6E₂ φ he z) ∧ sp6C₂ φ he z ≤ sp6N₂ φ e z ∧
      (∀ m ∈ sp6N₂ φ e z, ∀ c ∈ sp6C₂ φ he z, m * c * m⁻¹ ∈ sp6C₂ φ he z) ∧
      Nat.card (sp6C₂ φ he z) = 4096 ∧
      (IsElementaryAbelian 2 (sp6C₂ φ he z) → IsSimpleGroup (sp6Dstar φ he z) →
        (∃ x y : sp6Dstar φ he z, x * y ≠ y * x) →
        ∀ p f : ℕ, p.Prime → Odd p → 1 ≤ f →
          ¬ CFSG.Blueprint.LieModel (sp6Dstar φ he z) .PSL 2 p f) := by
  classical
  have hG : CFSG.oddCore G = ⊥ := oddCore_eq_bot_of_even hGs hL.2.1
  have hLn : ¬ L.Normal := not_normal_of_isStandardSubgroup hGs hGn hL
  have hmodel' : CFSG.Blueprint.LieModel L .PSp 3 2 1 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel
  have hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥ := hcore z hz
  obtain ⟨hTz, hzC, hsup, hinf, -⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths.{0} hG hL hLn hZ hmodel' T hT hzT hz hH
  obtain ⟨hθ₂inj, hlab, κ₂, lam, hκ, hlam⟩ :=
    exists_sp6_action_parameters hG hL hLn hZ hmodel' T hT hzT hz hH hb hnd hV φ e he hfull
  obtain ⟨-, C₁, E₂, hE₂eq, hC₂eq, -, -, -, -, -, -, -, -, -, -, -, -, hE₂F, hE₂c, hE₂card,
    hE₂uniq, hE₂el, hC₂n, hC₂card, hD₂C, -, -, -, -, -, -, -, ν₂, ε, hν₂, hsq, hε⟩ :=
    hF G hGs hGn hK hG L hL hLn hZ hmodel' T hT z hzT hz hH V b hb hnd hV φ e he hfull κ₂ lam hκ
      hlam
  have hC₂D₂ : sp6C₂ φ he z ≤ sp6D₂ φ e z := inf_le_left
  have hD₂N₂ : sp6D₂ φ e z ≤ sp6N₂ φ e z := Subgroup.map_subtype_le _
  refine ⟨hTz, hzC, hsup, hinf, ⟨E₂, ⟨hE₂F, hE₂c, hE₂card⟩, fun E' hE' => hE₂uniq E' hE'.1
    hE'.2.1 hE'.2.2⟩, hE₂eq ▸ hE₂el, hC₂D₂.trans hD₂N₂, hC₂eq ▸ hC₂n, hC₂eq ▸ hC₂card, ?_⟩
  intro hC₂el hDs hDn p f _ hpodd _
  have hε0 : ε = 0 := by
    by_contra hε1
    have hε1' : ε = 1 := by
      rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) ε with h | h
      · exact absurd h hε1
      · exact h
    let C₀ : ↥(binarySymMatrices 3) :=
      ⟨Matrix.diagonal ![1, 0, 0], by rw [mem_binarySymMatrices, diagonal_transpose]⟩
    obtain ⟨d, hd, hdz⟩ := hlab C₀
    have hd' : d ∈ (zpowers z : Set G) * (sp6D₂ φ e z ⊓ centralizer (E₂ : Set G) : Set G) :=
      hD₂C ▸ hd
    obtain ⟨y, hy, c, hc₀, rfl⟩ := hd'
    have hc : c ∈ sp6D₂ φ e z ⊓ centralizer (E₂ : Set G) := ⟨hc₀.1, hc₀.2⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    have hv1 : (1 : ZMod 2).val = 1 := rfl
    have hcz : c⁻¹ * z * c = tauHom φ he (Multiplicative.ofAdd C₀) * z := by
      have h1 : (z ^ k * c)⁻¹ * z * (z ^ k * c) = c⁻¹ * z * c := by group
      rw [← h1, hdz]
      simp [hv1]
    have hcD : c ∈ sp6D₂ φ e z := hc.1
    have hν₂' := hν₂ c hcD
    simp only at hν₂'
    have hτ : tauHom φ he (Multiplicative.ofAdd (ν₂ c)) =
        tauHom φ he (Multiplicative.ofAdd C₀) := by
      rw [← hν₂', hcz, mul_comm_z hzC (tauHom_mem φ he _), ← mul_assoc, inv_mul_cancel,
        one_mul]
    have hν₂c : ν₂ c = C₀ := by
      have h := @hθ₂inj (ν₂ c, 0) (C₀, 0) (by simpa using hτ)
      exact (Prod.ext_iff.mp h).1
    have hel : IsElementaryAbelian 2 ↥(sp6D₂ φ e z ⊓ centralizer (E₂ : Set G)) := hC₂eq ▸ hC₂el
    have hc2 : c ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian c hc
    have hsqc := hsq c hc
    rw [hc2, hν₂c, hε1'] at hsqc
    have h0 := @hθ₂inj (symThreeSquare 1 (symThreeDiag (C₀ : M₃)), 0) (0, 0)
      (by simpa using hsqc.symm)
    have h00 := congrArg (fun B : ↥(binarySymMatrices 3) => (B : M₃) 0 0) (Prod.ext_iff.mp h0).1
    revert h00
    simp [C₀, coe_symThreeSquare, vecMulVec, symThreeDiag]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, hLayer⟩ := hε hε0
  obtain ⟨-, -, -, -, ⟨ι, -, hιinj, hιrange⟩, -, -, -, -, -, -, hθinj, -, -, -, -, -, -, haBar,
    hJa, -, hCa, -, -, -, -, -, -, -, -, -, -, -, hCD, -⟩ := hLayer
  have hinjθι : Function.Injective ((sp6θ φ he z).comp ι) := by
    intro g h hgh
    have hg : ι g ∈ sp6JL φ he z := hιrange ▸ ⟨g, rfl⟩
    have hh : ι h ∈ sp6JL φ he z := hιrange ▸ ⟨h, rfl⟩
    exact hιinj (hθinj hg hh hgh)
  have hrange : ((sp6θ φ he z).comp ι).range = sp6JLBar φ he z := by
    rw [MonoidHom.range_comp, hιrange]
    rfl
  have eJ : GL (Fin 3) (ZMod 2) ≃* sp6JLBar φ he z :=
    (MonoidHom.ofInjective hinjθι).trans (MulEquiv.subgroupCongr hrange)
  have : (sp6Dstar φ he z).Normal := by
    show (normalClosure (sp6JLBar φ he z : Set (Sp6Y φ he z))).Normal
    infer_instance
  have hJD : sp6JLBar φ he z ≤ sp6Dstar φ he z := fun x hx => subset_normalClosure hx
  exact ComponentInitial.SteinbergCF.not_lieModel_psl_two_of_centralizer_eq_zpowers_sup hDs hDn
    hCD haBar hJD hCa.symm hJa ⟨eJ⟩ hpodd

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.SteinbergCF
