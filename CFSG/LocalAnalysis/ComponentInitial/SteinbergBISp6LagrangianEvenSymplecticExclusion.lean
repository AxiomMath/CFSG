module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianStatements
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBISp6EvenSymplecticCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBISp6ActionParameters
public import CFSG.Blueprint.EvenStandardExact
public import Certificates.Certificate113
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.Blueprint.LieModelAPI

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBI

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank
open BinarySymplecticSix BinarySymplecticSix.Degree64 BinarySymplecticSix.FusionOrbits
  BinarySymplecticSix.RadicalLabels
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem oddCore_eq_bot_of_isStandardSubgroup {G : Type} [Group G] [Finite G]
    (hGs : IsSimpleGroup G) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) : CFSG.oddCore G = ⊥ := by
  refine le_antisymm (sSup_le ?_) bot_le
  rintro N ⟨hN, hodd⟩
  rcases hGs.eq_bot_or_eq_top_of_normal N with h | h
  · exact h.le
  · exfalso
    rw [h, card_top] at hodd
    have heven : Even (Nat.card (centralizer (L : Set G))) := hL.2.1
    exact Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hodd (card_subgroup_dvd_card _)) heven

theorem not_normal_of_isStandardSubgroup {G : Type} [Group G] [Finite G]
    (hGs : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) : ¬ L.Normal :=
  CFSG.Open.standardComponentIsStandard.not_normal hL hGs hnab

theorem lieModel_PSp_of_center_eq_bot {X : Type} [Group X] (hZ : center X = ⊥) {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel (X ⧸ center X) .PSp n p f) :
    CFSG.Blueprint.LieModel X .PSp n p f :=
  CFSG.Blueprint.LieModel.of_quotient_center hZ h

theorem eps_eq_zero_of_sq_eq_one {G : Type} [Group G] {L : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V} (φ : L ≃* bilinIsometryGroup b)
    {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) {z : G} {c : G}
    {ε : ZMod 2} {B : ↥(binarySymMatrices 3)} (hB : symThreeDiag (B : M₃) = ![1, 0, 0])
    (hsq : c ^ 2 = tauHom φ he (Multiplicative.ofAdd (symThreeSquare ε (symThreeDiag (B : M₃))))
      * z ^ (0 : ZMod 2).val) (hc : c ^ 2 = 1) : ε = 0 := by
  rw [hc, ZMod.val_zero, pow_zero, mul_one, ← map_one (tauHom φ he), ← ofAdd_zero] at hsq
  have h := Multiplicative.ofAdd.injective (tauHom_injective φ he hsq.symm)
  have h00 := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  rw [hB, coe_symThreeSquare] at h00
  simpa [vecMulVec] using h00

theorem standard_binary_symplectic_six_elementary_lagrangian_even_symplectic_ambient_exclusion
    (hF : Sp6LagrangianFullOddCoreStmt)
    {G : Type} [Group G] [Finite G] (hGs : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hinv : ∀ t : G, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (_htype : CFSG.Blueprint.Recognition.Exact.EvenStandardType (L ⧸ center L))
    (_hexc : ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException (L ⧸ center L))
    (_hres : CFSG.Blueprint.Recognition.Exact.EvenStandardResidual L)
    (hZ : center L = ⊥) (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSp 3 2 1)
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
    (sp6E₂ φ he z : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative (sp6E₂ φ he z) ∧
    Nat.card (sp6E₂ φ he z) = 512 ∧
    (∀ E' : Subgroup G, (E' : Set G) ⊆ sp6F₂ φ he z → IsMulCommutative E' →
      Nat.card E' = 512 → E' = sp6E₂ φ he z) ∧
    IsElementaryAbelian 2 (sp6E₂ φ he z) ∧
    sp6C₂ φ he z ≤ sp6N₂ φ e z ∧
    (∀ m ∈ sp6N₂ φ e z, ∀ c ∈ sp6C₂ φ he z, m * c * m⁻¹ ∈ sp6C₂ φ he z) ∧
    Nat.card (sp6C₂ φ he z) = 4096 ∧
    (IsElementaryAbelian 2 (sp6C₂ φ he z) → IsSimpleGroup (sp6Dstar φ he z) →
      (∃ x y : sp6Dstar φ he z, x * y ≠ y * x) →
      ∀ r e' : ℕ, 2 ≤ r → 1 ≤ e' → ¬ CFSG.Blueprint.LieModel (sp6Dstar φ he z) .PSp r 2 e') := by
  classical
  have hG : CFSG.oddCore G = ⊥ := oddCore_eq_bot_of_isStandardSubgroup hGs hL
  have hLn : ¬ L.Normal := not_normal_of_isStandardSubgroup hGs hnab hL
  have hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1 := lieModel_PSp_of_center_eq_bot hZ hQ
  have hH := hinv z hz
  obtain ⟨hTz, hzC, hsup, hinf, -⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths.{0} hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨κ₂, lam, hκ₂, hlam⟩ :=
    exists_action_parameters hG hL hLn hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull
  obtain ⟨-, C₁, E₂, hE₂eq, hC₂eq, -, -, -, -, -, -, -, -, -, -, -, -, hE₂F, hE₂c, hE₂card,
    hE₂uniq, hE₂el, hC₂n, hC₂card, -, -, -, -, -, -, -, -, ν₂, ε, hν₂, hsq, hε⟩ :=
    hF G hGs hnab hK hG L hL hLn hZ hmodel T hT z hzT hz hH V b hb hnd hV φ e he hfull κ₂ lam
      hκ₂ hlam
  subst hE₂eq
  obtain ⟨-, C₁', E₂', hcomp⟩ :=
    standard_binary_symplectic_six_degree64_lagrangian_subgroup_completion hG hL hLn hZ hmodel T
      hT hzT hz hH hb hnd hV φ e he hfull κ₂ lam hκ₂ hlam
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE₂'F, hE₂'c, hE₂'card, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, ν₂', ε', hν₂', -, -, -, -, hdiag', -⟩ := hcomp
  have hE₂' : E₂' = sp6E₂ φ he z := hE₂uniq E₂' hE₂'F hE₂'c hE₂'card
  subst hE₂'
  refine ⟨hTz, hzC, hsup, hinf, hE₂F, hE₂c, hE₂card, hE₂uniq, hE₂el,
    hC₂eq ▸ inf_le_left.trans (map_subtype_le _), hC₂eq ▸ hC₂n, hC₂eq ▸ hC₂card, ?_⟩
  intro hC₂el hDs hDnab
  have hε0 : ε = 0 := by
    obtain ⟨c, hcC, hcw⟩ := hdiag' ![1, 0, 0]
    have hcC' : c ∈ sp6C₂ φ he z := hC₂eq ▸ hcC
    have hcD : c ∈ sp6D₂ φ e z := (mem_inf.1 hcC).1
    have hνc : ν₂ c = ν₂' c := by
      have h1 := (hν₂ c hcD).symm.trans (hν₂' c hcD)
      exact Multiplicative.ofAdd.injective (tauHom_injective φ he h1)
    have hc2 : c ^ 2 = 1 := by
      have : IsElementaryAbelian 2 (sp6C₂ φ he z) := hC₂el
      exact elemPow_eq_one_of_isElementaryAbelian c hcC'
    exact eps_eq_zero_of_sq_eq_one φ he (B := ν₂ c) (by rw [hνc]; exact hcw) (hsq c hcC) hc2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hlayer⟩ := hε hε0
  obtain ⟨-, -, -, -, ⟨ι, -, hιinj, hιrange⟩, -, -, -, -, -, -, hθinj, -, -, -, -, -, -, ha2, hJa,
    -, hC, -, -, -, -, -, -, -, -, -, -, -, hcentD, -⟩ := hlayer
  set ψ : GL (Fin 3) (ZMod 2) →* Sp6Y φ he z := (sp6θ φ he z).comp ι with hψ
  have hιmem : ∀ g, ι g ∈ sp6JL φ he z := fun g => hιrange ▸ MonoidHom.mem_range.2 ⟨g, rfl⟩
  have hψinj : Function.Injective ψ := by
    intro g g' h
    apply hιinj
    exact hθinj (hιmem g) (hιmem g') h
  have hψrange : ψ.range = sp6JLBar φ he z := by
    rw [hψ, MonoidHom.range_comp, hιrange]
    rfl
  have eJ : sp6JLBar φ he z ≃* GL (Fin 3) (ZMod 2) :=
    ((MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange)).symm
  have : (sp6Dstar φ he z).Normal := normalClosure_normal
  exact not_lieModel_PSp_of_GL_three_two_centralizer hDs hDnab hcentD ha2
    (fun x hx => subset_normalClosure hx) hJa hC ⟨eJ⟩

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBI
