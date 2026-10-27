module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCESp6ActionParameters
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCESp6EvenUnitaryCore
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.Blueprint.EvenStandardExact
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
  (he : IsSymplecticBasis b e) (z : G)

theorem sp6Dstar_not_lieModel_PSU {V₁ : Subgroup G}
    (hconc : Sp6LagrangianLayerConclusion φ he z V₁) (hsimple : Sp6LayerSimple φ he z)
    (n f : ℕ) : ¬ CFSG.Blueprint.LieModel (sp6Dstar φ he z) .PSU n 2 f := by
  obtain ⟨-, -, -, -, ⟨ι, -, hιinj, hιrange⟩, -, -, -, -, -, -, hθinj, -, -, -, -, -, -,
    haBar2, hJC, -, hCaBar, -, -, -, -, -, -, hJstd, -, -, -, -, hCD, -⟩ := hconc
  obtain ⟨hDs, hDnab, hJD, -⟩ := hsimple
  have hψinj : Function.Injective ((sp6θ φ he z).comp ι) := by
    intro g g' hgg
    apply hιinj
    refine hθinj ?_ ?_ hgg
    · rw [← hιrange]
      exact ⟨g, rfl⟩
    · rw [← hιrange]
      exact ⟨g', rfl⟩
  have hψrange : ((sp6θ φ he z).comp ι).range = sp6JLBar φ he z := by
    rw [MonoidHom.range_comp, hιrange]
    rfl
  have hJGL : Nonempty (sp6JLBar φ he z ≃* GL (Fin 3) (ZMod 2)) :=
    ⟨((MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange)).symm⟩
  have haN : sp6aBar φ he z ∈ normalizer (sp6JLBar φ he z : Set (Sp6Y φ he z)) :=
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun j hj =>
      mem_centralizer_singleton_iff.1 (hJC hj))
  have hJn : ((sp6JLBar φ he z).subgroupOf (centralizer {sp6aBar φ he z})).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hJC, ← hCaBar]
    exact sup_le (zpowers_le.2 haN) le_normalizer
  have hJcomp : CFSG.Assembly.IsComponentOf (sp6JLBar φ he z)
      (centralizer {sp6aBar φ he z}) :=
    ⟨hJC, CFSG.Assembly.IsSubnormal.step hJC hJn (CFSG.Assembly.IsSubnormal.refl _),
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hJstd.1⟩
  have : (sp6Dstar φ he z).Normal := by
    unfold sp6Dstar
    infer_instance
  rintro (⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩)
  · exact SteinbergCE.not_statedClassicalModel_PSU_of_GL_three_two_component hDs hDnab hCD haBar2
      hJD.le hJcomp hJGL n f hc
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

omit [Finite G] in
theorem eq_zero_of_symThreeSquare_ones {ε : ZMod 2} (h : symThreeSquare ε (fun _ => 1) = 0) :
    ε = 0 := by
  have h1 := congrArg (fun B : ↥(binarySymMatrices 3) => (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0)
    h
  simpa [coe_symThreeSquare, vecMulVec_apply] using h1

theorem sp6_lagrangian_branch (hF : Sp6LagrangianFullOddCoreStmt) (hGs : IsSimpleGroup G)
    (hGnab : ∃ x y : G, x * y ≠ y * x) (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hodd : ∀ t : G, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel (L ⧸ center L) .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) [FiniteDimensional (ZMod 2) V] (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6)
    (hfull : conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G)) :
    (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype = zpowers z ∧
    z ∈ centralizer (L : Set G) ∧ L ⊔ zpowers z = centralizer ({z} : Set G) ∧
    L ⊓ zpowers z = ⊥ ∧
    (sp6E₂ φ he z : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative (sp6E₂ φ he z) ∧
    Nat.card (sp6E₂ φ he z) = 512 ∧
    (∀ E' : Subgroup G, (E' : Set G) ⊆ sp6F₂ φ he z → IsMulCommutative E' → Nat.card E' = 512 →
      E' = sp6E₂ φ he z) ∧
    IsElementaryAbelian 2 (sp6E₂ φ he z) ∧
    (∀ m ∈ sp6N₂ φ e z, ∀ c ∈ sp6C₂ φ he z, m * c * m⁻¹ ∈ sp6C₂ φ he z) ∧
    Nat.card (sp6C₂ φ he z) = 4096 ∧
    (IsElementaryAbelian 2 (sp6C₂ φ he z) →
      ∃ V₁ : Subgroup G, Sp6LagrangianLayerConclusion φ he z V₁) := by
  classical
  have hZG : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hGnab
      have hy : y ∈ center G := by
        rw [h]
        exact mem_top y
      exact hxy ((mem_center_iff.mp hy) x)
  have heven : Even (Nat.card (centralizer (L : Set G))) := hL.2.1
  have hLtop : L ≠ ⊤ := by
    intro htop
    rw [htop, coe_top, centralizer_univ, hZG, card_bot] at heven
    exact Nat.not_even_one heven
  have hLbot : L ≠ ⊥ := by
    rintro rfl
    have hs : IsSimpleGroup (↥(⊥ : Subgroup G) ⧸ center ↥(⊥ : Subgroup G)) := hL.1.2
    exact not_nontrivial _ hs.toNontrivial
  have hLn : ¬ L.Normal := fun hN => by
    have := hN
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal L).elim hLbot hLtop
  have hG : CFSG.oddCore G = ⊥ := by
    refine sSup_eq_bot.2 fun N hN => ?_
    have := hN.1
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_right fun htop => ?_
    have hGodd : Odd (Nat.card G) := by
      rw [← Subgroup.card_top (G := G), ← htop]
      exact hN.2
    have hdvd := Subgroup.card_subgroup_dvd_card (centralizer (L : Set G))
    exact Nat.not_even_iff_odd.2 hGodd
      ((even_iff_two_dvd.1 heven).trans hdvd |> even_iff_two_dvd.2)
  have hmodelL : CFSG.Blueprint.LieModel L .PSp 3 2 1 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel
  have hH := hodd z hz
  obtain ⟨hTz, hzC, hsup, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodelL T hT hzT hz hH
  obtain ⟨κ₂, lam, hκ₂, hlam⟩ := exists_sp6_action_parameters hG hL hLn hZ hmodelL T hT hzT hz
    hH hb hnd hV φ e he hfull
  obtain ⟨-, C₁, E₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE₂F, hE₂ab, hE₂card, hE₂uniq,
    hE₂el, hC₂N, hC₂card, hD₂C₂, -, -, -, -, -, -, -, ν₂, ε, hν₂, hsq, hbranch⟩ :=
    hF G hGs hGnab hKP hG L hL hLn hZ hmodelL T hT z hzT hz hH V b hb hnd hV φ e he hfull κ₂
      lam hκ₂ hlam
  have hspec : (sp6E₂ φ he z : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative (sp6E₂ φ he z) ∧
      Nat.card (sp6E₂ φ he z) = 512 :=
    Classical.epsilon_spec (p := fun E : Subgroup G =>
      (E : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E ∧ Nat.card E = 512) ⟨E₂, hE₂F, hE₂ab, hE₂card⟩
  have hE₂eq : E₂ = sp6E₂ φ he z := (hE₂uniq _ hspec.1 hspec.2.1 hspec.2.2).symm
  subst hE₂eq
  refine ⟨hTz, hzC, hsup, hinf, hE₂F, hE₂ab, hE₂card, hE₂uniq, hE₂el, hC₂N, hC₂card,
    fun hC₂el => ?_⟩
  have hε : ε = 0 := by
    obtain ⟨-, hW⟩ := hrest hb hnd hV φ
    obtain ⟨-, -, -, -, -, -, -, -, -, hker, -, -, -, ⟨σ, -, -, -, hσ⟩, -⟩ :=
      hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
    obtain ⟨-, D₂', -, ν₂', hD₂, -, -, -, -, -, -, -, hν₂z, -, hν₂surj, -⟩ :=
      degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
    set I₃ : ↥(binarySymMatrices 3) := ⟨1, transpose_one⟩ with hI₃
    obtain ⟨d, hd, hdI⟩ := hν₂surj I₃
    have hd₂ : d ∈ sp6D₂ φ e z := by
      rw [hD₂] at hd
      exact hd
    have hdz : d⁻¹ * z * d = z * tauHom φ he (Multiplicative.ofAdd I₃) := by
      rw [hν₂z d hd, hdI, radHom_apply, zPow_one, mul_comm_z hzC (tauHom_mem φ he _)]
    have hdmem : d ∈ (zpowers z : Set G) * (sp6C₂ φ he z : Set G) := by
      have h1 : d ∈ (sp6D₂ φ e z : Set G) := hd₂
      rw [hD₂C₂] at h1
      exact h1
    obtain ⟨y, hy, c, hc, rfl⟩ := hdmem
    have hyz : y * z = z * y := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      exact (Commute.zpow_left (Commute.refl z) k).eq
    have hcz : c⁻¹ * z * c = z * tauHom φ he (Multiplicative.ofAdd I₃) := by
      rw [← hdz]
      have hy' : y⁻¹ * z * y = z := by
        rw [mul_assoc, ← hyz, ← mul_assoc, inv_mul_cancel, one_mul]
      calc c⁻¹ * z * c = c⁻¹ * (y⁻¹ * z * y) * c := by rw [hy']
        _ = (y * c)⁻¹ * z * (y * c) := by group
    have hcD : c ∈ sp6D₂ φ e z := (Subgroup.mem_inf.1 hc).1
    have hνc : ν₂ c = I₃ := by
      have h1 := hν₂ c hcD
      rw [hcz, ← mul_assoc, inv_mul_cancel, one_mul] at h1
      exact Multiplicative.ofAdd.injective (tauHom_injective φ he h1.symm)
    have := hC₂el
    have hc2 : c ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) c hc
    have h1 := hsq c hc
    rw [hc2, hνc] at h1
    have hdiag : symThreeDiag ((I₃ : ↥(binarySymMatrices 3)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        fun _ => 1 := funext fun k => Matrix.one_apply_eq k
    rw [hdiag] at h1
    have h2 : tauHom φ he (Multiplicative.ofAdd (symThreeSquare ε fun _ => 1)) = 1 := by
      have h3 : (1 : G) = tauHom φ he (Multiplicative.ofAdd (symThreeSquare ε fun _ => 1)) *
          z ^ (0 : ZMod 2).val := h1
      rw [ZMod.val_zero, pow_zero, mul_one] at h3
      exact h3.symm
    rw [← map_one (tauHom φ he)] at h2
    exact eq_zero_of_symThreeSquare_ones
      (Multiplicative.ofAdd.injective (tauHom_injective φ he h2))
  subst hε
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hlayer⟩ := hbranch rfl
  exact ⟨_, hlayer⟩

omit [Finite G] in
theorem sp6LayerSimple_of_isSimpleGroup {V₁ : Subgroup G}
    (hconc : Sp6LagrangianLayerConclusion φ he z V₁) (hDs : IsSimpleGroup (sp6Dstar φ he z)) :
    Sp6LayerSimple φ he z := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hxor, -⟩ := hconc
  rcases hxor with ⟨hs, -⟩ | ⟨htwo, -⟩
  · exact hs
  exfalso
  obtain ⟨D₁, D₂, -, -, -, hD₁s, -, hD₂s, -, hsup, hinf, hcomm, -⟩ := htwo
  have hD₁le : D₁ ≤ sp6Dstar φ he z := hsup ▸ le_sup_left
  have hD₂le : D₂ ≤ sp6Dstar φ he z := hsup ▸ le_sup_right
  have hD₂N : D₂ ≤ normalizer (D₁ : Set (Sp6Y φ he z)) := fun y hy =>
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx =>
      (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm hx) y hy).symm)
  have hn : (D₁.subgroupOf (sp6Dstar φ he z)).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hD₁le, ← hsup]
    exact sup_le le_normalizer hD₂N
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D₁.subgroupOf (sp6Dstar φ he z)) with h | h
  · have h1 : D₁ = ⊥ := by
      rw [subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hD₁le] at h
      exact h
    exact (nontrivial_iff_ne_bot D₁).1 hD₁s.toNontrivial h1
  · have h1 : D₂ ≤ D₁ := (subgroupOf_eq_top.1 h).trans' hD₂le
    have h2 : D₂ = ⊥ := by
      rw [← hinf, inf_of_le_right h1]
    exact (nontrivial_iff_ne_bot D₂).1 hD₂s.toNontrivial h2

theorem standard_binary_symplectic_six_elementary_lagrangian_even_unitary_ambient_exclusion
    (hF : Sp6LagrangianFullOddCoreStmt) (hGs : IsSimpleGroup G)
    (hGnab : ∃ x y : G, x * y ≠ y * x) (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hodd : ∀ t : G, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (_hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (_htype : CFSG.Blueprint.Recognition.Exact.EvenStandardType (L ⧸ center L))
    (_hexc : ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException (L ⧸ center L))
    (_hres : CFSG.Blueprint.Recognition.Exact.EvenStandardResidual L)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel (L ⧸ center L) .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) [FiniteDimensional (ZMod 2) V] (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6)
    (hfull : conjClass (sp6N₂ φ e z) z = z • (sp6A₂ φ e : Set G)) :
    (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype = zpowers z ∧
    z ∈ centralizer (L : Set G) ∧ L ⊔ zpowers z = centralizer ({z} : Set G) ∧
    L ⊓ zpowers z = ⊥ ∧
    (∃! E₂ : Subgroup G, (E₂ : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E₂ ∧
      Nat.card E₂ = 512) ∧
    IsElementaryAbelian 2 (sp6E₂ φ he z) ∧
    (∀ m ∈ sp6N₂ φ e z, ∀ c ∈ sp6C₂ φ he z, m * c * m⁻¹ ∈ sp6C₂ φ he z) ∧
    Nat.card (sp6C₂ φ he z) = 4096 ∧
    (IsElementaryAbelian 2 (sp6C₂ φ he z) → IsSimpleGroup (sp6Dstar φ he z) →
      (∃ x y : sp6Dstar φ he z, x * y ≠ y * x) →
      ∀ n f : ℕ, 3 ≤ n → 1 ≤ f → ¬ CFSG.Blueprint.LieModel (sp6Dstar φ he z) .PSU n 2 f) := by
  obtain ⟨hTz, hzC, hsup, hinf, hE₂F, hE₂ab, hE₂card, hE₂uniq, hE₂el, hC₂N, hC₂card, hlayer⟩ :=
    sp6_lagrangian_branch φ he z hF hGs hGnab hKP hL hodd hZ hmodel T hT hzT hz hb hnd hV hfull
  refine ⟨hTz, hzC, hsup, hinf, ⟨sp6E₂ φ he z, ⟨hE₂F, hE₂ab, hE₂card⟩,
    fun E' ⟨h1, h2, h3⟩ => hE₂uniq E' h1 h2 h3⟩, hE₂el, hC₂N, hC₂card,
    fun hC₂el hDs _ n f _ _ => ?_⟩
  obtain ⟨V₁, hconc⟩ := hlayer hC₂el
  exact sp6Dstar_not_lieModel_PSU φ he z hconc (sp6LayerSimple_of_isSimpleGroup φ he z hconc hDs)
    n f

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
