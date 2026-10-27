module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddFam
public import CFSG.LocalAnalysis.ComponentInitial.GroupComponents
public import CFSG.Walter.Ree.Model.Fusion

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC.DS81

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Walter.Ree.Model


theorem smallReeInvCentralizer_hasCompOrSolv (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) (ha : 1 ≤ a) :
    HasCompOrSolv ↥(smallReeInvCentralizer a K) := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨ψ, hψC, -, -, -, -, -, ⟨hsup, -, hcent⟩, e, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a K hK w₀ hw₀
  have hLC : ψ.range ≤ smallReeInvCentralizer a K := by
    rintro _ ⟨x, rfl⟩
    exact hψC x
  have hNn : (ψ.range.subgroupOf (smallReeInvCentralizer a K)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLC, ← hsup]
    exact sup_le (hcent.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hq27 : 27 ≤ Nat.card K := by
    rw [hK]
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  have hPSL : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 K le_rfl
      (Or.inr hK2) (Or.inr hK3)
  let e' : ↥(ψ.range.subgroupOf (smallReeInvCentralizer a K)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    (Subgroup.subgroupOfEquivOfLe hLC).trans e.symm
  haveI : IsSimpleGroup ↥(ψ.range.subgroupOf (smallReeInvCentralizer a K)) :=
    e'.isSimpleGroup
  have hnc : ∃ x y : ↥(ψ.range.subgroupOf (smallReeInvCentralizer a K)), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian
        K hK2 hK3
    exact ⟨e'.symm x, e'.symm y, fun hc => hxy (by simpa using congrArg e' hc)⟩
  exact Or.inr ⟨ψ.range.subgroupOf (smallReeInvCentralizer a K),
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1, Subgroup.Normal.isSubnormal hNn⟩

theorem oddDichotomyFamily_twistedG2 : OddDichotomyFamily .twistedG2 := by
  intro X _ _ n p f hp hp2 hadm hm τ hτ
  have hn0 : n = 0 := hadm.2.2.1
  have hp3 : p = 3 := hadm.2.2.2.1
  subst hn0
  subst hp3
  have hR : ReeTitsModel X .twistedG2 3 f := by
    rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
  obtain ⟨-, -, -, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier X 3 f hR
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := hR
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K ReeTag.G2.prime :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
  set Γ := ReeTag.G2.reeGamma K a' with hΓ
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Γ, t₀ = E τ := ⟨E τ, rfl⟩
  have ht₂ : orderOf (t₀ : ModGL ReeTag.G2.tag K) = 2 := by
    rw [Subgroup.orderOf_coe, ht₀]
    exact (orderOf_injective E.toMonoidHom E.injective τ).trans hτ
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨g, hgΓ, hgt⟩ :=
    (small_Ree_prime_field_involution_fusion a' K hK' w₀ hw₀).2.2.2.2.2 t₀ t₀.2 ht₂
  have hCmap : (Γ ⊓ Subgroup.centralizer {(t₀ : ModGL ReeTag.G2.tag K)}).map
      (MulAut.conj g).toMonoidHom = smallReeInvCentralizer a' K := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective,
      CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hgΓ),
      CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton, MulAut.conj_apply, hgt]
    rfl
  have hfix : (Subgroup.centralizer {t₀}).map Γ.subtype =
      Γ ⊓ Subgroup.centralizer {(t₀ : ModGL ReeTag.G2.tag K)} := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.2, congrArg Subtype.val hc⟩
    · rintro ⟨hzΓ, hz⟩
      exact ⟨⟨z, hzΓ⟩, Subtype.ext hz, rfl⟩
  have hcen : Subgroup.centralizer ({E τ} : Set Γ) = Subgroup.centralizer ({t₀} : Set Γ) := by
    rw [ht₀]
  let Φ1 : Subgroup.centralizer ({τ} : Set X) ≃* Subgroup.centralizer ({t₀} : Set Γ) :=
    (centEquiv E τ).trans (MulEquiv.subgroupCongr hcen)
  let Φ2 : Subgroup.centralizer ({t₀} : Set Γ) ≃*
      ↥(Γ ⊓ Subgroup.centralizer {(t₀ : ModGL ReeTag.G2.tag K)}) :=
    ((Subgroup.centralizer ({t₀} : Set Γ)).equivMapOfInjective Γ.subtype
      Γ.subtype_injective).trans (MulEquiv.subgroupCongr hfix)
  let Φ3 : ↥(Γ ⊓ Subgroup.centralizer {(t₀ : ModGL ReeTag.G2.tag K)}) ≃*
      ↥(smallReeInvCentralizer a' K) :=
    ((Γ ⊓ Subgroup.centralizer {(t₀ : ModGL ReeTag.G2.tag K)}).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hCmap)
  have hC : HasCompOrSolv ↥(smallReeInvCentralizer a' K) :=
    smallReeInvCentralizer_hasCompOrSolv a' K hK' ha
  exact (solvableOrComponent_iff X τ).2
    (HasCompOrSolv.of_mulEquiv (Φ1.trans (Φ2.trans Φ3)).symm hC)

end CFSG.ComponentClassification.CatFC.DS81
