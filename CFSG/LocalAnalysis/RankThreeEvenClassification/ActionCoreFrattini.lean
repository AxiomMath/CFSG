module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.StableActionCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalSylowIntersection
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ConjugateJoin

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem actionPrimeCore_eq_kernel_sup_sylow_inf {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite actor]
    (prime : ℕ) (hprime : prime.Prime) (action : actor →* MulAut acted) (sylow : Sylow prime actor) :
    actionPrimeCore prime action = action.ker ⊔ ((sylow : Subgroup actor) ⊓ actionPrimeCore prime action) := by
  have : Fact prime.Prime := ⟨hprime⟩
  let quotient := QuotientGroup.mk' action.ker
  let image := Sylow.mapSurjective (QuotientGroup.mk'_surjective action.ker) sylow
  have hcoreLe : pCore prime (actor ⧸ action.ker) ≤ (sylow : Subgroup actor).map quotient := by
    have hle := pCore_le_sylow prime image
    rwa [Sylow.coe_mapSurjective] at hle
  apply le_antisymm
  · intro member hmember
    have hquotient : quotient member ∈ pCore prime (actor ⧸ action.ker) := hmember
    obtain ⟨representative, hrepresentative, heq⟩ := hcoreLe hquotient
    have hrepresentativeCore : representative ∈ actionPrimeCore prime action := by
      change quotient representative ∈ pCore prime (actor ⧸ action.ker)
      rwa [heq]
    have hdifference : member * representative⁻¹ ∈ action.ker := by
      have hkernel : member * representative⁻¹ ∈ quotient.ker := by
        apply MonoidHom.mem_ker.mpr
        rw [map_mul, map_inv, heq, mul_inv_cancel]
      rwa [QuotientGroup.ker_mk'] at hkernel
    have hproduct : member = (member * representative⁻¹) * representative := by group
    rw [hproduct]
    exact (action.ker ⊔ ((sylow : Subgroup actor) ⊓ actionPrimeCore prime action)).mul_mem
      ((le_sup_left : action.ker ≤ action.ker ⊔ ((sylow : Subgroup actor) ⊓ actionPrimeCore prime action)) hdifference)
      ((le_sup_right : (sylow : Subgroup actor) ⊓ actionPrimeCore prime action ≤
        action.ker ⊔ ((sylow : Subgroup actor) ⊓ actionPrimeCore prime action))
          ⟨hrepresentative, hrepresentativeCore⟩)
  · exact sup_le (kernel_le_actionPrimeCore prime action) inf_le_right

theorem action_core_frattini_normalizer_eq_top {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite actor]
    (prime : ℕ) (hprime : prime.Prime) (action : actor →* MulAut acted) (sylow : Sylow prime actor) :
    action.ker ⊔ Subgroup.normalizer
      (((sylow : Subgroup actor) ⊓ actionPrimeCore prime action : Subgroup actor) : Set actor) = ⊤ := by
  have : Fact prime.Prime := ⟨hprime⟩
  let core := actionPrimeCore prime action
  have : core.Normal := actionPrimeCore_normal prime action
  let intersectionSylow := sylowNormalIntersection prime hprime sylow core
  have hmap : (intersectionSylow : Subgroup core).map core.subtype = (sylow : Subgroup actor) ⊓ core := by
    rw [sylowNormalIntersection_coe, Subgroup.subgroupOf_map_subtype]
  have hfrattini := intersectionSylow.normalizer_sup_eq_top
  rw [hmap] at hfrattini
  apply top_unique
  rw [← hfrattini]
  apply sup_le le_sup_right
  have hdecomposition : core = action.ker ⊔ ((sylow : Subgroup actor) ⊓ core) :=
    actionPrimeCore_eq_kernel_sup_sylow_inf prime hprime action sylow
  calc
    core = action.ker ⊔ ((sylow : Subgroup actor) ⊓ core) := hdecomposition
    _ ≤ action.ker ⊔ Subgroup.normalizer (((sylow : Subgroup actor) ⊓ core : Subgroup actor) : Set actor) :=
      sup_le le_sup_left (Subgroup.le_normalizer.trans le_sup_right)

theorem conjugateJoin_le_of_kernel_normalizer {G : Type u} [Group G] [Finite G]
    (subgroup normalizer kernel target : Subgroup G) [kernel.Normal]
    (hfactor : kernel ⊔ normalizer = ⊤)
    (hkernel : kernel ≤ Subgroup.centralizer (subgroup : Set G))
    (hsubgroup : subgroup ≤ target) (htarget : normalizer ≤ Subgroup.normalizer (target : Set G)) :
    conjugateJoin subgroup ≤ target := by
  apply iSup_le
  intro conjugator
  have hnormalizes : normalizer ≤ Subgroup.normalizer (kernel : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨left, hleft, right, hright, heq⟩ := normalized_sup_factorization kernel normalizer hnormalizes
    conjugator (by rw [hfactor]; exact Subgroup.mem_top _)
  rintro element ⟨representative, hrepresentative, rfl⟩
  rw [← heq]
  have hconjugate : right * representative * right⁻¹ ∈ target :=
    Subgroup.le_normalizer_iff.mp htarget right hright representative (hsubgroup hrepresentative)
  have hleftTarget : left * (right * representative * right⁻¹) * left⁻¹ = right * representative * right⁻¹ := by
    have hinverse : right⁻¹ * left * right ∈ kernel :=
      (inferInstance : kernel.Normal).conj_mem' left hleft right
    have hcommute := Subgroup.mem_centralizer_iff.mp (hkernel hinverse) representative hrepresentative
    have hmapped := congrArg (fun value : G => right * value * right⁻¹) hcommute
    have hresult : (right * representative * right⁻¹) * left = left * (right * representative * right⁻¹) := by
      convert hmapped using 1 <;> group
    rw [← hresult]
    group
  change (left * right) * representative * (left * right)⁻¹ ∈ target
  have helement : (left * right) * representative * (left * right)⁻¹ =
      left * (right * representative * right⁻¹) * left⁻¹ := by group
  rw [helement, hleftTarget]
  exact hconjugate

end CFSG.RankThreeEvenClassification.Helpers
