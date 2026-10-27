module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.AltSixCoreSection
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.AltSixCoreBase
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.AltSixCoreStepOne

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core

open Subgroup
open scoped commutatorElement

variable {K : Type*} [Group K] [Finite K]

private def kerCompToKer {G : Type*} [Group G] {ψ : K →* G} (Y : Subgroup K) :
    ↥((ψ.comp Y.subtype).ker) →* ↥ψ.ker where
  toFun x := ⟨(x.1 : ↥Y).1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem kerCompToKer_injective {G : Type*} [Group G] {ψ : K →* G} (Y : Subgroup K) :
    Function.Injective (kerCompToKer (ψ := ψ) Y) := by
  intro a b hab
  exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥ψ.ker => (x : K)) hab))

private theorem coprime_card_ker_comp {G : Type*} [Group G] {ψ : K →* G}
    (hcop : Nat.Coprime (Nat.card ψ.ker) 6) (Y : Subgroup K) :
    Nat.Coprime (Nat.card (ψ.comp Y.subtype).ker) 6 := by
  have hf := kerCompToKer_injective (ψ := ψ) Y
  have hdvd : Nat.card ↥((ψ.comp Y.subtype).ker) ∣ Nat.card ↥ψ.ker := by
    have h1 : Nat.card ↥((ψ.comp Y.subtype).ker) =
        Nat.card ↥(kerCompToKer (ψ := ψ) Y).range :=
      Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
    rw [h1]
    exact Subgroup.card_subgroup_dvd_card _
  exact hcop.coprime_dvd_left hdvd

private theorem isSolvable_ker_comp {G : Type*} [Group G] {ψ : K →* G}
    (hsol : IsSolvable ψ.ker) (Y : Subgroup K) : IsSolvable (ψ.comp Y.subtype).ker := by
  haveI : Group.IsSolvable ↥ψ.ker := hsol
  exact Group.isSolvable_of_isSolvable_injective (kerCompToKer_injective (ψ := ψ) Y)

theorem commutator_mem_of_card_le_pow_four {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (ψ : K →* alternatingGroup (Fin 6)) (hcop : Nat.Coprime (Nat.card ψ.ker) 6)
    (hsol : IsSolvable ψ.ker) {Y A B : Subgroup K} (hY : ⁅Y, Y⁆ = Y) (hYψ : Y.map ψ = ⊤)
    (hBA : B ≤ A) (hYA : Y ≤ normalizer (A : Set K)) (hYB : Y ≤ normalizer (B : Set K))
    (hexp : ∀ x ∈ A, x ^ r ∈ B) (hcomm : ∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ ∈ B)
    (hcard : Nat.card A ≤ r ^ 4 * Nat.card B) :
    ∀ y ∈ Y, ∀ x ∈ A, ⁅x, y⁆ ∈ B := by
  classical
  obtain ⟨V, hVadd, hVmod, hVfin, ρ, hdim, htriv⟩ :=
    exists_linearAction_of_section hBA hYA hYB hexp hcomm hcard
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod r) V := hVmod
  letI : FiniteDimensional (ZMod r) V := hVfin
  let ψY : ↥Y →* alternatingGroup (Fin 6) := ψ.comp Y.subtype
  have hψY : Function.Surjective ψY := by
    intro a
    have ha : a ∈ Y.map ψ := by rw [hYψ]; exact Subgroup.mem_top a
    obtain ⟨y, hy, hyψ⟩ := Subgroup.mem_map.mp ha
    exact ⟨⟨y, hy⟩, hyψ⟩
  have hcopY : Nat.Coprime (Nat.card ψY.ker) 6 := coprime_card_ker_comp hcop Y
  have hsolY : IsSolvable ψY.ker := isSolvable_ker_comp hsol Y
  haveI hperfY : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  haveI hMnorm : (ρ.ker ⊔ ψY.ker).Normal := inferInstance
  haveI hMmapN : ((ρ.ker ⊔ ψY.ker).map ψY).Normal := hMnorm.map ψY hψY
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 6)
    (N := (ρ.ker ⊔ ψY.ker).map ψY) (by simp) with hbot | htop
  · rw [Subgroup.map_eq_bot_iff] at hbot
    exact False.elim <| false_of_finrank_le_four (F := ZMod r) (V := V)
      (by exact_mod_cast ZMod.prime_ne_zero r 2 hr2) (by exact_mod_cast ZMod.prime_ne_zero r 3 hr3)
      hdim ψY hψY hcopY ρ (le_trans le_sup_left hbot)
  · have htop' : ρ.ker ⊔ ψY.ker = ⊤ := by
      have h1 : ρ.ker ⊔ ψY.ker = ((ρ.ker ⊔ ψY.ker).map ψY).comap ψY :=
        (Subgroup.comap_map_eq_self le_sup_right).symm
      rw [h1, htop]
      exact Subgroup.comap_top ψY
    have hsup : ψY.ker ⊔ ρ.ker = ⊤ := by rw [sup_comm]; exact htop'
    have hρtop : ρ.ker = ⊤ := eq_top_of_sup_eq_top_of_isSolvable hsolY hsup
    intro y hy x hx
    have hρy : ρ ⟨y, hy⟩ = 1 := by
      have hmem : (⟨y, hy⟩ : ↥Y) ∈ ρ.ker := by rw [hρtop]; exact Subgroup.mem_top _
      exact MonoidHom.mem_ker.mp hmem
    exact htriv ⟨y, hy⟩ hρy x hx

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core
