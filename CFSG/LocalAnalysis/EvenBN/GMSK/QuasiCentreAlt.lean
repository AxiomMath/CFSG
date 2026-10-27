module

public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreDatum
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatAltBender
import CFSG.Quasithin.SteinbergCBAlternatingAut
import CFSG.LocalAnalysis.ComponentInitial.AlternatingLocalComponents

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Equiv Subgroup CFSG.Blueprint

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification in
theorem qc_center_eq_bot_of_alt {m : ℕ} (hm : 5 ≤ m) (hm6 : m ≠ 6) {D : Type*} [Group D]
    (η : D ≃* alternatingGroup (Fin m)) (α : MulAut D) (hα : orderOf α = 2)
    (S : Subgroup D) (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSq : CFSG.IsQuasisimple S) : Subgroup.center S = ⊥ := by
  have hm' : m = 5 ∨ 7 ≤ m := by omega
  have hmemC : ∀ d, d ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ↔ α d = d := fun d => Iff.rfl
  let β : MulAut (alternatingGroup (Fin m)) := η.symm.trans (α.trans η)
  have hβ : ∀ g, β g = η (α (η.symm g)) := fun g => rfl
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation hm' β
  have hσ' : ∀ g : alternatingGroup (Fin m), (η (α (η.symm g)) : Perm (Fin m)) = σ * g * σ⁻¹ :=
    fun g => hσ g
  have hinj := Quasithin.SteinbergCB.conjPerm_injective (n := m) (by omega)
  have hconj : ∀ τ : Perm (Fin m),
      (∀ g : alternatingGroup (Fin m), (η (α (η.symm g)) : Perm (Fin m)) = τ * g * τ⁻¹) →
        Quasithin.SteinbergCB.conjPerm m τ = β := fun τ hτ =>
    MulEquiv.ext fun g => Subtype.ext (by rw [Quasithin.SteinbergCB.conjPerm_apply, hβ, hτ])
  have hα2 : ∀ d, α (α d) = d := by
    have h : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    intro d
    have := congrArg (fun γ : MulAut D => γ d) h
    simpa [sq] using this
  have hσσ : σ * σ = 1 := by
    apply hinj
    rw [map_mul, hconj σ hσ', map_one]
    refine MulEquiv.ext fun g => ?_
    rw [MulAut.mul_apply, hβ, hβ, MulEquiv.symm_apply_apply, hα2, MulEquiv.apply_symm_apply,
      MulAut.one_apply]
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hβ1 : β = 1 := by rw [← hconj σ hσ', h1, map_one]
    have hα1 : α ≠ 1 := fun h => by
      rw [h, orderOf_one] at hα
      omega
    apply hα1
    refine MulEquiv.ext fun d => ?_
    have := congrArg (fun γ : MulAut (alternatingGroup (Fin m)) => γ (η d)) hβ1
    simp only [hβ, MulEquiv.symm_apply_apply, MulAut.one_apply] at this
    exact η.injective this
  have hσ2 : orderOf σ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq, hσσ]) hσ1
  let ι : D →* Perm (Fin m) :=
    (alternatingGroup (Fin m)).subtype.comp (η : D →* alternatingGroup (Fin m))
  have hι : Function.Injective ι := (alternatingGroup (Fin m)).subtype_injective.comp η.injective
  have hιA : ∀ d, ι d ∈ alternatingGroup (Fin m) := fun d => (η d).2
  have hfix : ∀ d, d ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ↔ σ * ι d = ι d * σ := by
    intro d
    rw [hmemC]
    have h := hσ' (η d)
    rw [MulEquiv.symm_apply_apply] at h
    constructor
    · intro hd
      rw [hd] at h
      exact AltBender.mul_comm_of_conj_eq h.symm
    · intro hd
      apply η.injective
      apply Subtype.ext
      rw [h]
      change σ * ι d * σ⁻¹ = ι d
      rw [hd, mul_inv_cancel_right]
  set S' := S.map ι with hS'def
  set M := alternatingGroup (Fin m) ⊓ centralizer ({σ} : Set (Perm (Fin m))) with hMdef
  have hS'M : S' ≤ M := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hιA s, mem_centralizer_singleton_iff.2 ((hfix s).1 (hSα hs)).symm⟩
  have hS'n : (S'.subgroupOf M).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨s, hs, hsx⟩ := hx
    have hgA : (g : Perm (Fin m)) ∈ alternatingGroup (Fin m) := (mem_inf.1 g.2).1
    have hgC : (g : Perm (Fin m)) ∈ centralizer ({σ} : Set (Perm (Fin m))) := (mem_inf.1 g.2).2
    have hcg : ι (η.symm ⟨g, hgA⟩) = g := by
      change ((η (η.symm ⟨g, hgA⟩) : alternatingGroup (Fin m)) : Perm (Fin m)) = g
      rw [MulEquiv.apply_symm_apply]
    have hcC : η.symm ⟨g, hgA⟩ ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) :=
      (hfix _).2 (by rw [hcg]; exact (mem_centralizer_singleton_iff.1 hgC).symm)
    have hmem := hSn.conj_mem ⟨s, hSα hs⟩ (mem_subgroupOf.2 hs) ⟨_, hcC⟩
    rw [mem_subgroupOf] at hmem
    refine ⟨_, hmem, ?_⟩
    change ι (η.symm ⟨g, hgA⟩ * s * (η.symm ⟨g, hgA⟩)⁻¹) =
      (g : Perm (Fin m)) * x * (g : Perm (Fin m))⁻¹
    rw [map_mul, map_mul, map_inv, hcg, hsx]
  have hMN : (M.subgroupOf (centralizer ({σ} : Set (Perm (Fin m)))) ).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨hxA, hxC⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨?_, ?_⟩
    · exact (inferInstance : (alternatingGroup (Fin m)).Normal).conj_mem _ hxA _
    · exact mul_mem (mul_mem g.2 hxC) (inv_mem g.2)
  have hS'q : CFSG.Assembly.IsQuasisimple S' := by
    rw [AssemblyBPredicates.isQuasisimple_iff_native]
    exact (isQuasisimple_congr (S.equivMapOfInjective ι hι)).1 hSq
  have hcomp : CFSG.Assembly.IsComponentOf S'
      (⊤ ⊓ normalizer ((zpowers σ : Subgroup (Perm (Fin m))) : Set (Perm (Fin m)))) := by
    rw [top_inf_eq, ← centralizer_singleton_eq_normalizer_zpowers hσ2]
    exact ⟨hS'M.trans inf_le_right, CFSG.Assembly.IsSubnormal.step hS'M hS'n
      (CFSG.Assembly.IsSubnormal.step inf_le_right hMN (CFSG.Assembly.IsSubnormal.refl _)),
      hS'q⟩
  obtain ⟨hF5, hS'eq⟩ := ordinary_permutation_local_component_fixed_support (T := ⊤) le_top
    Nat.prime_two le_top (isPGroup_zpowers_of_orderOf_eq_two hσ2) hcomp
  classical
  let eSA : S ≃* alternatingGroup (MulAction.fixedPoints (zpowers σ) (Fin m)) :=
    ((S.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hS'eq)).trans
      ((alternatingGroup (MulAction.fixedPoints (zpowers σ) (Fin m))).equivMapOfInjective
        Equiv.Perm.ofSubtype Equiv.Perm.ofSubtype_injective).symm
  have hcentA : Subgroup.center
      (alternatingGroup (MulAction.fixedPoints (zpowers σ) (Fin m))) = ⊥ :=
    alternatingGroup.center_eq_bot (le_trans (by norm_num) hF5)
  exact center_eq_bot_of_mulEquiv_aux eSA.symm hcentA

theorem qFixedRootSelector_alternating :
    QFixedRootSelector fun D _ => ∃ m : ℕ, 5 ≤ m ∧ Nonempty (D ≃* alternatingGroup (Fin m)) := by
  intro D _ _ _ ⟨m, hm, ⟨η⟩⟩ n α J d
  by_cases hm6 : m = 6
  · subst hm6
    exfalso
    have h6 : 2 ^ 6 ∣ 2 ^ (3 * n) := pow_dvd_pow 2 (by have := d.two_le; omega)
    exact AltBender.not_two_pow_six_dvd_card_of_alt_six η J (h6.trans d.two_pow_dvd_card)
  · exact qc_center_eq_bot_of_alt hm hm6 η α d.orderOf_eq J d.le_fixed d.normal
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).mp
        d.quasisimple)

end CFSG.LocalAnalysis.EvenBN.GMSK
