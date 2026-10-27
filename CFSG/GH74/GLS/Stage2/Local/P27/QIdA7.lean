module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltInv
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltCent
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.QId

open Equiv Equiv.Perm CFSG.GH74.GLS.IVK.GHInv
open scoped commutatorElement

theorem card_dvd_sixty_of_perfect_le_symOn {Ω : Type*} [DecidableEq Ω] {F : Finset Ω}
    (hF : F.card = 5) {P : Subgroup (Perm Ω)} (hP : Group.IsPerfect P) (hPF : P ≤ symOn F) :
    Nat.card P ∣ 60 := by
  let φ : P →* Perm {x // x ∈ F} :=
    MonoidHom.mk' (fun k => (k : Perm Ω).subtypePerm (symOn_mem_iff (hPF k.2)))
      (fun x y => Equiv.ext fun u => Subtype.ext rfl)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ F
    · have := congrArg (fun f : Perm {x // x ∈ F} => (f ⟨x, hx⟩ : Ω)) hk
      simpa [φ] using this
    · exact hPF k.2 x hx
  have hsign : ∀ k : P, sign (φ k) = 1 := fun k =>
    MonoidHom.mem_ker.1
      (Abelianization.commutator_subset_ker (sign.comp φ) Group.IsPerfect.mem_commutator)
  let ψ : P →* alternatingGroup {x // x ∈ F} :=
    φ.codRestrict _ (fun k => Equiv.Perm.mem_alternatingGroup.2 (hsign k))
  have hψ : Function.Injective ψ := fun a b h => hφ (congrArg Subtype.val h)
  have hnt : Nontrivial {x // x ∈ F} :=
    Fintype.one_lt_card_iff_nontrivial.1 (by rw [Fintype.card_coe, hF]; norm_num)
  have hA : Nat.card (alternatingGroup {x // x ∈ F}) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := {x // x ∈ F}),
      Fintype.card_coe, hF]
    decide
  exact hA ▸ Subgroup.card_dvd_of_injective ψ hψ

theorem a7_fixed_perfect {K : Type} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 7)) (α : MulAut K) (hα : α * α = 1) (hne : α ≠ 1)
    (Ω : Subgroup K) (hΩ : ⁅Ω, Ω⁆ = Ω) (hfix : ∀ g ∈ Ω, α g = g) :
    Ω = ⊥ ∨ Nat.card ↥Ω ∣ 60 := by
  classical
  let α' : MulAut (alternatingGroup (Fin 7)) := (e.symm.trans α).trans e
  have hα' : ∀ y, α' y = e (α (e.symm y)) := fun y => rfl
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).2 α'
  have key : ∀ y : alternatingGroup (Fin 7),
      ((α' y : alternatingGroup (Fin 7)) : Perm (Fin 7)) = σ * y * σ⁻¹ := by
    intro y
    rw [← hσ, MulAut.conjNormal_apply]
  have hα'2 : ∀ y, α' (α' y) = y := by
    intro y
    rw [hα', hα', MulEquiv.symm_apply_apply]
    have : α (α (e.symm y)) = e.symm y := by
      have := congrArg (fun f : MulAut K => f (e.symm y)) hα
      simpa using this
    rw [this, MulEquiv.apply_symm_apply]
  have hσ2 : σ * σ = 1 := by
    refine eq_one_of_commute_alternating (α := Fin 7) (by simp) (fun g hg => ?_)
    have h1 := key ⟨g, hg⟩
    have h2 := key (α' ⟨g, hg⟩)
    rw [hα'2, h1] at h2
    have h2' : g = σ * (σ * g * σ⁻¹) * σ⁻¹ := h2
    calc σ * σ * g = σ * (σ * g * σ⁻¹) * σ⁻¹ * (σ * σ) := by group
      _ = g * (σ * σ) := by rw [← h2']
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hne
    ext x
    have h2 : α' (e x) = e x := Subtype.ext (by rw [key, h1]; simp)
    rw [hα', MulEquiv.symm_apply_apply] at h2
    exact e.injective h2
  obtain ⟨hsupp, -⟩ := involution_cycle_data hσ2
  have hc7 : 2 * σ.cycleType.card ≤ 7 := by
    have := Finset.card_le_univ σ.support
    simp only [Fintype.card_fin] at this
    omega
  have hc1 : 1 ≤ σ.cycleType.card := by
    by_contra h
    have : σ.support.card = 0 := by omega
    exact hσ1 (Equiv.Perm.card_support_eq_zero.1 this)
  let ι : K →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  let P : Subgroup (Perm (Fin 7)) := Ω.map ι
  have hP : Group.IsPerfect P := by
    rw [Subgroup.isPerfect_iff]
    show ⁅Ω.map ι, Ω.map ι⁆ = Ω.map ι
    rw [← Subgroup.map_commutator, hΩ]
  have hPc : ∀ x ∈ P, x * σ = σ * x := by
    rintro x ⟨g, hg, rfl⟩
    have h2 : α' (e g) = e g := by rw [hα', MulEquiv.symm_apply_apply, hfix g hg]
    have h3 := key (e g)
    rw [h2] at h3
    show ((e g : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ =
      σ * ((e g : alternatingGroup (Fin 7)) : Perm (Fin 7))
    calc ((e g : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ
        = σ * ((e g : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ⁻¹ * σ := by rw [← h3]
      _ = σ * ((e g : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by group
  have hfixsupp := perfect_fixes_support hσ2 (by omega) hP hPc
  let F : Finset (Fin 7) := σ.supportᶜ
  have hPF : P ≤ symOn F := by
    intro x hx a ha
    apply hfixsupp x hx a
    rw [← Equiv.Perm.mem_support]
    by_contra h
    exact ha (Finset.mem_compl.2 h)
  have hFcard : F.card = 7 - 2 * σ.cycleType.card := by
    rw [Finset.card_compl, hsupp]
    simp
  have hcardΩ : Nat.card Ω = Nat.card P := Nat.card_congr (Ω.equivMapOfInjective ι hι).toEquiv
  rcases Nat.lt_or_ge σ.cycleType.card 2 with hlt | hge
  · right
    rw [hcardΩ]
    exact card_dvd_sixty_of_perfect_le_symOn (by omega) hP hPF
  · left
    have hPbot : P = ⊥ := eq_bot_of_perfect_le_symOn (by omega) hP hPF
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have h1 : ι g ∈ P := ⟨g, hg, rfl⟩
    rw [hPbot, Subgroup.mem_bot] at h1
    exact hι (h1.trans (map_one ι).symm)

end CFSG.GH74.GLS.Stage2.Local.P27.QId
