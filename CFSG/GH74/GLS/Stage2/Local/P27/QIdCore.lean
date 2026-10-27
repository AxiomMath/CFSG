module

public import CFSG.GH74.GLS.Stage2.Local.P27.QIdL2
public import CFSG.GH74.GLS.Stage2.Local.P27.QIdA7
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.QId

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement

section Quasisimple

theorem isQuasisimple_psl2' {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    IsQuasisimple (PSL2 F) := by
  have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := exists_ne (1 : PSL2 F)
  have hxc : x ∈ Subgroup.center (PSL2 F) := Subgroup.mem_center_iff.mpr fun g => h g x
  rw [psl2_center_eq_bot F, Subgroup.mem_bot] at hxc
  exact hx hxc

theorem isQuasisimple_L2 {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    IsQuasisimple (L2 F) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (L2.equivPSL F).symm (isQuasisimple_psl2' h4)

theorem isQuasisimple_alt7 : IsQuasisimple (alternatingGroup (Fin 7)) := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  by_contra h
  push Not at h
  let : CommGroup (alternatingGroup (Fin 7)) :=
    { (inferInstance : Group (alternatingGroup (Fin 7))) with mul_comm := fun a b => h a b }
  have hp := IsSimpleGroup.prime_card (α := alternatingGroup (Fin 7))
  have hc : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  rw [hc] at hp
  exact absurd hp (by norm_num)

end Quasisimple

section Aux

variable {K : Type} [Group K]

theorem eq_bot_of_perfect_of_solvable {H : Subgroup K} (hperf : ⁅H, H⁆ = H)
    (hsolv : Group.IsSolvable ↥H) : H = ⊥ := by
  have hP : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hperf
  have hall : ∀ m : ℕ, derivedSeries ↥H m = ⊤ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [derivedSeries_succ, ih]
      exact hP.commutator_eq_top
  obtain ⟨n, hn⟩ := hsolv.solvable
  rw [hall n] at hn
  rw [eq_bot_iff]
  intro g hg
  have h1 : (⟨g, hg⟩ : ↥H) ∈ (⊤ : Subgroup ↥H) := Subgroup.mem_top _
  rw [hn, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)

end Aux

variable {K : Type} [Group K] [Finite K]

theorem qcore
    (hK : (∃ (F : Type) (_ : Field F) (_ : Finite F), L2Field F ∧ Nonempty (K ≃* L2 F)) ∨
      Nonempty (K ≃* alternatingGroup (Fin 7)))
    (α : MulAut K) (hα : α * α = 1)
    (I' : Subgroup K) (hperf : ⁅I', I'⁆ = I') (hne : I' ≠ ⊥) (hfix : ∀ g ∈ I', α g = g)
    (LH : ∀ Ω : Subgroup K, Ω ≤ fixedSubgroup K α → (Ω.subgroupOf (fixedSubgroup K α)).Normal →
      IsQuasisimple ↥Ω → Ω ≤ I') :
    (α = 1 ∧ I' = ⊤) ∨
    (α ≠ 1 ∧ ∃ q₀ : ℕ, Odd q₀ ∧ 3 < q₀ ∧ IsL2 K (fun r => r = q₀ ^ 2) ∧
      IsL2 ↥I' (fun r => r = q₀)) ∨
    (α ≠ 1 ∧ Nonempty (K ≃* alternatingGroup (Fin 7)) ∧ Nat.card ↥I' ∣ 60) := by
  classical
  have hI'C : I' ≤ fixedSubgroup K α := fun g hg => hfix g hg
  by_cases hα1 : α = 1
  ·
    left
    refine ⟨hα1, ?_⟩
    have hqK : IsQuasisimple K := by
      rcases hK with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩
      · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_L2 (by
          have := hF.2
          omega))
      · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm isQuasisimple_alt7
    have hC : fixedSubgroup K α = ⊤ := by
      ext g
      simp [hα1, mem_fixedSubgroup_iff']
    have hqtop : IsQuasisimple ↥(⊤ : Subgroup K) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hqK
    have hnorm : ((⊤ : Subgroup K).subgroupOf (fixedSubgroup K α)).Normal := by
      rw [Subgroup.top_subgroupOf]
      infer_instance
    exact eq_top_iff.2 (LH ⊤ (by rw [hC]) hnorm hqtop)
  · right
    rcases hK with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩
    · left
      refine ⟨hα1, ?_⟩
      rcases l2_fixed_dichotomy hF e α hα hα1 with hsolv | ⟨F₀, _, _, hcard, hodd, h3, ⟨ψ⟩⟩
      · exfalso
        have : Group.IsSolvable ↥I' :=
          Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hI'C)
            (Subgroup.inclusion_injective hI'C)
        exact hne (eq_bot_of_perfect_of_solvable hperf this)
      · set C := fixedSubgroup K α with hCdef
        have hΩC : ⁅C, C⁆ ≤ C := by
          rw [commutator_eq_map_commutator]
          exact Subgroup.map_subtype_le _
        have hΩsub : ⁅C, C⁆.subgroupOf C = commutator ↥C := by
          rw [commutator_eq_map_commutator]
          exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
        have hΩnormal : (⁅C, C⁆.subgroupOf C).Normal := by
          rw [hΩsub]
          infer_instance
        have hq0 : IsQuasisimple (L2 F₀) := isQuasisimple_L2 (by omega)
        have hΩq : IsQuasisimple ↥⁅C, C⁆ := CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ.symm hq0
        have h1 : ⁅C, C⁆ ≤ I' := LH _ hΩC hΩnormal hΩq
        have h2 : I' ≤ ⁅C, C⁆ := by
          calc I' = ⁅I', I'⁆ := hperf.symm
            _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hI'C hI'C
        have hI'eq : I' = ⁅C, C⁆ := le_antisymm h2 h1
        refine ⟨Nat.card F₀, hodd, h3, ⟨F, inferInstance, inferInstance, hcard.symm, ⟨e⟩⟩,
          ⟨F₀, inferInstance, inferInstance, rfl, ⟨(MulEquiv.subgroupCongr hI'eq).trans ψ⟩⟩⟩
    · right
      refine ⟨hα1, ⟨e⟩, ?_⟩
      rcases a7_fixed_perfect e α hα hα1 I' hperf hfix with h | h
      · exact absurd h hne
      · exact h

end CFSG.GH74.GLS.Stage2.Local.P27.QId
