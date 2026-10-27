module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveRhoDefect

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.Fischer CFSG.LieType.Steinberg.CentralExt.SLClosed
open CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SL
open CFSG.LieType.Steinberg.RankTwo
open scoped commutatorElement

namespace RhoExt

variable {E : Type*} [Group E] (X : RhoExt E)

theorem rootLift_hcomm : ∀ i j k l : Fin 4, i ≠ j → k ≠ l → j ≠ k → l ≠ i → ∀ s t,
    X.rootLift i j s * X.rootLift k l t = X.rootLift k l t * X.rootLift i j s := by
  intro i j k l hij hkl hjk hli s t
  rcases eq_or_ne k i with rfl | hki
  · rcases eq_or_ne l j with rfl | hlj
    · rw [← X.rootLift_add hij, ← X.rootLift_add hij, add_comm]
    · exact X.rootLift_commute_row hij hkl hlj.symm s t
  · rcases eq_or_ne l j with rfl | hlj
    · exact X.rootLift_commute_col hij hkl hki.symm s t
    · exact X.rootLift_commute_disj hij hkl hki hjk.symm hli hlj s t

theorem exists_section : ∃ σ : SpecialLinearGroup (Fin 4) F4 →* E,
    (∀ g, X.π (σ g) = g) ∧ ∀ g, X.τ (σ g) = σ (veeFrob g) := by
  have hm : 2 ≤ 3 := by norm_num
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (rootDatum 3 F4).isFiniteType
    (Dv := (rootDatum 3 F4).divisible) rfl
  have hx : PresentationB (Φ := Φ (m := 3) (F := F4)) (x 3 F4) := presentationB hm
  have hadd : ∀ i j : Fin 4, i ≠ j → ∀ s t,
      X.rootLift i j (s + t) = X.rootLift i j s * X.rootLift i j t :=
    fun i j h s t => X.rootLift_add h s t
  have hchain : ∀ i j l : Fin 4, i ≠ j → j ≠ l → i ≠ l → ∀ s t,
      ⁅X.rootLift i j s, X.rootLift j l t⁆ = X.rootLift i l (1 * s * t) :=
    fun i j l hij hjl hil s t => by rw [one_mul]; exact X.rootLift_chain hij hjl hil s t
  obtain ⟨σ, hσ, -⟩ := existsUnique_hom_of_presentationB hx O (commutatorFormula O)
    (⟨fun _ hγ c d => hadd _ _ (pairOf_spec (m := 3) hγ).1 c d,
      commutatorFormula_yL X.rootLift hadd X.rootLift_hcomm hchain O⟩ :
      ChevRels O (commC (m := 3)) (yL X.rootLift))
  have hgen := closure_range_eq_top_of_presentationB hx O
  refine ⟨σ, fun g => ?_, fun g => ?_⟩
  · have hid : X.π.comp σ = MonoidHom.id _ := by
      refine MonoidHom.eq_of_eqOn_dense hgen ?_
      intro g hg
      obtain ⟨γ, hγ, c, rfl⟩ : ∃ γ, γ ∈ (Φ (m := 3) (F := F4)).roots ∧ ∃ c, x 3 F4 γ c = g := by
        simpa using hg
      rw [MonoidHom.comp_apply, hσ γ hγ c, MonoidHom.id_apply]
      exact (X.π_rootLift (pairOf_spec (m := 3) hγ).1 c).trans (x_eq_tv γ c).symm
    exact DFunLike.congr_fun hid g
  · have hτ : X.τ.comp σ = σ.comp veeFrob := by
      refine MonoidHom.eq_of_eqOn_dense hgen ?_
      intro g hg
      obtain ⟨γ, hγ, c, rfl⟩ : ∃ γ, γ ∈ (Φ (m := 3) (F := F4)).roots ∧ ∃ c, x 3 F4 γ c = g := by
        simpa using hg
      have hpq := (pairOf_spec (m := 3) hγ).1
      have hv : veeFrob (x 3 F4 γ c) = x 3 F4 γ (c * c) := by
        rw [x_eq_tv γ c, x_eq_tv γ (c * c)]
        exact veeFrob_tv hpq c
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hσ γ hγ c, hv, hσ γ hγ (c * c)]
      exact X.τ_rootLift hpq c
    exact DFunLike.congr_fun hτ g

theorem exists_complement : ∃ C : Subgroup E,
    C ⊓ X.π.ker = ⊥ ∧ C ⊔ X.π.ker = ⊤ ∧ ∀ c ∈ C, X.τ c ∈ C := by
  obtain ⟨σ, hσ, hτ⟩ := X.exists_section
  refine ⟨σ.range, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro y ⟨⟨g, rfl⟩, hy⟩
    have hy' : X.π (σ g) = 1 := hy
    rw [hσ] at hy'
    rw [Subgroup.mem_bot, hy', map_one]
  · rw [eq_top_iff]
    intro y _
    have h1 : σ (X.π y) ∈ σ.range := ⟨_, rfl⟩
    have h2 : (σ (X.π y))⁻¹ * y ∈ X.π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
    have h3 : y = σ (X.π y) * ((σ (X.π y))⁻¹ * y) := by group
    rw [h3]
    exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  · rintro c ⟨g, rfl⟩
    exact ⟨veeFrob g, (hτ g).symm⟩

end RhoExt

end CFSG.SeitzReduction.LinearPilot
