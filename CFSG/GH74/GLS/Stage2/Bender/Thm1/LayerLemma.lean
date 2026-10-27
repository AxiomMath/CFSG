module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Layer

variable {G : Type} [Group G] [Finite G]

theorem Fm_nilpotent (M : Subgroup G) : Group.IsNilpotent ↥(Fm M) :=
  Group.nilpotent_of_mulEquiv (G := ↥(fittingSubgroup ↥M))
    ((fittingSubgroup ↥M).equivMapOfInjective M.subtype M.subtype_injective)

theorem centralizes_Em {M N X : Subgroup G} (hXN : X ≤ N) (hXF : X ≤ Fm M) (hEM : Em N ≤ M) :
    X ≤ centralizer (Em N : Set G) := by
  set E : Subgroup ↥N := layer ↥N with hE
  have hEn : E.Normal := Subgroup.normal_of_characteristic E (h := CFSG.LocalCores.layer_characteristic)
  have hEM' : ∀ e ∈ E, (e : G) ∈ M := fun e he => hEM ⟨e, he, rfl⟩
  set D : Subgroup ↥N := (Fm M).subgroupOf N with hD
  set X' : Subgroup ↥N := X.subgroupOf N with hX'
  have hEnormD : ∀ e ∈ E, ∀ d ∈ D, e * d * e⁻¹ ∈ D := by
    intro e he d hd
    rw [hD, Subgroup.mem_subgroupOf] at hd ⊢
    have := (mem_normalizer_iff.mp (le_normalizer_Fm M (hEM' e he)) (d : G)).mp hd
    simpa using this
  have hcomm : ⁅E, X'⁆ ≤ E ⊓ D := by
    rw [Subgroup.commutator_le]
    intro e he x hx
    have hxD : x ∈ D := by
      rw [hD, Subgroup.mem_subgroupOf]
      exact hXF (Subgroup.mem_subgroupOf.mp hx)
    refine ⟨?_, ?_⟩
    · have h1 : x * e⁻¹ * x⁻¹ ∈ E := hEn.conj_mem e⁻¹ (E.inv_mem he) x
      have : ⁅e, x⁆ = e * (x * e⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact E.mul_mem he h1
    · have : ⁅e, x⁆ = (e * x * e⁻¹) * x⁻¹ := by simp [commutatorElement_def]
      rw [this]
      exact D.mul_mem (hEnormD e he x hxD) (D.inv_mem hxD)
  set R : Subgroup ↥N := E ⊓ D with hR
  have hRsub : R.IsSubnormal := by
    refine Subgroup.IsSubnormal.step R E inf_le_left hEn.isSubnormal ?_
    refine ⟨fun r hr g => ?_⟩
    rw [hR, Subgroup.mem_subgroupOf] at hr ⊢
    obtain ⟨hrE, hrD⟩ := hr
    refine ⟨E.mul_mem (E.mul_mem g.2 hrE) (E.inv_mem g.2), ?_⟩
    have := hEnormD (g : ↥N) g.2 (r : ↥N) hrD
    simpa using this
  have hRs : Group.IsSolvable ↥R := by
    have : Group.IsNilpotent ↥(Fm M) := Fm_nilpotent M
    let φ : ↥R →* ↥(Fm M) := ((N.subtype).comp R.subtype).codRestrict (Fm M)
      (fun x => (x.2.2 : ((x : ↥N) : G) ∈ Fm M))
    have hinj : Function.Injective φ := by
      intro a b hab
      have h1 : ((φ a : ↥(Fm M)) : G) = ((φ b : ↥(Fm M)) : G) := congrArg Subtype.val hab
      have h2 : (((a : ↥R) : ↥N) : G) = (((b : ↥R) : ↥N) : G) := h1
      exact Subtype.ext (Subtype.ext h2)
    exact Group.isSolvable_of_isSolvable_injective hinj
  have hcent : ⁅layer ↥N, R⁆ = ⊥ := (CFSG.LocalCores.component_solvable_centralizer hRs hRsub).2
  have hdbl : ⁅⁅E, X'⁆, E⁆ = ⊥ := by
    refine eq_bot_iff.mpr ?_
    calc ⁅⁅E, X'⁆, E⁆ ≤ ⁅R, E⁆ := Subgroup.commutator_mono hcomm le_rfl
      _ = ⁅E, R⁆ := Subgroup.commutator_comm _ _
      _ = ⊥ := hcent
      _ ≤ ⊥ := le_rfl
  have hfin : ⁅E, X'⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator
    (CFSG.LocalCores.layer_isPerfect (G := ↥N)) hdbl
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨e, he, rfl⟩
  have hxN : x ∈ N := hXN hx
  have h1 : ⁅e, (⟨x, hxN⟩ : ↥N)⁆ ∈ (⊥ : Subgroup ↥N) := hfin ▸
    Subgroup.commutator_mem_commutator he (Subgroup.mem_subgroupOf.mpr hx)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  have := congrArg Subtype.val h1
  simpa using this

end Layer

end CFSG.GH74.GLS.Stage2.Bender.Thm1
