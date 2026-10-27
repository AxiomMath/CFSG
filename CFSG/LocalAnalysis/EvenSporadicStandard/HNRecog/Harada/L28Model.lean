module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L28Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L28Act
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] {A : Subgroup X} {w : X}
  {ψ : ↥(normalizer (A : Set X)) →* A5WrTwo}

theorem L28_linear_model (h : L28Hyp A w ψ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Finite V)
      (e : ↥A ≃* Multiplicative V)
      (σ : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* (V ≃ₗ[ZMod 2] V)),
      Module.finrank (ZMod 2) V = 8 ∧ Function.Injective σ ∧
      ∀ (n : ↥(normalizer (A : Set X))) (g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)),
        ψ n = A5WrTwo.baseEmb g → ∀ a : ↥A,
          ((e.symm (Multiplicative.ofAdd (σ g (Multiplicative.toAdd (e a)))) : ↥A) : X) =
            (n : X) * (a : X) * (n : X)⁻¹ := by
  obtain ⟨V, instACG, instMod, instFin, e, act, hfin, hact⟩ :=
    L28_exists_action h.elemAb h.card
  letI : AddCommGroup V := instACG
  letI : Module (ZMod 2) V := instMod
  letI : Finite V := instFin
  have hker_le : ψ.ker ≤ act.ker := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    have hnA : (n : X) ∈ A := by
      have : n ∈ A.subgroupOf (normalizer (A : Set X)) := by
        rw [← h.ker]
        exact hn
      exact Subgroup.mem_subgroupOf.mp this
    rw [MonoidHom.mem_ker]
    apply LinearEquiv.ext
    intro v
    have hfix : ∀ a : ↥A,
        act n (Multiplicative.toAdd (e a)) = Multiplicative.toAdd (e a) := by
      intro a
      have hcommA : (n : X) * (a : X) * (n : X)⁻¹ = (a : X) := by
        have hcomm : (⟨(n : X), hnA⟩ : ↥A) * a = a * ⟨(n : X), hnA⟩ := by
          haveI : IsMulCommutative ↥A := h.elemAb.1
          exact mul_comm' _ _
        have hc : (n : X) * (a : X) = (a : X) * (n : X) := by
          simpa using congrArg (fun z : ↥A => (z : X)) hcomm
        rw [hc]
        group
      have hsymm :
          e.symm (Multiplicative.ofAdd (act n (Multiplicative.toAdd (e a)))) = a := by
        apply Subtype.ext
        rw [hact n a, hcommA]
      have h2 : Multiplicative.ofAdd (act n (Multiplicative.toAdd (e a))) = e a := by
        have hc := congrArg e hsymm
        simpa using hc
      have h3 := congrArg Multiplicative.toAdd h2
      simpa using h3
    let a : ↥A := e.symm (Multiplicative.ofAdd v)
    have hv : Multiplicative.toAdd (e a) = v := by
      simp [a]
    rw [← hv]
    simpa using hfix a
  have hker_ge : act.ker ≤ ψ.ker := by
    intro n hn
    have hn1 : act n = 1 := MonoidHom.mem_ker.mp hn
    have hcommA : ∀ a ∈ A, (n : X) * a = a * (n : X) := by
      intro a ha
      have hsymm :
          e.symm (Multiplicative.ofAdd (act n (Multiplicative.toAdd (e ⟨a, ha⟩)))) =
            ⟨a, ha⟩ := by
        have h1 : act n (Multiplicative.toAdd (e ⟨a, ha⟩)) =
            Multiplicative.toAdd (e ⟨a, ha⟩) := by
          rw [hn1]
          rfl
        rw [h1]
        simp
      have h := hact n ⟨a, ha⟩
      rw [hsymm] at h
      have h2 : a = (n : X) * a * (n : X)⁻¹ := by
        simpa using h
      conv_rhs => rw [h2]
      group
    have hnA : (n : X) ∈ A := h.faithful (n : X) n.2 hcommA
    rw [h.ker]
    exact Subgroup.mem_subgroupOf.mpr hnA
  let ρ : A5WrTwo →* (V ≃ₗ[ZMod 2] V) :=
    MonoidHom.liftOfRightInverse ψ (Function.surjInv h.surj)
      (Function.rightInverse_surjInv h.surj) ⟨act, hker_le⟩
  have hρ : ∀ n : ↥(normalizer (A : Set X)), ρ (ψ n) = act n := by
    intro n
    dsimp only [ρ]
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ n
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨n, rfl⟩ := h.surj x
    rw [hρ n] at hx
    exact MonoidHom.mem_ker.mp (hker_ge (MonoidHom.mem_ker.mpr hx))
  let σ : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* (V ≃ₗ[ZMod 2] V) :=
    ρ.comp A5WrTwo.baseEmb
  have hσinj : Function.Injective σ := by
    intro g₁ g₂ hg
    exact A5WrTwo.baseEmb_injective (hρinj hg)
  have hcompat : ∀ (n : ↥(normalizer (A : Set X)))
      (g : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)),
      ψ n = A5WrTwo.baseEmb g → ∀ a : ↥A,
        ((e.symm (Multiplicative.ofAdd (σ g (Multiplicative.toAdd (e a)))) : ↥A) : X) =
          (n : X) * (a : X) * (n : X)⁻¹ := by
    intro n g hψ a
    have hσ : σ g = act n := by
      dsimp only [σ]
      rw [MonoidHom.comp_apply, ← hψ, hρ n]
    rw [hσ, hact n a]
  exact ⟨V, instACG, instMod, instFin, e, σ, hfin, hσinj, hcompat⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada
