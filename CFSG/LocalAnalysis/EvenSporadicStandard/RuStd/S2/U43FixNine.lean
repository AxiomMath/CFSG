module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Tables

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup
open CFSG.LieType.Multipliers.U43 (card_X₀)

private noncomputable abbrev Inn : Subgroup (MulAut U43) :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner U43

private theorem conj_mem_inn (x : U43) : MulAut.conj x ∈ Inn := ⟨x, rfl⟩

private theorem conj_conj (σ : MulAut U43) (x : U43) :
    σ * MulAut.conj x * σ⁻¹ = MulAut.conj (σ x) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

private theorem centralizer_inner_eq_bot : centralizer (Inn : Set (MulAut U43)) = ⊥ := by
  rw [eq_bot_iff]
  intro γ hγ
  rw [mem_bot]
  ext x
  have h := mem_centralizer_iff.mp hγ (MulAut.conj x) (conj_mem_inn x)
  have h2 : γ * MulAut.conj x * γ⁻¹ = MulAut.conj x := by rw [← h]; group
  rw [conj_conj] at h2
  exact conj_injective_u43 h2

private theorem card_inner_inf_centralizer (β : MulAut U43) :
    Nat.card ↥(Inn ⊓ centralizer ({β} : Set (MulAut U43))) =
      Nat.card {x : U43 // β x = x} := by
  have key : ∀ x : U43, MulAut.conj x ∈ centralizer ({β} : Set (MulAut U43)) ↔ β x = x := by
    intro x
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply conj_injective_u43
      rw [← conj_conj, ← h]; group
    · intro h
      have : β * MulAut.conj x * β⁻¹ = MulAut.conj x := by rw [conj_conj, h]
      calc MulAut.conj x * β = β * MulAut.conj x * β⁻¹ * β := by rw [this]
        _ = β * MulAut.conj x := by group
  symm
  refine Nat.card_congr
    { toFun := fun x => ⟨MulAut.conj x.1, mem_inf.mpr ⟨conj_mem_inn x.1, (key x.1).mpr x.2⟩⟩
      invFun := fun y => ⟨(mem_inf.mp y.2).1.choose, by
        have hy := (mem_inf.mp y.2).1.choose_spec
        exact (key _).mp (by rw [hy]; exact (mem_inf.mp y.2).2)⟩
      left_inv := fun x => Subtype.ext (conj_injective_u43
        (mem_inf.mp (⟨MulAut.conj x.1, mem_inf.mpr ⟨conj_mem_inn x.1,
          (key x.1).mpr x.2⟩⟩ : ↥(Inn ⊓ centralizer ({β} : Set (MulAut U43)))).2).1.choose_spec)
      right_inv := fun y => Subtype.ext (mem_inf.mp y.2).1.choose_spec }

theorem u43_nine_dvd_fix
    (β : MulAut U43) (hβ : β * β = 1) :
    9 ∣ Nat.card {x : U43 // β x = x} := by
  by_cases h1 : β = 1
  · subst h1
    have : Nat.card {x : U43 // (1 : MulAut U43) x = x} = Nat.card U43 :=
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun x => rfl))
    rw [this, card_X₀]; norm_num
  let eE : U43 ≃* Inn := MonoidHom.ofInjective conj_injective_u43
  let θ : Inn ≃* M24Std.CU43.P := eE.symm.trans M24Std.CU43.psiEquiv
  rw [← card_inner_inf_centralizer]
  by_cases hE : β ∈ Inn
  · rw [M24Std.CU43.card_inf_centralizer_inner Inn θ centralizer_inner_eq_bot hE hβ h1]
    norm_num
  · rcases M24Std.CU43.card_inf_centralizer_outer Inn θ centralizer_inner_eq_bot hE hβ with
      h | h | h | h <;> rw [h] <;> norm_num

theorem nine_dvd_card_fix_of_mulEquiv
    {N : Type*} [Group N] (e : N ≃* U43) (γ : MulAut N)
    (hγ : γ * γ = 1) : 9 ∣ Nat.card {n : N // γ n = n} := by
  have hβ : MulAut.congr e γ * MulAut.congr e γ = 1 := by rw [← map_mul, hγ, map_one]
  have h := u43_nine_dvd_fix (MulAut.congr e γ) hβ
  have hcard : Nat.card {x : U43 // MulAut.congr e γ x = x} = Nat.card {n : N // γ n = n} :=
    Nat.card_congr (e.symm.toEquiv.subtypeEquiv fun x => by
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.coe_toEquiv]
      exact e.toEquiv.apply_eq_iff_eq_symm_apply)
  rwa [hcard] at h

end CFSG.EvenSporadicStandard.RuStd.S2
