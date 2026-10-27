module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTPerm10
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTType
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpType

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpT

open Subgroup CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

namespace A8Cycles

theorem mem_alt8_of_two_swaps {a b c d : Fin 8} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd]
  rfl

@[expose] def five : alternatingGroup (Fin 8) :=
  ⟨(Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 2 3 * Equiv.swap 3 4),
    mul_mem (mem_alt8_of_two_swaps (by decide) (by decide))
      (mem_alt8_of_two_swaps (by decide) (by decide))⟩

@[expose] def three : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 5 6 * Equiv.swap 6 7, mem_alt8_of_two_swaps (by decide) (by decide)⟩

@[expose] def wFive : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 5, mem_alt8_of_two_swaps (by decide) (by decide)⟩

@[expose] def wThree : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 4 5 * Equiv.swap 5 6, mem_alt8_of_two_swaps (by decide) (by decide)⟩

theorem five_pow : five ^ 5 = 1 := by decide

theorem five_ne : five ≠ 1 := by decide

theorem three_pow : three ^ 3 = 1 := by decide

theorem three_ne : three ≠ 1 := by decide

theorem five_comm_three : five * three = three * five := by decide

theorem wFive_not_comm : wFive * five ≠ five * wFive := by decide

theorem wThree_not_comm : wThree * three ≠ three * wThree := by decide

theorem orderOf_five : orderOf five = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime five_pow five_ne

theorem orderOf_three : orderOf three = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime three_pow three_ne

end A8Cycles

open A8Cycles

theorem kgA10A8_proved : KGA10A8 := by
  intro K _ _ ⟨e⟩ A ⟨f⟩
  let ρ : alternatingGroup (Fin 8) →* Equiv.Perm (Fin 10) :=
    (alternatingGroup (Fin 10)).subtype.comp
      (e.toMonoidHom.comp (A.subtype.comp f.symm.toMonoidHom))
  have hρ : Function.Injective ρ := by
    intro p q h
    exact f.symm.injective (Subtype.ext (e.injective (Subtype.ext h)))
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10
    (by norm_num) (by norm_num)
  let Θ : {σ : MulAut K // ∀ a ∈ A, σ a = a} → Equiv.Perm (Fin 10) :=
    fun σ => Function.surjInv hbij.2 (MulAut.congr e σ.1)
  have hΘ : ∀ σ, MulAut.conjNormal (Θ σ) = MulAut.congr e σ.1 := fun σ =>
    Function.surjInv_eq hbij.2 _
  have hΘinj : Function.Injective Θ := by
    intro σ τ h
    have h1 : MulAut.congr e σ.1 = MulAut.congr e τ.1 := by rw [← hΘ σ, ← hΘ τ, h]
    exact Subtype.ext ((MulAut.congr e).injective h1)
  have hΘc : ∀ σ, Θ σ ∈ centralizer (Set.range ρ) := by
    intro σ
    rw [mem_centralizer_iff]
    rintro _ ⟨p, rfl⟩
    set a : K := ((f.symm p : ↥A) : K) with ha
    have hσa : σ.1 a = a := σ.2 a (f.symm p).2
    have h1 : (MulAut.conjNormal (Θ σ) (e a) : alternatingGroup (Fin 10)) = e a := by
      rw [hΘ σ]
      simp [MulAut.congr_apply, hσa]
    have h2 : Θ σ * ((e a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) * (Θ σ)⁻¹ =
        ((e a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) := by
      rw [← MulAut.conjNormal_apply, h1]
    show ((e a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) * Θ σ =
      Θ σ * ((e a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10))
    calc ((e a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) * Θ σ
        = (Θ σ * ((e a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) * (Θ σ)⁻¹) * Θ σ := by
          rw [h2]
      _ = Θ σ * ((e a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) := by group
  have hle : Nat.card {σ : MulAut K // ∀ a ∈ A, σ a = a} ≤ Nat.card (centralizer (Set.range ρ)) :=
    Nat.card_le_card_of_injective (fun σ => (⟨Θ σ, hΘc σ⟩ : centralizer (Set.range ρ)))
      (fun σ τ h => hΘinj (congrArg Subtype.val h))
  refine hle.trans ?_
  have hx5 : orderOf (ρ five) = 5 := by rw [orderOf_injective ρ hρ, orderOf_five]
  have hx3 : orderOf (ρ three) = 3 := by rw [orderOf_injective ρ hρ, orderOf_three]
  have hc : ρ five * ρ three = ρ three * ρ five := by
    rw [← map_mul, ← map_mul, five_comm_three]
  have hy : orderOf (ρ five * ρ three) = 15 := by
    rw [(show Commute (ρ five) (ρ three) from hc).orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [hx5, hx3]; norm_num), hx5, hx3]
  refine card_centralizer_le_two_of_order_fifteen (S := Set.range ρ) hx5 hx3 hc ⟨_, rfl⟩
    ⟨_, rfl⟩ ?_ ?_ (dvd_of_eq (card_centralizer_eq_thirty hy))
  · intro h
    have := mem_centralizer_iff.1 h (ρ wFive) ⟨_, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact wFive_not_comm (hρ this)
  · intro h
    have := mem_centralizer_iff.1 h (ρ wThree) ⟨_, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact wThree_not_comm (hρ this)

end CFSG.EvenSporadicStandard.HSStd.PumpT
