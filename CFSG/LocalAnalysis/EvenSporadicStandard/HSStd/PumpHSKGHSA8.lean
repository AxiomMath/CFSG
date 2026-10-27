module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSAutCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpType
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Ly.KeySpec
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

theorem mem_alt8_of_two_swaps {a b c d : Fin 8} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd]
  rfl

@[expose] def alt8C5 : alternatingGroup (Fin 8) :=
  ⟨(Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 2 3 * Equiv.swap 3 4),
    mul_mem (mem_alt8_of_two_swaps (by decide) (by decide))
      (mem_alt8_of_two_swaps (by decide) (by decide))⟩

@[expose] def alt8C3 : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 5 6 * Equiv.swap 6 7, mem_alt8_of_two_swaps (by decide) (by decide)⟩

@[expose] def alt8W5 : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 5, mem_alt8_of_two_swaps (by decide) (by decide)⟩

@[expose] def alt8W3 : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 4 5 * Equiv.swap 5 6, mem_alt8_of_two_swaps (by decide) (by decide)⟩

theorem alt8C5_pow : alt8C5 ^ 5 = 1 := by decide

theorem alt8C5_ne : alt8C5 ≠ 1 := by decide

theorem alt8C3_pow : alt8C3 ^ 3 = 1 := by decide

theorem alt8C3_ne : alt8C3 ≠ 1 := by decide

theorem alt8C5_comm_C3 : alt8C5 * alt8C3 = alt8C3 * alt8C5 := by decide

theorem alt8W5_not_comm : alt8W5 * alt8C5 ≠ alt8C5 * alt8W5 := by decide

theorem alt8W3_not_comm : alt8W3 * alt8C3 ≠ alt8C3 * alt8W3 := by decide

theorem orderOf_alt8C5 : orderOf alt8C5 = 5 := orderOf_eq_prime alt8C5_pow alt8C5_ne

theorem orderOf_alt8C3 : orderOf alt8C3 = 3 := orderOf_eq_prime alt8C3_pow alt8C3_ne

theorem kgHSA8_of_sporadic
    (M : HS100Model) {K : Type} [Group K] (hK : IsSporadic K .HS)
    (A : Subgroup K) (hA : Nonempty (↥A ≃* alternatingGroup (Fin 8))) :
    Nat.card {σ : MulAut K // ∀ a ∈ A, σ a = a} ≤ 2 := by
  obtain ⟨ε⟩ := M.equiv K hK
  obtain ⟨e, he⟩ := M.aut
  obtain ⟨φ⟩ := hA
  let ρ : alternatingGroup (Fin 8) →* ↥hs100R :=
    (Subgroup.inclusion hs100P_le_R).comp (ε.toMonoidHom.comp (A.subtype.comp φ.symm.toMonoidHom))
  have hρ : Function.Injective ρ := by
    intro p q h
    have h1 := Subgroup.inclusion_injective hs100P_le_R h
    have h2 := ε.injective h1
    exact φ.symm.injective (Subtype.ext h2)
  let Ψ : {σ : MulAut K // ∀ a ∈ A, σ a = a} → ↥hs100R := fun σ => e.symm (MulAut.congr ε σ.1)
  have hΨinj : Function.Injective Ψ := by
    intro σ τ h
    have h1 : MulAut.congr ε σ.1 = MulAut.congr ε τ.1 := e.symm.injective h
    exact Subtype.ext ((MulAut.congr ε).injective h1)
  have hΨ : ∀ σ, Ψ σ ∈ centralizer (Set.range ρ) := by
    intro σ
    rw [mem_centralizer_iff]
    rintro _ ⟨p, rfl⟩
    set a : K := ((φ.symm p : ↥A) : K) with ha
    have hσa : σ.1 a = a := σ.2 a (φ.symm p).2
    have h1 : (MulAut.congr ε σ.1) (ε a) = ε a := by
      simp [MulAut.congr_apply, hσa]
    have h2 := he (Ψ σ) (ε a)
    have h3 : e (Ψ σ) = MulAut.congr ε σ.1 := e.apply_symm_apply _
    rw [h3, h1] at h2
    apply Subtype.ext
    show ((ρ p : ↥hs100R) : Equiv.Perm (Fin 100)) * (Ψ σ : Equiv.Perm (Fin 100)) =
      (Ψ σ : Equiv.Perm (Fin 100)) * ((ρ p : ↥hs100R) : Equiv.Perm (Fin 100))
    have h4 : ((ρ p : ↥hs100R) : Equiv.Perm (Fin 100)) = ((ε a : ↥hs100P) : Equiv.Perm (Fin 100)) :=
      rfl
    rw [h4]
    calc ((ε a : ↥hs100P) : Equiv.Perm (Fin 100)) * (Ψ σ : Equiv.Perm (Fin 100))
        = ((Ψ σ : Equiv.Perm (Fin 100)) * ((ε a : ↥hs100P) : Equiv.Perm (Fin 100)) *
            (Ψ σ : Equiv.Perm (Fin 100))⁻¹) * (Ψ σ : Equiv.Perm (Fin 100)) := by rw [← h2]
      _ = (Ψ σ : Equiv.Perm (Fin 100)) * ((ε a : ↥hs100P) : Equiv.Perm (Fin 100)) := by group
  have hle : Nat.card {σ : MulAut K // ∀ a ∈ A, σ a = a} ≤
      Nat.card (centralizer (Set.range ρ)) :=
    Nat.card_le_card_of_injective (fun σ => (⟨Ψ σ, hΨ σ⟩ : centralizer (Set.range ρ)))
      (fun σ τ h => hΨinj (congrArg Subtype.val h))
  refine hle.trans ?_
  have hx5 : orderOf (ρ alt8C5) = 5 := by rw [orderOf_injective ρ hρ, orderOf_alt8C5]
  have hx3 : orderOf (ρ alt8C3) = 3 := by rw [orderOf_injective ρ hρ, orderOf_alt8C3]
  have hc : ρ alt8C5 * ρ alt8C3 = ρ alt8C3 * ρ alt8C5 := by
    rw [← map_mul, ← map_mul, alt8C5_comm_C3]
  have hmem : ρ alt8C3 ∈ centralizer ({ρ alt8C5} : Set ↥hs100R) :=
    mem_centralizer_singleton_iff.2 hc.symm
  have h3 : 3 ∣ Nat.card ↥(centralizer ({ρ alt8C5} : Set ↥hs100R)) := by
    have h := orderOf_dvd_natCard (⟨ρ alt8C3, hmem⟩ : ↥(centralizer ({ρ alt8C5} : Set ↥hs100R)))
    rwa [Subgroup.orderOf_mk, hx3] at h
  obtain ⟨θ⟩ := hs100R_five_centralizer hx5 h3
  refine card_centralizer_le_two_of_five_three (S := Set.range ρ) hx5 hx3 hc ⟨_, rfl⟩ ⟨_, rfl⟩
    ?_ ?_ θ
  · intro h
    have := mem_centralizer_iff.1 h (ρ alt8W5) ⟨_, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact alt8W5_not_comm (hρ this)
  · intro h
    have := mem_centralizer_iff.1 h (ρ alt8W3) ⟨_, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact alt8W3_not_comm (hρ this)

end CFSG.EvenSporadicStandard.HSStd.PumpHS
