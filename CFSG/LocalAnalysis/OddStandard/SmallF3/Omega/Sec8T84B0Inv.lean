module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0Co
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Facts

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix Certificates.Asc82NormA6

namespace T84Co

theorem inv_fix_card : ∀ a : Equiv.Perm (Fin 6), a.sign = 1 → a * a = 1 → a ≠ 1 →
    (Finset.univ.filter fun v : Fin 4 → ZMod 2 => rho a *ᵥ v = v).card = 4 := by
  decide +kernel

end T84Co

theorem sec8t84FactInv_of_cert : Sec8T84FactInv := by
  intro G _ B hB H hH x hx hx1 hxx
  obtain ⟨e, ψ, hact, -⟩ := sec8t84_a6_conj B hB H hH
  have hsign : ((ψ ⟨x, hx⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)).sign = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp (ψ ⟨x, hx⟩).2
  have hane : ((ψ ⟨x, hx⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ≠ 1 := by
    intro h1
    apply hx1
    have h2 : ψ ⟨x, hx⟩ = 1 := Subtype.ext h1
    have h3 : (⟨x, hx⟩ : ↥H) = 1 := ψ.injective (by rw [h2, map_one])
    exact congrArg Subtype.val h3
  have haa : ((ψ ⟨x, hx⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) *
      ((ψ ⟨x, hx⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = 1 := by
    have h3 : ψ (⟨x, hx⟩ * ⟨x, hx⟩) = 1 := by
      have h4 : (⟨x, hx⟩ * ⟨x, hx⟩ : ↥H) = 1 := Subtype.ext hxx
      rw [h4, map_one]
    rw [map_mul] at h3
    exact congrArg Subtype.val h3
  rw [T84Co.card_fix_eq (e := e) (M := rho ((ψ ⟨x, hx⟩ : alternatingGroup (Fin 6)) :
    Equiv.Perm (Fin 6))) (fun b => hact ⟨x, hx⟩ b)]
  exact T84Co.inv_fix_card _ hsign haa hane

end CFSG.OddStandard.SmallF3.Omega
