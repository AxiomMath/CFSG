module

public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3
public import CFSG.ClassicalInvolution.Asc77.AscT8Basic
public import CFSG.ClassicalInvolution.Asc77.AscT8RSyl

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8

namespace T8R

section Cert

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {T : Subgroup G}

theorem sylow_inf_omegaNbrGen_gen (hJ : J ∈ omegaNbr Ω K) (hTJ : T ≤ J) (hTS : T ≤ (S : Subgroup G))
    (hTsyl : IsSylow2In T J) (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) :
    (S : Subgroup G) ⊓ omegaNbrGen Ω K = T := by
  have hJX : J ≤ omegaNbrGen Ω K :=
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hJ
  have hTX : IsSylow2In T (omegaNbrGen Ω K) := isSylow2In_of_eq_sup_oddCoreOf hJX hX hTsyl
  exact hTX.eq_of_le S.isPGroup'.to_inf_left inf_le_right
    (le_inf hTS (hTsyl.1.trans hJX))

theorem not_mem_omegaNbr_of_four_le_gen (hJ : J ∈ omegaNbr Ω K) (hTJ : T ≤ J)
    (hTS : T ≤ (S : Subgroup G)) (hTsyl : IsSylow2In T J)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {M : Subgroup G}
    (heq : ∀ {A : Subgroup G}, IsPGroup 2 ↥A → 4 ≤ Nat.card ↥A → A ≤ M → A ≤ J → M = J)
    (h4 : 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G))) (hMJ : M ≠ J) : M ∉ omegaNbr Ω K := by
  intro hmem
  have hMX : M ≤ omegaNbrGen Ω K :=
    le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) M hmem
  have hle : M ⊓ (S : Subgroup G) ≤ J := by
    intro x hx
    have : x ∈ (S : Subgroup G) ⊓ omegaNbrGen Ω K := ⟨hx.2, hMX hx.1⟩
    rw [sylow_inf_omegaNbrGen_gen hJ hTJ hTS hTsyl hX] at this
    exact hTJ this
  exact hMJ (heq S.isPGroup'.to_inf_right h4 inf_le_left hle)

end Cert
end T8R

end CFSG.ClassicalInvolution.Asc77
