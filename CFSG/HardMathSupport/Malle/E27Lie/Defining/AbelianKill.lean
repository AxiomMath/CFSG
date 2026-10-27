module

public import CFSG.HardMathSupport.Malle.Proving.E27AbelianQuotient
public import CFSG.HardMathSupport.Foote.E27.SporSylowBound
public import CFSG.HardMathSupport.Foote.E27.SporKill

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27

theorem E27Config.false_of_sylow_hom_comm {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K) {J : Type*} [Group J] [Finite J]
    (ψ : ↥K ≃* J) (P : Subgroup J) (hP : Nat.card P = 3 ^ (Nat.card J).factorization 3)
    {A : Type*} [CommGroup A] (φ : P →* A) (hφ : Function.Surjective φ)
    (h81 : 81 ≤ Nat.card A) : False := by
  have hPp : IsPGroup 3 P := IsPGroup.of_card hP
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 3 ↥K))
  refine h.false_of_sylow_kill hz S₀ fun s hs hs3 => Or.inl ?_
  exact dvd81_card_sylow_inf_centralizer_of_equiv ψ P hP
    (fun w hw _ => Proving.eighty_one_dvd_inf_centralizer_of_three_group hPp φ hφ hw h81)
    S₀ hs hs3

end CFSG.HardMathSupport.Malle.E27Lie
