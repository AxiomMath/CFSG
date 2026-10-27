module

public import CFSG.GH74.GLS.IVK.Proofs2.NatModQuad
public import CFSG.GH74.GLS.IVK.Proofs2.NatModRoot

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup

section Iso

variable {F : Type} [Field F] [Finite F] {p n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [Finite V]

theorem exists_natIso (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n) (hD : OddSylowStmt F)
    (ρ : Representation (ZMod p) (SL2 F) V) (hρ : Function.Injective ρ)
    (hneg : ∀ v, ρ (-1) v = -v) (hV : Nat.card V = Nat.card F ^ 2) :
    ∃ Φ : (Fin 2 → F) ≃+ V, ∀ (g : SL2 F) (v : Fin 2 → F),
      Φ ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) = ρ g (Φ v) := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hQcard : Nat.card (Qup F) = Nat.card F := card_Qup
  have hQlcard : Nat.card (Qlow F) = Nat.card F := card_Qlow
  have hAcard : Nat.card (fixSub ρ (Qup F)) = Nat.card F := card_fixSub_Qup hp hp2 hF hD ρ hρ hneg hV
  have hA'card : Nat.card (fixSub ρ (Qlow F)) = Nat.card F := by
    obtain ⟨g, hg⟩ := exists_conj_of_card_eq hp hF hQlcard
    exact (card_fixSub_conj ρ g hg).trans hAcard
  have hne : Qup F ≠ Qlow F := by
    intro h
    have h1 : Qup F ⊓ Qlow F = Qup F := by rw [← h, inf_idem]
    rw [Qup_inf_Qlow] at h1
    have : Nat.card (Qup F) = 1 := by rw [← h1]; exact Subgroup.card_bot
    omega
  have hinf := fixSub_inf_eq_bot hp hp2 hF hD ρ hρ hneg hV hQcard hQlcard hne
  obtain ⟨Φ, hΦinj, hΦeq, -⟩ := exists_equivariant_injection_of_quadratic_representation ρ
    (fixSub ρ (Qup F)).toAddSubgroup (fixSub ρ (Qlow F)).toAddSubgroup
    (fun v => by
      constructor
      · intro hv c
        exact hv _ (upperSL_mem_Qup c)
      · intro hv h hh
        obtain ⟨c, rfl⟩ := mem_Qup.1 hh
        exact hv c)
    (fun v => by
      constructor
      · intro hv c
        exact hv _ (lowerSL_mem_Qlow c)
      · intro hv h hh
        obtain ⟨c, rfl⟩ := mem_Qlow.1 hh
        exact hv c)
    (hAcard) (hA'card)
    (by
      refine eq_bot_iff.2 fun v hv => ?_
      have hv' : v ∈ fixSub ρ (Qup F) ⊓ fixSub ρ (Qlow F) := hv
      rw [hinf] at hv'
      exact hv')
    (fun c v _ => sub_mem_fixSub_Qup hp hp2 hF hD ρ hρ hneg hV (upperSL_mem_Qup c) v)
    (fun d v _ => sub_mem_fixSub_of_card_eq hp hp2 hF hD ρ hρ hneg hV hQlcard (lowerSL_mem_Qlow d) v)
  have hcardN : Nat.card (Fin 2 → F) = Nat.card F ^ 2 := by simp [Nat.card_pi]
  have hbij : Function.Bijective Φ :=
    hΦinj.bijective_of_nat_card_le (by rw [hV, hcardN])
  exact ⟨AddEquiv.ofBijective Φ hbij, fun g v => hΦeq g v⟩

end Iso

end CFSG.GH74.GLS.IVK.Proofs2
