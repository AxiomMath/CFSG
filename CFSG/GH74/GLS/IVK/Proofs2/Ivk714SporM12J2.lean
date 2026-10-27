module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Spor
public import CFSG.GH74.Generic.S45.LSporM12Data
public import CFSG.GH74.Generic.S45.LSporJ2
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalOuter

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG CFSG.Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.IVK Subgroup

theorem card_fixed_conj {G : Type} [Group G] (g : G) :
    Nat.card {x : G // MulAut.conj g x = x} = Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MulAut.conj_apply]
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

theorem orderOf_eq_two_of_conj {G : Type} [Group G] (hZ : Subgroup.center G = ⊥) {g : G}
    {α : MulAut G} (hg : MulAut.conj g = α) (hα : orderOf α = 2) : orderOf g = 2 := by
  have hgg : g * g = 1 := by
    have h1 : MulAut.conj (g * g) = 1 := by
      rw [map_mul, hg, ← pow_two, ← hα]
      exact pow_orderOf_eq_one α
    have hc : g * g ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg (fun a : MulAut G => a x) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * (g * g) = (g * g * x * (g * g)⁻¹) * (g * g) := by rw [this]
        _ = g * g * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [map_one] at hg
    rw [← hg, orderOf_one] at hα
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.M12Cover in
theorem m12_fixed_card_aut
    (α : MulAut NativeSporadic.M12) (hα : orderOf α = 2) :
    Nat.card {x : NativeSporadic.M12 // α x = x} = 120 ∨
      Nat.card {x : NativeSporadic.M12 // α x = x} = 192 ∨
        Nat.card {x : NativeSporadic.M12 // α x = x} = 240 := by
  by_cases hin : α ∈ inner NativeSporadic.M12
  · obtain ⟨g, hg⟩ := hin
    have hgord : orderOf g = 2 := orderOf_eq_two_of_conj m12_center hg hα
    subst hg
    rw [card_fixed_conj]
    rcases CFSG.GH74.Generic.S45.LAlt.m12_involution_data g hgord with h | ⟨h, -⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · obtain ⟨g, hg⟩ := exists_conj_beta_of_outer hα hin
    left
    have h1 : Nat.card {x : NativeSporadic.M12 // α x = x} =
        Nat.card ↥(CFSG.Sporadic.Schreier.fixSub α) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => CFSG.Sporadic.Schreier.mem_fixSub.symm)
    rw [h1, hg]
    exact card_fixSub_conj_beta g

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.J2Cover
  CFSG.ComponentClassification.J2Cover.External in
theorem j2_fixed_card_aut
    (α : MulAut P) (hα : orderOf α = 2) :
    Nat.card {x : P // α x = x} = 336 ∨ Nat.card {x : P // α x = x} = 240 ∨
      Nat.card {x : P // α x = x} = 1920 := by
  by_cases hin : α ∈ inner P
  · obtain ⟨g, hg⟩ := hin
    have hgord : orderOf g = 2 := orderOf_eq_two_of_conj center_P hg hα
    subst hg
    rw [card_fixed_conj]
    rcases CFSG.GH74.Generic.S45.j2_involution_data hgord with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · obtain ⟨g, hg⟩ := exists_conj_beta_of_outer hα hin
    left
    have h1 : Nat.card {x : P // α x = x} = Nat.card ↥(CFSG.Sporadic.Schreier.fixSub α) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => CFSG.Sporadic.Schreier.mem_fixSub.symm)
    rw [h1, hg]
    exact card_fixSub_conj_beta g

theorem ivk714_m12 :
    Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .M12) := by
  intro K _ _ _ hK z hz h
  obtain ⟨e⟩ := hK
  have e' : K ≃* NativeSporadic.M12 := e
  have hz' : orderOf (MulAut.congr e' z) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hz
  rcases m12_fixed_card_aut _ hz' with hc | hc | hc
  · exact h.false_of_card_fixed e' hc (by norm_num)
  · exact h.false_of_card_fixed e' hc (by norm_num)
  · exact h.false_of_card_fixed e' hc (by norm_num)

theorem ivk714_j2 :
    Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .J2) := by
  intro K _ _ _ hK z hz h
  obtain ⟨e⟩ := hK
  let e' : K ≃* CFSG.ComponentClassification.J2Cover.P :=
    e.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
  have hz' : orderOf (MulAut.congr e' z) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hz
  rcases j2_fixed_card_aut _ hz' with hc | hc | hc
  · exact h.false_of_card_fixed e' hc (by norm_num)
  · exact h.false_of_card_fixed e' hc (by norm_num)
  · exact h.false_of_card_fixed e' hc (by norm_num)

end CFSG.GH74.GLS.IVK.Proofs2
