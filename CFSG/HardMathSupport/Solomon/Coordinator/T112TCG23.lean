module

public import CFSG.HardMathSupport.Timmesfeld.LieRank.G2Spec
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTables
public import CFSG.HardMathSupport.Timmesfeld.LieRank.Exc3Models
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Main

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.LieRank
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U

section Certs


theorem hatG23_four_le_pRank (L : Type) [Group L] [Finite L] (hG : IsHatGTwoThree L) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨-, hc3, q, d, hq3, hd, ⟨e⟩⟩ := hG
  have hqcard : q.p ^ q.exponent = 3 := by
    have := hq3
    rwa [TauCeti.PrimePower.card_def] at this
  obtain ⟨hp3, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).1 hqcard
  have hM0 : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie d).Group .G2 0 q.p q.exponent :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_lie (t := .G2)
      ⟨q.prime_p, q.exponent_pos, rfl, by omega⟩ d (by rw [hd]; exact ⟨rfl, rfl⟩)
  rw [hp3, hf1] at hM0
  have hM1 : CFSG.Models.LieModel (L ⧸ Subgroup.center L) .G2 0 3 1 :=
    models_lieModel_of_mulEquiv e.symm hM0
  have hB := blueprintLieModel_of_models hM1
  obtain ⟨eA⟩ := nonempty_mulEquiv_adjointGroup_G2_of_lieModel hB
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e', -⟩ : ∃ e' : L ⧸ Subgroup.center L ≃* RG, True :=
    ⟨eA.trans (Subgroup.equivMapOfInjective _ (glHom (RingEquiv.refl (ZMod 3)))
      (glHom_injective _)), trivial⟩
  have h3 : 3 ∣ Nat.card (Subgroup.center L) := by rw [hc3]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center L)) 3 h3
  have hzL : orderOf (z : L) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
  let φ : L →* RG :=
    (e' : L ⧸ Subgroup.center L →* RG).comp (QuotientGroup.mk' (Subgroup.center L))
  have hφ : Function.Surjective φ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center L := by
    ext x
    simp [φ]
  exact four_le_pRank_of_cover_RG φ hφ hker.le (z := (z : L)) (by rw [hker]; exact z.2) hzL

end Certs

end CFSG.HardMathSupport.Solomon.Coordinator
