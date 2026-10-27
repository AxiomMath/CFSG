module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDOmData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDS

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix

private theorem s8d_card_alt_five : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem s8d_shapeOm {Z : Subgroup S8A}
    (θ' : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) ≃* ↥Z)
    (hθ : ∀ a : ↥(alternatingGroup (Fin 5)), (θ' (a, a) : S8A) = s8dDiag a)
    (hf : (θ' (s8dG, 1) : S8A) = s8dOm1 ∨ (θ' (s8dG, 1) : S8A) = s8dOm2) :
    ∃ ψ : Sec12SL × Sec12SL ≃* ↥Z, ∀ (A B : Sec12SL) (p : EvW × EvW),
      s8dPom (s8dAp (ψ (A, B)) p) = (A : Sec12M) * s8dPom p * (B : Sec12M)ᵀ := by
  let ι : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) →* S8A :=
    Z.subtype.comp θ'.toMonoidHom
  have hR : ∀ x, ι x ∈ s8dOm.range := by
    refine s8d_range_le_of_diag ι s8dOm.range (fun b => ?_) s8dG_ne_one ?_
    · show (θ' (b, b) : S8A) ∈ s8dOm.range
      rw [hθ b]
      exact s8dDiag_mem_range b
    · show (θ' (s8dG, 1) : S8A) ∈ s8dOm.range
      rcases hf with h | h <;> rw [h]
      · exact MonoidHom.mem_range.mpr ⟨(s8dAg, 1), rfl⟩
      · exact MonoidHom.mem_range.mpr ⟨(1, s8dAgF), rfl⟩
  have hle : Z ≤ s8dOm.range := by
    intro z hz
    obtain ⟨x, hx⟩ := θ'.surjective ⟨z, hz⟩
    have h := hR x
    rwa [show ι x = z from congrArg Subtype.val hx] at h
  let e := MonoidHom.ofInjective s8dOm_injective
  haveI : Finite ↥s8dOm.range := Finite.of_equiv _ e.toEquiv
  have hcardZ : Nat.card ↥Z = 3600 := by
    rw [← Nat.card_congr θ'.toEquiv, Nat.card_prod, s8d_card_alt_five]
  have hcardR : Nat.card ↥s8dOm.range = 3600 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, sec12F4_card_sl]
  have hEq : Z = s8dOm.range := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardZ, hcardR])
  refine ⟨e.trans (MulEquiv.subgroupCongr hEq.symm), fun A B p => ?_⟩
  have hψ : ((e.trans (MulEquiv.subgroupCongr hEq.symm) (A, B) : ↥Z) : S8A) = s8dOm (A, B) :=
    MonoidHom.ofInjective_apply s8dOm_injective
  rw [hψ, s8dAp_om]

end CFSG.OddStandard.SmallF3.Omega
