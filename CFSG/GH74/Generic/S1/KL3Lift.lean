module

public import CFSG.GH74.Generic.S1.KL3SL3
public import CFSG.GH74.Generic.S1.KL5Lift

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

theorem kl3_exists_lift (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {H S : Type} [Group H] [Finite H] [Group S] (π : H →* S) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center H) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    (Pb : Subgroup S) (e : ↥Pb ≃* SL(3, F)) :
    ∃ θ : SL(3, F) →* H, Function.Injective θ ∧ ∀ g, π (θ g) = ((e.symm g : ↥Pb) : S) := by
  classical
  have hperfSL : Group.IsPerfect SL(3, F) := kl3_isPerfect_sl3
  have hperfPb : Group.IsPerfect ↥Pb :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hPbc : ⁅Pb, Pb⁆ = Pb := Subgroup.isPerfect_iff.1 hperfPb
  obtain ⟨At, hAtp, hAtm⟩ := kl5_exists_perfect_lift π hπ Pb hPbc
  have hAtperf : Group.IsPerfect ↥At := Subgroup.isPerfect_iff.2 hAtp
  have hmem : ∀ a : At, π a ∈ Pb := fun a => hAtm ▸ Subgroup.mem_map_of_mem π a.2
  let ρ : ↥At →* ↥Pb := (π.comp At.subtype).codRestrict Pb hmem
  have hρs : Function.Surjective ρ := by
    intro p
    have hp : (p : S) ∈ At.map π := by rw [hAtm]; exact p.2
    obtain ⟨a, ha, hap⟩ := Subgroup.mem_map.1 hp
    exact ⟨⟨a, ha⟩, Subtype.ext hap⟩
  let σ : ↥At →* SL(3, F) := e.toMonoidHom.comp ρ
  have hσs : Function.Surjective σ := e.surjective.comp hρs
  have hσker : σ.ker ≤ center ↥At := by
    intro a ha
    have h1 : π a = 1 := by
      have h2 : ρ a = 1 := e.injective (by simpa [σ] using ha)
      exact congrArg Subtype.val h2
    have h2 : (a : H) ∈ Subgroup.center H := hker (MonoidHom.mem_ker.2 h1)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 h2 (g : H))
  have hZ : center SL(3, F) = ⊥ := kl3_center_sl3 hF
  have hsimple : IsSimpleGroup SL(3, F) := kl3_isSimple_sl3 hF
  have hnonab : ∃ a b : SL(3, F), a * b ≠ b * a := kl3_nonabelian_sl3 hF
  have hAtq : CFSG.IsQuasisimple ↥At :=
    CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_of_perfect_cover hAtperf σ hσs hsimple hnonab hσker
  have hcen : center ↥At = σ.ker := by
    refine le_antisymm ?_ hσker
    intro x hx
    have : σ x ∈ center SL(3, F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨c, rfl⟩ := hσs y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx c]
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  let eC : ↥At ⧸ center ↥At ≃* SL(3, F) :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans (QuotientGroup.quotientKerEquivOfSurjective σ hσs)
  let ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F ≃* SL(3, F) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hmodel : StatedClassicalModel (↥At ⧸ center ↥At) .PSL 3 3 1 := by
    refine ⟨⟨Nat.prime_three, le_rfl, by norm_num, by norm_num, by norm_num⟩, F, inferInstance,
      inferInstance, by simpa using hF, ⟨?_⟩⟩
    exact eC.trans (ePSL.symm.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F))
  have hdvd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hAtq hmodel
  have hexc : exceptionalOrders .PSL 3 3 1 = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have hgen : genericOrders .PSL 3 3 1 = (Nat.gcd 3 (3 ^ 1 - 1), 1) := rfl
  rw [hexc, hgen] at hdvd
  have hc1 : Nat.card (center ↥At) = 1 := by
    have : Nat.card (center ↥At) ∣ 1 := by simpa using hdvd
    exact Nat.dvd_one.1 this
  have hbot : σ.ker = ⊥ := by
    rw [← hcen]
    exact Subgroup.eq_bot_of_card_eq _ hc1
  have hσi : Function.Injective σ := (MonoidHom.ker_eq_bot_iff σ).1 hbot
  let σe : ↥At ≃* SL(3, F) := MulEquiv.ofBijective σ ⟨hσi, hσs⟩
  refine ⟨At.subtype.comp σe.symm.toMonoidHom, ?_, ?_⟩
  · exact Subtype.val_injective.comp σe.symm.injective
  · intro g
    have h1 : e (ρ (σe.symm g)) = g := by
      have := σe.apply_symm_apply g
      exact this
    have h2 : ρ (σe.symm g) = e.symm g :=
      calc ρ (σe.symm g) = e.symm (e (ρ (σe.symm g))) := (e.symm_apply_apply _).symm
        _ = e.symm g := by rw [h1]
    exact congrArg Subtype.val h2

end CFSG.GH74.Generic.S1
