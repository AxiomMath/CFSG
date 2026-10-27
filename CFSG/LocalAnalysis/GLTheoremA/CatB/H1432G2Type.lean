module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432ClsRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeGen3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12G2Aut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.SporG2

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem card_outer_mul_card {T : Type} [Group T] [Finite T] (hZ : Subgroup.center T = ⊥) :
    Nat.card (Outer T) * Nat.card T = Nat.card (MulAut T) := by
  have hinj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : x ∈ Subgroup.center T := Subgroup.mem_center_iff.2 fun g => by
      have h := congrArg (fun φ : MulAut T => φ g) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * x = x * g * x⁻¹ * x := by rw [h]
        _ = x * g := by group
    rw [hZ] at hxZ
    exact hxZ
  have hin : Nat.card (inner T) = Nat.card T :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [← hin]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm


theorem typeHyp3_g2three : BMType.TypeHyp3 (S8.isG2of 3) 4245696 where
  card := fun _ _ _ h => ClsRed.card_g2three CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds h
  aut := by
    intro T _ _ h
    obtain ⟨i, hi, ⟨f⟩⟩ := h
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | G2 q =>
        have hq : q.card = 3 := hi
        have hp2 : q.p ≠ 2 := by
          intro hp
          have h3 : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def, hq]
          rw [hp] at h3
          have h0 : q.exponent ≠ 0 := q.exponent_pos.ne'
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
          rw [hk, pow_succ] at h3
          omega
        have : Fact q.p.Prime := ⟨q.prime_p⟩
        have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
          rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
        obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv hp2 _ hK
        set F := GaloisField q.p q.exponent
        have hU : UntwistedChevalleyModel T .G2 (3 ^ 1) :=
          ⟨F, inferInstance, inferInstance, by rw [hK, hq, pow_one], ⟨f.trans b.symm⟩⟩
        have hM : LieModel T .G2 0 3 1 :=
          Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_three, le_rfl, rfl, by norm_num⟩, hU⟩)
        have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.card_mulAut_G2_dvd Nat.prime_three
          (by norm_num) hM
        have hord : ordG2 3 = 4245696 := by norm_num [ordG2]
        rw [hord] at hdvd
        let e₁ : AdjointQuotient .G2 F ≃* ↥(adjointGroup .G2 F) :=
          (QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
            QuotientGroup.quotientBot
        let φ : T ≃* ↥(adjointGroup .G2 F) := (f.trans b.symm).trans e₁
        have hZ : Subgroup.center T = ⊥ := by
          rw [eq_bot_iff]
          intro z hz
          have h1 : φ z ∈ Subgroup.center ↥(adjointGroup .G2 F) := by
            rw [← Subgroup.map_center_eq φ]
            exact ⟨z, hz, rfl⟩
          rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at h1
          rw [Subgroup.mem_bot]
          exact φ.injective (h1.trans (map_one φ).symm)
        have hcT : Nat.card T = 4245696 :=
          ClsRed.card_g2three CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
            ⟨_, hi, ⟨f⟩⟩
        haveI : Finite (MulAut T) :=
          Finite.of_injective (fun φ : MulAut T => (φ : T → T)) DFunLike.coe_injective
        have heq := card_outer_mul_card hZ
        rw [hcT] at heq
        rw [heq]
        intro h8
        have := Nat.dvd_trans h8 hdvd
        norm_num at this
      | _ => exact False.elim hi
    | _ => exact False.elim hi
  big := by norm_num
  nine := by norm_num

end CFSG.LocalAnalysis.GLTheoremA.H1420.SporG2

end
