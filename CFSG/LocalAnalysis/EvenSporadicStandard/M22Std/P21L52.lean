module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21L52c
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Out
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2L52
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21NoInv31

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem false_of_layer_psl52
    {G : Type} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    (hC : Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)))
    (hG : Nat.card G ∣ gl8) {V : Type} [CommGroup V] (hsq : ∀ x : V, x * x = 1)
    (hcard : Nat.card V = 256) (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (h : LieModel (egaLayer (G ⧸ fusionOddCore G)) .PSL 5 2 1) : False := by
  have hc : CFSG.Assembly.LowTwoRank.StatedClassicalModel (egaLayer (G ⧸ fusionOddCore G))
      .PSL 5 2 1 :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have hE := eData_L52 h
  have hbig : 1440 < Nat.card (egaLayer (G ⧸ fusionOddCore G)) := by
    rw [card_of_statedClassicalModel_psl_five_two hc]
    norm_num
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hc
  have hK2 : Nat.card K = 2 := by simpa using hK
  have e' : ↥(egaLayer (G ⧸ fusionOddCore G)) ≃* LinearFlag.projectiveSL 5 K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 5 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 K)
  have hten : ∀ g : ↥(egaLayer (G ⧸ fusionOddCore G)), orderOf g ≠ 10 := by
    let := P21L52.charTwo hK2
    let : Algebra (ZMod 2) K := ZMod.algebra K 2
    exact fun g => P21L52.no_order_ten_of_equiv hK2 e' g
  have hsimp := isSimpleGroup_of_eData hE
  have hfinE : Finite ↥(egaLayer (G ⧸ fusionOddCore G)) := inferInstance
  have hTab := fun u (hu : u * u = 1) (hu1 : u ≠ 1) =>
    noBadCent_of_noTen (U := ↥(egaLayer (G ⧸ fusionOddCore G))) (by omega) hten u hu hu1
  obtain ⟨U, hUn, ⟨eU⟩, -, hzU⟩ := prop21_simple_case hz hC hG hE hbig hTab
  have hNoInv : ∀ x t : G, x ^ 31 = 1 → x ≠ 1 → t * x * t⁻¹ = x⁻¹ → False := by
    let : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) (fun a => by
      rw [two_nsmul, ← ofMul_toMul a, ← ofMul_mul, hsq, ofMul_one])
    intro x t hx hx1 ht
    exact no_inv_order_31 hcard ρ hρ x t hx hx1 ht
  exact P21L52.false_of_outer_psl5 hK2 U (eU.trans e') hzU hNoInv

end CFSG.EvenSporadicStandard.M22Std
