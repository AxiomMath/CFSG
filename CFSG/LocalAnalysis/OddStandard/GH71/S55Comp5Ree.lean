module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Pair
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Ree
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
public import CFSG.LieType.Steinberg.CentralExt.SmallReeMultiplier

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.LieType.Ree


variable {r : ℕ} {Y : Type} [Group Y]

theorem noR_two_of_FReed (h : FReed r Y) : NoR 2 Y := by
  intro J _ _ hJ ⟨e⟩
  obtain ⟨-, f, -, hm⟩ := h
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e₁⟩⟩ := ree_model_data (reeTitsModel_of_lieModel hm)
  have hZ : center (ReeTag.G2.reeGamma K a) = ⊥ := ReeTag.center_reeGamma_G2_eq_bot hK
  let e' : (J ⧸ center J) ≃* (ReeTag.G2.reeGamma K a ⧸ center (ReeTag.G2.reeGamma K a)) :=
    (e.trans e₁).trans ((QuotientGroup.quotientBot (G := ReeTag.G2.reeGamma K a)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm))
  obtain ⟨-, hsub⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SmallReeClosed.smallRee_hopfMultiplier hK ha
  have : Finite (CFSG.Open.griessHopfMultiplier (ReeTag.G2.reeGamma K a ⧸
      center (ReeTag.G2.reeGamma K a))) := Finite.of_subsingleton
  have h1 := card_center_dvd_hopf hJ e'
  rw [Nat.card_of_subsingleton (1 : CFSG.Open.griessHopfMultiplier (ReeTag.G2.reeGamma K a ⧸
    center (ReeTag.G2.reeGamma K a)))] at h1
  rw [Nat.dvd_one.1 h1]
  norm_num

theorem abelian_sylow_two_of_FReed [Finite Y] (h : FReed r Y) :
    ∀ S : Sylow 2 Y, ∀ a ∈ (S : Subgroup Y), ∀ b ∈ (S : Subgroup Y), a * b = b * a := by
  obtain ⟨-, f, -, hm⟩ := h
  obtain ⟨a, K, _, _, _, -, hK, ⟨e⟩⟩ := ree_model_data (reeTitsModel_of_lieModel hm)
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  intro S x hx y hy
  have hab := CFSG.Walter.Ree.Model.hasAbelianSylowTwo_reeGamma hK hw₀
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  change IsMulCommutative ((S : Subgroup Y).map e.toMonoidHom) at hab
  have h1 := hab.is_comm.comm ⟨e x, x, hx, rfl⟩ ⟨e y, y, hy, rfl⟩
  apply e.injective
  have h2 := congrArg Subtype.val h1
  simpa only [MulMemClass.coe_mul, map_mul] using h2

theorem comp5_freed : Comp5 FReed := by
  refine comp5_of fun r p Y _ _ _ _ hp hp5 _ hY y g _ _ hJ => ?_
  exact absurd hJ (not_pairSL2_of_abelian_sylow hp (by omega) (abelian_sylow_two_of_FReed hY)
    (noR_two_of_FReed hY) y g)

end CFSG.OddStandard.GH71.S55
