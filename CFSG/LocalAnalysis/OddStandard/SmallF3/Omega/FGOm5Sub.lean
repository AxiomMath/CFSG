module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOm5Model
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGPocketCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGPocketSix
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem fg_omega5_sub : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) →
        (∃ z ∈ layerCent L s, IsI4PlusIn L z) ∧
          ∃ u ∈ layerCent L s, orderOf u = 2 ∧ InducesTypeSome L u 6 1 2 (-1) := by
  intro G _ _ L hL s hs2 hsn ⟨α, V, _, _, _, Q, hQ, e, x, hdim, hsgn, hind, y, hy, hyT⟩
  have hKM2 : KM2 x := ⟨α, y, hy, hyT⟩
  obtain ⟨-, t, htt, htype, htoProj⟩ := hyT
  have hx : x = projOrthToProjSim Q (toProj Q t) := hy.symm.trans (by rw [htoProj])
  subst hx
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    rw [ff_center_eq_oddCore_six_plus hL]
    exact ff_odd_card_oddCore ↥L
  have hss : s * s = 1 := by
    rw [← pow_two]
    exact hs2 ▸ pow_orderOf_eq_one s
  obtain ⟨ρ, hρ, hρφ⟩ := ff6m_exists_centCover hQ h2 e hodd hind hss
  obtain ⟨w₀, w₁, hw₀r, hw₁r, hw₀2, hw₁2, hT₀, hT₁⟩ :=
    fg_model_om5_involutions hQ hdim hsgn htt htype
  have hXeq : twoPrimeRes (twoRes (L ⊓ centralizer ({s} : Set G))) = layerCent L s :=
    (ff6m_cover_isOmega5 hρ (ff_K2_layerModel hQ hdim hsgn hKM2)).2
  have key : ∀ w : ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t))),
      w ∈ twoRes (⊤ : Subgroup ↥(ffFix hQ h2 (projOrthToProjSim Q (toProj Q t)))) →
      w * w = 1 → ((w : ↥(omegaProj hQ)) : ProjOrth Q) ≠ 1 →
      ∃ (u : G) (hu : u ∈ L), u ∈ layerCent L s ∧ orderOf u = 2 ∧
        ff6mPhi e ⟨u, hu⟩ = (w : ↥(omegaProj hQ)) := by
    intro w hw hww hw1
    obtain ⟨u, huC, hutwo, huu, hρu⟩ := ff6m_cover_lift_involution_in hρ hw hww
    have huL : u ∈ L := (Subgroup.mem_inf.mp huC).1
    have hφ : ff6mPhi e ⟨u, huL⟩ = (w : ↥(omegaProj hQ)) := by
      rw [← hρφ ⟨u, huC⟩, hρu]
    have hu1 : u ≠ 1 := by
      intro h
      apply hw1
      have h' : (⟨u, huL⟩ : ↥L) = 1 := Subtype.ext h
      rw [← hφ, h', map_one]
      rfl
    have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
    refine ⟨u, huL, ?_, hu2, hφ⟩
    rw [← hXeq]
    exact Subgroup.subset_closure ⟨hutwo, 1, by rw [hu2]; rfl⟩
  constructor
  · obtain ⟨u, huL, hul, hu2, hφ⟩ := key w₀ hw₀r hw₀2 hT₀.1
    refine ⟨u, hul, ?_⟩
    refine (fg_isI4PlusIn_iff_of_cover (ff6m_phi_cover e hodd) huL hu2).mpr ?_
    rw [hφ]
    exact fg_isI4PlusIn_top_of_hasType_six_plus hQ hdim hsgn hT₀
  · obtain ⟨u, huL, hul, hu2, hφ⟩ := key w₁ hw₁r hw₁2 hT₁.1
    refine ⟨u, hul, hu2, V, inferInstance, inferInstance, inferInstance, Q, hQ, e,
      projOrthToProjSim Q ((ff6mPhi e ⟨u, huL⟩ : ↥(omegaProj hQ)) : ProjOrth Q), hdim, hsgn,
      ff6m_induces_of_mem hQ e huL, _, rfl, ?_⟩
    rw [hφ]
    exact hT₁

end CFSG.OddStandard.SmallF3.Omega
