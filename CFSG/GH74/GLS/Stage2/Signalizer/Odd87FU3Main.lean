module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Abs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Outer

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem normalizer_of_layerAut_fixed_fu3 {A : Type} [Group A] [Finite A] {zb : A} {p : ℕ}
    {X : Subgroup A} (hd : CellData zb p X) {j : ↥(layer A)} (hj : layerAut zb j = j) :
    (j : A) ∈ normalizer (X : Set A) := by
  have h1 := congrArg Subtype.val hj
  rw [coe_layerAut] at h1
  have hzi : zb⁻¹ = zb := inv_eq_of_mul_eq_one_right hd.z2
  rw [hzi] at h1
  refine hd.A4.inv (j : A) (Subgroup.mem_top _) (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  calc (j : A) * zb = (zb * (j : A) * zb) * zb := by rw [h1]
    _ = zb * j := by rw [mul_assoc (zb * (j : A)) _ _, hd.z2, mul_one]

theorem cell87_FU3 (hF : Generic.GenericKnownFacts) : Cell87 FU3 := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hU3
  exfalso
  classical
  have hd := CellData.of_ctx hctx hsig hyp
  obtain ⟨ℓ, f, hℓ, hf, hℓ2, hLie⟩ := hU3
  obtain ⟨-, -, F, _, _, hF', ⟨e₀⟩⟩ := Generic.lieModel_psu_data hLie
  have hpp : Fact p.Prime := ⟨hd.A4.prime⟩
  have hℓpos : 3 ≤ ℓ ^ f := by
    have h2 := hℓ.two_le
    have : ℓ ≤ ℓ ^ f := Nat.le_self_pow (by omega) ℓ
    have hodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
    obtain ⟨m, hm⟩ := hodd
    omega
  have hZ : center ↥(layer (Sec H₀ H₁)) = ⊥ :=
    hF.noTwoCover_psu3 ℓ f hℓ hℓ2 _ hLie ↥(layer (Sec H₀ H₁)) hd.quasi
      (by
        have := pCore_isPGroup (p := 2) (G := ↥(layer (Sec H₀ H₁)))
        rw [← hd.Zcore] at this
        exact this) ⟨MulEquiv.refl _⟩
  obtain ⟨e⟩ := Generic.nonempty_mulEquiv_of_center_eq_bot hZ e₀
  have hKn : (layer (Sec H₀ H₁)).Normal := layer_normal
  by_cases hin : ∃ s ∈ layer (Sec H₀ H₁), ∀ k ∈ layer (Sec H₀ H₁),
      zSec z H₀ hz H₁ * k * (zSec z H₀ hz H₁)⁻¹ = s * k * s⁻¹
  · obtain ⟨s, hs, hact⟩ := hin
    obtain ⟨hss, -, -, -, -, hcomm, hiff⟩ := hd.inner_decomp hZ hs hact
    have hXK := hd.le_layer_of_inner hZ hs hact
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right] at hcomm
      exact hd.A4.ne_bot hcomm.symm
    exact fu3_inner_false hℓ hℓ2 hf hℓpos hF' e hs hss hs1 hd.A4.odd hd.A4.pgroup hd.A4.ne_bot hXK
      (fun j hj hjs => hd.A4.inv j (Subgroup.mem_top _)
        (Subgroup.mem_centralizer_singleton_iff.mpr ((hiff j hj).mpr hjs))) hcomm
  · have hσσ : layerAut (zSec z H₀ hz H₁) * layerAut (zSec z H₀ hz H₁) = 1 := by
      ext x
      exact congrArg Subtype.val (layerAut_layerAut hd.z2 x)
    have hout : ¬ ∃ s : ↥(layer (Sec H₀ H₁)), ∀ k : ↥(layer (Sec H₀ H₁)),
        layerAut (zSec z H₀ hz H₁) k = s * k * s⁻¹ := by
      rintro ⟨s, hs⟩
      apply hin
      refine ⟨(s : Sec H₀ H₁), s.2, fun k hk => ?_⟩
      have := congrArg Subtype.val (hs ⟨k, hk⟩)
      rwa [coe_layerAut] at this
    exact fu3_outer_false hℓ hℓ2 hf hℓpos hF' e hσσ hout hd.A4.odd hd.A4.pgroup hd.A4.ne_bot
      hd.inf_centralizer_layer (fun j hj => normalizer_of_layerAut_fixed_fu3 hd hj)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
