module

public import CFSG.HardMathSupport.Malle.Coordinator.CaseTwoSieve
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4SocleFacts
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LieType.Ree.LargeReeInvolutionFusion

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.AGLEmbedding CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.ReeTag

theorem card_centralizer_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({e x} : Set H)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨e.symm g.1, ?_⟩
      invFun := fun g => ⟨e g.1, ?_⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp) }
  · have h := Subgroup.mem_centralizer_singleton_iff.1 g.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simpa using h
  · have h := Subgroup.mem_centralizer_singleton_iff.1 g.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using congrArg e h

theorem card_centralizer_subtype_eq_card_inf {G : Type*} [Group G] (Γ : Subgroup G) (s : Γ) :
    Nat.card (Subgroup.centralizer ({s} : Set Γ)) =
      Nat.card (Γ ⊓ Subgroup.centralizer ({(s : G)} : Set G) : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨(g.1 : G), g.1.2, ?_⟩
      invFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩, ?_⟩
      left_inv := fun g => Subtype.ext (Subtype.ext rfl)
      right_inv := fun g => Subtype.ext rfl }
  · have h := Subgroup.mem_centralizer_singleton_iff.1 g.2
    exact Subgroup.mem_centralizer_singleton_iff.2 (by simpa using congrArg Subtype.val h)
  · have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext h

theorem not_fifteen_dvd_centralizer_orders :
    ¬ 15 ∣ (2 ^ (2 * 2 + 1)) ^ 12 * (2 ^ (2 * 2 + 1) - 1) * ((2 ^ (2 * 2 + 1)) ^ 2 + 1) ∧
    ¬ 15 ∣ (2 ^ (2 * 2 + 1)) ^ 10 * ((2 ^ (2 * 2 + 1)) ^ 2 - 1) := by
  norm_num

theorem not_fifteen_dvd_card_centralizer_reeGamma
    {F : Type} [Field F] [Finite F] [CharP F F4.prime] (hF : Nat.card F = 2 ^ (2 * 2 + 1))
    (s : F4.reeGamma F 2) (hs1 : s ≠ 1) (hss : s * s = 1) :
    ¬ 15 ∣ Nat.card (Subgroup.centralizer ({s} : Set (F4.reeGamma F 2))) := by
  have hs2 : (s : ModGL F4.tag F) ^ 2 = 1 := by
    rw [pow_two, ← Subgroup.coe_mul, hss, Subgroup.coe_one]
  have hs1' : (s : ModGL F4.tag F) ≠ 1 := fun h => hs1 (Subtype.ext h)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzcard, htcard, -⟩ :=
    large_Ree_two_involution_centralizers 2 (by norm_num) F hF
  have hconj : ∀ s₀ : ModGL F4.tag F, ∀ x ∈ F4.reeGamma F 2, x * (s : ModGL F4.tag F) * x⁻¹ = s₀ →
      Nat.card (F4.reeGamma F 2 ⊓ Subgroup.centralizer {s₀} : Subgroup (ModGL F4.tag F)) =
        Nat.card (Subgroup.centralizer ({s} : Set (F4.reeGamma F 2))) := by
    intro s₀ x hx hxs
    rw [card_centralizer_subtype_eq_card_inf, ← hxs]
    exact card_inf_centralizer_conj hx
  rcases (large_Ree_every_involution_fuses 2 (by norm_num) F hF).1 s s.2 hs2 hs1' with
    ⟨x, hx, hxs⟩ | ⟨x, hx, hxs⟩
  · rw [sylowH_zero_eq_centralZ] at hxs
    rw [← hconj _ x hx hxs, hzcard]
    exact not_fifteen_dvd_centralizer_orders.1
  · rw [← hconj _ x hx hxs, htcard]
    exact not_fifteen_dvd_centralizer_orders.2

theorem reeF4InvolutionCentralizerCoprime_of_certs :
    Coordinator.ReeF4InvolutionCentralizerCoprime := by
  intro K _ _ d hd e s hs1 hss
  obtain ⟨F, _, _, _, hF, ⟨eΓ⟩⟩ := exists_reeGamma_model hd e
  have hs1' : eΓ s ≠ 1 := fun h => hs1 (eΓ.injective (by rw [h, map_one]))
  have hss' : eΓ s * eΓ s = 1 := by rw [← map_mul, hss, map_one]
  rw [← card_centralizer_equiv eΓ s]
  exact not_fifteen_dvd_card_centralizer_reeGamma hF (eΓ s) hs1' hss'

end CFSG.HardMathSupport.Malle.LocalAction
