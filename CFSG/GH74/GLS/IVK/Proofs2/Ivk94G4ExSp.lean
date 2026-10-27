module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Assembly
public import CFSG.GH74.Generic.GKFMcL
public import CFSG.GH74.Generic.GKFLy
public import CFSG.GH74.Generic.S45.LEvSporFacts

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

theorem comm_of_sq_eq_one {G : Type*} [Group G] (h : ∀ x : G, x ^ 2 = 1) (x y : G) :
    x * y = y * x := by
  have hxy : (x * y) * (x * y) = 1 := by rw [← pow_two]; exact h _
  have hx : x * x = 1 := by rw [← pow_two]; exact h x
  have hy : y * y = 1 := by rw [← pow_two]; exact h y
  have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  rw [mul_inv_rev, hxi, hyi] at h1
  exact h1.symm

theorem false_of_E16 {K : Type} [Group K] [Finite K] (htwo : Open.twoRank K = 3) (E : Subgroup K)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hcard : Nat.card E = 16) : False := by
  have hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have := comm_of_sq_eq_one (G := ↥E) (fun a => Subtype.ext (hE2 a a.2)) ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have h4 := le_pRank_two_of_comm_sq hc hE2 (k := 4) (by rw [hcard]; norm_num)
  have h1 : Open.twoRank K = CFSG.pRank 2 K :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 2 K).symm
  omega

theorem k94_j2 :
    K94Excl fun K _ => NativeSporadic.IsSporadic K .J2 := by
  intro K _ _ hs hnab hgen htwo ⟨e⟩ z I₁ I₂ F₁ F₂ _ _ _ _ cfg
  have hF : Generic.S45.J2Facts (⊤ : Subgroup K) :=
    Generic.S45.J2Facts.of_equiv ((Subgroup.topEquiv (G := K)).trans (e.trans j2PermEquiv))
      Generic.S45.EvSpor.j2_facts
  obtain ⟨-, -, -, -, E, -, -, -, -, -, -, -, -, -, -, -, -, -, hEa, hE16⟩ := hF
  have := hEa
  exact false_of_E16 htwo E (fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx) hE16


theorem false_of_E16_equiv {K G : Type} [Group K] [Finite K] [Group G] (e : K ≃* G)
    (htwo : Open.twoRank K = 3) (E : Subgroup G) (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hcard : Nat.card E = 16) : False := by
  refine false_of_E16 htwo (E.map e.symm.toMonoidHom) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hcard]

theorem k94_mcl_ly :
    K94Excl fun K _ => NativeSporadic.IsSporadic K .McL ∨ NativeSporadic.IsSporadic K .Ly := by
  intro K _ _ hs hnab hgen htwo hP z I₁ I₂ F₁ F₂ _ _ _ _ cfg
  rcases hP with he | he
  · obtain ⟨e⟩ := he
    obtain ⟨ev, h1, h2, h3, h4⟩ := Generic.exists_e_McL
    obtain ⟨E, hcard, hsq, -, -⟩ :=
      @KGroups.exists_E16 NativeSporadic.McL inferInstance ev h1 h2 h3 h4
    exact @false_of_E16_equiv K NativeSporadic.McL _ _ inferInstance e htwo E hsq hcard
  · obtain ⟨e⟩ := he
    obtain ⟨ev, h1, h2, h3, h4⟩ := Generic.exists_e_Ly
    obtain ⟨E, hcard, hsq, -, -⟩ :=
      @KGroups.exists_E16 NativeSporadic.Ly inferInstance ev h1 h2 h3 h4
    exact @false_of_E16_equiv K NativeSporadic.Ly _ _ inferInstance e htwo E hsq hcard

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
