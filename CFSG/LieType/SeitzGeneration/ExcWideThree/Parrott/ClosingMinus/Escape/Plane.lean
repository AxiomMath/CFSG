module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.Sylow
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddBClose
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddBClass
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddGType
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19

section Plane


theorem isGLine_conj {X : Type} [Field X] [Finite X] {σ : X ≃+* X} {γ : MulAut (C0 σ)}
    (hγ : TriOddIsGLine σ γ) (ψ : MulAut (C0 σ)) : TriOddIsGLine σ (ψ * γ * ψ⁻¹) := by
  obtain ⟨φ, hφ⟩ := hγ
  refine ⟨φ * ψ⁻¹, ?_⟩
  have e : φ * ψ⁻¹ * (ψ * γ * ψ⁻¹) * (φ * ψ⁻¹)⁻¹ = φ * γ * φ⁻¹ := by group
  rw [e]
  exact hφ

theorem closure_fixUnion_eq_top_minus (hT : TwoLineGen) (hN : OuterToralForm) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 2)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (E : Subgroup (MulAut (C0 σ))) (x : C0 σ)
    (hE : CFSG.IsElementaryAbelian 3 E) (hcard : Nat.card E = 3 ^ 2)
    (hout : ¬ E ≤ innerAut (C0 σ)) (hng : ¬ TriOddHasGLine σ E) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hcx : MulAut.conj x ∈ E) (hX : TriOddIsClassX σ x) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  classical
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
  have hinj : Function.Injective (MulAut.conj : C0 σ →* MulAut (C0 σ)) := nf1_conj_injective hZ
  haveI : Finite (C0 σ) := by
    have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
    exact Finite.of_injective (fun x : C0 σ => (x : ModGL TwistTag.D4.tag K)) Subtype.val_injective
  obtain ⟨β, hβE, hβout⟩ : ∃ β ∈ E, β ∉ innerAut (C0 σ) := by
    by_contra hcon
    push Not at hcon
    exact hout hcon
  have hβ3 : β ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) β hβE
  have hβ1 : β ≠ 1 := fun h => hβout (h ▸ one_mem _)
  have hβcx : β * MulAut.conj x = MulAut.conj x * β := elemAb_comm hE _ hβE _ hcx
  have hβx : β x = x := by
    have h2 := aut_conj_conj β x
    apply hinj
    rw [← h2, hβcx, mul_inv_cancel_right]
  by_cases hc : ∃ γ : MulAut (C0 σ), TriOddIsGLine σ γ ∧ ∀ α ∈ E, α * γ = γ * α
  · obtain ⟨γ, hγ, hγc⟩ := hc
    exact triOdd_closure_fixUnion_eq_top_of_central_gline σ hℓ hℓ2 hℓ3 hf hK hσ E hE hcard hout γ
      hγ hγc (fun hγE => hng ⟨γ, hγE, hγ⟩)
  obtain ⟨s, hsβ, hs3, hsG⟩ :=
    hN ℓ f hℓ hℓ2 hℓ3 hf hq K hK σ hσ β hβ3 hβout (fun h => hng ⟨β, hβE, h⟩)
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcx1 : MulAut.conj x ≠ 1 := fun h => hx1 (hinj (h.trans (map_one MulAut.conj).symm))
  have hcx3 : MulAut.conj x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hEcl : E = Subgroup.closure ({MulAut.conj x, β} : Set (MulAut (C0 σ))) :=
    nf1_closure_pair_eq E hcard hcx hβE hcx1 hcx3 hβ1 (fun h => hβout ⟨x, h.symm⟩)
      (fun h => hβout ⟨x ^ 2, by rw [map_pow]; exact h.symm⟩)
  set Y : Subgroup (C0 σ) := fixedSubgroup β with hY
  rcases exists_conj_comm_or_fusion (G := Y) (x := ⟨x, hβx⟩) (s := ⟨s, hsβ⟩)
      (Subtype.ext (by simpa using hx3)) (fun h => hx1 (congrArg Subtype.val h))
      (Subtype.ext (by simpa using hs3)) with ⟨g, hg⟩ | ⟨g, hg1, hg2⟩
  ·
    exfalso
    apply hc
    set t : C0 σ := (g : C0 σ) * s * (g : C0 σ)⁻¹ with ht
    have htx : t * x = x * t := by
      have := congrArg Subtype.val hg
      simpa [ht] using this
    have hgβ : β (g : C0 σ) = g := g.2
    have hcg : β * MulAut.conj (g : C0 σ) = MulAut.conj (g : C0 σ) * β := by
      have h2 := aut_conj_conj β (g : C0 σ)
      rw [hgβ] at h2
      exact mul_inv_eq_iff_eq_mul.1 h2
    have htβ : β t = t := by
      rw [ht, map_mul, map_mul, map_inv, hgβ, hsβ]
    have hct : β * MulAut.conj t = MulAut.conj t * β := by
      have h2 := aut_conj_conj β t
      rw [htβ] at h2
      exact mul_inv_eq_iff_eq_mul.1 h2
    have hctx : MulAut.conj t * MulAut.conj x = MulAut.conj x * MulAut.conj t := by
      rw [← map_mul, ← map_mul, htx]
    refine ⟨(MulAut.conj t)⁻¹ * β, ?_, ?_⟩
    · have e : (MulAut.conj t)⁻¹ * β =
          MulAut.conj (g : C0 σ) * ((MulAut.conj s)⁻¹ * β) * (MulAut.conj (g : C0 σ))⁻¹ := by
        have e1 : MulAut.conj t = MulAut.conj (g : C0 σ) * MulAut.conj s *
            (MulAut.conj (g : C0 σ))⁻¹ := by
          rw [ht, map_mul, map_mul, map_inv]
        have e2 : β * (MulAut.conj (g : C0 σ))⁻¹ = (MulAut.conj (g : C0 σ))⁻¹ * β :=
          (Commute.inv_right (show Commute β (MulAut.conj (g : C0 σ)) from hcg)).eq
        rw [e1]
        calc (MulAut.conj (g : C0 σ) * MulAut.conj s * (MulAut.conj (g : C0 σ))⁻¹)⁻¹ * β
            = MulAut.conj (g : C0 σ) * (MulAut.conj s)⁻¹ * ((MulAut.conj (g : C0 σ))⁻¹ * β) := by
              group
          _ = MulAut.conj (g : C0 σ) * (MulAut.conj s)⁻¹ * (β * (MulAut.conj (g : C0 σ))⁻¹) := by
              rw [e2]
          _ = _ := by group
      rw [e]
      exact isGLine_conj hsG _
    · have h1 : MulAut.conj x * (MulAut.conj t)⁻¹ = (MulAut.conj t)⁻¹ * MulAut.conj x :=
        (Commute.inv_right (show Commute (MulAut.conj x) (MulAut.conj t) from hctx.symm)).eq
      have h2 : β * (MulAut.conj t)⁻¹ = (MulAut.conj t)⁻¹ * β :=
        (Commute.inv_right (show Commute β (MulAut.conj t) from hct)).eq
      have hle : E ≤ Subgroup.centralizer {(MulAut.conj t)⁻¹ * β} := by
        rw [hEcl, Subgroup.closure_le]
        rintro a (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        · calc MulAut.conj x * ((MulAut.conj t)⁻¹ * β)
              = (MulAut.conj t)⁻¹ * (MulAut.conj x * β) := by rw [← mul_assoc, h1, mul_assoc]
            _ = (MulAut.conj t)⁻¹ * β * MulAut.conj x := by rw [← hβcx, mul_assoc]
        · rw [← mul_assoc, h2, mul_assoc]
      exact fun α hα => Subgroup.mem_centralizer_singleton_iff.1 (hle hα)
  ·
    set H := Subgroup.closure (fixUnion E) with hH
    have hCH : Subgroup.centralizer ({x} : Set (C0 σ)) ≤ H := by
      intro w hw
      refine Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hcx hcx1 ?_)
      have h := Subgroup.mem_centralizer_singleton_iff.1 hw
      show x * w * x⁻¹ = w
      rw [← h, mul_inv_cancel_right]
    have hgH : (g : C0 σ) ∈ H := Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hβE hβ1 g.2)
    have hcomm : ((g : C0 σ) * x * (g : C0 σ)⁻¹) * x = x * ((g : C0 σ) * x * (g : C0 σ)⁻¹) := by
      have := congrArg Subtype.val hg1
      simpa using this
    have hnot : (g : C0 σ) * x * (g : C0 σ)⁻¹ ∉ Subgroup.zpowers x := by
      intro hmem
      apply hg2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
      refine Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext ?_⟩
      simpa using hn
    exact hT ℓ f hℓ hℓ2 hℓ3 hf hq K hK σ hσ x g hx3 hx1 hX hcomm hnot H hCH hgH

theorem triOddXNoG_of_inputs (hT : TwoLineGen) (hN : OuterToralForm) : TriOddXNoG := by
  intro ℓ f hℓ hℓ2 hℓ3 hf K _ _ hK σ hσ E x hE hcard hout hng hx3 hx1 hcx hX
  classical
  rcases (by omega : (ℓ ^ f) % 3 = 0 ∨ (ℓ ^ f) % 3 = 1 ∨ (ℓ ^ f) % 3 = 2) with hq | hq | hq
  · exfalso
    exact hℓ3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.dvd_of_mod_eq_zero hq))).symm)
  · obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
      odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
    have hinj : Function.Injective (MulAut.conj : C0 σ →* MulAut (C0 σ)) := nf1_conj_injective hZ
    obtain ⟨β, hβE, hβout⟩ : ∃ β ∈ E, β ∉ innerAut (C0 σ) := by
      by_contra hcon
      push Not at hcon
      exact hout hcon
    have hβ3 : β ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) β hβE
    have hβ1 : β ≠ 1 := fun h => hβout (h ▸ one_mem _)
    have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
    have hβx : β x = x := by
      have h1 := elemAb_comm hE _ hβE _ hcx
      have h2 := aut_conj_conj β x
      apply hinj
      rw [← h2, h1, mul_inv_cancel_right]
    have hNA := (triOdd_d4OuterThree ℓ f hℓ hℓ2 hℓ3 hf K hK σ hσ β hβord hβout).1
    obtain ⟨y, hyβ, hyx⟩ := triOdd_exists_fixed_not_mem_zpowers hNA hβx hx1
    have hyH : y ∈ Subgroup.closure (fixUnion E) :=
      Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hβE hβ1 hyβ)
    have hcx1 : MulAut.conj x ≠ 1 := fun h => hx1 (hinj (h.trans (map_one MulAut.conj).symm))
    have hCH : Subgroup.centralizer ({x} : Set (C0 σ)) ≤ Subgroup.closure (fixUnion E) := by
      intro w hw
      refine Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hcx hcx1 ?_)
      have h := Subgroup.mem_centralizer_singleton_iff.1 hw
      show x * w * x⁻¹ = w
      rw [← h, mul_inv_cancel_right]
    exact triOddClosingXPlus_holds ℓ f hℓ hℓ2 hℓ3 hf hq K hK σ hσ x hx3 hx1 hX _ hCH ⟨y, hyH, hyx⟩
  · exact closure_fixUnion_eq_top_minus hT hN hℓ hℓ2 hℓ3 hf hq hK σ hσ E x hE hcard hout hng hx3
      hx1 hcx hX

theorem trialityThreePlanesOdd_of_inputs (hT : TwoLineGen) (hN : OuterToralForm) :
    TrialityThreePlanesOdd :=
  trialityThreePlanesOdd_of_X (triOddXNoG_of_inputs hT hN)

end Plane

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape
