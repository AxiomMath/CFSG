module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyOutFinal
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyCover
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Subgroup Equiv Equiv.Perm CFSG CFSG.Blueprint CFSG.Sporadic.Recognition.LyonsSims
  CFSG.GH74.GLS.Stage2.Bender.Thm1

@[expose] def LyThreeInvStar : Prop :=
  ∀ (X : Type) [Group X] [Finite X], NativeSporadic.IsSporadic X .Ly →
    ∀ A : Subgroup X, Nat.card ↥A = 2 ^ 8 → ∀ τ : X, τ ∈ A → orderOf τ = 2 →
      (∀ a ∈ A, a * τ = τ * a) → ∀ W : Subgroup X, IsPGroup 3 ↥W → W ≠ ⊥ →
        A ≤ normalizer (W : Set X) → W ⊓ centralizer ({τ} : Set X) ≠ ⊥

theorem exists_mem_normalizer_not_mem {X : Type*} [Group X] {U V : Subgroup X} [Finite ↥U]
    (hU : IsPGroup 3 ↥U) (hVU : V ≤ U) (hne : ¬ U ≤ V) :
    ∃ u ∈ U, u ∉ V ∧ u ∈ normalizer (V : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnil : Group.IsNilpotent ↥U := hU.isNilpotent
  have hNC := Group.normalizerCondition_of_isNilpotent (G := ↥U)
  obtain ⟨u₀, hu₀U, hu₀V⟩ := Set.not_subset.1 hne
  have hlt : V.subgroupOf U < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hu₀V ?_
    have : (⟨u₀, hu₀U⟩ : ↥U) ∈ V.subgroupOf U := by rw [h]; trivial
    exact this
  have hlt' := hNC _ hlt
  obtain ⟨g, hgN, hgH⟩ := Set.exists_of_ssubset hlt'
  refine ⟨g.1, g.2, fun hg => hgH hg, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    have h1 := (Subgroup.mem_normalizer_iff.1 hgN) ⟨v, hVU hv⟩
    exact h1.1 hv
  · intro hv
    have hvU : v ∈ U := by
      have : g.1 * v * g.1⁻¹ ∈ U := hVU hv
      have h2 := U.mul_mem (U.inv_mem g.2) (U.mul_mem this g.2)
      simpa [mul_assoc] using h2
    exact (Subgroup.mem_normalizer_iff.1 hgN ⟨v, hvU⟩).2 hv

theorem card_centralizer_of_normalizes_sylow
    {Y : Type} [Group Y] [Finite Y] (hY : Nonempty (Y ≃* NativeSporadic.Ly))
    {x : Y} (hx3 : orderOf x = 3) {A : Subgroup Y} (hA : Nat.card ↥A = 2 ^ 8)
    (hAn : A ≤ normalizer (zpowers x : Set Y)) :
    Nat.card ↥(centralizer ({x} : Set Y)) = 2694384000 := by
  classical
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly hY)
  obtain ⟨x₁, x₂, x₃, S⟩ := D.exists_lyStd
  have hconj : IsConj x (x₁ : Y) := isConj_x₁_of_normalizes_sylow hY D S hx3 hA hAn
  have hcen := D.center_centralizer S
  have hc3 := D.card_center_centralizer S
  obtain ⟨eM⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  set M : Subgroup Y := centralizer ({(x₁ : Y)} : Set Y) with hMdef
  have e : ↥M ⧸ center ↥M ≃* NativeSporadic.McL :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans eM
  have hcardM : Nat.card ↥M = 2694384000 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥M)
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL, hc3] at h1
    omega
  rw [CFSG.Sporadic.Recognition.JankoWong.card_centralizer_eq_of_isConj hconj]
  exact hcardM

theorem lyInvariantThree_of_star_of_outer
    (hOut : LyThreeAOuter) (hStar : LyThreeInvStar) : LyInvariantThree := by
  classical
  intro X _ _ hX A hA W W' hW hW' hW1 hW1' hnW hnW'
  obtain ⟨e⟩ := hX
  have hXne : Nonempty (X ≃* NativeSporadic.Ly) := ⟨e⟩
  obtain ⟨τ, hτA, hτ2, hτc, hτu, hτcomm⟩ := exists_central_involution_sylow_ly hXne hA
  have hAK : A ≤ centralizer ({τ} : Set X) := fun a ha => by
    rw [mem_centralizer_singleton_iff]
    exact hτc a ha
  have key : ∀ U : Subgroup X, IsPGroup 3 ↥U → U ≠ ⊥ → A ≤ normalizer (U : Set X) →
      U ≤ centralizer ({τ} : Set X) := by
    intro U hU hU1 hAU
    set V : Subgroup X := U ⊓ centralizer ({τ} : Set X) with hVdef
    have hV1 : V ≠ ⊥ := hStar X ⟨e⟩ A hA τ hτA hτ2 hτc U hU hU1 hAU
    have hVK : V ≤ centralizer ({τ} : Set X) := inf_le_right
    have hVU : V ≤ U := inf_le_left
    have hVp : IsPGroup 3 ↥V := hU.to_le hVU
    have hAV : A ≤ normalizer (V : Set X) :=
      le_trans (le_inf hAU (hAK.trans Subgroup.le_normalizer)) inf_normalizer_le_normalizer_inf
    obtain ⟨-, hV3⟩ := ly_centralizer_cover_unique hXne hτ2 hAK hA hVK hVK hVp hVp hV1 hV1 hAV hAV
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hV1
    have hx1' : (x : X) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hx3 : orderOf (x : X) = 3 := by
      rw [Subgroup.orderOf_coe]
      have hd : orderOf x ∣ Nat.card ↥V := orderOf_dvd_natCard x
      rw [hV3] at hd
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hx1
      · exact h
    have hVx : V = zpowers (x : X) := by
      symm
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 x.2) ?_
      rw [hV3, Nat.card_zpowers, hx3]
    have hAx : A ≤ normalizer (zpowers (x : X) : Set X) := by rw [← hVx]; exact hAV
    have hxc := card_centralizer_of_normalizes_sylow hXne hx3 hA hAx
    have hAW₁ : A ≤ normalizer ((U ⊓ normalizer (V : Set X) : Subgroup X) : Set X) :=
      le_trans (le_inf hAU (hAV.trans Subgroup.le_normalizer))
        inf_normalizer_le_normalizer_inf
    have hW₁x : U ⊓ normalizer (V : Set X) ≤ zpowers (x : X) :=
      hOut X hXne (x : X) hx3 hxc A hA hAx (U ⊓ normalizer (V : Set X))
        (hU.to_le inf_le_left) (by rw [← hVx]; exact inf_le_right) hAW₁
    have hUV : U ≤ V := by
      by_contra hne
      obtain ⟨u, huU, huV, huN⟩ := exists_mem_normalizer_not_mem hU hVU hne
      exact huV (by rw [hVx]; exact hW₁x ⟨huU, huN⟩)
    exact hUV.trans hVK
  exact ly_centralizer_cover_unique hXne hτ2 hAK hA (key W hW hW1 hnW) (key W' hW' hW1' hnW')
    hW hW' hW1 hW1' hnW hnW'

theorem lyInvariantThree_of_star
    (hStar : LyThreeInvStar) : LyInvariantThree :=
  lyInvariantThree_of_star_of_outer lyThreeAOuter_thm hStar

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
