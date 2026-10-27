module

public import CFSG.CGT.PushingUpLit.SolKNA.Lemma18Amb

public section

open scoped IsMulCommutative

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n
open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule Matrix
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] [CharP F 2]

namespace Lemma17Psl

variable {ψ : X →* SL(2, F)} {N R : Subgroup X} (D : Lemma17Psl ψ N R)
include D

theorem second_coord_eq_zero {θ : (Fin 2 → F) → X} (hθinj : Function.Injective θ)
    (hθ : ∀ (x : X) (v : Fin 2 → F),
      θ ((ψ x : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = x * θ v * x⁻¹)
    {v : Fin 2 → F} (hv : ∀ r ∈ R, r * θ v = θ v * r) : v 1 = 0 := by
  refine (forall_upperElt_mulVec_eq_iff v).mp fun t => ?_
  obtain ⟨r, hr, hrt⟩ := D.exists_mem_of_upper t
  have h2 : θ ((ψ r : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = θ v := by
    rw [hθ, hv r hr]
    group
  rw [← hrt]
  exact hθinj h2

end Lemma17Psl

namespace Prop18Setup

variable {R Rb L Lb N : Subgroup X} (S : Prop18Setup R Rb L Lb N)
include S

theorem exists_normalizer_conj_of_four
    (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) [N.Normal]
    (hrel : L.relIndex R = 4) (hL4 : Nat.card L = 4) :
    ∀ z ∈ L, z ≠ 1 → ∀ z' ∈ L, z' ≠ 1 →
      ∃ k : X, k ∈ Subgroup.normalizer (R : Set X) ∧ k * z * k⁻¹ = z' := by
  classical
  obtain ⟨-, hmod⟩ := S.exists_models hCen hU
  rcases hmod with ⟨f, hf, hrel', ⟨e⟩⟩ | ⟨a, ha, hrel', -⟩ | ⟨m, hm, h3, hrel', -⟩
  swap
  · exfalso
    have h4 : 2 ^ (2 * a + 1) = 4 := hrel'.symm.trans hrel
    have h : 2 ^ (2 * a + 1) = 2 ^ 2 := by simp [h4]
    have := Nat.pow_right_injective le_rfl h
    omega
  swap
  · exfalso
    rw [hrel] at hrel'
    omega
  have hf2 : f = 2 := by
    have h4 : 2 ^ f = 4 := hrel'.symm.trans hrel
    exact Nat.pow_right_injective le_rfl (show 2 ^ f = 2 ^ 2 by simp [h4])
  subst hf2
  obtain ⟨F, hF, hFin, hchar, ψ, hcard, hψs, hψk, hψR, s, hs, hsN, hW⟩ := S.struct_psl hf e
  have hD := S.lemma17Psl hψs hψk hψR hs hsN fun W hW' => ⟨(hW W hW').2.1, (hW W hW').2.2.2.2⟩
  have hNcard : Nat.card N = 16 := by
    rw [S.card_N, S.card_eq, hL4]
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.sup_empty] at hsN
    have h1 : Nat.card N = 1 := by rw [← hsN]; exact Subgroup.card_bot
    omega
  obtain ⟨W, hWs⟩ := hsne
  obtain ⟨hWN, -, -, -, θ, hθadd, hθinj, hθr, hθ⟩ := hW W hWs
  have hWcard : Nat.card W = 16 := by
    have h1 : Nat.card W = Nat.card (Set.range θ) := by rw [hθr]; rfl
    rw [h1, ← Nat.card_congr (Equiv.ofInjective θ hθinj), Nat.card_fun, hcard]
    simp
  have hWeq : W = N := (Subgroup.eq_of_le_of_card_ge hWN (by rw [hWcard, hNcard])).symm.symm
  have hθ0 : θ 0 = 1 := by
    have := hθadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  have hLθ : ∀ z ∈ L, z ≠ 1 → ∃ a : F, a ≠ 0 ∧ z = θ ![a, 0] := by
    intro z hz hz1
    have hzN : z ∈ W := hWeq ▸ S.L_le_N hz
    obtain ⟨v, rfl⟩ : z ∈ Set.range θ := hθr ▸ hzN
    have hv1 : v 1 = 0 := hD.second_coord_eq_zero hθinj hθ fun r hr => (S.L_cent _ hz r hr).symm
    have hv : v = ![v 0, 0] := by
      ext i
      fin_cases i <;> simp [hv1]
    refine ⟨v 0, fun h0 => hz1 ?_, by rw [← hv]⟩
    have : v = 0 := by rw [hv, h0]; ext i; fin_cases i <;> simp
    rw [this, hθ0]
  intro z hz hz1 z' hz' hz'1
  obtain ⟨a, ha0, rfl⟩ := hLθ z hz hz1
  obtain ⟨a', ha'0, rfl⟩ := hLθ z' hz' hz'1
  obtain ⟨k, hk⟩ := hψs (diagElt (Units.mk0 (a' / a) (div_ne_zero ha'0 ha0)))
  refine ⟨k, hD.mem_normalizer_R hk, ?_⟩
  rw [hD.conj_theta hθ hk (by simp)]
  congr 1
  ext i
  fin_cases i
  · show a' / a * a = a'
    field_simp
  · rfl

end Prop18Setup

variable {G : Type} [Group G] [Finite G]

theorem lemma18_exists_normalizer_conj_of_four
    (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {R : Subgroup G} {g : G} {Z : Subgroup G} (hgZ : g ∈ Z) (hRZ : R ≤ Z)
    (hR2 : IsPGroup 2 R) (hTI : IsTIIn Z R)
    {T C N : Subgroup G}
    (hT : T = conjSubgroup g R ⊓ Subgroup.normalizer (R : Set G)) (hT0 : T ≠ ⊥)
    (hinf : R ⊓ conjSubgroup g R = ⊥)
    (hC : C = R ⊓ Subgroup.centralizer (T : Set G))
    (hΦ₁ : ∀ x ∈ R, x * x ∈ C) (hΦ₂ : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ C)
    (hCZ : ∀ c ∈ C, ∀ x ∈ R, c * x = x * c)
    (hCT : Nonempty (↥C ≃* ↥T)) (hT2 : ∀ x ∈ T, x * x = 1) (hCR : C ≠ R)
    (hrel : C.relIndex R = 4) (hT4 : Nat.card T = 4)
    (hN : N = C ⊔ T) (hNnorm : R ⊔ conjSubgroup g R ≤ Subgroup.normalizer (N : Set G))
    (hΦb₁ : ∀ x ∈ conjSubgroup g R, x * x ∈ T)
    (hΦb₂ : ∀ x ∈ conjSubgroup g R, ∀ y ∈ conjSubgroup g R, x * y * x⁻¹ * y⁻¹ ∈ T)
    (hTZ : ∀ t ∈ T, ∀ x ∈ conjSubgroup g R, t * x = x * t) :
    ∀ z ∈ C, z ≠ 1 → ∀ z' ∈ C, z' ≠ 1 →
      ∃ k ∈ R ⊔ conjSubgroup g R, k ∈ Subgroup.normalizer (R : Set G) ∧ k * z * k⁻¹ = z' := by
  have S := prop18Setup_of_ambient hgZ hRZ hR2 hTI hT hT0 hinf hC hΦ₁ hΦ₂ hCZ hCT hT2 hCR hN
    hNnorm hΦb₁ hΦb₂ hTZ
  have := S.normal
  have hCR' : C ≤ R := hC ▸ inf_le_left
  have hCY : C ≤ R ⊔ conjSubgroup g R := hCR'.trans le_sup_left
  obtain ⟨e⟩ := hCT
  have hCT4 : Nat.card C = 4 := by rw [Nat.card_congr e.toEquiv, hT4]
  have hrel' : (C.subgroupOf (R ⊔ conjSubgroup g R)).relIndex
      (R.subgroupOf (R ⊔ conjSubgroup g R)) = 4 := by
    rw [relIndex_subgroupOf_of_le hCR' le_sup_left, hrel]
  have hL4 : Nat.card (C.subgroupOf (R ⊔ conjSubgroup g R)) = 4 := by
    rw [card_subgroupOf_of_le hCY, hCT4]
  intro z hz hz1 z' hz' hz'1
  obtain ⟨k, hkN, hk⟩ := S.exists_normalizer_conj_of_four hCen hU hrel' hL4 ⟨z, hCY hz⟩
    (Subgroup.mem_subgroupOf.mpr hz) (fun h => hz1 (congrArg Subtype.val h)) ⟨z', hCY hz'⟩
    (Subgroup.mem_subgroupOf.mpr hz') (fun h => hz'1 (congrArg Subtype.val h))
  refine ⟨k, k.2, ?_, congrArg Subtype.val hk⟩
  have : k ∈ (Subgroup.normalizer (R : Set G)).subgroupOf (R ⊔ conjSubgroup g R) := by
    rw [Subgroup.subgroupOf_normalizer_eq le_sup_left]
    exact hkN
  exact Subgroup.mem_subgroupOf.mp this

end CFSG.CGT.PushingUpLit.SolKNA
