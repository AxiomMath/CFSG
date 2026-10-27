module

public import CFSG.LargeExtraspecial.S8A5D

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.CGT.Timmesfeld75

universe u

theorem card_le_two_mul_of_coset {Γ : Type*} [Group Γ] [Finite Γ] {A K : Subgroup Γ}
    (h : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ∉ K → a₂ ∉ K → a₁⁻¹ * a₂ ∈ K) :
    Nat.card A ≤ 2 * Nat.card K := by
  by_cases hA : A ≤ K
  · have := Subgroup.card_le_of_le hA
    omega
  obtain ⟨a₀, ha₀A, ha₀K⟩ := IsConcreteLE.not_le_iff_exists.mp hA
  classical
  let f : A → K ⊕ K := fun a =>
    if ha : (a : Γ) ∈ K then Sum.inl ⟨a, ha⟩
    else Sum.inr ⟨a₀⁻¹ * a, h a₀ ha₀A a a.2 ha₀K ha⟩
  have hf : Function.Injective f := by
    intro a b hab
    by_cases ha : (a : Γ) ∈ K <;> by_cases hb : (b : Γ) ∈ K
    · simp only [f, ha, hb, ↓reduceDIte, Sum.inl.injEq, Subtype.mk.injEq] at hab
      exact Subtype.ext hab
    · simp only [f, ha, hb, ↓reduceDIte, reduceCtorEq] at hab
    · simp only [f, ha, hb, ↓reduceDIte, reduceCtorEq] at hab
    · simp only [f, ha, hb, ↓reduceDIte, Sum.inr.injEq, Subtype.mk.injEq] at hab
      exact Subtype.ext (mul_left_cancel hab)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum] at this
  omega

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem conj_comm_of_mem_normalizer_mul (ht : t ∈ S.Lbar g)
    (h5 : ∀ z ∈ S.Mbar, z * t * z⁻¹ ∈ S.Lbar g → z * t * z⁻¹ = t) (k : S.M) {x : S.O}
    (hxM : x ∈ S.Mbar)
    (hx : x ∈ normalizer (S.Lbar ((k : G) * g) : Set S.O)) :
    x * (S.ρ k * t * (S.ρ k)⁻¹) * x⁻¹ = S.ρ k * t * (S.ρ k)⁻¹ := by
  have htk : S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar ((k : G) * g) := by
    rw [Lbar_mul S k g]
    exact ⟨t, ht, rfl⟩
  have h1 := (mem_normalizer_iff.mp hx _).mp htk
  rw [Lbar_mul S k g, mem_map_equiv, MulAut.conj_symm_apply] at h1
  have hzM : (S.ρ k)⁻¹ * x * S.ρ k ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem (inv_mem ⟨k, rfl⟩) hxM) ⟨k, rfl⟩
  have h2 := h5 _ hzM (by
    rw [show (S.ρ k)⁻¹ * x * S.ρ k * t * ((S.ρ k)⁻¹ * x * S.ρ k)⁻¹ =
      (S.ρ k)⁻¹ * (x * (S.ρ k * t * (S.ρ k)⁻¹) * x⁻¹) * S.ρ k by group]
    exact h1)
  calc x * (S.ρ k * t * (S.ρ k)⁻¹) * x⁻¹ =
      S.ρ k * ((S.ρ k)⁻¹ * x * S.ρ k * t * ((S.ρ k)⁻¹ * x * S.ρ k)⁻¹) * (S.ρ k)⁻¹ := by group
    _ = S.ρ k * t * (S.ρ k)⁻¹ := by rw [h2]

theorem card_le_two_mul_card_centralizer_of_linCase (H : Hyp4 S g) (ht : t ∈ S.Lbar g)
    (h5 : ∀ z ∈ S.Mbar, z * t * z⁻¹ ∈ S.Lbar g → z * t * z⁻¹ = t) {y : S.O} (hyM : y ∈ S.Mbar)
    {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Nbar S g t ⊓ conjSubgroup y (S.Lbar g ⊓ Nbar S g t))
    (hL : LinCase S g hτ.1.1) :
    Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) ≤
      2 * Nat.card (S.Lbar g ⊓ Nbar S g t ⊓ centralizer ({y * t * y⁻¹} : Set S.O) :
        Subgroup S.O) := by
  have haQ := H.conj_mem
  have hτL : τ ∈ S.Lbar g := hτ.1.1
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hyM
  have hτk : τ ∈ S.Lbar ((k : G) * g) := by
    rw [Lbar_mul S k g]
    refine ⟨(S.ρ k)⁻¹ * τ * S.ρ k, (mem_conjSubgroup.mp hτ.2).1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  set b := S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) with hb
  have hbV : b ∈ Vt S g τ := cl_mem_Vt hτk
  have hafix : ∀ l ∈ S.Lbar g, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := by
    intro l hl
    have hmem : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar g) := by
      rw [H.fixSub_eq]
      exact Submodule.mem_span_singleton_self _
    exact (mem_fixSub S).mp hmem l hl
  have hmove : ∀ l ∈ S.Lbar g, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b ∈
      (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    intro l hl
    have he : resL haQ hτL ⟨l, hl⟩ ∈ centreGroup (Vt S g τ) (aV hτL) := by
      rw [← hL.LmodN_eq, ← range_resL haQ hτL]
      exact ⟨_, rfl⟩
    have h1 := (mem_centreGroup.mp he) ⟨b, hbV⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    have h2 := congrArg Subtype.val hc
    rw [Submodule.coe_smul, Submodule.coe_sub] at h2
    exact h2
  have hfixb : ∀ l ∈ S.Lbar g, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) b = b →
      l ∈ centralizer ({S.ρ k * t * (S.ρ k)⁻¹} : Set S.O) := by
    intro l hl hlb
    have hlM : l ∈ S.Mbar := S.Lbar_le_Mbar g hl
    have hlN := mem_normalizer_of_fix haQ H.conj_ne (h := k) hlM hlb
    have h1 := conj_comm_of_mem_normalizer_mul ht h5 k hlM hlN
    rw [mem_centralizer_singleton_iff]
    calc l * (S.ρ k * t * (S.ρ k)⁻¹) = l * (S.ρ k * t * (S.ρ k)⁻¹) * l⁻¹ * l := by group
      _ = S.ρ k * t * (S.ρ k)⁻¹ * l := by rw [h1]
  refine card_le_two_mul_of_coset fun a₁ ha₁ a₂ ha₂ h₁ h₂ => ?_
  have hmv : ∀ a ∈ S.Lbar g ⊓ Nbar S g t,
      a ∉ S.Lbar g ⊓ Nbar S g t ⊓ centralizer ({S.ρ k * t * (S.ρ k)⁻¹} : Set S.O) →
        (a : S.Qt ≃ₗ[ZMod 2] S.Qt) b = b + S.cl (g * S.z * g⁻¹) := by
    intro a ha hna
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hmove a ha.1)
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · rw [zero_smul, eq_comm, sub_eq_zero] at hc
      exact absurd (Subgroup.mem_inf.mpr ⟨ha, hfixb a ha.1 hc⟩) hna
    · rw [one_smul] at hc
      rw [hc]
      abel
  have e1 := hmv a₁ ha₁ h₁
  have e2 := hmv a₂ ha₂ h₂
  refine Subgroup.mem_inf.mpr ⟨(mul_mem (inv_mem ha₁) ha₂ : a₁⁻¹ * a₂ ∈ S.Lbar g ⊓ Nbar S g t),
    hfixb _ (mul_mem (inv_mem ha₁.1) ha₂.1) ?_⟩
  have e3 : ((a₁⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (b + S.cl (g * S.z * g⁻¹)) = b := by
    rw [← e1, inv_apply_apply_O]
  rw [coe_mul_apply, e2, e3]

theorem not_linCase_of_good (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {y : S.O} (hyM : y ∈ S.Mbar)
    (hyc : y * t * y⁻¹ * t = t * (y * t * y⁻¹))
    (hnb : ¬ ∀ w ∈ Wt S g t, ((y * t * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
    {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Nbar S g t ⊓ conjSubgroup y (S.Lbar g ⊓ Nbar S g t)) :
    ¬ LinCase S g hτ.1.1 := by
  intro hL
  have hσM : y * t * y⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hyM (S.Lbar_le_Mbar g ht)) (inv_mem hyM)
  have h5 : ∀ z ∈ S.Mbar, z * t * z⁻¹ ∈ S.Lbar g → z * t * z⁻¹ = t := fun z hz h =>
    conj_eq_of_conj_mem_Lbar_A5 hCE hNo hΩ D hm2 hmin hA7 hz h
  have hσV := step1_fix_Vt_A5 hCE hNo hΩ D hm2 hmin hA7 _ ⟨hσM, hyc, y, hyM, rfl⟩
  obtain ⟨hgood, hU⟩ : Vt S g t ⊓ commSpace ((y * t * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ ∧
      (Wt S g t).map (((y * t * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔
        Vt S g t = Vt S g t ⊔ commSpace ((y * t * y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rcases bad_or_good_A5 hCE hNo hΩ D hm2 hmin hyM rfl hyc hσV with h | h
    · exact absurd h hnb
    · exact h
  have htN := self_mem_Nbar H ht
  have hF : ∀ α ∈ S.Lbar g ⊓ Nbar S g t,
      α ∈ normalizer (conjSubgroup y (S.Lbar g ⊓ Nbar S g t) : Set S.O) →
        α * (y * t * y⁻¹) = y * t * y⁻¹ * α := fun α hα h =>
    comm_of_mem_normalizer_conj ht htN h5 hyM (S.Lbar_le_Mbar g hα.1) h
  have h4 := four_mul_card_le_of_good hCE hNo hΩ D hm2 hyM rfl hyc hσV hgood hU hF
  have hle : S.Lbar g ⊓ Nbar S g t ⊓ centralizer ({y * t * y⁻¹} : Set S.O) ≤
      S.Lbar g ⊓ Nbar S g t ⊓
        normalizer (conjSubgroup y (S.Lbar g ⊓ Nbar S g t) : Set S.O) := by
    rintro α ⟨hα, hαc⟩
    exact ⟨hα, mem_normalizer_conj_of_good D hyM rfl hσV hgood hα
      (mem_centralizer_singleton_iff.mp hαc)⟩
  have h6 := Subgroup.card_le_of_le hle
  have h7 := card_le_two_mul_card_centralizer_of_linCase H ht h5 hyM hτ hL
  have hpos : 0 < Nat.card (S.Lbar g ⊓ Nbar S g t ⊓ centralizer ({y * t * y⁻¹} : Set S.O) :
    Subgroup S.O) := Nat.card_pos
  omega

end CFSG.LargeExtraspecial.S8
