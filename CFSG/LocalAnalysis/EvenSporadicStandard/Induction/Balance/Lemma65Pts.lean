module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65ShortOrbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Even

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Wong77
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.EvenSporadicStandard.Wong77.Module (Cocode pt coMk cocodeRep golayRep golayEven golayCode)
open scoped IsMulCommutative

section Xset

variable {Γ : Type} [Group Γ] {E H₁ : Subgroup Γ} {e : Γ}

@[expose] def Xset (E H₁ : Subgroup Γ) (e : Γ) : Set ↥(E.subgroupOf H₁) :=
  {n | ∃ ω ∈ omega e, ω ≠ e ∧ ((n : ↥H₁) : Γ) = ω * e}

@[expose] def toN (hS : Setting65 Γ E H₁ e) {ω : Γ} (hω : ω ∈ omega e) (hB : ω * e ∈ H₁) :
    ↥(E.subgroupOf H₁) :=
  ⟨⟨ω * e, hB⟩, mem_subgroupOf.2 (E.mul_mem (hS.omega_subset_E hω) hS.mem)⟩

namespace Setting65

variable [Finite Γ] (hS : Setting65 Γ E H₁ e)
include hS

theorem mul_e_mem_H₁ : ∀ w ∈ omega e, w ≠ e → w * e ∈ H₁ :=
  hS.eps_dichotomy.resolve_left hS.not_forall_mem_H₁

theorem Xset_ncard : (Xset E H₁ e).ncard = 23 := by
  have hval : Function.Injective fun n : ↥(E.subgroupOf H₁) => ((n : ↥H₁) : Γ) :=
    Subtype.val_injective.comp Subtype.val_injective
  have himg : (fun n : ↥(E.subgroupOf H₁) => ((n : ↥H₁) : Γ)) '' Xset E H₁ e =
      (fun ω => ω * e) '' (omega e \ {e}) := by
    ext y
    constructor
    · rintro ⟨n, ⟨ω, hω, hne, hv⟩, rfl⟩
      exact ⟨ω, ⟨hω, hne⟩, hv.symm⟩
    · rintro ⟨ω, ⟨hω, hne⟩, rfl⟩
      exact ⟨toN hS hω (hS.mul_e_mem_H₁ ω hω hne), ⟨ω, hω, hne, rfl⟩, rfl⟩
  rw [← Set.ncard_image_of_injective _ hval, himg,
    Set.ncard_image_of_injective _ (mul_left_injective e), hS.ncard_X]

omit [Finite Γ] in
theorem Xset_conj [(E.subgroupOf H₁).Normal] (k : ↥H₁) {n : ↥(E.subgroupOf H₁)}
    (hn : n ∈ Xset E H₁ e) : MulAut.conjNormal k n ∈ Xset E H₁ e := by
  obtain ⟨ω, hω, hne, hv⟩ := hn
  have hc : (k : Γ) * e = e * k := hS.commute_of_mem_H₁ k.2
  have hke : (k : Γ) * e * (k : Γ)⁻¹ = e := by rw [hc]; group
  refine ⟨(k : Γ) * ω * (k : Γ)⁻¹, conj_mem_omega hω k, ?_, ?_⟩
  · intro h
    apply hne
    calc ω = (k : Γ)⁻¹ * ((k : Γ) * ω * (k : Γ)⁻¹) * k := by group
      _ = (k : Γ)⁻¹ * e * k := by rw [h]
      _ = e := by rw [mul_assoc, ← hc]; group
  · have h1 : (((MulAut.conjNormal k n : ↥(E.subgroupOf H₁)) : ↥H₁) : Γ) =
        (k : Γ) * ((n : ↥H₁) : Γ) * (k : Γ)⁻¹ := by
      rw [MulAut.conjNormal_apply]
      rfl
    rw [h1, hv]
    calc (k : Γ) * (ω * e) * (k : Γ)⁻¹ = ((k : Γ) * ω * (k : Γ)⁻¹) * ((k : Γ) * e * (k : Γ)⁻¹) := by
          group
      _ = ((k : Γ) * ω * (k : Γ)⁻¹) * e := by rw [hke]

end Setting65

end Xset

section Orbit

variable {Γ : Type} [Group Γ] {E H₁ : Subgroup Γ} {e : Γ} [Finite Γ]
  [(E.subgroupOf H₁).Normal] [IsMulCommutative ↥(E.subgroupOf H₁)]
  [Module (ZMod 2) (Additive ↥(E.subgroupOf H₁))]

theorem orbit_ncard_le (hS : Setting65 Γ E H₁ e) (φ : ↥H₁ ⧸ E.subgroupOf H₁ ≃* Carrier .M23)
    (ρ : Carrier .M23 →*
      (Additive ↥(E.subgroupOf H₁) ≃ₗ[ZMod 2] Additive ↥(E.subgroupOf H₁)))
    (hρ : ∀ (k : ↥H₁) (n : ↥(E.subgroupOf H₁)),
      ρ (φ (QuotientGroup.mk k)) (Additive.ofMul n) = Additive.ofMul (MulAut.conjNormal k n))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (F : Additive ↥(E.subgroupOf H₁) ≃ₗ[ZMod 2] W) (act : Carrier .M23 →* (W ≃ₗ[ZMod 2] W))
    (hF : ∀ g v, F (ρ g v) = act g (F v)) {n₀ : ↥(E.subgroupOf H₁)}
    (hn₀ : n₀ ∈ Xset E H₁ e) :
    (Set.range fun g : Carrier .M23 => act g (F (Additive.ofMul n₀))).ncard ≤ 23 := by
  have hsub : (Set.range fun g : Carrier .M23 => act g (F (Additive.ofMul n₀))) ⊆
      (fun n : ↥(E.subgroupOf H₁) => F (Additive.ofMul n)) '' Xset E H₁ e := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨q, rfl⟩ := φ.surjective g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨MulAut.conjNormal k n₀, hS.Xset_conj k hn₀, ?_⟩
    simp only
    rw [← hρ, hF]
  calc _ ≤ ((fun n : ↥(E.subgroupOf H₁) => F (Additive.ofMul n)) '' Xset E H₁ e).ncard :=
        Set.ncard_le_ncard hsub ((Set.toFinite _).image _)
    _ ≤ (Xset E H₁ e).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = 23 := hS.Xset_ncard

omit [Finite Γ] [(E.subgroupOf H₁).Normal] [IsMulCommutative ↥(E.subgroupOf H₁)]
  [Module (ZMod 2) (Additive ↥(E.subgroupOf H₁))] in
theorem Xset_ne_one (hS : Setting65 Γ E H₁ e) {n : ↥(E.subgroupOf H₁)} (hn : n ∈ Xset E H₁ e) :
    Additive.ofMul n ≠ 0 := by
  obtain ⟨ω, hω, hne, hv⟩ := hn
  intro h
  have h1 : n = 1 := by simpa using h
  apply hne
  have h2 : ω * e = 1 := by rw [← hv, h1]; rfl
  calc ω = ω * e * e := by rw [mul_assoc, hS.e_mul_e, mul_one]
    _ = e := by rw [h2, one_mul]

theorem not_golayEven (hS : Setting65 Γ E H₁ e) (φ : ↥H₁ ⧸ E.subgroupOf H₁ ≃* Carrier .M23)
    (ρ : Carrier .M23 →*
      (Additive ↥(E.subgroupOf H₁) ≃ₗ[ZMod 2] Additive ↥(E.subgroupOf H₁)))
    (hρ : ∀ (k : ↥H₁) (n : ↥(E.subgroupOf H₁)),
      ρ (φ (QuotientGroup.mk k)) (Additive.ofMul n) = Additive.ofMul (MulAut.conjNormal k n))
    (F : Additive ↥(E.subgroupOf H₁) ≃ₗ[ZMod 2] ↥golayEven)
    (hF : ∀ g v, F (ρ g v) = golayRep g (F v)) : False := by
  obtain ⟨ω₀, hω₀, hne⟩ := hS.exists_mem_omega_ne
  have hn₀ : toN hS hω₀ (hS.mul_e_mem_H₁ ω₀ hω₀ hne) ∈ Xset E H₁ e := ⟨ω₀, hω₀, hne, rfl⟩
  have hu : F (Additive.ofMul (toN hS hω₀ (hS.mul_e_mem_H₁ ω₀ hω₀ hne))) ≠ 0 := by
    intro h
    exact Xset_ne_one hS hn₀ (F.map_eq_zero_iff.1 h)
  have h1 := golayEven_orbit_large _ hu
  have h2 := orbit_ncard_le hS φ ρ hρ F golayRep hF hn₀
  omega

theorem points_of_cocode (hS : Setting65 Γ E H₁ e) (φ : ↥H₁ ⧸ E.subgroupOf H₁ ≃* Carrier .M23)
    (ρ : Carrier .M23 →*
      (Additive ↥(E.subgroupOf H₁) ≃ₗ[ZMod 2] Additive ↥(E.subgroupOf H₁)))
    (hρ : ∀ (k : ↥H₁) (n : ↥(E.subgroupOf H₁)),
      ρ (φ (QuotientGroup.mk k)) (Additive.ofMul n) = Additive.ofMul (MulAut.conjNormal k n))
    (F : Additive ↥(E.subgroupOf H₁) ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ g v, F (ρ g v) = cocodeRep g (F v)) {n : ↥(E.subgroupOf H₁)}
    (hn : n ∈ Xset E H₁ e) : ∃ i, F (Additive.ofMul n) = pt i :=
  cocode_orbit_points _ (fun h => Xset_ne_one hS hn (F.map_eq_zero_iff.1 h))
    (orbit_ncard_le hS φ ρ hρ F cocodeRep hF hn)

end Orbit

end CFSG.EvenSporadicStandard.Induction.Balance
