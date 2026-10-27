module

public import CFSG.CGT.Stroth77.Section41Types
public import CFSG.CGT.Stroth77.AlperinHS
public import CFSG.CGT.Stroth77.StrothFrameD
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGH

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.ONan76 CFSG.OddStandard.HigherRank.G2Three.Sec2
open CFSG.ComponentClassification.HSFLit

theorem isTypeHS_of_isHSType
    {G : Type} [Group G] (S : Sylow 2 G)
    (h : IsHSType ↥(S : Subgroup G)) : IsTypeHS G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite CFSG.Blueprint.NativeSporadic.HS := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Sporadic.HS.card_HS]; norm_num)
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  obtain ⟨Q⟩ : Nonempty (Sylow 2 CFSG.Blueprint.NativeSporadic.HS) := inferInstance
  let f₀ : CFSG.Blueprint.NativeSporadic.HS →* TauCeti.SporadicName.HS.Group := b
  have hb : Function.Surjective f₀ := b.surjective
  obtain ⟨f⟩ := h (Q.mapSurjective hb)
  have e₁ : ↥(Q.mapSurjective hb : Subgroup TauCeti.SporadicName.HS.Group) ≃*
      ↥((Q : Subgroup CFSG.Blueprint.NativeSporadic.HS).map f₀) :=
    MulEquiv.subgroupCongr (Sylow.coe_mapSurjective hb Q)
  have e₂ : ↥(Q : Subgroup CFSG.Blueprint.NativeSporadic.HS) ≃*
      ↥((Q : Subgroup CFSG.Blueprint.NativeSporadic.HS).map f₀) :=
    (Q : Subgroup CFSG.Blueprint.NativeSporadic.HS).equivMapOfInjective f₀ b.injective
  exact ⟨S, Q, ⟨(f.trans e₁).trans e₂.symm⟩⟩

section FrameFree

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {D : Subgroup G} {uv t u : G}

theorem isSporadic_HS_of_type310_two
    (hGH : GorensteinHarrisInput) (e : Additive D ≃+ Torus (Type310.k 2))
    (ht : t ∈ Subgroup.normalizer (D : Set G)) (hu : u ∈ Subgroup.normalizer (D : Set G))
    (ht_conj : ∀ x : D,
      e (Additive.ofMul (conjBy ht x)) = (Type310.action 2 le_rfl).φt (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D,
      e (Additive.ofMul (conjBy hu x)) = (Type310.action 2 le_rfl).φu (e (Additive.ofMul x)))
    (ht2 : t * t = 1) (hu2 : u * u = 1) (huv2 : uv * uv = 1) (htu : t * u = u * uv * t)
    (S : Sylow 2 G) (hS : (S : Subgroup G) = D ⊔ Subgroup.closure {uv, t, u}) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .HS := by
  obtain ⟨v₁, v₂, v₃, s, r, hF, hs, hcl⟩ :=
    exists_alperinFrame_of_type310 e ht hu ht_conj hu_conj ht2 hu2 huv2 htu
  have hHS := isHSType_of_alperinFrame_two hF hs
  rw [hcl, ← hS] at hHS
  exact gorensteinHarris_corollaryA hGH (isTypeHS_of_isHSType S hHS)

theorem isSporadic_HS_of_stroth41
    (hGH : GorensteinHarrisInput)
    (hON : ∀ {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (P : Sylow 2 X) {n : ℕ},
      3 ≤ n → ∀ {v₁ v₂ v₃ s t : X}, AlperinFrame n v₁ v₂ v₃ s t →
        Subgroup.closure ({v₁, v₂, v₃, s, t} : Set X) = P → False)
    {τ : StrothTypeIndex} (hτ : τ.k 0 = τ.k 1) (hn : 2 ≤ τ.k 1) (e : Additive D ≃+ Torus τ.k)
    (huv : uv ∈ Subgroup.normalizer (D : Set G)) (ht : t ∈ Subgroup.normalizer (D : Set G))
    (hu : u ∈ Subgroup.normalizer (D : Set G))
    (huv_conj : ∀ x : D, e (Additive.ofMul (conjBy huv x)) = τ.action.φuv (e (Additive.ofMul x)))
    (ht_conj : ∀ x : D, e (Additive.ofMul (conjBy ht x)) = τ.action.φt (e (Additive.ofMul x)))
    (hu_conj : ∀ x : D, e (Additive.ofMul (conjBy hu x)) = τ.action.φu (e (Additive.ofMul x)))
    (huv2 : uv * uv = 1) (ht2 : t * t = 1) (hu2 : u * u = 1) (htu : t * u = u * uv * t)
    (S : Sylow 2 G) (hS : (S : Subgroup G) = D ⊔ Subgroup.closure {uv, t, u})
    (φ : ↥(Subgroup.normalizer (D : Set G)) →* GL (Fin 3) (ZMod 2)) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (D : Set G)).subgroupOf
      (Subgroup.normalizer (D : Set G))) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .HS := by
  obtain rfl := eq_t310_two_of_stroth41 hON hτ hn e huv ht hu huv_conj ht_conj hu_conj huv2 ht2
    hu2 htu S hS φ hφ hker
  exact isSporadic_HS_of_type310_two hGH e ht hu ht_conj hu_conj ht2 hu2 huv2 htu S hS

end FrameFree

section Frame

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem StrothFrame.IsD.two_le_k_one (h : F.IsD D dD) (hτ : τ.k 0 = τ.k 1) : 2 ≤ τ.k 1 := by
  by_contra hlt
  have hk : ∀ i, τ.k i = τ.k 1 := by
    have h21 : τ.k 2 = τ.k 1 := by cases τ <;> rfl
    intro i
    fin_cases i
    exacts [hτ, rfl, h21]
  have h2 : ∀ y : Torus τ.k, 2 • y = 0 := by
    intro y
    have hy := two_pow_nsmul_torus hk y
    obtain h0 | h1 : τ.k 1 = 0 ∨ τ.k 1 = 1 := by omega
    · rw [h0, pow_zero, one_smul] at hy
      rw [hy, smul_zero]
    · rwa [h1, pow_one] at hy
  set x : D := ⟨((F.dA.a : F.A) : G), h.A_le (F.dA.a).2⟩
  have hx : x * x = 1 := by
    apply Additive.ofMul.injective
    apply dD.e.injective
    rw [ofMul_mul, map_add, ← two_nsmul, h2, ofMul_one, map_zero]
  have ha : F.dA.a * F.dA.a = 1 := by
    apply Subtype.ext
    simpa [x] using congrArg Subtype.val hx
  have hea : F.dA.e (Additive.ofMul F.dA.a) = Torus.a := by
    simp [StrothWeakTypeData.a]
  have h0 := congrArg (fun z => F.dA.e (Additive.ofMul z)) ha
  simp only [ofMul_mul, map_add, hea, ofMul_one, map_zero] at h0
  exact (show (Torus.a + Torus.a : Torus (Type100.k 1)) ≠ 0 by decide) h0

theorem StrothFrame.IsD.isSporadic_HS_of_stroth41
    (hGH : GorensteinHarrisInput)
    (hON : ∀ {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (P : Sylow 2 X) {n : ℕ},
      3 ≤ n → ∀ {v₁ v₂ v₃ s t : X}, AlperinFrame n v₁ v₂ v₃ s t →
        Subgroup.closure ({v₁, v₂, v₃, s, t} : Set X) = P → False)
    (h : F.IsD D dD) (hτ : τ.k 0 = τ.k 1)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u})
    (φ : ↥(Subgroup.normalizer (D : Set G)) →* GL (Fin 3) (ZMod 2)) (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (D : Set G)).subgroupOf
      (Subgroup.normalizer (D : Set G))) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .HS := by
  have := F.simple
  rw [← h.uv_eq, ← h.t_eq, ← h.u_eq] at hS
  exact CFSG.CGT.Stroth77.isSporadic_HS_of_stroth41 hGH hON hτ (h.two_le_k_one hτ) dD.e
    dD.uv_mem dD.t_mem dD.u_mem dD.uv_conj dD.t_conj dD.u_conj dD.uv_sq dD.t_sq dD.u_sq dD.t_u
    F.S hS φ hφ hker

end Frame

end CFSG.CGT.Stroth77
