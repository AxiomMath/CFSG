module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParPIdx

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Subgroup CFSG.ABGLocalTools CFSG.EvenSmallLie.UnitarySix.YamadaEnd
  CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped MatrixGroups

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem std_coords_linear (hL44 : L44Input) (ψ : SL(4, CFSG.Fischer.F4) →* Γ)
    (hψ : Function.Bijective ψ) (τ : Γ →* Γ) (hττ : ∀ g, τ (τ g) = g)
    (χb : msigma CFSG.Fischer.F4 →* Γ) (hχb : Function.Injective χb)
    (hfix : ∀ γ, τ γ = γ ↔ γ ∈ χb.range) {Pb : Subgroup Γ} (hPS : IsSylowOf 2 Pb ⊤)
    (hPσ : ∀ A ∈ pSig CFSG.Fischer.F4, χb A ∈ Pb) :
    ∃ Φ : SL(4, CFSG.Fischer.F4) ≃* Γ, (pstd CFSG.Fischer.F4).map Φ.toMonoidHom = Pb ∧
      (∀ A : msigma CFSG.Fischer.F4, Φ A = χb A) ∧
      ∀ A, τ (Φ A) = Φ (sigmaSL CFSG.Fischer.F4 A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut Γ) := Finite.of_injective (fun f : MulAut Γ => (f : Γ → Γ))
    (fun f g hfg => MulEquiv.ext (congrFun hfg))
  have hcent : ∀ g : Γ, (∀ x, g * x = x * g) → g = 1 := by
    intro g hg
    obtain ⟨a, rfl⟩ := hψ.2 g
    have ha : a ∈ center SL(4, CFSG.Fischer.F4) := Subgroup.mem_center_iff.mpr fun b => hψ.1 (by
      rw [map_mul, map_mul, hg])
    rw [center_SL4_eq_bot, Subgroup.mem_bot] at ha
    rw [ha, map_one]
  set c := (MulAut.conj : Γ →* MulAut Γ)
  have hc : Function.Injective c := by
    intro g g' hgg'
    have h1 : ∀ x, g * x * g⁻¹ = g' * x * g'⁻¹ := fun x => by
      have := congrArg (fun f : MulAut Γ => f x) hgg'
      simpa [c, MulAut.conj_apply] using this
    have h2 := hcent (g'⁻¹ * g) fun x => by
      have := h1 x
      calc g'⁻¹ * g * x = g'⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g'⁻¹ * (g' * x * g'⁻¹) * g := by rw [this]
        _ = x * (g'⁻¹ * g) := by group
    calc g = g' * (g'⁻¹ * g) := by group
      _ = g' := by rw [h2, mul_one]
  set L₁ := c.range
  set ψ' : SL(4, CFSG.Fischer.F4) →* L₁ := c.rangeRestrict.comp ψ
  have hψ' : Function.Surjective ψ' := c.rangeRestrict_surjective.comp hψ.2
  have hker : ψ'.ker ≤ center SL(4, CFSG.Fischer.F4) := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have h1 : c (ψ a) = c 1 := by
      have := congrArg Subtype.val ha
      simpa [ψ', c] using this
    rw [hψ.1 ((hc h1).trans (map_one ψ).symm)]
    exact Subgroup.one_mem _
  set tb := autOf τ hττ
  have htb : tb * tb = 1 := MulEquiv.ext fun x => hττ x
  have htinv : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right htb
  have hconj : ∀ g, tb * c g * tb⁻¹ = c (τ g) := autOf_mul_conj τ hττ
  have htN : tb ∈ normalizer (L₁ : Set (MulAut Γ)) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨τ g, (hconj g).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨τ g, ?_⟩
      rw [← hconj g, hg, htinv]
      calc tb * (tb * x * tb) * tb = (tb * tb) * x * (tb * tb) := by group
        _ = x := by rw [htb]; group
  have hχL : ∀ A, c (χb A) ∈ (L₁ ⊓ centralizer ({tb} : Set (MulAut Γ)) : Subgroup _) :=
    fun A => ⟨⟨χb A, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr (by
      have h1 := hconj (χb A)
      rw [(hfix (χb A)).mpr ⟨A, rfl⟩] at h1
      calc c (χb A) * tb = tb * c (χb A) * tb⁻¹ * tb := by rw [h1]
        _ = tb * c (χb A) := by group)⟩
  set χ'' := (c.comp χb).codRestrict _ hχL
  have hχ''b : Function.Bijective χ'' := by
    refine ⟨fun A B hAB => hχb (hc (congrArg Subtype.val hAB)), ?_⟩
    rintro ⟨x, ⟨g, rfl⟩, hx⟩
    have h1 : c g * tb = tb * c g := Subgroup.mem_centralizer_singleton_iff.mp hx
    have h2 : c (τ g) = c g := by
      rw [← hconj, ← h1, mul_inv_cancel_right]
    obtain ⟨A, hA⟩ := (hfix g).mp (hc h2)
    exact ⟨A, Subtype.ext (by simp [χ'', hA])⟩
  set χ' := MulEquiv.ofBijective χ'' hχ''b
  have hχ' : ∀ A, (χ' A : MulAut Γ) = c (χb A) := fun A => rfl
  set P₁ := Pb.map c
  have hP₁ : IsSylowOf 2 P₁ L₁ := by
    refine isSylowOf_of_card (Subgroup.map_le_range c Pb) ?_
    rw [card_map_inj c hc, hPS.card_eq, Subgroup.card_top,
      Nat.card_congr (MonoidHom.ofInjective hc).toEquiv]
  have hS : ∀ A : msigma CFSG.Fischer.F4, (A : SL(4, CFSG.Fischer.F4)) ∈ pstd CFSG.Fischer.F4 →
      (χ' A : MulAut Γ) ∈ P₁ := fun A hA =>
    ⟨χb A, hPσ A (Subgroup.mem_subgroupOf.mpr hA), rfl⟩
  obtain ⟨φ, hφ, hφr, hφχ, hφt, hφP⟩ :=
    hL44 CFSG.Fischer.F4 natCard_F4 (MulAut Γ) L₁ ψ' hψ' hker tb htb htN χ' P₁ hP₁ hS
  have hmem : ∀ A, φ A ∈ c.range := fun A => by
    have : φ A ∈ φ.range := ⟨A, rfl⟩
    rw [hφr] at this
    exact this
  set e := MonoidHom.ofInjective hc
  set Φ₀ : SL(4, CFSG.Fischer.F4) →* Γ := e.symm.toMonoidHom.comp (φ.codRestrict _ hmem)
  have hcΦ : ∀ A, c (Φ₀ A) = φ A := fun A => by
    have := e.apply_symm_apply ⟨φ A, hmem A⟩
    exact congrArg Subtype.val this
  have hΦ₀inj : Function.Injective Φ₀ := fun A B hAB => hφ (by rw [← hcΦ, ← hcΦ, hAB])
  have hΦ₀surj : Function.Surjective Φ₀ := by
    intro g
    obtain ⟨A, hA⟩ : c g ∈ φ.range := by rw [hφr]; exact ⟨g, rfl⟩
    exact ⟨A, hc (by rw [hcΦ, hA])⟩
  set Φ := MulEquiv.ofBijective Φ₀ ⟨hΦ₀inj, hΦ₀surj⟩
  have hΦc : ∀ A, c (Φ A) = φ A := hcΦ
  refine ⟨Φ, ?_, fun A => hc (by rw [hΦc, hφχ, hχ']), fun A => hc ?_⟩
  · apply Subgroup.map_injective hc
    rw [Subgroup.map_map]
    calc (pstd CFSG.Fischer.F4).map (c.comp Φ.toMonoidHom) = (pstd CFSG.Fischer.F4).map φ := by
          congr 1; exact MonoidHom.ext fun A => hΦc A
      _ = P₁ := hφP
  · rw [hΦc, ← hφt, ← hconj, hΦc]

section Unitary


omit [Finite Γ] in
theorem std_coords_unitary (ψ : SU42b × SU42b ≃* Γ) (τ : Γ →* Γ)
    (hτ : ∀ p, τ (ψ p) = ψ p.swap) (χb : msigma CFSG.Fischer.F4 →* Γ)
    (hχb : Function.Injective χb) (hfix : ∀ A, τ (χb A) = χb A) {Pb : Subgroup Γ}
    (hP2 : IsPGroup 2 Pb) (hPc : Nat.card Pb = 2 ^ 12)
    (hPσ : ∀ A ∈ pSig CFSG.Fischer.F4, χb A ∈ Pb) :
    ∃ β : msigma CFSG.Fischer.F4 →* SU42b, Function.Injective β ∧
      (∀ A, ψ.symm (χb A) = (β A, β A)) ∧
      Pb.map ψ.symm.toMonoidHom =
        ((pSig CFSG.Fischer.F4).map β).prod ((pSig CFSG.Fischer.F4).map β) := by
  set ψi := ψ.symm.toMonoidHom
  have hψi : Function.Injective ψi := ψ.symm.injective
  set β : msigma CFSG.Fischer.F4 →* SU42b := (MonoidHom.fst _ _).comp (ψi.comp χb)
  have hdiag : ∀ A, ψi (χb A) = (β A, β A) := fun A => by
    have h1 : ψ (ψi (χb A)).swap = ψ (ψi (χb A)) := by
      rw [← hτ]
      simp only [ψi, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hfix]
    have h2 := ψ.injective h1
    exact Prod.ext rfl (congrArg Prod.snd h2).symm
  have hβ : Function.Injective β := fun A B hAB => by
    apply hχb
    apply hψi
    rw [hdiag, hdiag, hAB]
  set U := (pSig CFSG.Fischer.F4).map β
  have hU : Nat.card U = 2 ^ 6 := by rw [card_map_inj _ hβ, card_pSig natCard_F4]
  set Q := Pb.map ψi
  have hQ : Nat.card Q = 2 ^ 12 := by rw [card_map_inj _ hψi, hPc]
  have hQ2 : IsPGroup 2 Q := hP2.map ψi
  have hUQ : ∀ x ∈ U, (x, x) ∈ Q := by
    rintro _ ⟨A, hA, rfl⟩
    exact ⟨χb A, hPσ A hA, hdiag A⟩
  have hcard : Nat.card SU42b = 2 ^ 6 * 405 := by rw [card_SU42b]; norm_num
  have hfst : Q.map (MonoidHom.fst _ _) = U := by
    refine (Subgroup.eq_of_le_of_card_ge
      (fun x hx => Subgroup.mem_map.mpr ⟨(x, x), hUQ x hx, rfl⟩) ?_).symm
    rw [hU]
    exact card_le_of_isPGroup (hQ2.map _) (by norm_num) hcard
  have hsnd : Q.map (MonoidHom.snd _ _) = U := by
    refine (Subgroup.eq_of_le_of_card_ge
      (fun x hx => Subgroup.mem_map.mpr ⟨(x, x), hUQ x hx, rfl⟩) ?_).symm
    rw [hU]
    exact card_le_of_isPGroup (hQ2.map _) (by norm_num) hcard
  refine ⟨β, hβ, hdiag, Subgroup.eq_of_le_of_card_ge (fun q hq => ?_) ?_⟩
  · have h1 : q.1 ∈ Q.map (MonoidHom.fst _ _) := Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    have h2 : q.2 ∈ Q.map (MonoidHom.snd _ _) := Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    rw [hfst] at h1
    rw [hsnd] at h2
    exact ⟨h1, h2⟩
  · rw [card_prod', hU, hQ]; norm_num

end Unitary

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
