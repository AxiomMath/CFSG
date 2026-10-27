module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBasic

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {X : Type*} [Group X]

@[expose] def resSub (ρ : X →* (V ≃ₗ[k] V)) (B : Subgroup X) (W : Submodule k V)
    (hW : Offender.IsInvariant ρ B W) : ↥B →* (W ≃ₗ[k] W) :=
  resHom (ρ.comp B.subtype) W (fun a w hw => hW a a.2 w hw)

theorem resSub_apply (ρ : X →* (V ≃ₗ[k] V)) (B : Subgroup X) (W : Submodule k V)
    (hW : Offender.IsInvariant ρ B W) (b : ↥B) (w : W) : ((resSub ρ B W hW b w : W) : V) = ρ b w :=
  coe_resHom_apply (ρ.comp B.subtype) W _ b w

theorem resSub_conj_mem_range {ρ : X →* (V ≃ₗ[k] V)} {H A : Subgroup X} {W : Submodule k V}
    (hWH : Offender.IsInvariant ρ H W) (hWA : Offender.IsInvariant ρ A W) {g : X} (hgA : g ∈ A)
    (hg : g ∈ Subgroup.normalizer (H : Set X)) {x : W ≃ₗ[k] W}
    (hx : x ∈ (resSub ρ H W hWH).range) :
    resSub ρ A W hWA ⟨g, hgA⟩ * x * (resSub ρ A W hWA ⟨g, hgA⟩)⁻¹ ∈
      (resSub ρ H W hWH).range := by
  obtain ⟨h, rfl⟩ := hx
  refine ⟨⟨g * h * g⁻¹, conj_mem_of_mem_normalizer hg h.2⟩, ?_⟩
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  have hinv : (resSub ρ A W hWA ⟨g, hgA⟩)⁻¹ = resSub ρ A W hWA ⟨g⁻¹, A.inv_mem hgA⟩ := by
    rw [← map_inv]; rfl
  rw [hinv]
  show ((resSub ρ H W hWH ⟨g * h * g⁻¹, _⟩ w : W) : V) = _
  rw [resSub_apply]
  show ρ (g * h * g⁻¹) w = ((resSub ρ A W hWA ⟨g, hgA⟩ (resSub ρ H W hWH h
    (resSub ρ A W hWA ⟨g⁻¹, A.inv_mem hgA⟩ w)) : W) : V)
  rw [resSub_apply, resSub_apply, resSub_apply]
  show ρ (g * h * g⁻¹) w = ρ g (ρ h (ρ g⁻¹ w))
  rw [ρ_mul_apply, ρ_mul_apply]

theorem detect_of_trivial_mod [CharP k 2] [Finite X] (ρ : X →* (V ≃ₗ[k] V)) (H A : Subgroup X)
    (hAn : A ≤ Subgroup.normalizer (H : Set X))
    (hno : NoPQuotient 2 H) (hch : CentralPChief 2 H)
    (W : Submodule k V) (hWH : Offender.IsInvariant ρ H W) (hWA : Offender.IsInvariant ρ A W)
    (hWc : commSub ρ H W = W) {b : X} (hb : b ∈ A)
    (htriv : ∀ w ∈ W, ρ b w - w ∈ fixSub ρ H) : ∀ w ∈ W, ρ b w = w := by
  let rH : ↥H →* (W ≃ₗ[k] W) := resSub ρ H W hWH
  let H₁ : Subgroup (W ≃ₗ[k] W) := rH.range
  have hsurj : Function.Surjective rH.rangeRestrict := rH.rangeRestrict_surjective
  have hno₁ : NoPQuotient 2 H₁ := noPQuotient_of_surjective rH.rangeRestrict hsurj hno
  have hch₁ : CentralPChief 2 H₁ := centralPChief_of_surjective rH.rangeRestrict hsurj hch
  have : Finite H₁ := Finite.of_surjective rH.rangeRestrict hsurj
  have hcent : ∀ E : Subgroup H₁, E.Normal → CFSG.IsElementaryAbelian 2 E →
      E ≤ Subgroup.center H₁ := by
    intro E hEn hE
    have := hE
    have h1 : E ≤ CFSG.pCore 2 H₁ :=
      le_sSup (show E ∈ CFSG.normalPSubgroups 2 H₁ from
        ⟨hEn, CFSG.IsElementaryAbelian.isPGroup 2 E⟩)
    exact h1.trans (pCore_le_center_of_central_chief Nat.prime_two hno₁ hch₁)
  have hV : commGL H₁ ⊤ = ⊤ := by
    have hle : W ≤ Submodule.map W.subtype (commGL H₁ ⊤) := by
      refine le_trans (le_of_eq hWc.symm) ?_
      rw [commSub_le_iff]
      intro h hh u hu
      have hbmem : rH ⟨h, hh⟩ ∈ H₁ := ⟨⟨h, hh⟩, rfl⟩
      have hcomm := mem_commSub_of (ρ := MonoidHom.id (W ≃ₗ[k] W)) (B := H₁) (U := ⊤)
        (b := rH ⟨h, hh⟩) hbmem (u := (⟨u, hu⟩ : W)) Submodule.mem_top
      refine ⟨rH ⟨h, hh⟩ ⟨u, hu⟩ - ⟨u, hu⟩, hcomm, ?_⟩
      simp only [Submodule.subtype_apply, Submodule.coe_sub]
      rw [resSub_apply]
    have hle2 : Submodule.map W.subtype (commGL H₁ ⊤) ≤ W := Submodule.map_subtype_le W _
    have heq : Submodule.map W.subtype (commGL H₁ ⊤) = Submodule.map W.subtype ⊤ := by
      rw [Submodule.map_subtype_top]
      exact le_antisymm hle2 hle
    exact Submodule.map_injective_of_injective W.injective_subtype heq
  let b₁ : W ≃ₗ[k] W := resSub ρ A W hWA ⟨b, hb⟩
  have hb₁n : b₁ ∈ Subgroup.normalizer (H₁ : Set (W ≃ₗ[k] W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact resSub_conj_mem_range hWH hWA hb (hAn hb) hx
    · intro hx
      have := resSub_conj_mem_range hWH hWA (A.inv_mem hb) (Subgroup.inv_mem _ (hAn hb)) hx
      have hinv : resSub ρ A W hWA ⟨b⁻¹, A.inv_mem hb⟩ = b₁⁻¹ := by
        show resSub ρ A W hWA ((⟨b, hb⟩ : ↥A)⁻¹) = _
        rw [map_inv]
      rw [hinv, inv_inv] at this
      have e : b₁⁻¹ * (b₁ * x * b₁⁻¹) * b₁ = x := by group
      rwa [e] at this
  have hdet := (commutatorModule_fixedQuotient_detects (p := 2) H₁ hno₁ hcent hV).2 b₁ hb₁n ?_
  · intro w hw
    have := congrArg (fun f : W ≃ₗ[k] W => ((f ⟨w, hw⟩ : W) : V)) hdet
    simpa [b₁, resSub_apply] using this
  · intro w
    rw [mem_fixGL]
    intro x hx
    obtain ⟨h, rfl⟩ := hx
    apply Subtype.ext
    show ((rH h (b₁ w - w) : W) : V) = ((b₁ w - w : W) : V)
    rw [resSub_apply]
    simp only [Submodule.coe_sub]
    have : ((b₁ w : W) : V) = ρ b w := resSub_apply ρ A W hWA ⟨b, hb⟩ w
    rw [this]
    exact htriv w w.2 h h.2

end CFSG.QuasithinUnique.Setup.Layer
