module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect2

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem not_top_le_fix_of_quasisimple {L : Subgroup (V ≃ₗ[k] V)} (hL : CFSG.IsQuasisimple L) :
    ¬ (⊤ : Submodule k V) ≤ fixGL L := by
  intro hle
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hL
  obtain ⟨⟨l, hl⟩, hne⟩ := exists_ne (1 : ↥L)
  apply hne
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact hle Submodule.mem_top l hl

theorem trivial_of_trivial_A {L A : Subgroup (V ≃ₗ[k] V)} {I : Submodule k V}
    (hLA : ⁅L, A⁆ = L) (hIL : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) L I)
    (hA : ∀ a ∈ A, ∀ u ∈ I, a u = u) : ∀ l ∈ L, ∀ u ∈ I, l u = u := by
  have hle : L ≤ centSub (MonoidHom.id (V ≃ₗ[k] V)) I := by
    rw [← hLA]
    refine Subgroup.commutator_le.2 fun l hl a ha u hu => ?_
    have h1 : a⁻¹ u = u := hA a⁻¹ (A.inv_mem ha) u hu
    have h2 : l⁻¹ u ∈ I := hIL l⁻¹ (L.inv_mem hl) u hu
    have h3 : a (l⁻¹ u) = l⁻¹ u := hA a ha _ h2
    show (⁅l, a⁆ : V ≃ₗ[k] V) u = u
    rw [commutatorElement_def]
    show l (a (l⁻¹ (a⁻¹ u))) = u
    rw [h1, h3, gl_apply_inv]
  exact fun l hl u hu => hle hl u hu

theorem weight_range_of_injective {B : Type*} [Group B] {M : Type*} [AddCommGroup M]
    [Module k M] (ρ : B →* (M ≃ₗ[k] M)) (hinj : Function.Injective ρ) :
    weight (MonoidHom.id (M ≃ₗ[k] M)) ρ.range = weight ρ ⊤ := by
  unfold weight
  have h1 : Nat.card ↥ρ.range = Nat.card ↥(⊤ : Subgroup B) := by
    rw [Subgroup.card_top]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h2 : fixSub (MonoidHom.id (M ≃ₗ[k] M)) ρ.range = fixSub ρ ⊤ := by
    ext v
    simp only [mem_fixSub, MonoidHom.mem_range]
    constructor
    · intro h b _
      exact h (ρ b) ⟨b, rfl⟩
    · rintro h _ ⟨b, rfl⟩
      exact h b (Subgroup.mem_top b)
  rw [h1, h2]

section Act

variable {L A : Subgroup (V ≃ₗ[k] V)} {I : Submodule k V}
  (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[k] V)))
  (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I)

theorem actW_mk (x : ↥(L ⊔ A)) (w : ↥I) :
    actW L A I hAn hI x (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (resSub (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I hI x w) :=
  quotHom_mk _ _ _ _ _

include hAn hI in
theorem disp_mem_fix_of_actW_eq_one {x : ↥(L ⊔ A)} (hx : actW L A I hAn hI x = 1) :
    ∀ w ∈ I, (x : V ≃ₗ[k] V) w - w ∈ fixGL L := by
  intro w hw
  have h1 := actW_mk hAn hI x ⟨w, hw⟩
  rw [hx] at h1
  have h2 : (Submodule.Quotient.mk ⟨w, hw⟩ : ↥I ⧸ fixIn L I) =
      Submodule.Quotient.mk (resSub (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I hI x ⟨w, hw⟩) := h1
  rw [Submodule.Quotient.eq] at h2
  intro l hl
  have h3 := h2 l hl
  have e : ((⟨w, hw⟩ - resSub (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I hI x ⟨w, hw⟩ : ↥I) : V) =
      w - (x : V ≃ₗ[k] V) w := by
    rw [Submodule.coe_sub, resSub_apply]
    rfl
  have h4 : l (w - (x : V ≃ₗ[k] V) w) = w - (x : V ≃ₗ[k] V) w := by
    have h5 : l ((⟨w, hw⟩ - resSub (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I hI x ⟨w, hw⟩ : ↥I) : V) =
        ((⟨w, hw⟩ - resSub (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I hI x ⟨w, hw⟩ : ↥I) : V) := h3
    rwa [e] at h5
  have h6 : (x : V ≃ₗ[k] V) w - w = -(w - (x : V ≃ₗ[k] V) w) := by abel
  show l ((x : V ≃ₗ[k] V) w - w) = (x : V ≃ₗ[k] V) w - w
  rw [h6, map_neg, h4]

end Act

end CFSG.QuasithinUnique.Setup.Layer
