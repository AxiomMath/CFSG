module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7Module
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourLocal

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Module CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem trivial_of_quad (ρ : Representation (ZMod 2) G W) {L : Subgroup G}
    (eL : ↥L ≃* alternatingGroup (Fin 7)) (U' : Submodule (ZMod 2) W)
    (h : ∀ l₁ ∈ L, ∀ l₂ ∈ L, ∀ w ∈ U', ρ l₁ (ρ l₂ w - w) = ρ l₂ w - w) :
    ∀ l ∈ L, ∀ w ∈ U', ρ l w = w := by
  classical
  have hsimple := isSimpleGroup_alt7
  have hsL : IsSimpleGroup ↥L := eL.isSimpleGroup
  let Φ₀ : ↥L → (↥U' →ₗ[ZMod 2] W) := fun l => (ρ l - LinearMap.id).comp U'.subtype
  let Φ : ↥L →* Multiplicative (↥U' →ₗ[ZMod 2] W) :=
    { toFun := fun l => Multiplicative.ofAdd (Φ₀ l)
      map_one' := by
        show Multiplicative.ofAdd (Φ₀ 1) = 1
        have : Φ₀ 1 = 0 := by
          ext w
          simp [Φ₀]
        rw [this]; rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (Φ₀ (a * b)) =
          Multiplicative.ofAdd (Φ₀ a) * Multiplicative.ofAdd (Φ₀ b)
        rw [← ofAdd_add]
        congr 1
        ext w
        have h1 := h a a.2 b b.2 w w.2
        simp only [Φ₀, Subgroup.coe_mul, map_mul, Module.End.mul_apply, LinearMap.add_apply,
          LinearMap.comp_apply, LinearMap.sub_apply, Submodule.subtype_apply,
          LinearMap.id_apply]
        rw [map_sub] at h1
        have h2 : ρ (a : G) (ρ (b : G) (w : W)) = ρ b w - w + ρ a w := by
          rw [← h1]; abel
        rw [h2]; abel }
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Φ.ker with hb | ht
  · exfalso
    have hinj : Function.Injective Φ := (MonoidHom.ker_eq_bot_iff Φ).1 hb
    obtain ⟨a, b, hab⟩ := exists_ne_comm_alt7
    apply hab
    have : eL.symm a * eL.symm b = eL.symm b * eL.symm a := by
      apply hinj
      rw [map_mul, map_mul, mul_comm]
    have := congrArg eL this
    simpa using this
  · intro l hl w hw
    have hl' : (⟨l, hl⟩ : ↥L) ∈ Φ.ker := by rw [ht]; trivial
    have := (MonoidHom.mem_ker.1 hl')
    have h3 := congrArg (fun x : Multiplicative (↥U' →ₗ[ZMod 2] W) => (Multiplicative.toAdd x) ⟨w, hw⟩) this
    simp only [Φ, Φ₀, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one, LinearMap.comp_apply,
      LinearMap.sub_apply, Submodule.subtype_apply, LinearMap.id_apply, LinearMap.zero_apply] at h3
    exact sub_eq_zero.1 h3

theorem finrank_eq_four_of_card_sixteen [Finite W] {M : Submodule (ZMod 2) W} (h : Nat.card M = 16) :
    finrank (ZMod 2) M = 4 := by
  have h1 := natCard_submodule_zmod2 M
  rw [h] at h1
  have h' : 2 ^ finrank (ZMod 2) M = 2 ^ 4 := by rw [← h1]; norm_num
  exact Nat.pow_right_injective (le_refl 2) h'

theorem commOn_eq_of_card_sixteen [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {L : Subgroup G} (eL : ↥L ≃* alternatingGroup (Fin 7))
    {A : Subgroup G} (hA2 : CFSG.IsElementaryAbelian 2 ↥A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hLA : ⁅L, A⁆ = L)
    (hb : IsBestOffenderOn ρ A ⊤) {U' : Submodule (ZMod 2) W} (hU'16 : Nat.card U' = 16)
    (hU'inv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L U') (hnt : ∃ l ∈ L, ∃ u ∈ U', ρ l u ≠ u) :
    commOn ρ L ⊤ = U' ∧ fixOn ρ L U' = ⊥ := by
  classical
  have hfin : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hfU' : finrank (ZMod 2) U' = 4 := finrank_eq_four_of_card_sixteen hU'16
  obtain ⟨hirr, hlt⟩ := a7_commOn_quot ρ hρ eL hA2 hAN hLA hb
  have hUU : commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤ := commOn_commOn_eq hA2 hAN hLA
  set J := commOn ρ L U' with hJ
  have hLconj : ∀ g ∈ L, ∀ b ∈ L, g * b * g⁻¹ ∈ L := fun g hg b hb =>
    L.mul_mem (L.mul_mem hg hb) (L.inv_mem hg)
  have hJinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L J := fun g hg w hw => rep_mem_commOn (hLconj g hg)
    (hU'inv g hg) hw
  have hJle : J ≤ U' := by
    rw [hJ, commOn, Submodule.span_le]
    rintro _ ⟨a, ha, u, hu, rfl⟩
    exact U'.sub_mem (hU'inv a ha u hu) hu
  have hbot : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (⊥ : Submodule (ZMod 2) W) := fun _ _ u hu => by
    rw [Submodule.mem_bot] at hu ⊢
    rw [hu, map_zero]
  have hgen : ∀ l ∈ L, ∀ w ∈ U', ρ l w - w ∈ J := fun l hl w hw =>
    Submodule.subset_span ⟨l, hl, w, hw, rfl⟩
  have hJeq : J = U' := by
    by_contra hne
    have hlt' : J < U' := lt_of_le_of_ne hJle hne
    have hfJ : finrank (ZMod 2) J < 4 := hfU' ▸ Submodule.finrank_lt_finrank_of_lt hlt'
    have hsec : SecTrivial ρ L ⊥ J := by
      by_contra hn
      obtain ⟨k, hk⟩ := exists_secRep_ne_one hbot hJinv hn
      have : Finite (SecQ (⊥ : Submodule (ZMod 2) W) J) := Module.finite_of_finite (ZMod 2)
      have h4 := four_le_finrank_of_alt7 eL (secRep ρ L hbot hJinv) ⟨k, hk⟩
      have h5 := finrank_secQ (Z₀ := (⊥ : Submodule (ZMod 2) W)) (Z₁ := J) bot_le
      simp only [finrank_bot, add_zero] at h5
      omega
    have hJfix : ∀ l ∈ L, ∀ j ∈ J, ρ l j = j := fun l hl j hj => by
      have := hsec l hl j hj
      rwa [Submodule.mem_bot, sub_eq_zero] at this
    obtain ⟨l, hl, u, hu, hne'⟩ := hnt
    exact hne' (trivial_of_quad ρ eL U'
      (fun l₁ hl₁ l₂ hl₂ w hw => hJfix l₁ hl₁ _ (hgen l₂ hl₂ w hw)) l hl u hu)
  have hU'le : U' ≤ commOn ρ L ⊤ := hJeq ▸ commOn_mono_right le_top
  have hF : fixOn ρ L U' = ⊥ := by
    by_contra hFne
    have hFinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (fixOn ρ L U') := fun g hg u hu => by
      rw [hu.2 g hg]; exact hu
    have hnt' : ¬ SecTrivial ρ L (fixOn ρ L U') U' := by
      intro htriv
      have hJF : J ≤ fixOn ρ L U' := by
        rw [hJ, commOn, Submodule.span_le]
        rintro _ ⟨a, ha, u, hu, rfl⟩
        exact htriv a ha u hu
      obtain ⟨l, hl, u, hu, hne'⟩ := hnt
      exact hne' ((hJeq ▸ hJF) hu |>.2 l hl)
    obtain ⟨k, hk⟩ := exists_secRep_ne_one hFinv hU'inv hnt'
    have : Finite (SecQ (fixOn ρ L U') U') := Module.finite_of_finite (ZMod 2)
    have h4 := four_le_finrank_of_alt7 eL (secRep ρ L hFinv hU'inv) ⟨k, hk⟩
    have h5 := finrank_secQ (Z₀ := fixOn ρ L U') (Z₁ := U') (fun v hv => hv.1)
    have h6 : finrank (ZMod 2) (fixOn ρ L U') = 0 := by omega
    exact hFne (Submodule.finrank_eq_zero.1 h6)
  set C₀ := fixOn ρ L (commOn ρ L ⊤) with hC₀
  have hZinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (U' ⊔ C₀) := by
    intro g hg z hz
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add, hc.2 g hg]
    exact Submodule.add_mem_sup (hU'inv g hg u hu) hc
  rcases hirr (U' ⊔ C₀) hZinv le_sup_right (sup_le hU'le (fun v hv => hv.1)) with hZ | hZ
  · exfalso
    obtain ⟨l, hl, u, hu, hne'⟩ := hnt
    have : u ∈ C₀ := hZ ▸ Submodule.mem_sup_left hu
    exact hne' (this.2 l hl)
  · refine ⟨le_antisymm ?_ hU'le, hF⟩
    rw [← hUU]
    rw [commOn, Submodule.span_le]
    rintro _ ⟨a, ha, u, hu, rfl⟩
    have hu' : u ∈ U' ⊔ C₀ := hZ ▸ hu
    obtain ⟨u', hu'U, c, hc, rfl⟩ := Submodule.mem_sup.1 hu'
    rw [map_add, hc.2 a ha]
    have : ρ a u' + c - (u' + c) = ρ a u' - u' := by abel
    rw [this]
    exact U'.sub_mem (hU'inv a ha u' hu'U) hu'U

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
