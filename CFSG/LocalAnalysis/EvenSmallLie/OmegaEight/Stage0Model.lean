module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeMain
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Defs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Shape

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage0

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

theorem finite_mulAut {L : Type*} [Group L] [Finite L] : Finite (MulAut L) :=
  Finite.of_injective (fun α : MulAut L => (α : L → L)) DFunLike.coe_injective

theorem involutionLifting_of_card_outer {L : Type*} [Group L] [Finite L] {m : ℕ}
    (hcard : Nat.card (Outer L) = 2 * m) (hm : Odd m) {β₀ : MulAut L} (hβ₀ : β₀ * β₀ = 1)
    (hβ₀I : β₀ ∉ inner L) : InvolutionLifting L := by
  have := finite_mulAut (L := L)
  intro α hα hα2
  obtain ⟨γ, hγ⟩ := exists_conj_mem_of_card_quotient hcard hm (by rw [hβ₀]; exact one_mem _)
    hβ₀I hα hα2
  refine ⟨γ * β₀ * γ⁻¹, ?_, hγ⟩
  calc γ * β₀ * γ⁻¹ * (γ * β₀ * γ⁻¹) = γ * (β₀ * β₀) * γ⁻¹ := by group
    _ = 1 := by rw [hβ₀, mul_one, mul_inv_cancel]

theorem exists_outer_involution_of_mulEquiv {L T : Type*} [Group L] [Group T] (e : L ≃* T)
    {x : MulAut T} (hx : x * x = 1) (hxI : x ∉ inner T) :
    ∃ β : MulAut L, β * β = 1 ∧ β ∉ inner L := by
  refine ⟨(MulAut.congr e).symm x, by rw [← map_mul, hx, map_one], fun hβ => hxI ?_⟩
  rw [← inner_map_congr e]
  exact ⟨_, hβ, MulEquiv.apply_symm_apply _ x⟩

theorem exists_automizer_of_equiv {G : Type} [Group G] {t : G} {L : Subgroup G}
    {T A : Type*} [Group T] [Group A] (hK : StepK t L) (e : L ≃* T) (φ : A ≃* MulAut T) :
    ∃ Θ : centralizer ({t} : Set G) →* A,
      (∀ (x : centralizer ({t} : Set G)) (l l' : L), (l' : G) = x * l * (x : G)⁻¹ →
        φ (Θ x) (e l) = e l') ∧
      (∀ x, Θ x = 1 ↔ (x : G) ∈ zpowers t) ∧
      ∀ x, φ (Θ x) ∈ inner T ↔ (x : G) ∈ L ⊔ zpowers t := by
  obtain ⟨θ, hθ, hker, hinn⟩ :=
    Stage1.exists_automizer hK.le_centralizer hK.le_normalizer hK.inf_eq
  refine ⟨φ.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp θ), ?_, ?_, ?_⟩
  · intro x l l' hl'
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
    exact Subtype.ext ((hθ x l).trans hl'.symm)
  · intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact hker x
  · intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rw [← hinn x, ← inner_map_congr e]
    constructor
    · rintro ⟨y, ⟨m, rfl⟩, hy⟩
      exact ⟨m, (MulAut.congr e).injective hy.symm⟩
    · rintro ⟨m, hm⟩
      exact ⟨MulAut.conj m, ⟨m, rfl⟩, by rw [hm]; rfl⟩

section Plus


theorem outer_involution_plus : ∃ x : MulAut omegaT, x * x = 1 ∧ x ∉ inner omegaT := by
  have h5 : (5 : ℕ) < 38 := by norm_num
  have hA : repPerm 5 ∈ autT := sylowT_le_autT (repPerm_spec h5).2
  refine ⟨autEquiv ⟨repPerm 5, hA⟩, ?_, ?_⟩
  · rw [← map_mul, MulEquiv.map_eq_one_iff]
    apply Subtype.ext
    change repPerm 5 * repPerm 5 = 1
    rw [← sq, ← orderOf_repPerm h5, pow_orderOf_eq_one]
  · rintro ⟨w, hw⟩
    rw [← autEquiv_omegaT] at hw
    have hval : (w : Equiv.Perm (Fin 360)) = repPerm 5 :=
      congrArg Subtype.val (autEquiv.injective hw)
    have hmem : repPerm 5 ∈ omegaT := hval ▸ w.2
    exact absurd ((repPerm_mem_omegaT_iff h5).1 hmem) (by decide)

theorem card_outer_plus {L : Type} [Group L] (hZ : center L = ⊥)
    (h : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) :
    Nat.card (Outer L) = 6 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT h
  rw [Nat.card_congr (equivalence ((mulEquivQuotientCenter hZ).symm.trans e)).toEquiv,
    card_outer_omegaT]

theorem involutionLifting_plus {L : Type} [Group L] [Finite L] (hZ : center L = ⊥)
    (h : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) : InvolutionLifting L := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT h
  obtain ⟨x, hx, hxI⟩ := outer_involution_plus
  obtain ⟨β, hβ, hβI⟩ :=
    exists_outer_involution_of_mulEquiv ((mulEquivQuotientCenter hZ).symm.trans e) hx hxI
  exact involutionLifting_of_card_outer (m := 3) (by rw [card_outer_plus hZ h]) (by decide) hβ hβI

theorem autEquiv_mem_inner_iff_plus (a : autT) :
    autEquiv a ∈ inner omegaT ↔ (a : Equiv.Perm (Fin 360)) ∈ omegaT := by
  constructor
  · rintro ⟨w, hw⟩
    rw [← autEquiv_omegaT] at hw
    have h1 := autEquiv.injective hw
    have hval : (w : Equiv.Perm (Fin 360)) = (a : Equiv.Perm (Fin 360)) := by rw [← h1]
    rw [← hval]
    exact w.2
  · intro ha
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [← autEquiv_omegaT]

theorem exists_model_automizer_plus {G : Type} [Group G] {t : G} {L : Subgroup G}
    (hK : StepK t L) (θ : L ≃* omega1T) :
    ∃ Θ : centralizer ({t} : Set G) →* autT,
      (∀ (x : centralizer ({t} : Set G)) (l l' : L), (l' : G) = x * l * (x : G)⁻¹ →
        (Θ x : Equiv.Perm (Fin 360)) * (omegaRestrictEquiv.symm (θ l) : Equiv.Perm (Fin 360)) *
          (Θ x : Equiv.Perm (Fin 360))⁻¹ = omegaRestrictEquiv.symm (θ l')) ∧
      (∀ x, Θ x = 1 ↔ (x : G) ∈ zpowers t) ∧
      ∀ x, (Θ x : Equiv.Perm (Fin 360)) ∈ omegaT ↔ (x : G) ∈ L ⊔ zpowers t := by
  obtain ⟨Θ, h1, h2, h3⟩ :=
    exists_automizer_of_equiv hK (θ.trans omegaRestrictEquiv.symm) autEquiv
  refine ⟨Θ, fun x l l' hl' => ?_, h2, fun x => (autEquiv_mem_inner_iff_plus _).symm.trans
    (h3 x)⟩
  have h := h1 x l l' hl'
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply] at h
  rw [← autEquiv_apply, h]

end Plus

section Minus


theorem outer_involution_minus :
    ∃ x : MulAut OmegaEightMinus.omegaT, x * x = 1 ∧ x ∉ inner OmegaEightMinus.omegaT := by
  have h0 : (0 : ℕ) < 36 := by norm_num
  have hA : OmegaEightMinus.repPerm 0 ∈ OmegaEightMinus.autT :=
    OmegaEightMinus.sylowT_le_autT (OmegaEightMinus.repPerm_spec h0).2
  refine ⟨OmegaEightMinus.autEquiv ⟨OmegaEightMinus.repPerm 0, hA⟩, ?_, ?_⟩
  · rw [← map_mul, MulEquiv.map_eq_one_iff]
    apply Subtype.ext
    change OmegaEightMinus.repPerm 0 * OmegaEightMinus.repPerm 0 = 1
    rw [← sq, ← OmegaEightMinus.orderOf_repPerm h0, pow_orderOf_eq_one]
  · rintro ⟨w, hw⟩
    rw [← OmegaEightMinus.autEquiv_omegaT] at hw
    have hval : (w : Equiv.Perm (Fin 136)) = OmegaEightMinus.repPerm 0 :=
      congrArg Subtype.val (OmegaEightMinus.autEquiv.injective hw)
    have hmem : OmegaEightMinus.repPerm 0 ∈ OmegaEightMinus.omegaT := hval ▸ w.2
    exact absurd ((OmegaEightMinus.repPerm_mem_omegaT_iff h0).1 hmem) (by decide)

theorem card_outer_minus {L : Type} [Group L]
    (h : CFSG.Blueprint.LieModel L .POmegaMinus 4 2 1) : Nat.card (Outer L) = 2 :=
  OmegaEightMinus.card_outer_of_lieModel_minus h

theorem involutionLifting_minus {L : Type} [Group L] [Finite L]
    (h : CFSG.Blueprint.LieModel L .POmegaMinus 4 2 1) : InvolutionLifting L := by
  obtain ⟨e⟩ := OmegaEightMinus.nonempty_mulEquiv_omegaT h
  obtain ⟨x, hx, hxI⟩ := outer_involution_minus
  obtain ⟨β, hβ, hβI⟩ := exists_outer_involution_of_mulEquiv e hx hxI
  exact involutionLifting_of_card_outer (m := 1) (by rw [card_outer_minus h]) (by decide) hβ hβI

theorem autEquiv_mem_inner_iff_minus (a : OmegaEightMinus.autT) :
    OmegaEightMinus.autEquiv a ∈ inner OmegaEightMinus.omegaT ↔
      (a : Equiv.Perm (Fin 136)) ∈ OmegaEightMinus.omegaT := by
  constructor
  · rintro ⟨w, hw⟩
    rw [← OmegaEightMinus.autEquiv_omegaT] at hw
    have h1 := OmegaEightMinus.autEquiv.injective hw
    have hval : (w : Equiv.Perm (Fin 136)) = (a : Equiv.Perm (Fin 136)) := by rw [← h1]
    rw [← hval]
    exact w.2
  · intro ha
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [← OmegaEightMinus.autEquiv_omegaT]

theorem exists_model_automizer_minus {G : Type} [Group G] {t : G} {L : Subgroup G}
    (hK : StepK t L) (θ : L ≃* OmegaEightMinus.omegaT) :
    ∃ Θ : centralizer ({t} : Set G) →* OmegaEightMinus.autT,
      (∀ (x : centralizer ({t} : Set G)) (l l' : L), (l' : G) = x * l * (x : G)⁻¹ →
        (Θ x : Equiv.Perm (Fin 136)) * (θ l : Equiv.Perm (Fin 136)) *
          (Θ x : Equiv.Perm (Fin 136))⁻¹ = θ l') ∧
      (∀ x, Θ x = 1 ↔ (x : G) ∈ zpowers t) ∧
      ∀ x, (Θ x : Equiv.Perm (Fin 136)) ∈ OmegaEightMinus.omegaT ↔ (x : G) ∈ L ⊔ zpowers t := by
  obtain ⟨Θ, h1, h2, h3⟩ := exists_automizer_of_equiv hK θ OmegaEightMinus.autEquiv
  refine ⟨Θ, fun x l l' hl' => ?_, h2, fun x => (autEquiv_mem_inner_iff_minus _).symm.trans
    (h3 x)⟩
  rw [← OmegaEightMinus.autEquiv_apply, h1 x l l' hl']

end Minus

end CFSG.EvenSmallLie.OmegaEight.Stage0
