module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISpSocleSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISpSocleRow

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem sp_socle_extension {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    [IsSimpleGroup W] (hWnonab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2)
    {r e : ℕ} (hr : 2 ≤ r) (he : 1 ≤ e) (hre : ¬ (r = 2 ∧ e = 1)) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ e) (φ : W ≃* StatedProj (StatedSp r K)) :
    ∃ ρ : A →* MulAut (StatedProj (StatedSp r K)), Function.Injective ρ ∧
      (∀ w : W, ρ w = MulAut.conj (φ w)) ∧
      (∀ ρ' : A →* MulAut (StatedProj (StatedSp r K)), (∀ w : W, ρ' w = MulAut.conj (φ w)) →
        ρ' = ρ) ∧
      ∃ (g : StatedSp r K) (σ : K ≃+* K), σ ≠ 1 ∧ ρ a = spInner r K g * fieldAut r K σ := by
  have : IsSimpleGroup (StatedProj (StatedSp r K)) := φ.symm.isSimpleGroup
  have hnabP : ∃ x y : StatedProj (StatedSp r K), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hWnonab
    refine ⟨φ x, φ y, fun hc => hxy (φ.injective ?_)⟩
    rw [map_mul, map_mul, hc]
  have hZ := center_eq_bot_of_isSimpleGroup hnabP
  obtain ⟨ρ, hinj, hρW, huniq, -⟩ := socle_extension hCW φ hZ
  exact ⟨ρ, hinj, hρW, huniq,
    sp_socle_classify ha hLCW hr he hre hK φ hinj hρW hZ hp2 hsrc⟩

theorem faithful_even_symplectic_socle_small_source_involution_selector
    {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hWsimple : IsSimpleGroup W) (hWnonab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    {p f : ℕ} (_hp : p.Prime) (hp2 : p ≠ 2) (_hf : 1 ≤ f)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2)
    {r e : ℕ} (hr : 2 ≤ r) (he : 1 ≤ e) (hre : ¬ (r = 2 ∧ e = 1)) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ e) (φ : W ≃* StatedProj (StatedSp r K)) :
    ∃ ρ : A →* MulAut (StatedProj (StatedSp r K)), Function.Injective ρ ∧
      (∀ w : W, ρ w = MulAut.conj (φ w)) ∧
      (∀ ρ' : A →* MulAut (StatedProj (StatedSp r K)), (∀ w : W, ρ' w = MulAut.conj (φ w)) →
        ρ' = ρ) ∧
      r = 2 ∧ e = 2 ∧ p = 3 ∧ f = 2 ∧ IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧
      StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∧
      IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∧
      ¬ StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 ∧
      ∀ (φ₂ : W ≃* StatedProj (StatedSp 2 K)) (σ : K ≃+* K), (∀ t, σ t = t ^ 2) →
      ∀ γ : MulAut (StatedProj (StatedSp 2 K)),
        (∀ g : StatedSp 2 K, γ (proj 2 K g) = proj 2 K (exceptionalSpAut K g)) →
      ∃ ρ₂ : A →* MulAut (StatedProj (StatedSp 2 K)), Function.Injective ρ₂ ∧
        (∀ w : W, ρ₂ w = MulAut.conj (φ₂ w)) ∧
        (∀ ρ' : A →* MulAut (StatedProj (StatedSp 2 K)),
          (∀ w : W, ρ' w = MulAut.conj (φ₂ w)) → ρ' = ρ₂) ∧
        (let β := fieldAut 2 K σ
         let ι₀ := (spInner 2 K).comp (subfieldSpHom 2 (descentField σ))
         let N₀ := ι₀.range
         let N₀' : Subgroup (MulAut (StatedProj (StatedSp 2 K))) := ⁅N₀, N₀⁆
         let M₀ := centralizer {β}
         orderOf γ = 4 ∧ γ ^ 2 = β ∧ Function.Injective ι₀ ∧
         M₀ = N₀ ⊔ zpowers γ ∧ N₀ ⊓ zpowers γ = ⊥ ∧ (∀ n ∈ N₀, γ * n * γ⁻¹ ∈ N₀) ∧
         (∀ α ∈ M₀, ∃! q : StatedSp 2 (descentField σ) × Fin 4, α = ι₀ q.1 * γ ^ (q.2 : ℕ)) ∧
         M₀ ⊓ OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) = N₀ ∧
         (N₀.subgroupOf M₀).Normal ∧
         (∃ E : N₀ ≃* PresentationLocal.sympFour, ∀ x : N₀,
           (x : MulAut (StatedProj (StatedSp 2 K))) ∈ N₀' ↔
             PresentationLocal.omegaPerm (E x) ∈ alternatingGroup (Fin 6)) ∧
         Nonempty (N₀ ≃* Equiv.Perm (Fin 6)) ∧ Nonempty (N₀' ≃* alternatingGroup (Fin 6)) ∧
         ∃ h : StatedSp 2 K,
           ρ₂ a = spInner 2 K h * β * (spInner 2 K h)⁻¹ ∧
           (centralizer {a}).map ρ₂ = ρ₂.range ⊓
             M₀.map (MulAut.conj (spInner 2 K h)).toMonoidHom ∧
           (W ⊓ centralizer {a}).map ρ₂ = N₀.map (MulAut.conj (spInner 2 K h)).toMonoidHom ∧
           L.map ρ₂ = N₀'.map (MulAut.conj (spInner 2 K h)).toMonoidHom ∧
           ∃ θ : L ≃* N₀', ∀ l : L,
             (θ l : MulAut (StatedProj (StatedSp 2 K))) =
               (spInner 2 K h)⁻¹ * ρ₂ l * spInner 2 K h) := by
  classical
  have hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}) :=
    isComponentOf_of_le hL (le_inf hLW hL.1) inf_le_right
  have hLnab := exists_ne_commute_of_isQuasisimple hL.2.2
  obtain ⟨ρ, hinj, hρW, huniq, g, σ₁, hσ₁, hρa⟩ :=
    sp_socle_extension hWnonab hCW ha hLCW hp2 hsrc hr he hre hK φ
  have hF := sp_socle_field_case ha hLCW hr he hK φ hinj hρW hσ₁ hρa hp2 hsrc
  have hr2 : r = 2 := hF.1
  have he2 : e = 2 := hF.2.1
  refine ⟨ρ, hinj, hρW, huniq, hr2, he2, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.2.2.2.2.1, hLnab,
    hF.2.2.2.2.2.1, hF.2.2.2.2.2.2.1, hF.2.2.2.2.2.2.2.1, fun φ₂ σ hσ γ hγ => ?_⟩
  subst he2
  obtain ⟨ρ₂, hinj₂, hρW₂, huniq₂, g₂, σ₂, hσ₂, hρa₂⟩ :=
    sp_socle_extension hWnonab hCW ha hLCW hp2 hsrc le_rfl he (by omega) hK φ₂
  have hF₂ := sp_socle_field_case ha hLCW le_rfl he hK φ₂ hinj₂ hρW₂ hσ₂ hρa₂ hp2 hsrc
  have hσσ : σ₂ = σ := RingEquiv.ext fun t => by rw [hF₂.2.2.2.2.1 t, hσ t]
  subst hσσ
  obtain ⟨hι₀, hIC, hE, hP6, hA6, h, hh, hCA, hCWa, hLimg, θ, hθ⟩ :=
    hF₂.2.2.2.2.2.2.2.2.2
  obtain ⟨hord, hγ2, hM, hinf, hnorm, huq, hNn⟩ := sp_socle_row hK hσ hγ hι₀ hIC
  exact ⟨ρ₂, hinj₂, hρW₂, huniq₂, hord, hγ2, hι₀, hM, hinf, hnorm, huq, hIC, hNn, hE, hP6, hA6,
    h, hh, hCA, hCWa, hLimg, θ, hθ⟩

end CFSG.ComponentClassification.OutcomeLocal
