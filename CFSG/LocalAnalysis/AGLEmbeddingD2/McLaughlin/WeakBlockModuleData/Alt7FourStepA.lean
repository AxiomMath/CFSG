module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourMain
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7FourNorm

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Module CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem sa_of_irr [Finite W] (ρ : Representation (ZMod 2) G W) {L : Subgroup G}
    (eL : ↥L ≃* alternatingGroup (Fin 7)) {U : Submodule (ZMod 2) W} (hU16 : Nat.card U = 16)
    (hUN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (Subgroup.normalizer (L : Set G)) U)
    (hirr : ∀ Z : Submodule (ZMod 2) W, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L Z → Z ≤ U → Z = ⊥ ∨ Z = U) :
    ∀ γ ∈ Subgroup.normalizer (L : Set G), ∃ l ∈ L, ∀ u ∈ U, ρ γ u = ρ l u := by
  classical
  intro γ hγ
  set N : Subgroup G := Subgroup.normalizer (L : Set G) with hN
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hdim : finrank (ZMod 2) ↥U = 4 := finrank_eq_four_of_card_sixteen hU16
  let ρ' : Representation (ZMod 2) ↥N ↥U := restRep ρ U N hUN
  let L' : Subgroup ↥N := L.subgroupOf N
  have hnorm : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).2 le_rfl
  let eL' : ↥L' ≃* alternatingGroup (Fin 7) := (Subgroup.subgroupOfEquivOfLe hLN).trans eL
  have hLinv : ∀ l ∈ L, ∀ u ∈ U, ρ l u ∈ U := fun l hl u hu => hUN l (hLN hl) u hu
  have hirr' : ∀ M : Submodule (ZMod 2) ↥U, (∀ l ∈ L', ∀ q ∈ M, ρ' l q ∈ M) → M = ⊥ ∨ M = ⊤ := by
    intro M hM
    have hZinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (M.map U.subtype) := by
      rintro l hl _ ⟨q, hq, rfl⟩
      exact ⟨ρ' ⟨l, hLN hl⟩ q, hM ⟨l, hLN hl⟩ (Subgroup.mem_subgroupOf.2 hl) q hq, rfl⟩
    rcases hirr _ hZinv (by rintro _ ⟨q, -, rfl⟩; exact q.2) with h | h
    · left
      refine eq_bot_iff.2 fun q hq => ?_
      have : (q : W) ∈ M.map U.subtype := ⟨q, hq, rfl⟩
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact Subtype.ext this
    · right
      refine eq_top_iff.2 fun q _ => ?_
      have : (q : W) ∈ M.map U.subtype := by rw [h]; exact q.2
      obtain ⟨q', hq', hqq⟩ := this
      have : q' = q := Subtype.ext hqq
      rwa [← this]
  have hg : (⟨γ, hγ⟩ : ↥N) ∈ Subgroup.normalizer (L' : Set ↥N) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]; trivial
  obtain ⟨l', hl', hall⟩ := a7_four_normalizer ρ' eL' hdim hirr' hg
  have hc := a7_four_centralizer_trivial ρ' eL' hdim hirr' hall
  refine ⟨(l' : G), Subgroup.mem_subgroupOf.1 hl', fun u hu => ?_⟩
  have hdec : (⟨γ, hγ⟩ : ↥N) = l' * (l'⁻¹ * ⟨γ, hγ⟩) := by group
  have h1 : ρ' (⟨γ, hγ⟩ : ↥N) ⟨u, hu⟩ = ρ' l' ⟨u, hu⟩ := by
    conv_lhs => rw [hdec, map_mul, Module.End.mul_apply, hc]
    rfl
  exact congrArg Subtype.val h1

theorem rep4_of_sixteen [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {L : Subgroup G} (eL : ↥L ≃* alternatingGroup (Fin 7))
    (HA : Alt7Hyp (alternatingGroup (Fin 7))) {U' : Submodule (ZMod 2) W}
    (hU'16 : Nat.card U' = 16) (hU'inv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L U')
    (hnt : ∃ l ∈ L, ∃ u ∈ U', ρ l u ≠ u) {T₁ : Subgroup G}
    (hT₁ : CFSG.QuasithinUnique.IsSylowTwoOf T₁ (Subgroup.normalizer (L : Set G)))
    {Fam : Set (Subgroup G)}
    (hFam : ∀ A ∈ Fam, A ≤ T₁ ∧ CFSG.IsElementaryAbelian 2 ↥A ∧ IsBestOffenderOn ρ A ⊤)
    (hA₀ : ∃ A ∈ Fam, ⁅L, A⁆ = L) :
    commOn ρ L ⊤ = U' ∧ ∃ ℓ : Submodule (ZMod 2) W, ℓ ≤ U' ∧
      (∀ A ∈ Fam, ∀ a ∈ A, ∀ v ∈ ℓ, ρ a v = v) ∧
      ∃ E : Subgroup G, E ≤ L ∧ Nat.card E = 9 ∧ ∀ e ∈ E, ∀ t ∈ T₁, (∀ v ∈ ℓ, ρ t v = v) →
        e * t * e⁻¹ ∈ T₁ ∧ ∀ v ∈ ℓ, ρ (e * t * e⁻¹) v = v := by
  classical
  obtain ⟨A₀, hA₀F, hLA₀⟩ := hA₀
  obtain ⟨hA₀T, hA₀2, hA₀b⟩ := hFam A₀ hA₀F
  have hAN : A₀ ≤ Subgroup.normalizer (L : Set G) := hA₀T.trans hT₁.1
  obtain ⟨hcomm, hfix⟩ := commOn_eq_of_card_sixteen ρ hρ eL hA₀2 hAN hLA₀ hA₀b hU'16 hU'inv hnt
  have hUUL : commOn ρ L U' = U' := by
    have := commOn_commOn_eq (ρ := ρ) hA₀2 hAN hLA₀
    rwa [hcomm] at this
  obtain ⟨hirr, -⟩ := a7_commOn_quot ρ hρ eL hA₀2 hAN hLA₀ hA₀b
  rw [hcomm, hfix] at hirr
  have hUN : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (Subgroup.normalizer (L : Set G)) U' := by
    rw [← hcomm]
    exact CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isInvariant_commOn_top ρ le_rfl
  have hSA := sa_of_irr ρ eL hU'16 hUN fun Z hZ hZU => by
    exact hirr Z hZ bot_le hZU
  have hU0 : U' ≠ ⊥ := by
    rintro rfl
    simp at hU'16
  exact ⟨hcomm, rep4 ρ hρ eL HA hcomm.symm hUUL hU0 hU'16 hfix hSA hT₁ hFam ⟨A₀, hA₀F, hLA₀⟩⟩

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
