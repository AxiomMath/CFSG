module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterPositiveInputs
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialEqualParameterPositiveGeneric

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open _root_.CFSG.Semidihedral.FixedCoreNontrivial.Positive

namespace PositiveInputs

variable {G : Type} [Group G] [Finite G] {t s₀ d d₁ : G} {J : Subgroup G} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {κ : C t →* Equiv.Perm (Omega F)}
  {F' : Type} [Field F'] [Finite F']
  {φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃* CFSG.GorensteinWalter.PGL2 F'}

theorem inf_C_eq_bot (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1) {X : Subgroup G}
    (hX : IsPGroup p X)
    (hVX : Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤ Subgroup.normalizer (X : Set G)) :
    X ⊓ C t = ⊥ := by
  apply (hI.eq_bot_of_mod_four_eq_one he).2.1 _ inf_le_right hX.to_inf_left
  have hs₀X : s₀ ∈ Subgroup.normalizer (X : Set G) :=
    hVX (Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀))
  have hs₀C : s₀ ∈ Subgroup.normalizer ((C t : Subgroup G) : Set G) :=
    Subgroup.le_normalizer h.localData.s_mem_C
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.mp hs₀X y)
    (Subgroup.mem_normalizer_iff.mp hs₀C y)

omit [Finite G] in
theorem conj_mem_V {τ : G} (hτt : τ * t * τ⁻¹ = s₀) (hτs : τ * s₀ * τ⁻¹ = t * s₀) {v : G}
    (hv : v ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers s₀) :
    τ * v * τ⁻¹ ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ := by
  have hle : (Subgroup.zpowers t ⊔ Subgroup.zpowers s₀).map (MulAut.conj τ).toMonoidHom ≤
      Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      change τ * t * τ⁻¹ ∈ _
      rw [hτt]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀)
    · rw [Subgroup.zpowers_le]
      change τ * s₀ * τ⁻¹ ∈ _
      rw [hτs]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀))
  exact hle ⟨v, hv, rfl⟩

omit [Finite G] in
theorem le_normalizer_map_conj {τ : G} (hτt : τ * t * τ⁻¹ = s₀) (hτs : τ * s₀ * τ⁻¹ = t * s₀)
    {X : Subgroup G}
    (hVX : Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤ Subgroup.normalizer (X : Set G)) :
    Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤
      Subgroup.normalizer ((X.map (MulAut.conj τ⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  intro v hv
  have hu := hVX (conj_mem_V hτt hτs hv)
  have e : τ⁻¹ * (τ * v * τ⁻¹) * τ⁻¹⁻¹ = v := by group
  rw [← e]
  exact conj_mem_normalizer_map τ⁻¹ hu

omit [Finite G] in
theorem inf_centralizer_eq_bot_of_conj {τ : G} (hτt : τ * t * τ⁻¹ = s₀)
    (hτs : τ * s₀ * τ⁻¹ = t * s₀) {a b : G} (hab : τ⁻¹ * b * τ = a)
    (hA : ∀ X : Subgroup G, IsPGroup p X →
      Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤ Subgroup.normalizer (X : Set G) →
        X ⊓ Subgroup.centralizer {a} = ⊥)
    {X : Subgroup G} (hX : IsPGroup p X)
    (hVX : Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤ Subgroup.normalizer (X : Set G)) :
    X ⊓ Subgroup.centralizer {b} = ⊥ := by
  have h1 := hA _ (hX.map _) (le_normalizer_map_conj hτt hτs hVX)
  rw [eq_bot_iff]
  intro x hx
  have hmem : τ⁻¹ * x * τ⁻¹⁻¹ ∈
      X.map (MulAut.conj τ⁻¹).toMonoidHom ⊓ Subgroup.centralizer {a} := by
    refine Subgroup.mem_inf.mpr ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    rw [← hab]
    calc τ⁻¹ * x * τ⁻¹⁻¹ * (τ⁻¹ * b * τ) = τ⁻¹ * (x * b) * τ := by group
      _ = τ⁻¹ * (b * x) * τ := by rw [hxb]
      _ = τ⁻¹ * b * τ * (τ⁻¹ * x * τ⁻¹⁻¹) := by group
  rw [h1, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  calc x = τ * (τ⁻¹ * x * τ⁻¹⁻¹) * τ⁻¹ := by group
    _ = 1 := by rw [hmem]; group

theorem eq_bot_of_V_le_normalizer (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1) {X : Subgroup G}
    (hX : IsPGroup p X)
    (hVX : Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤ Subgroup.normalizer (X : Set G)) :
    X = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨τ, hτt, hτs⟩ := h.three_cycle
  have hA : ∀ Y : Subgroup G, IsPGroup p Y →
      Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤ Subgroup.normalizer (Y : Set G) →
        Y ⊓ Subgroup.centralizer {t} = ⊥ := fun Y hY hVY => hI.inf_C_eq_bot h he hY hVY
  have hB : ∀ Y : Subgroup G, IsPGroup p Y →
      Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤ Subgroup.normalizer (Y : Set G) →
        Y ⊓ Subgroup.centralizer {s₀} = ⊥ := fun Y hY hVY =>
    inf_centralizer_eq_bot_of_conj hτt hτs (by rw [← hτt]; group) hA hY hVY
  have hC : X ⊓ Subgroup.centralizer {t * s₀} = ⊥ :=
    inf_centralizer_eq_bot_of_conj hτt hτs (by rw [← hτs]; group) hB hX hVX
  have hXodd : Odd (Nat.card X) := odd_card_of_isPGroup h.odd hX
  have ht := (hI.conj_eq_inv_of_inf_centralizer_eq_bot hXodd h.localData.t_sq
    (hVX (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))) (hA X hX hVX)).1
  have hs := (hI.conj_eq_inv_of_inf_centralizer_eq_bot hXodd h.localData.s_sq
    (hVX (Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀))) (hB X hX hVX)).1
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ X ⊓ Subgroup.centralizer {t * s₀} := by
    refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : t * s₀ * x * (t * s₀)⁻¹ = x := by
      calc t * s₀ * x * (t * s₀)⁻¹ = t * (s₀ * x * s₀⁻¹) * t⁻¹ := by group
        _ = t * x⁻¹ * t⁻¹ := by rw [hs x hx]
        _ = (t * x * t⁻¹)⁻¹ := by group
        _ = x := by rw [ht x hx, inv_inv]
    calc x * (t * s₀) = t * s₀ * x * (t * s₀)⁻¹ * (t * s₀) := by rw [e1]
      _ = t * s₀ * x := by group
  rw [hC] at hx'
  exact hx'

theorem not_le_normalizer_of_isKleinFour (hI : PositiveInputs G t s₀ d J p f)
    (h : EqualParameterData G t s₀ d d₁ J p f F κ F' φ) (he : p ^ f % 4 = 1)
    {P T : Subgroup G} (hP : IsPGroup p P) (hP1 : P ≠ ⊥) (hT : IsKleinFour T) :
    ¬ T ≤ Subgroup.normalizer (P : Set G) := by
  intro hTP
  obtain ⟨g, hg⟩ := h.four_conj T hT
  have hVP : Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ ≤
      Subgroup.normalizer ((P.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [← hg]
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_normalizer_map g (hTP hx)
  have hbot := hI.eq_bot_of_V_le_normalizer h he (hP.map _) hVP
  exact hP1 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hbot)

end PositiveInputs

end CFSG.Semidihedral.FixedCoreNontrivial
