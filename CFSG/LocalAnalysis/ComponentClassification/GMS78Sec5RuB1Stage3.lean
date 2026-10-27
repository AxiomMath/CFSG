module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1SC
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Ru
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1CentA
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Sylow
public import CFSG.LocalAnalysis.ComponentClassification.GMS78GapHKSAffineProof
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Gold
public import CFSG.LocalAnalysis.ComponentClassification.GMS78GapHKS

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools

@[expose] def B1Stage3Transport : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T L₀ R R₂ : Subgroup G) (y d f : G),
    SzMinCounter G L 1 → Sec3.SzR G L T R 1 y d → NoStronglyClosedAbelian G →
    Sec3.IsR₂ L T R R₂ d → Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4 →
    Sec3.B1Frame L T L₀ → f ∈ gmsA L T → f ≠ 1 →
    ∃ (S₀ X : Subgroup G) (g : G), IsSylowOf 2 S₀ L₀ ∧ R ≤ S₀ ∧ (∀ s ∈ S₀, s * f = f * s) ∧
      gmsA L T ≤ X ∧ X ≤ S₀ ∧ (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) ∧ (∀ x ∈ X, x * x = 1) ∧
      Nat.card X = 32 ∧ (∀ l ∈ L₀ ⊓ centralizer ({f} : Set G), ∀ x ∈ X, l⁻¹ * x * l ∈ X) ∧
      g ∈ L₀ ⊓ centralizer ({f} : Set G) ∧ Odd (orderOf g) ∧
      (∀ U : Subgroup G, f ∈ U → U ≤ X → g ∈ normalizer (U : Set G) →
        U = zpowers f ∨ U = X) ∧
      ∀ u ∈ S₀, u * u = 1 → u ∉ R → ∃ l ∈ L₀,
        (gmsA L T).map (MulAut.conj l).toMonoidHom ≤ S₀ ⊓ centralizer ({u} : Set G)

@[expose] def B1Stage3Alpha : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T R R₂ : Subgroup G) (y d : G),
    SzMinCounter G L 1 → Sec3.SzR G L T R 1 y d → NoStronglyClosedAbelian G →
    Sec3.IsR₂ L T R R₂ d → Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4 →
    ∀ g : G, (gmsA L T).map (MulAut.conj g).toMonoidHom ≤
      centralizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) →
      g ∈ normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G)

theorem b1Stage3Components :
    ∀ (G : Type) [Group G] [Finite G] (W X P S₀ : Subgroup G) (f g : G),
      Odd (Nat.card W) → W ≤ centralizer (S₀ : Set G) →
      AS76b.oddCoreIn (centralizer ({f} : Set G)) = ⊥ →
      IsSylowOf 2 S₀ (centralizer ({f} : Set G)) → X ≤ S₀ →
      (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) → Nat.card X = 32 → f ∈ X → orderOf f = 2 →
      (∀ x ∈ X, ∀ h ∈ centralizer ({f} : Set G), h⁻¹ * x * h ∈ S₀ → h⁻¹ * x * h ∈ X) →
      g ∈ centralizer ({f} : Set G) → g ∈ normalizer (X : Set G) → Odd (orderOf g) →
      (∀ U : Subgroup G, f ∈ U → U ≤ X → g ∈ normalizer (U : Set G) →
        U = zpowers f ∨ U = X) →
      IsPGroup 2 P → centralizer (X : Set G) = P ⊔ W →
      normalizer (X : Set G) ≤ normalizer (W : Set G) →
      centralizer ({f} : Set G) ≤ normalizer (W : Set G) :=
  fun _ _ _ _ _ _ _ _ _ hW hWS₀ hO hS₀ hXS₀ hXab hX hfX hf hcl hgf hgX hg hirr hP hCX hNX =>
    centralizer_le_normalizer_of_irreducible hW hWS₀ hO hS₀ hXS₀ hXab hX hfX hf hcl hgf hgX hg
      hirr hP hCX hNX

theorem b1Stage3_of
    (hTr : B1Stage3Transport) (hα : B1Stage3Alpha) : B1Stage3 := by
  have hD := b1Stage3Components
  intro G _ _ L T L₀ hM h3 hF h4 hW hfr f hfA hf1 hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Odd (Nat.card (center L)) := hM.hyp.odd_card_center hF
  have h34 : NoStronglyClosedAbelian G := fun S _ hAS hAab hA1 hcl =>
    hM.hyp.lemma34 S hAS hAab hA1 hcl
  obtain ⟨eS⟩ := hM.nonempty_mulEquiv_sz
  have hX := h3.facts_of_sz hF hZ hM.one_le eS
  have h313 := h3.lemma313_of_sz_of_odd hF hZ hM.one_le eS
  obtain ⟨y₀, hy₀⟩ := hX.exists_isTorus h3
  obtain ⟨R, y, d, hS⟩ := h3.exists_szR hF hZ hM.one_le eS
    (hy₀.exists_translation_of_affine h313 hX h3 hF hksRegularNormalAffine)
  obtain ⟨R₂, hR₂⟩ := hS.exists_isR₂ h34
  obtain ⟨S₀, X, g, hS₀, hRS₀, hS₀f, hAX, hXS₀, hXab, hX2, hX32, hF4, hg, hgo, hirr, hF8⟩ :=
    hTr G L T L₀ R R₂ y d f hM hS h34 hR₂ h4 hfr hfA hf1
  set W := AS76b.oddCoreIn (centralizer (L : Set G)) with hWdef
  have hWL : W ≤ centralizer (L₀ : Set G) := hfr.centralizer_eq.ge
  have hNW : normalizer (W : Set G) ≤ L₀ ⊔ W := hfr.normalizer_eq.le
  have hS₀L : S₀ ≤ L₀ := hS₀.le
  have hLW : L₀ ≤ centralizer (W : Set G) := le_centralizer_iff.mp hWL
  have hTS₀ : T ≤ S₀ := (le_sup_left.trans hR₂.sup_eq.le).trans hRS₀
  have hS₀G : IsSylowOf 2 S₀ ⊤ := hM.isSylowOf_top_of_isSylowOf h3 hF hZ h4 hfr.inf_eq hWL hNW
    (fun t ht ht1 => hM.centralizer_le_normalizer_oddCoreIn h3 hF ht ht1) hS₀ hTS₀
  have hS₀C : S₀ ≤ centralizer ({f} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hS₀f s hs)
  have hRA : R ≤ centralizer (gmsA L T : Set G) := fun _ hr =>
    mem_centralizer_iff.mpr fun _ hb => (hS.commute_gmsA hr hb).symm
  have hcl := forall_conj_mem_of_conj_control_centralizer hWL hNW hS₀G hS₀f hS₀L hfA hAX hXS₀
    hXab hX2 hRA (hα G L T R R₂ y d hM hS h34 hR₂ h4) hF4 hF8
  have hXW : X ≤ centralizer (W : Set G) := hXS₀.trans (hS₀L.trans hLW)
  have hfX : f ∈ X := hAX hfA
  have hf2 : orderOf f = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hX2 f hfX) hf1
  have hgX : g ∈ normalizer (X : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := hF4 g⁻¹ (inv_mem hg) x hx
      rwa [inv_inv] at h1
    · intro hx
      have h1 := hF4 g hg _ hx
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1
  have hP2 : IsPGroup 2 (R ⊓ centralizer (X : Set G) : Subgroup G) :=
    (hS₀.isPGroup.to_le hRS₀).to_inf_left
  exact hD G W X (R ⊓ centralizer (X : Set G)) S₀ f g (AS76b.odd_card_oddCoreIn _)
    (hWL.trans (centralizer_le hS₀L)) hP (hS₀G.of_le hS₀C le_top) hXS₀ hXab hX32 hfX hf2 hcl
    (mem_inf.mp hg).2 hgX hgo hirr hP2
    (hM.centralizer_eq_sup_of_gmsA_le hS h34 hR₂ h4 hAX hXW)
    (hM.normalizer_le_normalizer_oddCoreIn_of_gmsA_le hS h34 hR₂ h4 hAX hXW)

end CFSG.ComponentClassification.GMS78
