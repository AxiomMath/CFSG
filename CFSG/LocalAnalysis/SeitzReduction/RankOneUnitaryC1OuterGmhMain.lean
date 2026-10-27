module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmhLocal
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmeLang
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmhConj
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmsSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

@[expose] def U3C1GmhTransInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P →
      ∀ a ∈ U₁ ⊓ centralizer ({t * w} : Set G), ∃ u ∈ U₁,
        (∀ x ∈ U₁ ⊓ centralizer ({t * w} : Set G), x * u = u * x) ∧
          u * (t * w) * u⁻¹ = a * (t * w)

@[expose] def U3C1GmhNArgInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P →
    (∀ x ∈ D, (t * w) * x * (t * w)⁻¹ ∈ D) →
    (∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁) →
      (∃ S : Sylow 2 G, (S : Subgroup G) = swapS₂ P U T) →
      (∀ g : G, g * t * g⁻¹ ∈ swapS₂ P U T → g * t * g⁻¹ ∈ U ⊔ T) →
      (∀ g : G, g * t * g⁻¹ ≠ t * w) →
      IsSylowOf 2 (swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
        (centralizer ({t * w} : Set G)) →
      ∀ H : Subgroup G, H ≤ centralizer ({t * w} : Set G) →
        H ≤ normalizer ((U₁ ⊓ centralizer ({t * w} : Set G) : Subgroup G) : Set G) →
        Odd (Nat.card H) → D ⊓ centralizer ({t * w} : Set G) ≤ H →
        (∀ h₁ ∈ H, ∀ h₂ ∈ H, ∀ x ∈ U₁ ⊓ centralizer ({t * w} : Set G),
          (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * x * (h₁ * h₂ * h₁⁻¹ * h₂⁻¹)⁻¹ = x) →
        (∀ X : Subgroup G, X ≤ U₁ ⊓ centralizer ({t * w} : Set G) →
          (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) → (∀ x ∈ X, t * x * t⁻¹ ∈ X) →
            X = ⊥ ∨ X = U₁ ⊓ centralizer ({t * w} : Set G)) → False

theorem u3C1GmhNArgInput_of_trans (hT : U3C1GmhTransInput) :
    U3C1GmhNArgInput := by
  intro G _ _ L f t T R₂ D d V U U₁ w s P hW hvD _ _ _ _ he H hHv hHF hHodd hDH hHab hirr
  have hS := hW.step
  have hL := hW.level
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨hAmem, -, -⟩ := hW.gmh_A_facts
  set F := U₁ ⊓ centralizer ({t * w} : Set G) with hF
  set A := F ⊔ zpowers (t * w) with hA
  set A₁ := szA₁ (szT₁ L T) with hA₁
  obtain ⟨e, heD, hev, hetr⟩ := hW.gmh_exists_torus hvD
  have heH : e ∈ H := hDH (mem_inf.mpr ⟨heD, mem_centralizer_singleton_iff.mpr hev⟩)
  have heU₁ : e ∈ normalizer (U₁ : Set G) := hL.D_le heD
  have heT₁ : e ∈ normalizer (szT₁ L T : Set G) := hS.cartan.le_normalizer heD
  have heA : e ∈ normalizer (A : Set G) := hW.gmh_mem_normalizer_A heU₁ hev
  have heF : e ∈ normalizer (F : Set G) :=
    gmh_mem_normalizer_of_conj_mem fun a ha => hW.gmh_conj_mem_F heU₁ hev ha
  have hefix : ∀ a ∈ A₁, e * a * e⁻¹ = a → a = 1 := by
    intro a ha hea
    refine h.gmh_eq_one_of_conj_eq hS2 hetr ha ?_
    calc e⁻¹ * a * e = e⁻¹ * (e * a * e⁻¹) * e := by rw [hea]
      _ = a := by group
  obtain ⟨y, hyU, hyF, hyN, hy⟩ := hW.gmh_exists_comm_sq_ne heT₁ hev hefix
  set Pn : Subgroup G := (U₁ ⊓ centralizer (F : Set G)) ⊓ normalizer (A : Set G) with hPn
  have hFP : F ≤ Pn := fun a ha => mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp ha).1,
    mem_centralizer_iff.mpr fun b hb => hW.F_comm hb ha⟩, Subgroup.le_normalizer (mem_sup_left ha)⟩
  have hPsq : ∀ x ∈ Pn, x ^ 2 ∈ A₁ := by
    obtain ⟨K, _, _, _, v, μ, hK, hcK, hμ⟩ := hS.exists_coords
    intro x hx
    exact hL.muOne_sq_mem_szA₁ hS hcK hW.mu hK hμ (mem_inf.mp (mem_inf.mp hx).1).1
  have hPtr : ∀ a ∈ F, ∃ u ∈ Pn, u * (t * w) * u⁻¹ = a * (t * w) := by
    intro a ha
    obtain ⟨u, hu, huF, hua⟩ := hT G L f t T R₂ D d V U U₁ w s P hW a ha
    have huC : u ∈ centralizer (F : Set G) := mem_centralizer_iff.mpr huF
    refine ⟨u, mem_inf.mpr ⟨mem_inf.mpr ⟨hu, huC⟩, ?_⟩, hua⟩
    apply gmh_mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨b, hb, h1 | h1⟩ := hAmem x hx <;> rw [h1]
    · rw [← huF b hb, mul_inv_cancel_right]
      exact mem_sup_left hb
    · rw [show u * (b * (t * w)) * u⁻¹ = (u * b * u⁻¹) * (u * (t * w) * u⁻¹) by group, hua,
        ← huF b hb, mul_inv_cancel_right]
      exact mul_mem (mem_sup_left hb) (mul_mem (mem_sup_left ha) (mem_sup_right (mem_zpowers _)))
  set R := (swapS₂ P U T ⊓ centralizer ({t * w} : Set G)) ⊓ centralizer (A : Set G) with hR
  have hRsyl : IsSylowOf 2 R (centralizer (A : Set G)) := hW.gmh_isSylowOf_centralizer he
  have hRcard : Nat.card R ≤ 2 * Nat.card A :=
    (Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)).trans hW.gmh_card_centralizer_le
  have heP : e ∈ normalizer (Pn : Set G) := by
    apply gmh_mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨hx1, hxA⟩ := mem_inf.mp hx
    obtain ⟨hxU, hxF⟩ := mem_inf.mp hx1
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_normalizer_iff.mp heU₁ x).mp hxU,
      gmh_conj_mem_centralizer heF hxF⟩, mul_mem (mul_mem heA hxA) (inv_mem heA)⟩
  have hmain := gmh_conj_mem_of_nArg (F := F) (A₁ := A₁) (P := Pn) (R := R) (H := H)
    (v := t * w) (e := e) (fun a ha b hb => hW.F_comm ha hb) (fun a ha => hW.F_sq ha)
    hW.gmh_szA₁_le_F
    (fun a ha => (mem_centralizer_singleton_iff.mp (mem_inf.mp ha).2).symm) hW.tw_sq
    (fun h' => hW.gmh_tw_not_mem_U₁ (mem_inf.mp h').1)
    hRsyl hRcard hFP inf_le_right (fun x hx => (mem_inf.mp (mem_inf.mp hx).1).2) hPsq hPtr
    hHv hHF hHodd hHab heH heP hetr ⟨y, mem_inf.mpr ⟨mem_inf.mpr ⟨hyU, hyF⟩, hyN⟩, hy⟩
  have htA₁ : ∀ a ∈ A₁, t * a * t⁻¹ ∈ A₁ := by
    intro a ha
    rw [← mem_centralizer_iff.mp h.mem_centralizer_szT₁ a (szA₁_le _ ha), mul_inv_cancel_right]
    exact ha
  have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  rcases hirr A₁ hW.gmh_szA₁_le_F (fun g hg a ha => hmain g hg a ha) htA₁ with h1 | h1
  · rw [h1, Subgroup.card_bot] at hA₁card
    rw [← hA₁card] at h4
    exact absurd h4 (by norm_num)
  · have h2 : Nat.card F = (2 ^ f) ^ 2 := hW.card_F
    rw [← h1, hA₁card] at h2
    have h3 : 2 ≤ 2 ^ f := le_trans (by norm_num) h4
    generalize 2 ^ f = q at h2 h3
    nlinarith

theorem u3C1OuterSwapHighInput_of_gmh (hC : U3C1GmsCharInput)
    (hc : U3C1GmsFusionInput) (hf : U3C1GmsClosureInput) (hg : U3C1GmsLayerInput)
    (hh : U3C1GmhNArgInput) : U3C1OuterSwapHighInput := by
  refine u3C1OuterSwapHighInput_of_false fun G _ _ L f t T R₂ D d V U U₁ w s P hW₀ => ?_
  obtain ⟨c, hc₁, hcD⟩ := hW₀.gmh_exists_normalizes
  have hW := hW₀.gmh_conj hc₁
  have h1 := u3C1GmsNormInput_holds G L f t T R₂ _ _ V U U₁ w s P hW
  have h2 := u3C1GmsSylowInput_of_char hC G L f t T R₂ _ _ V U U₁ w s P hW h1
  have h3 := hc G L f t T R₂ _ _ V U U₁ w s P hW h1 h2
  have h4 := u3C1GmsNotConjInput_holds G L f t T R₂ _ _ V U U₁ w s P hW
  have h5 := u3C1GmsExtremalInput_holds G L f t T R₂ _ _ V U U₁ w s P hW h1 h2 h3 h4
  obtain ⟨J, hJ1, hJ2, -, hJ3, hJ4⟩ := hf G L f t T R₂ _ _ V U U₁ w s P hW h1 h2 h3 h4 h5
  obtain ⟨H, hH1, hH2, hH3, hH4, hH5, hH6⟩ :=
    hg G L f t T R₂ _ _ V U U₁ w s P hW h1 h2 h3 h4 h5 J hJ1 hJ2 hJ3 hJ4
  exact hh G L f t T R₂ _ _ V U U₁ w s P hW hcD h1 h2 h3 h4 h5 H hH1 hH2 hH3 hH4 hH5 hH6

end CFSG.SeitzReduction.RankOne
