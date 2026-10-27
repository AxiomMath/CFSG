module

public import CFSG.LocalAnalysis.GH72.Sec5NineteenTools
import CFSG.Foundations.MaxOrderThompson
import CFSG.LocalAnalysis.ABGTheoremB.IV1
public import CFSG.LocalAnalysis.GH72.Sec4Bar
public import CFSG.LocalAnalysis.GH72.Sec4CStruct
public import CFSG.LocalAnalysis.GH72.Sec5Eighteen

public section

namespace CFSG.GH72

open Subgroup
open scoped Pointwise

namespace G5d

open CFSG.ABGLocalTools (IsSylowOf)

section Helpers

variable {G : Type*} [Group G] [Finite G]

private theorem ambientMaxCardZJ_ne_bot' {t : ℕ} (ht : t.Prime) {F : Subgroup G}
    (hF : IsPGroup t F) (hF1 : F ≠ ⊥) : CFSG.ambientMaxCardZJ F ≠ ⊥ := by
  have : Nontrivial F := (nontrivial_iff_ne_bot F).mpr hF1
  rw [CFSG.ambientMaxCardZJ_eq_map, CFSG.maxCardZJ_eq_orderZJ, Ne,
    map_eq_bot_iff_of_injective _ F.subtype_injective]
  exact CFSG.orderZJ_ne_bot_of_isPGroup ht hF

private theorem eq_of_inf_normalizer_le' {t : ℕ} [Fact t.Prime] {F R : Subgroup G}
    (hR : IsPGroup t R) (hFR : F ≤ R) (h : R ⊓ normalizer (F : Set G) ≤ F) : F = R := by
  by_contra hne
  have : Group.IsNilpotent R := hR.isNilpotent
  have hU : F.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [subgroupOf_eq_top] at htop
    exact hne (le_antisymm hFR htop)
  obtain ⟨y, hy, hyU⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hU)
  rw [← subgroupOf_normalizer_eq hFR, mem_subgroupOf] at hy
  exact hyU (mem_subgroupOf.mpr (h ⟨y.2, hy⟩))

theorem covers_normalizer_ambientMaxCardZJ_of_isSylowOf {t : ℕ} [Fact t.Prime]
    {X T M₀ : Subgroup G} {x₁ : G} (hX2 : IsPGroup 2 X) (hXc : X ≤ centralizer (X : Set G))
    (hx₁ : x₁ ∈ X) (hXT : X ≤ normalizer (T : Set G))
    (hT : IsSylowOf t T (O (C x₁))) (hM₀ : M₀ ≤ centralizer (X : Set G))
    (hOM₀ : O (centralizer (X : Set G)) ≤ M₀) :
    Covers (normalizer (CFSG.ambientMaxCardZJ T : Set G)) M₀ (O (centralizer (X : Set G))) := by
  have h := covers_C_inf_normalizer_of_isSylowOf hX2 hXc hx₁ hXT hT hM₀ hOM₀
  unfold Covers at h ⊢
  refine h.trans (sup_le_sup_right ?_ _)
  rintro m ⟨⟨-, hmT⟩, hmM₀⟩
  exact ⟨CFSG.normalizer_le_normalizer_ambientMaxCardZJ T hmT, hmM₀⟩

end Helpers

section Inputs

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_bar_data_of_W {H W X Y A : Subgroup G} {L₁ : Subgroup (Bar H)} (hWH : W ≤ H)
    (hYW : Y ≤ W) (hWn : ((W ⊔ O H).subgroupOf H).Normal) (hWs : IsL2OrA7 (bar H W) 5)
    (hL₁n : L₁.Normal) (hXL₁ : bar H X ≤ L₁) (hinf : L₁ ⊓ bar H W = ⊥)
    (hL₁c : L₁ ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)))
    (hL₁s : IsL2PGL2OrA7OrV4 L₁ ∨ IsPGroup 2 L₁)
    (hΓ : L₁ ⊔ bar H W ⊔ normalizer ((bar H A : Subgroup (Bar H)) : Set (Bar H)) = ⊤) :
    ∃ L L₁ : Subgroup (Bar H), L.Normal ∧ L₁.Normal ∧ IsL2OrA7 L 5 ∧
      (IsL2PGL2OrA7OrV4 L₁ ∨ IsPGroup 2 L₁) ∧ L₁ ≤ centralizer (L : Set (Bar H)) ∧
      L ⊓ L₁ = ⊥ ∧ bar H Y ≤ L ∧ bar H X ≤ L₁ ∧
      L₁ ⊔ L ⊔ normalizer ((bar H A : Subgroup (Bar H)) : Set (Bar H)) = ⊤ := by
  refine ⟨bar H W, L₁, ?_, hL₁n, hWs, hL₁s, hL₁c, by rw [inf_comm]; exact hinf,
    G4c.bar_mono hYW, hXL₁, hΓ⟩
  rw [← G4c.bar_sup_O hWH]
  exact hWn.map _ (QuotientGroup.mk'_surjective _)

end Inputs

end G5d

namespace Sec5Roles

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (ρ : Sec5Roles G A)

theorem exists_bar_data_of_h1R
    (hHns : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5))
    (h1ML : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, ∃ L₁ : Subgroup (Bar H), W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧
        Covers W ρ.M₀ (O ρ.M) ∧ H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧
        ((W ⊔ O H).subgroupOf H).Normal ∧ O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer ((bar H A : Subgroup (Bar H)) : Set (Bar H)) ∧
        L₁.Normal ∧ bar H ρ.X ≤ L₁ ∧ L₁ ⊓ bar H W = ⊥ ∧
        L₁ ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)) ∧
        (IsL2PGL2OrA7OrV4 L₁ ∨ IsPGroup 2 L₁) ∧
        L₁ ⊔ bar H W ⊔ normalizer ((bar H A : Subgroup (Bar H)) : Set (Bar H)) = ⊤)
    {H : Subgroup G} (hH : H ≠ ⊤) (hAH : A ≤ H) (hcov : Covers H ρ.M₀ (O ρ.M)) :
    ∃ L L₁ : Subgroup (Bar H), L.Normal ∧ L₁.Normal ∧ IsL2OrA7 L 5 ∧
      (IsL2PGL2OrA7OrV4 L₁ ∨ IsPGroup 2 L₁) ∧ L₁ ≤ centralizer (L : Set (Bar H)) ∧
      L ⊓ L₁ = ⊥ ∧ bar H ρ.Y ≤ L ∧ bar H ρ.X ≤ L₁ ∧
      L₁ ⊔ L ⊔ normalizer ((bar H A : Subgroup (Bar H)) : Set (Bar H)) = ⊤ := by
  obtain ⟨W, L₁, hWHM, hYW, hcovW, -, hWn, hOW, -, -, -, hL₁n, hXL₁, hinf, hL₁c, hL₁s, hΓ⟩ :=
    h1ML H hH hAH hcov
  exact G5d.exists_bar_data_of_W (hWHM.trans inf_le_left) hYW hWn
    (G5d.isL2OrA7_bar_of_covers (hWHM.trans inf_le_left) (hWHM.trans inf_le_right)
      ρ.M₀_le_normalizer_O_M hcovW hOW hHns) hL₁n hXL₁ hinf hL₁c hL₁s hΓ

end Sec5Roles

open G5d

namespace Sec5ConfigTR

open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  {𝔠 : Sec5ConfigR ρ p} (𝔱 : Sec5ConfigTR 𝔠)

theorem lemma_5_19_of
    (h47 : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₂ ρ.M₀ ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (A : Set G)) ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (ρ.S₂ : Set G)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → O2 (C x) = (O2 ρ.M ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (ρ.M₀ ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (hHns : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5))
    (h1M : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H A : Set (Bar H)))
    (h1ML : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, ∃ L₁ : Subgroup (Bar H), W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧
        Covers W ρ.M₀ (O ρ.M) ∧ H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧
        ((W ⊔ O H).subgroupOf H).Normal ∧ O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer ((bar H A : Subgroup (Bar H)) : Set (Bar H)) ∧
        L₁.Normal ∧ bar H ρ.X ≤ L₁ ∧ L₁ ⊓ bar H W = ⊥ ∧
        L₁ ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)) ∧
        (IsL2PGL2OrA7OrV4 L₁ ∨ IsPGroup 2 L₁) ∧
        L₁ ⊔ bar H W ⊔ normalizer ((bar H A : Subgroup (Bar H)) : Set (Bar H)) = ⊤)
    (h51 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H →
      (Covers H ρ.M₀ (O ρ.M) → (∃ x ∈ ρ.X, x ≠ 1 ∧ ∃ P ≤ H, IsPGroup 𝔱.t P ∧
        A ≤ normalizer (P : Set G) ∧ P ≤ O (C x) ∧ ¬ ρ.Y ≤ centralizer (P : Set G)) →
        Sec4Setting.PConstrainedWrt 𝔱.t A H ρ.Y) ∧
      (Covers H ρ.N₀ (O ρ.N) → (∃ y ∈ ρ.Y, y ≠ 1 ∧ ∃ P ≤ H, IsPGroup 𝔱.t P ∧
        A ≤ normalizer (P : Set G) ∧ P ≤ O (C y) ∧ ¬ ρ.X ≤ centralizer (P : Set G)) →
        Sec4Setting.PConstrainedWrt 𝔱.t A H ρ.X))
    (h52core : ∀ H F : Subgroup G, CFSG.IsPLocal 𝔱.t H → A ≤ H →
      Covers H ρ.M₀ (O ρ.M) → Sec4Setting.PConstrainedWrt 𝔱.t A H ρ.Y →
      IsMaxInvIn 𝔱.t A H F →
      Covers (normalizer (CFSG.ambientMaxCardZJ F : Set G)) ρ.M₀ (O ρ.M))
    (hPGL : ∀ {Γ : Type} [Group Γ] [Finite Γ], CFSG.oddCore Γ = ⊥ →
      ∀ {L L₁ Z V : Subgroup Γ}, L.Normal → L₁.Normal → IsL2OrA7 L 5 →
      (IsL2PGL2OrA7OrV4 L₁ ∨ IsPGroup 2 L₁) → L₁ ≤ centralizer (L : Set Γ) → L ⊓ L₁ = ⊥ →
      IsKleinFour V → V ≤ L → IsKleinFour Z → Z ≤ L₁ →
      L₁ ⊔ L ⊔ normalizer ((Z ⊔ V : Subgroup Γ) : Set Γ) = ⊤ →
      IsSylowOf 2 (Z ⊔ V) (centralizer ((Z ⊔ V : Subgroup Γ) : Set Γ)) →
      ∀ {p t : ℕ}, p.Prime → t.Prime → p ≠ 2 → t ≠ 2 → p ≠ t →
      ∀ {P F : Subgroup Γ}, IsMaxInvIn p (Z ⊔ V) ⊤ P → Z ≤ centralizer (P : Set Γ) →
      IsPGroup t F → Z ⊔ V ≤ normalizer (F : Set Γ) →
      (F : Set Γ) * (P : Set Γ) = (P : Set Γ) * (F : Set Γ) →
      ∃ F' : Subgroup Γ, IsMaxInvIn t (Z ⊔ V) ⊤ F' ∧ F ≤ F' ∧
        (F' : Set Γ) * (P : Set Γ) = (P : Set Γ) * (F' : Set Γ))
    (h : 𝔠.Q ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) = ⊥) :
    ∃ Tt : Subgroup G, IsMaxInvIn 𝔱.t A ⊤ Tt ∧
      𝔠.P ≤ normalizer (CFSG.ambientMaxCardZJ Tt : Set G) := by
  have : Fact p.Prime := ⟨𝔠.hp⟩
  have : Fact 𝔱.t.Prime := ⟨𝔱.ht.1⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpt : p ≠ 𝔱.t := Ne.symm 𝔱.ht.2.2
  have hA2 : IsPGroup 2 A := ρ.isPGroup_A
  have hXA : ρ.X ≤ A := ρ.X_le_A
  have hYA : ρ.Y ≤ A := ρ.Y_le_A
  have hAX : A ≤ centralizer (ρ.X : Set G) := fun a ha =>
    mem_centralizer_iff.mpr fun x hx => ρ.comm (hXA hx) ha
  have hPX : 𝔠.P ≤ centralizer (ρ.X : Set G) := 𝔱.hXP
  have hQP : 𝔠.Q ≤ 𝔠.P := inf_le_left
  have hAH₀ : A ≤ 𝔠.H₀ := le_sup_right.trans 𝔠.hH₀.1
  have hAQ : A ≤ normalizer (𝔠.Q : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨𝔠.hP.2.2.1 ha, le_normalizer_O _ (hAH₀ ha)⟩
  have hAT : A ≤ normalizer (𝔱.T : Set G) := 𝔱.hT.2.2.1
  have hTt : IsPGroup 𝔱.t 𝔱.T := 𝔱.hT.2.1.isPGroup
  have hYE' : ¬ ρ.Y ≤ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) := fun hY =>
    𝔠.hH₁.1 (le_centralizer_of_le_centralizer_commutator (hQP.trans hPX) 𝔱.hT.2.2.2.1
      (hYA.trans hAQ) h hY)
  have hET : (⁅𝔱.T, ρ.X⁆ : Subgroup G) ≤ 𝔱.T :=
    le_normalizer_iff_commutator_le_left.mp (hXA.trans hAT)
  have hYT : ¬ ρ.Y ≤ centralizer (𝔱.T : Set G) := fun hY => hYE' (hY.trans (centralizer_le hET))
  have hT1 : 𝔱.T ≠ ⊥ := by
    rintro hbot
    apply hYT
    rw [hbot]
    intro y _
    rw [mem_centralizer_iff]
    intro e he
    rw [SetLike.mem_coe, mem_bot] at he
    rw [he, one_mul, mul_one]
  have h518 : CFSG.pCore p ↥(𝔠.P ⊔ 𝔱.T) = ⊥ := 𝔱.lemma_5_18_of h47 hHns h1M h
  obtain ⟨F, ⟨hFt, hAF, hTF, hPF, hcovJ⟩, hFmax⟩ := Set.exists_max_image
    {F : Subgroup G | IsPGroup 𝔱.t F ∧ A ≤ normalizer (F : Set G) ∧ 𝔱.T ≤ F ∧
      (𝔠.P : Set G) * (F : Set G) = (F : Set G) * (𝔠.P : Set G) ∧
      Covers (normalizer (CFSG.ambientMaxCardZJ F : Set G)) ρ.M₀ (O ρ.M)}
    (fun F => Nat.card F) (Set.toFinite _)
    ⟨𝔱.T, hTt, hAT, le_rfl, 𝔱.hT.2.2.2.2.symm,
      covers_normalizer_ambientMaxCardZJ_of_isSylowOf (hA2.to_le hXA) (hXA.trans hAX) 𝔱.hx₁.1
        (hXA.trans hAT) 𝔱.hT.2.1 ρ.M₀_le ρ.O_M_le_M₀⟩
  have hPFJ : 𝔠.P ⊔ F ≤ normalizer (CFSG.ambientMaxCardZJ F : Set G) := by
    have hcore := pPrimeCore_eq_bot_of_pCore_eq_bot hpt 𝔠.hP.2.1 hFt hPF
      (pCore_sup_eq_bot_of_le 𝔠.hP hAF hTF h518)
    have hodd : Odd (Nat.card (𝔠.P ⊔ F : Subgroup G)) := by
      rw [card_sup_of_mul_comm' hpt 𝔠.hP.2.1 hFt hPF]
      obtain ⟨a, ha⟩ := 𝔠.hP.2.1.exists_card_eq
      obtain ⟨b, hb⟩ := hFt.exists_card_eq
      rw [ha, hb]
      exact (𝔠.hp.odd_of_ne_two 𝔠.hp2).pow.mul (𝔱.ht.1.odd_of_ne_two 𝔱.ht.2.1).pow
    exact le_normalizer_ambientMaxCardZJ_of_odd hodd
      (isSylowOf_right_of_mul_comm hpt 𝔠.hP.2.1 hFt hPF) hcore
  set J : Subgroup G := normalizer (CFSG.ambientMaxCardZJ F : Set G) with hJdef
  have hPJ : 𝔠.P ≤ J := le_sup_left.trans hPFJ
  have hFJ : F ≤ J := le_sup_right.trans hPFJ
  have hAJ : A ≤ J := hAF.trans (CFSG.normalizer_le_normalizer_ambientMaxCardZJ F)
  have hTJ : 𝔱.T ≤ J := hTF.trans hFJ
  have hF1 : F ≠ ⊥ := fun hF => hT1 (le_bot_iff.mp (hF ▸ hTF))
  have hJloc : CFSG.IsPLocal 𝔱.t J :=
    ⟨_, ambientMaxCardZJ_ne_bot' 𝔱.ht.1 hFt hF1, hFt.to_le (CFSG.ambientMaxCardZJ_le F), rfl⟩
  have hJtop : J ≠ ⊤ := ρ.ne_top_of_isPLocal 𝔱.ht.1 𝔱.ht.2.1 hJloc
  have hJpc : Sec4Setting.PConstrainedWrt 𝔱.t A J ρ.Y :=
    (h51 J hJtop hAJ).1 hcovJ ⟨𝔱.x₁, 𝔱.hx₁.1, 𝔱.hx₁.2.1, 𝔱.T, hTJ, hTt, hAT, 𝔱.hT.2.1.le, hYT⟩
  obtain ⟨L, L₁, hLn, hL₁n, hLs, hL₁s, hL₁c, hinf, hYL, hXL₁, hΓ⟩ :=
    ρ.exists_bar_data_of_h1R hHns h1ML hJtop hAJ hcovJ
  have hXJ : ρ.X ≤ J := hXA.trans hAJ
  have hYJ : ρ.Y ≤ J := hYA.trans hAJ
  have hZV : bar J ρ.X ⊔ bar J ρ.Y = bar J A := by
    rw [← G4c.bar_sup hXJ hYJ, ρ.X_sup_Y]
  have hsylJ := isSylowOf_bar_centralizer hA2 hAJ ρ.isSylowOf_centralizer
  have hPmaxJ := isMaxInvIn_bar 𝔠.hp 𝔠.hp2 hA2 hAJ hPJ 𝔠.hP
  rw [← hZV] at hsylJ hPmaxJ
  obtain ⟨F', hF'max, hFF', hF'P⟩ := hPGL (G4c.oddCore_bar_eq_bot J) hLn hL₁n hLs hL₁s hL₁c hinf
    (G4c.isKleinFour_bar hYJ ρ.isKleinFour_Y) hYL
    (G4c.isKleinFour_bar hXJ ρ.isKleinFour_X) hXL₁ (by rw [hZV]; exact hΓ)
    hsylJ 𝔠.hp 𝔱.ht.1 𝔠.hp2 𝔱.ht.2.1 hpt hPmaxJ (bar_le_centralizer (le_centralizer_iff.mp hPX))
    (G4c.isPGroup_bar hFt) (by rw [hZV]; exact G4c.bar_le_normalizer hAF)
    (bar_mul_comm hPJ hFJ hPF).symm
  rw [hZV] at hF'max hPmaxJ
  obtain ⟨Js, hOJs, hJsJ, hJsbar⟩ := exists_preimage J (F' ⊔ bar J 𝔠.P)
  have hPJs : 𝔠.P ≤ Js := (le_iff_bar_le_bar hPJ hOJs).mpr (hJsbar ▸ le_sup_right)
  have hFJs : F ≤ Js := (le_iff_bar_le_bar hFJ hOJs).mpr (hJsbar ▸ hFF'.trans le_sup_left)
  have hAJs : A ≤ normalizer (Js : Set G) := by
    refine le_normalizer_of_bar_le_normalizer hAJ hOJs hJsJ ?_
    rw [hJsbar]
    exact fun a ha => mem_normalizer_sup (hF'max.2.2.1 ha) (hPmaxJ.2.2.1 ha)
  have hJs'card : Nat.card (F' ⊔ bar J 𝔠.P : Subgroup (Bar J)) =
      Nat.card F' * Nat.card (bar J 𝔠.P) :=
    card_sup_of_mul_comm' hpt.symm hF'max.2.1 hPmaxJ.2.1 hF'P
  have hJsodd : Odd (Nat.card Js) := by
    rw [card_eq_card_bar_mul hOJs hJsJ, hJsbar, hJs'card]
    obtain ⟨a, ha⟩ := hF'max.2.1.exists_card_eq
    obtain ⟨b, hb⟩ := hPmaxJ.2.1.exists_card_eq
    rw [ha, hb]
    exact ((𝔱.ht.1.odd_of_ne_two 𝔱.ht.2.1).pow.mul (𝔠.hp.odd_of_ne_two 𝔠.hp2).pow).mul
      (card_O_odd J)
  obtain ⟨Fs, hFFs, hFsJs, hAFs, hPFs⟩ :=
    exists_isSylowOf_mul_comm hpt hA2 hAJs hJsodd 𝔠.hP hPJs hFt hFJs hAF hPF
  have hFsJ : Fs ≤ J := hFsJs.le.trans hJsJ
  have hFbs : IsSylowOf 𝔱.t (bar J Fs) (F' ⊔ bar J 𝔠.P) := by
    rw [← hJsbar, CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨G4c.bar_mono hFsJs.le, G4c.isPGroup_bar hFsJs.isPGroup, fun hdvd => ?_⟩
    exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hFsJs).2.2
      (hdvd.trans (relIndex_bar_dvd (U := Fs) hJsJ))
  have hFb' : IsSylowOf 𝔱.t F' (F' ⊔ bar J 𝔠.P) := by
    rw [sup_comm]
    exact isSylowOf_right_of_mul_comm hpt hPmaxJ.2.1 hF'max.2.1 hF'P.symm
  obtain ⟨c, ⟨-, hcA⟩, hc⟩ := CFSG.ABGTheoremB.exists_conj_eq_of_isSylowOf_normalized_of_coprime
    Nat.prime_two 𝔱.ht.1 (G4c.isPGroup_bar hA2)
    (fun a ha => mem_normalizer_sup (hF'max.2.2.1 ha) (hPmaxJ.2.2.1 ha))
    (by
      rw [hJs'card]
      obtain ⟨a, ha⟩ := hF'max.2.1.exists_card_eq
      obtain ⟨b, hb⟩ := hPmaxJ.2.1.exists_card_eq
      rw [ha, hb, ← even_iff_two_dvd, Nat.not_even_iff_odd]
      exact (𝔱.ht.1.odd_of_ne_two 𝔱.ht.2.1).pow.mul (𝔠.hp.odd_of_ne_two 𝔠.hp2).pow)
    hFb' hFbs hF'max.2.2.1 (G4c.bar_le_normalizer hAFs)
  have hFbsmax : IsMaxInvIn 𝔱.t (bar J A) ⊤ (bar J Fs) := by
    have hmap := G4b.IsMaxInvIn.map hF'max (MulAut.conj c)
    rwa [G4b.mem_normalizer_iff_map_conj_eq'.mp (centralizer_le_normalizer _ hcA),
      map_top_of_surjective _ (MulAut.conj c).surjective, hc] at hmap
  have hFsmax : IsMaxInvIn 𝔱.t A J Fs := by
    refine ⟨hFsJ, hFsJs.isPGroup, hAFs, fun R hRJ hRt hAR hFsR => ?_⟩
    have hR : bar J R = bar J Fs := hFbsmax.2.2.2 _ le_top (G4c.isPGroup_bar hRt)
      (G4c.bar_le_normalizer hAR) (G4c.bar_mono hFsR)
    have hRJs : R ≤ Js := by
      rw [le_iff_bar_le_bar hRJ hOJs, hR, hJsbar]
      exact hFbs.le
    exact hFsJs.eq_of_le hFsR hRJs hRt
  have hFsF : Fs = F := by
    have hcard := hFmax Fs ⟨hFsJs.isPGroup, hAFs, hTF.trans hFFs, hPFs,
      h52core J Fs hJloc hAJ hcovJ hJpc hFsmax⟩
    exact (eq_of_le_of_card_ge hFFs hcard).symm
  rw [hFsF] at hFsmax
  refine ⟨F, ⟨le_top, hFt, hAF, fun R _ hRt hAR hFR => ?_⟩, hPJ⟩
  have hN : R ⊓ normalizer (F : Set G) = F :=
    hFsmax.2.2.2 _ (inf_le_right.trans (CFSG.normalizer_le_normalizer_ambientMaxCardZJ F))
      (hRt.to_le inf_le_left)
      (fun a ha => inf_normalizer_le_normalizer_inf ⟨hAR ha, le_normalizer (hAF ha)⟩)
      (le_inf hFR le_normalizer)
  exact (eq_of_inf_normalizer_le' hRt hFR hN.le).symm

end Sec5ConfigTR

end CFSG.GH72
