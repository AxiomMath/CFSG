module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductDecomp

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure
  (BarM barMap barSub barMap_eq_iff)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative ProductAlternative)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc)
open CFSG.LocalAnalysis.EvenBN.Common (diagonalHom)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

section Generic

variable {G : Type*} [Group G]

theorem range_diagonalHom_eq_inf_centralizer {A : Subgroup G} {t : G} (htt : t * t = 1)
    (hcomm : ⁅A, Aᵍ[t]⁆ = ⊥) (hinf : A ⊓ Aᵍ[t] = ⊥) :
    (diagonalHom A t hcomm).range = (A ⊔ Aᵍ[t]) ⊓ centralizer ({t} : Set G) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  refine le_antisymm (le_inf ?_ (Common.range_diagonalHom_le hcomm htt)) ?_
  · rintro _ ⟨a, rfl⟩
    exact mul_mem (mem_sup_left a.2) (mem_sup_right (Common.conj_mem_map_conj_inv t a.2))
  · rintro g ⟨hg, hgt⟩
    have hnorm : A ≤ normalizer ((Aᵍ[t] : Subgroup G) : Set G) :=
      (commutator_eq_bot_iff_le_centralizer.1 hcomm).trans (centralizer_le_normalizer _)
    have hg2 : g ∈ (((A ⊔ Aᵍ[t] : Subgroup G) : Set G)) := hg
    rw [coe_mul_of_left_le_normalizer_right _ _ hnorm, Set.mem_mul] at hg2
    obtain ⟨a, ha', b, hb', rfl⟩ := hg2
    have ha : a ∈ A := ha'
    have hb : b ∈ Aᵍ[t] := hb'
    have hcm : ∀ x ∈ A, ∀ z ∈ Aᵍ[t], z * x = x * z := fun x hx z hz =>
      mem_centralizer_iff.1 ((commutator_eq_bot_iff_le_centralizer.1 hcomm) hx) z hz
    have hc : t⁻¹ * a * t ∈ Aᵍ[t] := Common.conj_mem_map_conj_inv t ha
    have hy : t⁻¹ * b * t ∈ A := by
      have := Common.mem_map_conj_inv_iff.1 hb
      rw [hti] at this ⊢
      exact this
    have hfix : t⁻¹ * (a * b) * t = a * b := by
      have := mem_centralizer_singleton_iff.1 hgt
      calc t⁻¹ * (a * b) * t = t⁻¹ * ((a * b) * t) := by group
        _ = a * b := by rw [this]; group
    have hcy : (t⁻¹ * a * t) * (t⁻¹ * b * t) = a * b := by
      calc (t⁻¹ * a * t) * (t⁻¹ * b * t) = t⁻¹ * (a * b) * t := by group
        _ = a * b := hfix
    have h1 : (t⁻¹ * b * t) * (t⁻¹ * a * t) = a * b := (hcm _ hy _ hc).symm.trans hcy
    have h2 : a⁻¹ * (t⁻¹ * b * t) = b * (t⁻¹ * a * t)⁻¹ := by
      calc a⁻¹ * (t⁻¹ * b * t)
          = a⁻¹ * ((t⁻¹ * b * t) * (t⁻¹ * a * t)) * (t⁻¹ * a * t)⁻¹ := by group
        _ = b * (t⁻¹ * a * t)⁻¹ := by rw [h1]; group
    have h3 : a⁻¹ * (t⁻¹ * b * t) ∈ A ⊓ Aᵍ[t] :=
      mem_inf.2 ⟨mul_mem (inv_mem ha) hy, by rw [h2]; exact mul_mem hb (inv_mem hc)⟩
    rw [hinf, mem_bot] at h3
    have hya : t⁻¹ * b * t = a := (inv_mul_eq_one.1 h3).symm
    rw [hya] at h1
    have hbc : t⁻¹ * a * t = b := mul_left_cancel h1
    exact ⟨⟨a, ha⟩, by show a * (t⁻¹ * a * t) = a * b; rw [hbc]⟩

end Generic

namespace ProductPairAux

section Abstract

theorem mem_of_fixed_productAlternative {M : Type} [Group M] {A : Subgroup M} {k : Type}
    [Field k] {α : A ≃* SL(2, k)} {τ : M} (hP : ProductAlternative A α τ) {x : M}
    (hx : x ∈ normalClosure (A : Set M)) (hτ : τ⁻¹ * x * τ = x) : x ∈ A := by
  obtain ⟨ψ, hψA, hψτ⟩ := hP
  set x' : normalClosure (A : Set M) := ⟨x, hx⟩ with hx'
  have h1 : ψ x' = (ψ x').swap := hψτ x' x' (by simpa using hτ.symm)
  have h2 : (ψ x').1 = (ψ x').2 := by
    have := congrArg Prod.fst h1
    simpa using this
  set a : A := α.symm (ψ x').1 with ha
  set a' : normalClosure (A : Set M) := ⟨a, subset_normalClosure a.2⟩ with ha'
  have h3 : ψ a' = (α a, α a) := hψA a a' rfl
  have h4 : α a = (ψ x').1 := by simp [ha]
  have h5 : ψ a' = ψ x' := by
    rw [h3, h4]
    exact Prod.ext rfl h2
  have h6 : a' = x' := ψ.injective h5
  have h7 : (x : M) = (a : M) := congrArg Subtype.val h6.symm
  rw [h7]
  exact a.2

theorem inf_centralizer_eq_of_productAlternative {G : Type} [Group G] {X N KK : Subgroup G}
    {t : G} {k : Type} [Field k] {α : ↥(barSub X KK) ≃* SL(2, k)}
    (hNn : N ≤ normalizer (X : Set G)) (hXN : X ≤ N) (hKN : KK ≤ N)
    (ht : t ∈ normalizer (X : Set G))
    (hbar : barSub X N = normalClosure (barSub X KK : Set (BarM X)))
    (hP : ProductAlternative (barSub X KK) α (barMap X ⟨t, ht⟩))
    (hKt : KK ≤ centralizer ({t} : Set G)) (hXC : X ⊓ centralizer ({t} : Set G) ≤ KK) :
    N ⊓ centralizer ({t} : Set G) = KK := by
  refine le_antisymm ?_ (le_inf hKN hKt)
  rintro x ⟨hxN, hxC⟩
  have hxn : x ∈ normalizer (X : Set G) := hNn hxN
  have hxbar : barMap X ⟨x, hxn⟩ ∈ normalClosure (barSub X KK : Set (BarM X)) := by
    rw [← hbar]
    exact ⟨⟨x, hxn⟩, hxN, rfl⟩
  have hτ : (barMap X ⟨t, ht⟩)⁻¹ * barMap X ⟨x, hxn⟩ * barMap X ⟨t, ht⟩ =
      barMap X ⟨x, hxn⟩ := by
    have hcomm : t⁻¹ * x * t = x := by
      have := mem_centralizer_singleton_iff.1 hxC
      calc t⁻¹ * x * t = t⁻¹ * (x * t) := by group
        _ = x := by rw [this]; group
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hcomm)
  obtain ⟨m, hm, hmx⟩ := mem_of_fixed_productAlternative hP hxbar hτ
  have hmK : (m : G) ∈ KK := hm
  have hz : (m : G)⁻¹ * x ∈ X := barMap_eq_iff.1 hmx
  have hzC : (m : G)⁻¹ * x ∈ centralizer ({t} : Set G) :=
    mul_mem (inv_mem (hKt hmK)) hxC
  have hzK : (m : G)⁻¹ * x ∈ KK := hXC ⟨hz, hzC⟩
  simpa using mul_mem hmK hzK

end Abstract

end ProductPairAux


namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]


private theorem S_le_yamadaK₁ (d : G2Data L K) (hK4 : 4 ≤ Nat.card K) : d.S ≤ yamadaK₁ d := by
  obtain ⟨-, -, -, -, -, hFD, -, -, -, -⟩ := d.inclusions
  obtain ⟨-, -, -, -, -, hM, -, -, hS⟩ := d.yamada_defs
  have hr : d.rootGroup g2r ≤ d.leviA := fun g hg =>
    (d.yamada_3_11_G.2.2.1 g).2 (Or.inl ⟨g, hg, 1, one_mem _, (mul_one g).symm⟩)
  rw [yamadaK₁_eq d hK4, ← hS, ← hM]
  exact sup_le le_sup_left (sup_le (hr.trans le_sup_right) (hFD.trans le_sup_left))

theorem yamada_N_inf_centralizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) :
    yamadaN₁ d t ⊓ centralizer ({t} : Set G) = yamadaK₁ d ∧
      yamadaN₂ d t ⊓ centralizer ({t} : Set G) = yamadaK₂ d := by
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  have hLC := h.L_le_centralizer
  have hK₁L : yamadaK₁ d ≤ L :=
    (TrialityD4.ProductCase.ProductDecompAux.commutator_self_le _).trans inf_le_left
  have hK₂L : yamadaK₂ d ≤ L :=
    (TrialityD4.ProductCase.ProductDecompAux.commutator_self_le _).trans inf_le_left
  obtain ⟨-, -, -, -, hMC, hPC⟩ := h.yamada_series_inf_centralizer hW d hK hQ
  obtain ⟨hnD, hnM⟩ := h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ
  refine ⟨?_, ?_⟩
  · have htN : t ∈ normalizer (yamadaD₇ d t : Set G) := (h.yamada_5_51 hW d hK hQ).2.2.2.1
    have hKN : yamadaK₁ d ≤ normalizer (yamadaD₇ d t : Set G) :=
      (TrialityD4.ProductCase.ProductDecompAux.commutator_self_le _).trans
        ((inf_le_inf_left L (le_refl _)).trans hnD)
    obtain ⟨α, hex⟩ := hp.exact₁
    have hPA : ProductAlternative (yamadaBarK₁ d t) α (yamadaT₁ d t) := by
      rcases Sp4.BothTrivialCases.xor_of_exactClosure hex with ⟨hP, -⟩ | ⟨hF, -⟩
      · exact hP
      · exact absurd hF (h.yamada_7_3_eight hW d hK hQ hp)
    rw [yamadaT₁_eq d htN] at hPA
    refine ProductPairAux.inf_centralizer_eq_of_productAlternative
      (yamadaN₁_le_normalizer d t hKN) (yamadaD₇_le_yamadaN₁ d t) (yamadaK₁_le_yamadaN₁ d t) htN
      (barSub_yamadaN₁ d t hKN) hPA (fun x hx => hLC (hK₁L hx)) ?_
    rintro x ⟨hxD, hxC⟩
    exact S_le_yamadaK₁ d hK4 (hPC ▸ ⟨yamadaD₇_le_yamadaP d t hxD, hxC⟩)
  · have htN : t ∈ normalizer (yamadaM₆ d t : Set G) := ((h.yamada_5_44_1 hW d hK hQ).1).2.1
    have hKN : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
      (TrialityD4.ProductCase.ProductDecompAux.commutator_self_le _).trans
        ((inf_le_inf_left L (le_refl _)).trans hnM)
    obtain ⟨α, -, hPA⟩ := hp.exact₂
    rw [yamadaT₂_eq d htN] at hPA
    refine ProductPairAux.inf_centralizer_eq_of_productAlternative
      (yamadaN₂_le_normalizer d t hKN) (yamadaM₆_le_yamadaN₂ d t) (yamadaK₂_le_yamadaN₂ d t) htN
      (barSub_yamadaN₂ d t hKN) hPA (fun x hx => hLC (hK₂L hx)) ?_
    rintro x ⟨hxM, hxC⟩
    have : x ∈ d.M := hMC ▸ ⟨hxM, hxC⟩
    rw [yamadaK₂_eq d hK4]
    exact mem_sup_left this

theorem exists_diagonalPair (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f)
    {Λ₁ Λ₂ : Subgroup G} (hL : Labelled d t Λ₁ Λ₂) :
    ∃ X : DiagonalPair d t, X.A₁ = derived₂ Λ₁ ∧ X.A₂ = derived₂ Λ₂ ∧
      X.P₀ = yamadaP d t ⊓ derived₂ Λ₁ ∧ yamadaP d t = X.P₀ ⊔ X.P₀ᵍ[t] ∧
      yamadaN₁ d t = X.A₁ ⊔ X.A₁ᵍ[t] ∧ yamadaN₂ d t = X.A₂ ⊔ X.A₂ᵍ[t] ∧
      X.A₁ ⊓ X.A₁ᵍ[t] = ⊥ ∧ X.A₂ ⊓ X.A₂ᵍ[t] = ⊥ := by
  have htt := h.t_mul_t
  obtain ⟨⟨hN₁, hI₁, hc₁, -, -, -, -⟩, -⟩ := h.yamada_7_16 hW d hK hQ hp hL
  obtain ⟨⟨hN₂, hI₂, hc₂, -, -, -, -⟩, -⟩ := h.yamada_7_15 hW d hK hQ hp hL
  obtain ⟨hP₀eq, hPeq, -, hP₀card⟩ := h.yamada_7_18 hW d hK hQ hp hL
  obtain ⟨hC₁, hC₂⟩ := h.yamada_N_inf_centralizer hW d hK hQ hp
  have hPt : t ∈ normalizer (yamadaP d t : Set G) := (h.yamada_5_51 hW d hK hQ).1.2.1
  have hPC := (h.yamada_series_inf_centralizer hW d hK hQ).2.2.2.2.2
  have inj : ∀ {A : Subgroup G} (hc : ⁅A, Aᵍ[t]⁆ = ⊥), A ⊓ Aᵍ[t] = ⊥ →
      Function.Injective (diagonalHom A t hc) := by
    intro A hc hinf
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 := Common.map_ker_diagonalHom_le hc ⟨x, hx, rfl⟩
    rw [hinf] at h1
    exact mem_bot.2 (Subtype.ext (mem_bot.1 h1))
  have hle₁ : yamadaP d t ⊓ derived₂ Λ₁ ≤ derived₂ Λ₁ := inf_le_right
  have hδS : (((yamadaP d t ⊓ derived₂ Λ₁).subgroupOf (derived₂ Λ₁)).map
      (diagonalHom (derived₂ Λ₁) t hc₁)) ≤ d.S := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : (x : G) ∈ yamadaP d t := (mem_subgroupOf.1 hx).1
    have h1 : t⁻¹ * (x : G) * t ∈ yamadaP d t := by
      have := (mem_normalizer_iff.1 (inv_mem hPt) x).1 hxP
      rwa [inv_inv] at this
    rw [← hPC]
    exact ⟨mul_mem hxP h1, Common.range_diagonalHom_le hc₁ htt ⟨x, rfl⟩⟩
  have hcard : Nat.card d.S ≤ Nat.card (((yamadaP d t ⊓ derived₂ Λ₁).subgroupOf
      (derived₂ Λ₁)).map (diagonalHom (derived₂ Λ₁) t hc₁)) := by
    rw [Subgroup.card_map_of_injective (inj hc₁ hI₁),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₁).toEquiv, hP₀card,
      d.cards.2.2.2.2.2.2.2]
  have hle₂ : yamadaP d t ⊓ derived₂ Λ₁ ≤ derived₂ Λ₂ := by
    rw [hP₀eq]
    exact inf_le_right
  have hrP := Subgroup.eq_of_le_of_card_ge hδS hcard
  refine ⟨DiagonalPair.mk (derived₂ Λ₁) (derived₂ Λ₂) (yamadaP d t ⊓ derived₂ Λ₁) hc₁ hc₂ hle₁
    hle₂ (inj hc₁ hI₁) (inj hc₂ hI₂) ?_ ?_ hrP, rfl, rfl, rfl, hPeq, hN₁, hN₂, hI₁, hI₂⟩
  · rw [range_diagonalHom_eq_inf_centralizer htt hc₁ hI₁, ← hN₁, hC₁]
  · rw [range_diagonalHom_eq_inf_centralizer htt hc₂ hI₂, ← hN₂, hC₂]

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
