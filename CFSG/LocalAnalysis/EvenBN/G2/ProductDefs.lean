module

public import CFSG.LocalAnalysis.EvenBN.G2.SeriesCenters
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProduct
public import CFSG.LocalAnalysis.EvenBN.Common.ProductClosure
public import CFSG.LocalAnalysis.EvenBN.Common.Diagonal
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductToolbox

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative ProductAlternative)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso)
open CFSG.LocalAnalysis.EvenBN.Common (diagonalHom)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

section Defs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

structure IsFactor (X N Λ : Subgroup G) (t : G) (K : Type) [Field K] : Prop where
  X_le : X ≤ Λ
  le : Λ ≤ N
  sup : Λ ⊔ Λᵍ[t] = N
  inf : Λ ⊓ Λᵍ[t] = X
  comm : ⁅Λ, Λᵍ[t]⁆ ≤ X
  quot : IsQuotientIso Λ X (SL(2, K))

@[expose] def derivedMod (N Λ : Subgroup G) : Subgroup G :=
  ⁅Λ, Λ⁆ ⊔ N

abbrev derived₁ (Λ : Subgroup G) : Subgroup G :=
  ⁅Λ, Λ⁆

abbrev derived₂ (Λ : Subgroup G) : Subgroup G :=
  ⁅⁅Λ, Λ⁆, ⁅Λ, Λ⁆⁆

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

@[expose] noncomputable def leviFactor₁ (d : G2Data L K) (Λ₁ : Subgroup G) : Subgroup G :=
  Λ₁ ⊓ centralizer (d.J₃ : Set G)

@[expose] noncomputable def leviFactor₂ (A Λ₂ : Subgroup G) : Subgroup G :=
  Λ₂ ⊓ A

@[expose] noncomputable def yamadaN₃ (d : G2Data L K) (t : G) : Subgroup G :=
  (yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G)) ⊔ yamadaY₂ d t

@[expose] noncomputable def yamadaK₃ (d : G2Data L K) (t : G) (Λ₂ : Subgroup G) : Subgroup G :=
  Λ₂ ⊓ yamadaN₃ d t

@[expose] noncomputable def yamadaP₃ (d : G2Data L K) (t : G) (Λ₂ : Subgroup G) : Subgroup G :=
  yamadaP d t ⊓ yamadaK₃ d t Λ₂

structure Complement₂ (d : G2Data L K) (t : G) (A : Subgroup G) : Prop where
  le_cen : A ≤ yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G)
  inf_eq : A ⊓ yamadaM₆ d t = ⊥
  sup_eq : yamadaN₂ d t = A ⊔ yamadaM₆ d t
  conj_eq : Aᵍ[t] = A
  levi_le : d.leviB ≤ A

structure ProductHyp (d : G2Data L K) (t : G) (f : ℕ) : Prop where
  sylow₁ : IsSylowOf 2 (yamadaP d t) (yamadaN₁ d t)
  sylow₂ : IsSylowOf 2 (yamadaP d t) (yamadaN₂ d t)
  exact₁ : ∃ α : ↥(yamadaBarK₁ d t) ≃* SL(2, K),
    ExactClosure (yamadaBarK₁ d t) α (yamadaT₁ d t) (yamadaBarP₁ d t) f
  exact₂ : ∃ α : ↥(yamadaBarK₂ d t) ≃* SL(2, K),
    ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f ∧
      ProductAlternative (yamadaBarK₂ d t) α (yamadaT₂ d t)
  compl₁ : yamadaN₁ d t = (yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G)) ⊔ yamadaD₇ d t ∧
    (yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G)) ⊓ yamadaD₇ d t = ⊥ ∧
    d.leviA ≤ yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G)
  inf₂ : (yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G)) ⊓ yamadaM₆ d t ≤ yamadaY₂ d t
  compl₂ : ∃ A : Subgroup G, Complement₂ d t A

noncomputable def ProductHyp.Astar {d : G2Data L K} {t : G} {f : ℕ} (hp : ProductHyp d t f) :
    Subgroup G :=
  hp.compl₂.choose

theorem ProductHyp.Astar_spec {d : G2Data L K} {t : G} {f : ℕ} (hp : ProductHyp d t f) :
    Complement₂ d t hp.Astar :=
  hp.compl₂.choose_spec

theorem Complement₂.yamadaN₃_eq {d : G2Data L K} {t : G} {A : Subgroup G}
    (hA : Complement₂ d t A) (hN : yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G))
    (hinf : (yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G)) ⊓ yamadaM₆ d t ≤ yamadaY₂ d t) :
    yamadaN₃ d t = A ⊔ yamadaY₂ d t := by
  have hAN : A ≤ normalizer (yamadaM₆ d t : Set G) := (hA.le_cen.trans inf_le_left).trans hN
  refine le_antisymm (sup_le (fun x hx => ?_) le_sup_right) (sup_le_sup_right hA.le_cen _)
  have hxN : x ∈ A ⊔ yamadaM₆ d t := hA.sup_eq ▸ (mem_inf.1 hx).1
  obtain ⟨a, ha, m, hm, rfl⟩ := Common.exists_mul_of_le_normalizer' hAN x hxN
  have hmC : m ∈ yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G) := by
    have := mul_mem (inv_mem (hA.le_cen ha)) hx
    rwa [inv_mul_cancel_left] at this
  exact mul_mem (mem_sup_left ha) (mem_sup_right (hinf (mem_inf.2 ⟨hmC, hm⟩)))

structure Labelled (d : G2Data L K) (t : G) (Λ₁ Λ₂ : Subgroup G) : Prop where
  fac₁ : IsFactor (yamadaD₇ d t) (yamadaN₁ d t) Λ₁ t K
  fac₂ : IsFactor (yamadaM₆ d t) (yamadaN₂ d t) Λ₂ t K
  label : (yamadaP d t ⊓ Λ₁)ᵍ[t] =
    centerMod (yamadaY₂ d t) (yamadaP d t ⊓ Λ₂) ⊔ yamadaD₇ d t

structure DiagonalPair (d : G2Data L K) (t : G) where
  A₁ : Subgroup G
  A₂ : Subgroup G
  P₀ : Subgroup G
  comm₁ : ⁅A₁, A₁ᵍ[t]⁆ = ⊥
  comm₂ : ⁅A₂, A₂ᵍ[t]⁆ = ⊥
  le₁ : P₀ ≤ A₁
  le₂ : P₀ ≤ A₂
  injective₁ : Function.Injective (diagonalHom A₁ t comm₁)
  injective₂ : Function.Injective (diagonalHom A₂ t comm₂)
  range₁ : (diagonalHom A₁ t comm₁).range = yamadaK₁ d
  range₂ : (diagonalHom A₂ t comm₂).range = yamadaK₂ d
  rangeP : (P₀.subgroupOf A₁).map (diagonalHom A₁ t comm₁) = d.S

end Local

end Defs

namespace ProductDefsAux

section Abstract

variable {G : Type} [Group G] {k : Type} [Field k]

theorem exists_rho {X CU NC : Subgroup G} {t : G}
    (hNCN : NC ≤ normalizer (X : Set G))
    (hbar : barSub X NC = normalClosure (barSub X CU : Set (BarM X)))
    (ht : t ∈ normalizer (X : Set G)) (hτ : orderOf (barMap X ⟨t, ht⟩) = 2)
    (α : ↥(barSub X CU) ≃* SL(2, k))
    (hP : ProductAlternative (barSub X CU) α (barMap X ⟨t, ht⟩)) :
    ∃ ρ : NC →* SL(2, k) × SL(2, k), Function.Surjective ρ ∧
      ρ.ker = X.subgroupOf NC ∧
      ∀ x y : NC, (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap := by
  obtain ⟨ψ, -, hψswap⟩ := hP
  have hτ2 : barMap X ⟨t, ht⟩ * barMap X ⟨t, ht⟩ = 1 := by
    have := pow_orderOf_eq_one (barMap X ⟨t, ht⟩)
    rwa [hτ, pow_two] at this
  let ρ₁ : NC →* normalClosure (barSub X CU : Set (BarM X)) :=
    ((barMap X).comp (Subgroup.inclusion hNCN)).codRestrict _ fun n => by
      rw [← hbar]
      exact ⟨⟨(n : G), hNCN n.2⟩, mem_subgroupOf.mpr n.2, rfl⟩
  have hρ₁ : ∀ n : NC,
      ((ρ₁ n : normalClosure (barSub X CU : Set (BarM X))) : BarM X) =
        barMap X ⟨(n : G), hNCN n.2⟩ := fun _ => rfl
  have hρ₁surj : Function.Surjective ρ₁ := by
    rintro ⟨x, hx⟩
    rw [← hbar] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨⟨m, mem_subgroupOf.mp hm⟩, Subtype.ext rfl⟩
  refine ⟨ψ.toMonoidHom.comp ρ₁, ψ.surjective.comp hρ₁surj, ?_, ?_⟩
  · ext n
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change ψ (ρ₁ n) = 1 ↔ (n : G) ∈ X
    refine (map_eq_one_iff ψ ψ.injective).trans ?_
    rw [Subtype.ext_iff]
    exact CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.barMap_eq_one_iff
      (a := ⟨(n : G), hNCN n.2⟩)
  · intro x y hxy
    change ψ (ρ₁ y) = (ψ (ρ₁ x)).swap
    refine hψswap (ρ₁ x) (ρ₁ y) ?_
    have hy : barMap X ⟨(y : G), hNCN y.2⟩ =
        barMap X ⟨t, ht⟩ * barMap X ⟨(x : G), hNCN x.2⟩ * (barMap X ⟨t, ht⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hxy)
    rw [hρ₁, hρ₁, hy, inv_eq_of_mul_eq_one_right hτ2]

end Abstract

end ProductDefsAux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_isFactor₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) :
    ∃ Λ₂ : Subgroup G, IsFactor (yamadaM₆ d t) (yamadaN₂ d t) Λ₂ t K := by
  obtain ⟨α, -, hPA⟩ := hp.exact₂
  obtain ⟨-, htN, htM⟩ := (h.yamada_5_44_1 hW d hK hQ).1
  have ht2 : t * t = 1 := h.t_mul_t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hKN : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
    (commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) :
        yamadaK₂ d ≤ L ⊓ normalizer (d.Y : Set G)).trans
      (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).2
  have hNCN : yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) :=
    yamadaN₂_le_normalizer d t hKN
  have hbar := barSub_yamadaN₂ d t hKN
  have hτ : orderOf (barMap (yamadaM₆ d t) ⟨t, htN⟩) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← map_mul]
      have : (⟨t, htN⟩ * ⟨t, htN⟩ : normalizer (yamadaM₆ d t : Set G)) = 1 := Subtype.ext ht2
      rw [this, map_one]
    · intro h1
      exact htM
        ((CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.barMap_eq_one_iff).1 h1)
  have hPA' : ProductAlternative (barSub (yamadaM₆ d t) (yamadaK₂ d)) α
      (barMap (yamadaM₆ d t) ⟨t, htN⟩) := by
    rw [← yamadaT₂_eq d htN]
    exact hPA
  obtain ⟨ρ, hρ, hker, hswap⟩ :=
    ProductDefsAux.exists_rho (X := yamadaM₆ d t) (CU := yamadaK₂ d) (NC := yamadaN₂ d t)
      hNCN hbar htN hτ α hPA'
  have hN₂ : t ∈ normalizer (yamadaN₂ d t : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNCN).1
      (Common.RankOneLayerRadical.normal_subgroupOf_normalClosureInNormalizer hKN) htN
  have hMN := yamadaM₆_le_yamadaN₂ d t
  have hmem := fun g => Common.mem_map_conj_prodFst_iff (ρ := ρ) hN₂ ht2 hswap (g := g)
  have hconj : (Common.prodFst ρ)ᵍ[t] = (Common.prodFst ρ).map (MulAut.conj t).toMonoidHom := by
    rw [hti]
  refine ⟨Common.prodFst ρ, ?_, Common.prodFst_le ρ, ?_, ?_, ?_, ?_⟩
  · exact Common.le_prodFst hMN hker
  · rw [hconj]
    exact Common.prodFst_sup_map_conj hN₂ ht2 hswap hρ
  · rw [hconj]
    refine le_antisymm (fun g hg => ?_) (le_inf (Common.le_prodFst hMN hker) fun g hg => ?_)
    · obtain ⟨hg1, hg2⟩ := mem_inf.1 hg
      obtain ⟨hgN, hg2'⟩ := (Common.mem_prodFst_iff ρ).1 hg1
      obtain ⟨_, hg1'⟩ := (hmem g).1 hg2
      have : (⟨g, hgN⟩ : yamadaN₂ d t) ∈ ρ.ker := by
        rw [MonoidHom.mem_ker]
        exact Prod.ext hg1' hg2'
      rw [hker, mem_subgroupOf] at this
      exact this
    · have hgN : g ∈ yamadaN₂ d t := hMN hg
      refine (hmem g).2 ⟨hgN, ?_⟩
      have : (⟨g, hgN⟩ : yamadaN₂ d t) ∈ ρ.ker := by
        rw [hker, mem_subgroupOf]
        exact hg
      rw [MonoidHom.mem_ker] at this
      rw [this]
      rfl
  · rw [hconj]
    exact Common.commutator_prodFst_map_conj_le hN₂ ht2 hswap hker
  · exact ⟨Common.prodFstHom ρ, Common.surjective_prodFstHom hρ, Common.ker_prodFstHom hker⟩

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
