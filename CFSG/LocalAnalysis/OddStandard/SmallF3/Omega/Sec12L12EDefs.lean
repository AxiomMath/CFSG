module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def sec12f (t p : G) : G :=
  p * t * p⁻¹ * t⁻¹

@[expose] def secR (t : G) : Subgroup G :=
  oddCoreIn (centralizer ({t} : Set G))

@[expose] def secXR (t : G) (S L : Subgroup G) : Subgroup G :=
  secCMB t S L ⊓ centralizer (secR t : Set G)

structure Sec12Frame [Finite G] (t : G) (L S : Subgroup G) : Prop where
  ht2 : orderOf t = 2
  htC : t ∈ centralizer (L : Set G)
  hLC : L ⊓ centralizer (L : Set G) = ⊥
  hCt : centralizer ({t} : Set G) ≤ normalizer (L : Set G)
  hSM : S ≤ secM t S L
  bdata : Sec10BData t L S
  centB : ∀ g ∈ normalizer (L : Set G), (∀ b ∈ secB S L, g * b = b * g) →
    g ∈ secB S L ⊔ centralizer (L : Set G)
  normB : ∀ m ∈ secM t S L, ∀ b ∈ secB S L, m * b * m⁻¹ ∈ secB S L
  alt1 : Sec1011Alt1 t S L
  rcent : secR t ≤ centralizer (L : Set G)
  rmem : ∀ c ∈ centralizer (L : Set G), c ∈ centralizer ({t} : Set G) → Odd (orderOf c) →
    c ∈ secR t
  two : ∀ c ∈ centralizer (L : Set G), c ∈ centralizer ({t} : Set G) →
    (∃ k : ℕ, c ^ (2 ^ k) = 1) → c ∈ zpowers t

end CFSG.OddStandard.SmallF3.Omega
