module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Rest4

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

structure OuterS8Hyp (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G)
    (T E : Subgroup G) (Q : Sylow 2 G) (x : G) (B : Subgroup G) (β : G) (S : Subgroup G) :
    Prop where
  std : StdHyp G L
  sporadic : IsSporadic L .J2 ∨ IsSporadic L .J3
  cyclicC : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2
  relIdx : (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) = 2
  outerE : OuterE G L z t T E
  autE : Nat.card (MulAut ↥E) = 1920
  cardT : Nat.card ↥T = 512
  wFacts : WFacts L t E
  normE : ∀ m ∈ normalizer (E : Set G), ∃ c ∈ centralizer (E : Set G),
    ∃ n ∈ normalizer (E : Set G), n ∈ centralizer ({z} : Set G) ∧ m = c * n
  centZ : ∀ v ∈ centralizer (E : Set G), v * z = z * v → v = 1 ∨ v = z ∨ v = t ∨ v = t * z
  outerB : OuterB L t B β
  cardEβ : Nat.card ↥(E ⊓ centralizer ({β} : Set G)) = 8
  sylowS : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
    (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) →
    z ∈ S → OuterSylowFacts z E S ∧ ∀ b ∈ B, ∀ s ∈ S, b * s = s * b
  T_le_Q : T ≤ (Q : Subgroup G)
  x_mem : x ∈ (Q : Subgroup G)
  x_not_mem : x ∉ T
  x_norm : x ∈ normalizer (T : Set G)
  x_z : x * z * x⁻¹ = z * t
  x_t : x * t * x⁻¹ = t
  t_central : ∀ q ∈ (Q : Subgroup G), q * t = t * q
  Q_cent : (Q : Subgroup G) ⊓ centralizer ({z} : Set G) = T
  z_comm : z ∈ (commutator ↥(centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype
  lemma96 : ∃ hz : z ∈ centralizer ({β} : Set G), Lemma96Conclusion ↥(centralizer ({β} : Set G))
    (QuotientGroup.mk (⟨z, hz⟩ : ↥(centralizer ({β} : Set G))))
  sqL : ∀ y ∈ centralizer ({z} : Set G), y * y ∈ L
  sigma : ∃ σ ∈ T, σ * σ = 1 ∧ σ ∉ L ⊔ zpowers z
  z_not_L : ∀ g : G, g * z * g⁻¹ ∉ L
  S2 : IsPGroup 2 S
  SC : S ≤ centralizer (E : Set G)
  Smax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S
  zS : z ∈ S
  D8 : Nonempty (S ≃* DihedralGroup 4)
  alpha : ∃ α : G, AlphaSpec S z t α
  odd : ∃ N : Subgroup (centralizer (E : Set G)), N.Normal ∧ (∀ x, x ∈ N ↔ Odd (orderOf x)) ∧
    N ⊓ S.subgroupOf (centralizer (E : Set G)) = ⊥ ∧
    (N : Set (centralizer (E : Set G))) *
      (S.subgroupOf (centralizer (E : Set G)) : Set (centralizer (E : Set G))) = Set.univ
  BS : ∀ b ∈ B, ∀ s ∈ S, b * s = s * b
  h67 : ∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t
  cU : ∀ c : G, (∀ u ∈ S ⊔ E, c * u = u * c) → c = 1 ∨ c = t
  h112 : ∀ g : G, g * z * g⁻¹ ∈ S ⊔ E →
    ∃ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), m * z * m⁻¹ = g * z * g⁻¹

theorem fin76bOuterS8₄_of_hyp
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T E : Subgroup G)
      (Q : Sylow 2 G) (x : G) (B : Subgroup G) (β : G) (S : Subgroup G),
      OuterS8Hyp G L z t T E Q x B β S → False) :
    Fin76bOuterS8₄ := by
  intro G _ _ L z t T E Q x B β hstd hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
    hxz hxt htQ hQz hcomm hconc hsq hσ h98 hS3
  obtain ⟨S, hS2, hSC, hSmax, hzS, hD8, hα, h67, hodd, hBS, hcU, h112⟩ := hS3
  exact h G L z t T E Q x B β S
    { std := hstd, sporadic := hJ, cyclicC := hS, relIdx := hidx, outerE := hE, autE := haut,
      cardT := hT, wFacts := hW, normE := hN, centZ := hcent, outerB := hB, cardEβ := hβ8,
      sylowS := hSyl, T_le_Q := hTQ, x_mem := hxQ, x_not_mem := hxT, x_norm := hxN, x_z := hxz,
      x_t := hxt, t_central := htQ, Q_cent := hQz, z_comm := hcomm, lemma96 := hconc, sqL := hsq,
      sigma := hσ, z_not_L := h98, S2 := hS2, SC := hSC, Smax := hSmax, zS := hzS, D8 := hD8,
      alpha := hα, odd := hodd, BS := hBS, h67 := h67, cU := hcU, h112 := h112 }

end CFSG.EvenSporadicStandard.Fin76b
