module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Facts

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Spec

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

@[expose] def Hyp2519 (N : Notation25 hs) (i : G) : Prop :=
  i ∈ N.S ⊓ Subgroup.centralizer (N.K : Set G) ∧ i ≠ 1 ∧ i ^ 2 = 1 ∧
    ¬ IsComponentIn N.K (Subgroup.centralizer ({i} : Set G))

@[expose] def Rgrp2519 (N : Notation25 hs) (i : G) : Subgroup G :=
  N.S ⊓ Subgroup.centralizer ({i} : Set G) ⊓ (N.S ⊓ Subgroup.centralizer (N.K : Set G))

structure Ident2519 (N : Notation25 hs) (t i : G) (Ki KP R2 : Subgroup G) : Prop where
  comp : IsComponentIn Ki (Subgroup.centralizer ({i} : Set G))
  K_le : N.K ≤ KP
  KP_le : KP ≤ Subgroup.centralizer ({i} : Set G)
  shape : (Ki ≠ CFSG.conjugate Ki t ∧ KP = Ki ⊔ CFSG.conjugate Ki t ∧
      ⁅Ki, CFSG.conjugate Ki t⁆ = ⊥) ∨
    (KP = Ki ∧ ⁅Ki, Subgroup.zpowers t⁆ = Ki)
  K_eq : N.K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
    (KP ⊓ Subgroup.centralizer ({t} : Set G))
  three_rank : ∃ A : Subgroup G, A ≤ KP ∧ IsElemAbelian 3 A ∧ Nat.card A = 9
  center_three : ∀ x ∈ centerOf KP, x ^ 3 = 1 → x = 1
  R2_le : R2 ≤ Rgrp2519 N i
  R2_index : R2.relIndex (Rgrp2519 N i) = 2
  R2_norm : N.S ⊓ Subgroup.centralizer (N.K : Set G) ≤ N.S ⊓ Subgroup.centralizer ({i} : Set G) →
    (∀ c ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G), c ∈ Subgroup.normalizer (N.K : Set G)) →
    (∀ j : G, Hyp2519 N j → Nat.card (Rgrp2519 N j) = Nat.card (Rgrp2519 N i) →
      Nat.card ↥(N.S ⊓ Subgroup.centralizer ({j} : Set G)) ≤
        Nat.card ↥(N.S ⊓ Subgroup.centralizer ({i} : Set G))) →
    (∃ n ∈ N.S ⊓ Subgroup.normalizer (N.K : Set G), n * i ≠ i * n) →
    ∀ c ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G), c ∈ Subgroup.normalizer (N.K : Set G) →
      c ∈ Subgroup.normalizer (R2 : Set G)
  R2_not_comp : ∀ r ∈ R2, r ≠ 1 → r ^ 2 = 1 →
    ¬ IsComponentIn N.K (Subgroup.centralizer ({r} : Set G))
  R0_index : IsL2pType ↥N.K →
    (Rgrp2519 N i ⊓ Subgroup.centralizer (KP : Set G)).relIndex (Rgrp2519 N i) = 2
  normal_C : IsL2pType ↥N.K → ∀ j ∈ Rgrp2519 N i ⊓ Subgroup.centralizer (KP : Set G), j ≠ 1 →
    j ^ 2 = 1 → Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (KP : Set G)
  perfect_cent : IsL2pType ↥N.K → ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (KP : Set G) →
    Y ≤ Subgroup.centralizer (N.K : Set G) → ⁅Y, Y⁆ = Y → Y ≤ Subgroup.centralizer (KP : Set G)

@[expose] def Part1_2519 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2518 N t zK → ∀ i : G, Hyp2519 N i →
      ∃ Ki KP R2 : Subgroup G, Ident2519 N t i Ki KP R2

@[expose] def Part2_2519 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2518 N t zK →
      (∀ i : G, Hyp2519 N i → ∃ Ki KP R2 : Subgroup G, Ident2519 N t i Ki KP R2) →
      ∀ i : G, Hyp2519 N i → Rgrp2519 N i = Subgroup.closure {t, i}

@[expose] def Concl2519Three (N : Notation25 hs) (t i : G) : Prop :=
  ∃ Ki : Subgroup G, IsComponentIn Ki (Subgroup.centralizer ({i} : Set G)) ∧
    ((Ki ≠ CFSG.conjugate Ki t ∧
        N.K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
          ((Ki ⊔ CFSG.conjugate Ki t) ⊓ Subgroup.centralizer ({t} : Set G)) ∧
        ∃ p : ℕ, IsFermatOrMersenne p ∧ 7 ≤ p ∧ StatedClassicalModel ↥N.K .PSL 2 p 1 ∧
          StatedClassicalModel ↥Ki .PSL 2 p 1) ∨
      (N.K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
          (Ki ⊓ Subgroup.centralizer ({t} : Set G)) ∧
        ((StatedClassicalModel ↥N.K .PSL 3 2 1 ∧
            StatedClassicalModel (↥Ki ⧸ Subgroup.center ↥Ki) .PSL 3 2 2 ∧
            Nat.card (Subgroup.center ↥Ki) ≤ 2 ∧ InducesOuter t Ki) ∨
          (StatedClassicalModel ↥N.K .PSL 3 2 1 ∧
            Nonempty (↥Ki ≃* CFSG.Blueprint.NativeSporadic.Carrier .J2) ∧
            InducesOuter t Ki) ∨
          (Nonempty (↥N.K ≃* alternatingGroup (Fin 6)) ∧
            (StatedClassicalModel ↥Ki .PSp 2 2 2 ∨ StatedClassicalModel ↥Ki .PSL 5 2 1 ∨
              Nonempty (↥Ki ≃* CFSG.Blueprint.NativeSporadic.Carrier .HS) ∨
              Nonempty (↥Ki ≃* alternatingGroup (Fin 8))))))) ∧
    ((N.z ∈ N.K ∧ ∃ g : G, g⁻¹ * t * g = t * N.z) ∨
      (Nonempty (↥Ki ≃* alternatingGroup (Fin 8)) ∧
        ∃ (φ : ↥Ki ≃* alternatingGroup (Fin 8)) (a b : Fin 8), a ≠ b ∧
          InducesAut t Ki φ (MulAut.conjNormal (Equiv.swap a b))))

@[expose] def Part3_2519 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2518 N t zK → ∀ i : G, Hyp2519 N i →
      (∀ i' : G, Hyp2519 N i' → Rgrp2519 N i' = Subgroup.closure {t, i'}) →
      N.K0 = N.K ∧ Concl2519Three N t i

theorem lemma2519_of_parts (h1 : Part1_2519) (h2 : Part2_2519) (h3 : Part3_2519) : Lemma2519 := by
  intro G _ _ T M hs N t zK hlv i hi hi1 hi2 hnc
  have hH : Hyp2519 N i := ⟨hi, hi1, hi2, hnc⟩
  have hR : ∀ i' : G, Hyp2519 N i' → Rgrp2519 N i' = Subgroup.closure {t, i'} := fun i' hi' =>
    h2 G T M hs N t zK hlv (h1 G T M hs N t zK hlv) i' hi'
  obtain ⟨hK0, h3'⟩ := h3 G T M hs N t zK hlv i hH hR
  exact ⟨hK0, hR i hH, h3'⟩

end Spec

end CFSG.QuasithinUnique
