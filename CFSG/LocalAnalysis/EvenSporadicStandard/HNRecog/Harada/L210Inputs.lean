module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAR

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

abbrev NVgrp (t z : G) : Subgroup G :=
  normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G)

structure Lemma27Spec (h : Setting25 G t z z₁ ι zv R0 F)
    (φ : ↥(normalizer (Rgrp h : Set G)) →* A5WrTwo) : Prop where
  surj : Function.Surjective φ
  ker : φ.ker = (Rgrp h).subgroupOf (normalizer (Rgrp h : Set G))
  faithful : ∀ n ∈ normalizer (Rgrp h : Set G),
    (∀ x ∈ Rgrp h, n * x * n⁻¹ * x⁻¹ ∈ zpowers z) → n ∈ Rgrp h
  outer : ∀ (n : G) (hn : n ∈ normalizer (Rgrp h : Set G)), n ∈ ι.range → n ∉ Rgrp h →
    φ ⟨n, hn⟩ ∉ commutator A5WrTwo
  stab : Nonempty (↥(Subgroup.map φ
    (Subgroup.subgroupOf (NVgrp t z) (normalizer (Rgrp h : Set G)))) ≃* Equiv.Perm (Fin 5))

@[expose] def Lemma27Out (h : Setting25 G t z z₁ ι zv R0 F) : Prop :=
  ∃ φ : ↥(normalizer (Rgrp h : Set G)) →* A5WrTwo, Lemma27Spec h φ

@[expose] def Facts210 (G : Type) [Group G] (t z : G) : Prop :=
  ∀ Y : Subgroup G, Y ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) → ⁅Y, Y⁆ = Y →
    ∀ f : ↥Y →* alternatingGroup (Fin 5), Function.Surjective f →
      f.ker ≤ (zpowers z).subgroupOf Y → False

end CFSG.EvenSporadicStandard.HNRecog.Harada
