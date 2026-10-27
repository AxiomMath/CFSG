module

public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

@[expose] def torusW (G : Type) [Group G] (t s₀ : G) : Subgroup G :=
  (CFSG.pPrimeCore 2 (Subgroup.centralizer
    ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) : Set G))).map
      (Subgroup.centralizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ : Subgroup G) :
        Set G)).subtype

@[expose] def torusH (G : Type) [Group G] (t s₀ : G) : Subgroup G :=
  Subgroup.normalizer ((torusW G t s₀ : Subgroup G) : Set G)

@[expose] def torusK (G : Type) [Group G] (t s₀ : G) : Subgroup G :=
  Subgroup.centralizer ((torusW G t s₀ : Subgroup G) : Set G)

@[expose] def TorusNormalizerClauses (G : Type) [Group G] (t s₀ d : G) (q : ℕ)
    (F' : Type) [Field F'] [Finite F']
    (φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃*
      CFSG.GorensteinWalter.PGL2 F') : Prop :=
  let e : ℤ := if q % 4 = 1 then 1 else -1
  let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
  let D : Subgroup G := Subgroup.centralizer (V : Set G)
  let W : Subgroup G := torusW G t s₀
  let B : Subgroup G := (N t).map (C t).subtype
  let H : Subgroup G := torusH G t s₀
  let K : Subgroup G := torusK G t s₀
  let q' : ℕ := Nat.card F'
  let e' : ℤ := if q' % 4 = 1 then 1 else -1
  let v : G := s₀ * d
  let X : Subgroup G := H ⊓ Subgroup.centralizer {v}
  let U : Subgroup G := (CFSG.pPrimeCore 2 X).map X.subtype
  IsCyclic W ∧ (Nat.card W : ℤ) = ((q : ℤ) + e) / 2 ∧ V ⊔ W = D ∧ Disjoint V W ∧
    B ≤ K ∧ K.relIndex H = 2 ∧ (∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧
    (CFSG.pPrimeCore 2 H).map H.subtype = W ∧ (CFSG.pPrimeCore 2 K).map K.subtype = W ∧
    (∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = V) ∧
    (∀ W₀ : Subgroup G, W₀ ≤ W → W₀ ≠ ⊥ → Subgroup.normalizer (W₀ : Set G) = H) ∧
    (∀ w ∈ W, w ≠ 1 → Subgroup.centralizer {w} = K) ∧
    d ∈ C t ∧ orderOf d = 4 ∧ d ^ 2 = t ∧ d * s₀ * d⁻¹ = t * s₀ ∧
    (∀ w ∈ W, d * w * d⁻¹ = w⁻¹) ∧ (∀ x ∈ B, d * x = x * d) ∧
    (∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype =
      Subgroup.zpowers d ⊔ Subgroup.zpowers s₀) ∧
    C t ⊓ H = W ⊔ B ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers s₀) ∧
    (q' % 8 = 3 ∨ q' % 8 = 5) ∧
    ((K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 2 H))).map φ.toMonoidHom =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F')).range ∧
    4 * (Nat.card B : ℤ) = q' - e' ∧
    orderOf v = 2 ∧ v ∈ H ∧ v ∉ K ∧ IsCyclic U ∧ 2 * (Nat.card U : ℤ) = q' + e' ∧
    U ≤ K ∧ (∀ u ∈ U, t * u * t⁻¹ = u⁻¹) ∧ Nat.Coprime (Nat.card U) (Nat.card B)

end CFSG.Semidihedral.FixedCoreNontrivial
