module

public import CFSG.GF2Type.Aschbacher1976Full.HSPartCGen
public import CFSG.GF2Type.Aschbacher1976Full.WidthCbit

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup PartC

section Vocabulary

variable {G : Type} [Group G] [Finite G]

@[expose] def BadAt (z : G) (T : Sylow 2 G) : Prop :=
  HSSetting G z ∧ HSTI z ∧ (T : Subgroup G) ≤ Hz z ∧ Nat.card (ET (T : Subgroup G) z) = 4

@[expose] def Dtil (z : G) : Set (Qbar z) := yBar z '' Dinv z

@[expose] def FibreProp (z : G) : Prop :=
  ∀ u ∈ Dinv z, ∀ u' ∈ Dinv z,
    IsPGroup 2 ↥(Subgroup.closure ({yBar z u, yBar z u'} : Set (Qbar z))) → u' = u ∨ u' = u * z

@[expose] def PLocalFacts (z : G) : Prop :=
  ∀ u ∈ Dinv z,
    IsPGroup 2 ↥(Fz u ⊓ Hz z) ∧ Nat.card (Fz u ⊓ Hz z : Subgroup G) = 32 ∧ u ∈ Fz u ⊓ Hz z ∧
    Nat.card (Fz u ⊓ Fz z : Subgroup G) ≤ 8 ∧
    (∀ p ∈ Fz u ⊓ Hz z, p * p ∈ Subgroup.zpowers u) ∧
    (∀ p ∈ Fz u ⊓ Hz z, ∀ p' ∈ Fz u ⊓ Hz z, p * p' * p⁻¹ * p'⁻¹ ∈ Subgroup.zpowers u) ∧
    (∀ c ∈ Hz z, c * u = u * c → ∀ p ∈ Fz u ⊓ Hz z, c * p * c⁻¹ ∈ Fz u ⊓ Hz z)

@[expose] def IsCruxE (z k : G) (E : Subgroup G) : Prop :=
  E ≤ Fz z ∧ (∀ h ∈ Hz z, ∀ e ∈ E, h * e * h⁻¹ ∈ E) ∧ z ∈ E ∧ k ∉ E ∧
    Fz z ≤ Subgroup.zpowers k ⊔ E ∧ Dinv z ⊆ E

@[expose] def QuadFun (z : G) (θ : G → ZMod 2) : Prop :=
  (∀ x ∈ Fz z, ∀ y ∈ Fz z, θ (x * y) = θ x + θ y + Width.cbit z x y) ∧
    (∀ x ∈ Fz z, ∀ c ∈ ZF z, θ (x * c) = θ x) ∧
    (∀ h ∈ Hz z, ∀ x ∈ Fz z, θ (h * x * h⁻¹) = θ x) ∧ (∀ d ∈ Dinv z, θ d = 0)

end Vocabulary

section Finite

variable {Q : Type*} [Group Q]

@[expose] def HasYStmt (D : Set Q) : Prop :=
  ∃ Y : Subgroup Q, (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) ∧ (∀ x ∈ Y, x * x = 1) ∧ 4 ≤ Nat.card Y ∧
    ∀ y ∈ Y, (∀ d ∈ D, y * d = d * y) → y = 1

@[expose] def nineSet : Set (Equiv.Perm (Fin 6)) :=
  {s | ∃ a b d e : Fin 6, a.val < 3 ∧ b.val < 3 ∧ 3 ≤ d.val ∧ 3 ≤ e.val ∧ a ≠ b ∧ d ≠ e ∧
    s = Equiv.swap a b * Equiv.swap d e}

@[expose] def ConjNine (ι : Q →* Equiv.Perm (Fin 6)) (D : Set Q) : Prop :=
  ∃ σ : Equiv.Perm (Fin 6), (∀ d ∈ D, σ * ι d * σ⁻¹ ∈ nineSet) ∧
    ∀ s ∈ nineSet, ∃ d ∈ D, σ * ι d * σ⁻¹ = s

@[expose] def NineFree (D : Set Q) : Prop :=
  ∃ N : Subgroup Q, N.Normal ∧ Nat.card N = 9 ∧ ∀ n ∈ N, n ≠ 1 → ∀ d ∈ D, n * d * n⁻¹ ≠ d

@[expose] def TbarFacts (D : Set Q) : Prop :=
  ∀ S : Subgroup Q, IsPGroup 2 ↥S → ∀ a ∈ D, a ∈ S →
    (∀ x ∈ S, x * x = 1 ∨ x * x = a) ∧
    (∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = a) ∧
    (∀ x ∈ S, ∀ y ∈ S, x * y = y * x → x = 1 ∨ x = a ∨ y = 1 ∨ y = a ∨ y = x ∨ y = x * a)

end Finite

@[expose] def CruxSixStmt : Prop :=
  ∀ {Q : Type} [Group Q] [Finite Q] (ι : Q →* Equiv.Perm (Fin 6)), Function.Injective ι →
    (∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥) →
    ∀ D : Set Q, D.Nonempty → (∀ d ∈ D, d * d = 1 ∧ d ≠ 1) → (∀ q : Q, ∀ d ∈ D, q * d * q⁻¹ ∈ D) →
      (∀ d ∈ D, ∀ e ∈ D, d ≠ e → ¬ IsPGroup 2 ↥(Subgroup.closure ({d, e} : Set Q))) →
      (∀ d ∈ D, ∀ e ∈ D, d ≠ e → orderOf (d * e) = 3 ∨ orderOf (d * e) = 5) ∧
        (((D.ncard = 3 ∨ D.ncard = 5) ∧ ¬ HasYStmt D) ∨ (D.ncard = 9 ∧ ConjNine ι D))

@[expose] def CruxNineStmt : Prop :=
  ∀ {Q : Type} [Group Q] [Finite Q] (ι : Q →* Equiv.Perm (Fin 6)), Function.Injective ι →
    ∀ D : Set Q, (∀ q : Q, ∀ d ∈ D, q * d * q⁻¹ ∈ D) → ConjNine ι D → NineFree D ∧ TbarFacts D

@[expose] def CruxPLocalStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {z : G}, HSSetting G z → HSTI z → PLocalFacts z

@[expose] def CruxFrattiniStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {z : G}, HSSetting G z → HSTI z → FibreProp z → PLocalFacts z →
    (∀ d ∈ Dtil z, ∀ e ∈ Dtil z, ∃ m ∈ Subgroup.closure (Dtil z), m * d * m⁻¹ = e) →
      HasYStmt (Dtil z)

@[expose] def CruxFinWStmt : Prop :=
  ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (b : LinearMap.BilinForm (ZMod 2) V), b.IsAlt → b.Nondegenerate →
    Module.finrank (ZMod 2) V = 4 →
    ∀ N : Subgroup (V ≃ₗ[ZMod 2] V), Nat.card N = 9 → (∀ g ∈ N, ∀ x y : V, b (g x) (g y) = b x y) →
    ∃ q : V → ZMod 2, q 0 = 0 ∧ (∀ x y : V, q (x + y) = q x + q y + b x y) ∧
      (∀ g : V ≃ₗ[ZMod 2] V, (∀ x y : V, b (g x) (g y) = b x y) → (∀ n ∈ N, g * n * g⁻¹ ∈ N) →
        ∀ x : V, q (g x) = q x) ∧
      ∀ v : V, v ≠ 0 → (∀ n ∈ N, n ≠ 1 → n v ≠ v) → q v = 0

@[expose] def CruxQuadStmt : Prop :=
  CruxFinWStmt → ∀ {G : Type} [Group G] [Finite G] {z : G}, HSSetting G z → HSTI z →
    NineFree (Dtil z) → ∃ θ : G → ZMod 2, QuadFun z θ

@[expose] def CruxL5Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {z : G} {T : Sylow 2 G}, BadAt z T → FibreProp z →
    ∀ k : G, ZF z = Subgroup.zpowers k → ∀ E : Subgroup G, IsCruxE z k E → TbarFacts (Dtil z) →
      k ∉ ⁅(T : Subgroup G), (T : Subgroup G)⁆ ⊔ E

end CFSG.GF2Type.Aschbacher1976Full.HS
