module

public import CFSG.LargeExtraspecial.O62Model
public import CFSG.LargeExtraspecial.Types

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

@[expose] noncomputable def codeSubgroup (gens : List ℕ) : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) :=
  Subgroup.closure {g | ∃ m ∈ gens, Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) m}

@[expose] def kPGLGens : List ℕ := [34647329153, 34630549889, 17717821506]

@[expose] def kPGL0Gens : List ℕ := [6730164633, 34630541704]

@[expose] noncomputable def KPGL : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) := codeSubgroup kPGLGens

@[expose] noncomputable def KPGL0 : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) := codeSubgroup kPGL0Gens

@[expose] noncomputable def VPlus : Submodule (ZMod 2) V₀ :=
  Submodule.span (ZMod 2) {Code.vec 2, Code.vec 4, Code.vec 32}

@[expose] noncomputable def VStar : Submodule (ZMod 2) V₀ :=
  Submodule.span (ZMod 2) {Code.vec 1, Code.vec 8, Code.vec 16}

@[expose] def CensusCond (minus : Bool) (H L : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) (e : V₀) : Prop :=
  L ≤ H ∧ (∀ x ∈ L, x e = e) ∧ (∀ x ∈ L, x * x = 1) ∧ (if minus then 8 else 4) ≤ Nat.card L ∧
    (∀ h ∈ H, h ∈ Subgroup.normalizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)) ↔ h e = e) ∧
    IsPGroup 2 ↥(H ⊓ Subgroup.centralizer (L : Set (V₀ ≃ₗ[ZMod 2] V₀)))

@[expose] def CensusPlusProp : Prop :=
  ∀ H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), H ≤ O₀ false →
    (∀ N : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), N ≤ H →
      (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → IsPGroup 2 N → N = ⊥) →
    (∀ W : Submodule (ZMod 2) V₀, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ b : V₀, b ≠ 0 ∧ qModel false b = 0 ∧ ∃ L, CensusCond false H L b ∧
      ∃ t ∈ L, IsTypeA (qModel false) t 2) →
    H = Ω₀ false ∨ H = O₀ false ∨ ∃ g ∈ O₀ false, ∀ x, x ∈ H ↔ g⁻¹ * x * g ∈ KPGL

@[expose] def CensusMinusProp : Prop :=
  ∀ H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), H ≤ O₀ true →
    (∀ N : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), N ≤ H →
      (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → IsPGroup 2 N → N = ⊥) →
    (∀ W : Submodule (ZMod 2) V₀, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ b : V₀, b ≠ 0 ∧ qModel true b = 0 ∧ ∃ L, CensusCond true H L b ∧
      ∃ t ∈ L, IsTypeA (qModel true) t 2) →
    H = Ω₀ true ∨ H = O₀ true

@[expose] def PGLFactsProp : Prop :=
  KPGL ≤ O₀ false ∧
  Nat.card KPGL = 336 ∧
  ⁅KPGL, KPGL⁆ = KPGL0 ∧
  Nat.card KPGL0 = 168 ∧
  (∀ v ∈ VPlus, qModel false v = 0) ∧
  (∀ v ∈ VStar, qModel false v = 0) ∧
  VPlus ⊓ VStar = ⊥ ∧
  VPlus ⊔ VStar = ⊤ ∧
  (∀ k ∈ KPGL0, VPlus.map (k : V₀ →ₗ[ZMod 2] V₀) = VPlus ∧
    VStar.map (k : V₀ →ₗ[ZMod 2] V₀) = VStar) ∧
  (∀ k ∈ KPGL, k ∉ KPGL0 → VPlus.map (k : V₀ →ₗ[ZMod 2] V₀) = VStar ∧
    VStar.map (k : V₀ →ₗ[ZMod 2] V₀) = VPlus) ∧
  (∀ W : Submodule (ZMod 2) V₀, (∀ k ∈ KPGL0, ∀ w ∈ W, k w ∈ W) →
    W = ⊥ ∨ W = VPlus ∨ W = VStar ∨ W = ⊤) ∧
  (∀ e e' : V₀, e ≠ 0 → e' ≠ 0 → (e ∈ VPlus ∨ e ∈ VStar) →
    (e' ∈ VPlus ∨ e' ∈ VStar) → ∃ k ∈ KPGL, k e = e') ∧
  (∀ e : V₀, e ≠ 0 → qModel false e = 0 → e ∉ VPlus → e ∉ VStar →
    ∀ L, ¬ CensusCond false KPGL L e) ∧
  (∀ u ∈ KPGL, u ∉ KPGL0 → u * u = 1 →
    Nat.card ↥(KPGL ⊓ Subgroup.centralizer {u}) = 12 ∧
    ∀ N : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), N ≤ KPGL ⊓ Subgroup.centralizer {u} →
      (∀ c ∈ KPGL ⊓ Subgroup.centralizer {u}, ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
      IsPGroup 2 N → N ≤ Subgroup.zpowers u) ∧
  (∀ u ∈ KPGL, u ∉ KPGL0 → u * u = 1 → ∀ u' ∈ KPGL, u' ∉ KPGL0 → u' * u' = 1 →
    ∃ k ∈ KPGL, k * u * k⁻¹ = u') ∧
  (∀ w ∈ KPGL0, w ≠ 1 → w * w = 1 →
    Nat.card ↥(KPGL ⊓ Subgroup.centralizer {w}) = 16 ∧
    Nat.card {v : V₀ // w v = v} = 16)

@[expose] def beta0 (v w : V₀) : ZMod 2 := v 1 * w 0 + v 3 * w 2 + v 5 * w 4

@[ext] structure Q0 where
  a : ZMod 2
  v : V₀
  deriving DecidableEq

instance : Group Q0 where
  mul x y := ⟨x.a + y.a + beta0 x.v y.v, x.v + y.v⟩
  one := ⟨0, 0⟩
  inv x := ⟨x.a + beta0 x.v x.v, x.v⟩
  mul_assoc x y z :=
    Q0.ext (show x.a + y.a + beta0 x.v y.v + z.a + beta0 (x.v + y.v) z.v =
        x.a + (y.a + z.a + beta0 y.v z.v) + beta0 x.v (y.v + z.v) by
      simp only [beta0, Pi.add_apply]
      ring) (add_assoc x.v y.v z.v)
  one_mul x :=
    Q0.ext (show 0 + x.a + beta0 0 x.v = x.a by simp [beta0]) (zero_add x.v)
  mul_one x :=
    Q0.ext (show x.a + 0 + beta0 x.v 0 = x.a by simp [beta0]) (add_zero x.v)
  inv_mul_cancel x :=
    Q0.ext (show x.a + beta0 x.v x.v + x.a + beta0 x.v x.v = 0 by
      have h1 : x.a + x.a = 0 := CharTwo.add_self_eq_zero x.a
      have h2 : beta0 x.v x.v + beta0 x.v x.v = 0 := CharTwo.add_self_eq_zero _
      rw [show x.a + beta0 x.v x.v + x.a + beta0 x.v x.v =
        (x.a + x.a) + (beta0 x.v x.v + beta0 x.v x.v) by ring, h1, h2, add_zero])
      (CharTwo.add_self_eq_zero x.v)

instance : Fintype Q0 :=
  Fintype.ofEquiv (ZMod 2 × V₀)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun x => (x.a, x.v)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[expose] def z0 : Q0 := ⟨1, 0⟩

@[expose] def a0 : Q0 := ⟨0, Code.vec 1⟩

@[expose] def inn (e : Q0) : Q0 ≃* Q0 := MulAut.conj e⁻¹

@[expose] def XOver (K : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) : Set (Q0 ≃* Q0) :=
  {φ | ∃ g ∈ K, ∀ x, (φ x).v = g x.v}

@[expose] def ThetaOver (K : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) : Set (Q0 ≃* Q0) :=
  {θ | ∃ g ∈ K, g * g = 1 ∧ ∀ x, (θ x).v = g x.v}

@[expose] def IsSquareData (K : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) (σ : (Q0 ≃* Q0) → Q0) : Prop :=
  σ 1 = 1 ∧ (∀ θ ∈ ThetaOver K, θ * θ = inn (σ θ)) ∧
  (∀ θ ∈ ThetaOver K, ∀ ψ ∈ XOver K, σ (ψ * θ * ψ⁻¹) = ψ (σ θ)) ∧
  (∀ θ ∈ ThetaOver K, ∀ e : Q0, σ (inn e * θ) = σ θ * θ e * e)

@[expose] def PGLSquareProp : Prop :=
  ∀ σ, IsSquareData KPGL σ → ∀ u ∈ KPGL, u ∉ KPGL0 → u * u = 1 →
    ((Set.ncard {θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u x.v) ∧ σ θ = 1} = 8 ∧
        {θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u x.v) ∧ σ θ = z0} = ∅) ∨
      ({θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u x.v) ∧ σ θ = 1} = ∅ ∧
        Set.ncard {θ : Q0 ≃* Q0 | (∀ x, (θ x).v = u x.v) ∧ σ θ = z0} = 8)) ∧
    ∀ θ : Q0 ≃* Q0, (∀ x, (θ x).v = u x.v) → (σ θ = 1 ∨ σ θ = z0) →
      Set.ncard {x : Q0 | θ x = x} = 8 ∧ (∀ x, θ x = x → x * x = 1) ∧
      ∀ w ∈ KPGL0, w ≠ 1 → w * w = 1 → w * u = u * w → ∃ x, θ x = x ∧ w x.v ≠ x.v

@[expose] def A8SquareProp : Prop :=
  ∀ σ, IsSquareData (Ω₀ false) σ →
    Set.ncard {θ : Q0 ≃* Q0 | θ ∈ ThetaOver (Ω₀ false) ∧ θ a0 = a0 ∧ σ θ = a0} = 120 ∧
    (Set.ncard {θ : Q0 ≃* Q0 | θ ∈ ThetaOver (Ω₀ false) ∧ θ a0 = a0 ∧ σ θ = z0} ∈
      ({72, 336, 408, 672} : Finset ℕ))

end CFSG.GF2Type.Smith1979W3.Cert690

end
