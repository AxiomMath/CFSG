module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter CFSG.GH74.GLS
open scoped MatrixGroups Pointwise commutatorElement

@[expose] def IVK_1_2a : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F),
    (∀ T : Sylow 2 (MulAut K), ∃ e' : K ≃* L2 F, ∃ N : L2Notation e', N.T = T) ∧
    ∀ N : L2Notation e,
      innAut K ⊔ zpowers N.t ⊔ fieldAutSub e = ⊤ ∧ IsCyclic ↥(fieldAutSub e) ∧
      (innAut K ⊔ zpowers N.t) ⊓ fieldAutSub e = ⊥ ∧
      ∀ x ∈ fieldAutSub e, ∀ y ∈ innAut K ⊔ zpowers N.t, ⁅x, y⁆ ∈ innAut K

@[expose] def IVK_1_2a_exists : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F)
    (T : Sylow 2 (MulAut K)), ∃ e' : K ≃* L2 F, ∃ N : L2Notation e', N.T = T

@[expose] def IVK_1_2a_struct : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e),
      innAut K ⊔ zpowers N.t ⊔ fieldAutSub e = ⊤ ∧ IsCyclic ↥(fieldAutSub e) ∧
      (innAut K ⊔ zpowers N.t) ⊓ fieldAutSub e = ⊥ ∧
      ∀ x ∈ fieldAutSub e, ∀ y ∈ innAut K ⊔ zpowers N.t, ⁅x, y⁆ ∈ innAut K

theorem IVK_1_2a_of_parts (h1 : IVK_1_2a_exists) (h2 : IVK_1_2a_struct) : IVK_1_2a := by
  intro F _ _ hF K _ _ e
  exact ⟨fun T => h1 F hF K e T, fun N => h2 F hF K e N⟩

@[expose] def IVK_1_2b : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] (_ : K ≃* L2 F),
    Nat.card K = Nat.card F * (Nat.card F ^ 2 - 1) / 2

@[expose] def IVK_1_2c : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e), ∃ n : ℕ, IsDihedralTwoGroup ↥N.P n

@[expose] def IVK_1_2d : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e),
    innAut K ⊔ zpowers N.t = innDiagSub e ∧ Nonempty (↥(innDiagSub e) ≃* PGL2 F) ∧
      N.P ⊔ zpowers N.t = N.Pt ∧ ∃ n : ℕ, IsDihedralTwoGroup ↥N.Pt n

@[expose] def IVK_1_2e : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F),
    IsCyclic ↥(fieldAutSub e) ∧ Nonempty (↥(fieldAutSub e) ≃* (F ≃+* F)) ∧
      ∀ p n : ℕ, p.Prime → Nat.card F = p ^ n → Nat.card ↥(fieldAutSub e) = n

@[expose] def IVK_1_2f : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e),
    N.Pt ⊓ N.R = ⊥ ∧ ∀ n : ℕ, Nat.card ↥N.P = 2 ^ n → Nat.card ↥N.R ≤ 2 ^ (n - 2)

@[expose] def IVK_1_2g : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e),
    (∀ x ∈ N.P, ∀ y ∈ N.P, orderOf x = 2 → orderOf y = 2 → ConjUnder (innAut K) x y) ∧
    (∀ x y : MulAut K, x ∈ N.Pt → x ∉ N.P → y ∈ N.Pt → y ∉ N.P → orderOf x = 2 → orderOf y = 2 →
      ConjUnder (innAut K) x y)

@[expose] def IVK_1_2h_a : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e), ∀ f ∈ N.R, orderOf f = 2 →
      N.P ⊓ zpowers f = ⊥ ∧ ∀ x ∈ N.P, x * f = f * x

@[expose] def IVK_1_2h_b : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e), ∀ f ∈ N.R, orderOf f = 2 →
      ∀ z ∈ N.P, orderOf z = 2 → (∀ x ∈ N.P, x * z = z * x) →
        (∀ x ∈ N.P, x ∈ ((oResidual 2 ↥(fixedSubgroup K f)).map (fixedSubgroup K f).subtype).map
            (MulAut.conj : K →* MulAut K) → x ≠ 1 → orderOf (x * f) = 2 →
          ConjUnder (innAut K) (x * f) (f * z)) ∧
        (∀ x ∈ N.P, x ∉ ((oResidual 2 ↥(fixedSubgroup K f)).map (fixedSubgroup K f).subtype).map
            (MulAut.conj : K →* MulAut K) → orderOf (x * f) = 2 →
          ConjUnder (innAut K) (x * f) f)

@[expose] def IVK_1_2h_c : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e), ∀ f ∈ N.R, orderOf f = 2 →
      ∀ x ∈ innDiagSub e, orderOf (x * f) = 2 → ConjUnder (innDiagSub e) (x * f) f

@[expose] def IVK_1_2h : Prop := IVK_1_2h_a ∧ IVK_1_2h_b ∧ IVK_1_2h_c

@[expose] def IVK_1_2i_a : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e), ∀ f ∈ N.R, orderOf f = 2 →
      ∀ z ∈ N.P, orderOf z = 2 → (∀ x ∈ N.P, x * z = z * x) → ⁅N.t, f⁆ = z

@[expose] def IVK_1_2i_b : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e), ∀ f ∈ N.R, orderOf f = 2 →
      ∃ n : ℕ, IsSemidihedralTwoGroup ↥(N.P ⊔ zpowers (f * N.t)) n

@[expose] def IVK_1_2i_c : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e), ∀ f ∈ N.R, orderOf f = 2 →
      ∀ x ∈ (N.T : Subgroup (MulAut K)), orderOf x = 2 →
        x ∈ N.P ∨ (x ∈ N.Pt ∧ x ∉ N.P) ∨ ∃ p ∈ N.P, x = p * f

@[expose] def IVK_1_2i : Prop := IVK_1_2i_a ∧ IVK_1_2i_b ∧ IVK_1_2i_c

@[expose] def IVK_1_2j : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e), ∀ D : Subgroup (MulAut K), D ≤ (N.T : Subgroup (MulAut K)) → N.P ≤ D →
      (∃ n : ℕ, IsDihedralTwoGroup ↥D n) → D = N.P ∨ D = N.P ⊔ zpowers N.t

@[expose] def IVK_1_2k_a : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F),
    pRank 2 (MulAut K) = 2 ∨ pRank 2 (MulAut K) = 3

@[expose] def IVK_1_2k_b : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F),
    ∀ E : Subgroup (MulAut K), IsElementaryAbelian 2 ↥E → Nat.card ↥E = 8 →
      ∃ x ∈ E, orderOf x = 2 ∧ IsFAutL2 x

@[expose] def IVK_1_2k : Prop := IVK_1_2k_a ∧ IVK_1_2k_b

@[expose] def IVK_1_2l : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F),
    ∀ X : Subgroup K, Odd (Nat.card ↥X) → Group.IsNilpotent ↥X →
      (IsCyclic ↥X ∧ (Nat.card ↥X ∣ Nat.card F - 1 ∨ Nat.card ↥X ∣ Nat.card F + 1)) ∨
      ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p ↥X ∧ Nat.card ↥X ∣ Nat.card F

@[expose] def IVK_1_3a : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (ε : ℤ), (ε = 1 ∨ ε = -1) → (Nat.card F : ℤ) ≡ ε [ZMOD 4] →
    ∀ d : ℕ, (d : ℤ) = Nat.card F - ε → ∀ u : K, orderOf u = 2 →
      IsDihedralOrder ↥(centralizer ({MulAut.conj u} : Set (MulAut K)) ⊓ innDiagSub e) (2 * d) ∧
      IsDihedralOrder ↥(centralizer ({u} : Set K)) d ∧
      ∀ û : SL2 F, L2.mk F û = e u →
        IsCyclic ↥(centralizer ({û} : Set (SL2 F))) ∧
          Nat.card ↥(centralizer ({û} : Set (SL2 F))) = d

@[expose] def IVK_1_3b : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (ε : ℤ), (ε = 1 ∨ ε = -1) → (Nat.card F : ℤ) ≡ ε [ZMOD 4] →
    ∀ d : ℕ, (d : ℤ) = Nat.card F + ε → ∀ v : MulAut K, v ∈ innDiagSub e → v ∉ innAut K →
      orderOf v = 2 →
      IsDihedralOrder ↥(centralizer ({v} : Set (MulAut K)) ⊓ innDiagSub e) (2 * d) ∧
      IsDihedralOrder ↥(fixedSubgroup K v) d ∧
      ∀ g : GL (Fin 2) F, innDiagHom e (Matrix.ProjGenLinGroup.mk g) = v →
        IsCyclic ↥(slCentralizer g) ∧ Nat.card ↥(slCentralizer g) = d

@[expose] def IVK_1_3c : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F),
    ∀ u : MulAut K, u ∈ innDiagSub e → orderOf u = 2 →
      ∀ X : Subgroup K, X ≠ ⊥ →
        X ≤ xu u →
        autNormalizer (innDiagSub e) X = centralizer ({u} : Set (MulAut K)) ⊓ innDiagSub e

@[expose] def IVK_1_3d : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F),
    ∀ u : MulAut K, u ∈ innDiagSub e → orderOf u = 2 →
      ∃ Y : Subgroup (MulAut K), Y ≤ centralizer ({u} : Set (MulAut K)) ∧
        (∀ c ∈ centralizer ({u} : Set (MulAut K)), ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) ∧
        Odd (Nat.card ↥Y) ∧
        (∃ k : ℕ, Nat.card ↥Y * 2 ^ k = Nat.card ↥(centralizer ({u} : Set (MulAut K)))) ∧
        (fittingSubgroup ↥Y).map Y.subtype = xuInn u ∧
        (∃ (_ : ((xuInn u).subgroupOf Y).Normal), IsCyclic (↥Y ⧸ (xuInn u).subgroupOf Y)) ∧
        ∃ e' : K ≃* L2 F, Y ≤ xuInn u ⊔ fieldAutSub e'

@[expose] def IVK_1_3e : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F),
    ∀ u : MulAut K, u ∈ innDiagSub e → orderOf u = 2 →
      (11 < Nat.card F → IsCoatom (fixedSubgroup K u)) ∧
      (u ∉ innAut K → fixedSubgroup K u ≠ ⊤ ∧
        ∀ M : Subgroup K, fixedSubgroup K u ≤ M → M.map u.toMonoidHom = M →
          M = fixedSubgroup K u ∨ M = ⊤)

@[expose] def IVK_1_3f_a : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e),
    ∀ U₁ U₂ : Subgroup (MulAut K), U₁ ≤ N.P → U₂ ≤ N.P → IsFourSubgroup U₁ → IsFourSubgroup U₂ →
      ∃ g ∈ N.Pt, U₁.map (MulAut.conj g).toMonoidHom = U₂

@[expose] def IVK_1_3f_b : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e),
    ∃ U : Subgroup (MulAut K), U ≤ N.P ∧ IsFourSubgroup U ∧
      centralizer (U : Set (MulAut K)) = U ⊔ fieldAutSub e ∧ U ⊓ fieldAutSub e = ⊥

@[expose] def IVK_1_3f_c : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F),
    ∀ U : Subgroup (MulAut K), U ≤ innAut K → IsFourSubgroup U →
      Nonempty (↥(normalizer (U : Set (MulAut K)) ⊓ innAut K) ≃* alternatingGroup (Fin 4)) ∨
        Nonempty (↥(normalizer (U : Set (MulAut K)) ⊓ innAut K) ≃* Equiv.Perm (Fin 4))

@[expose] def IVK_1_3f : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e),
    (∀ U₁ U₂ : Subgroup (MulAut K), U₁ ≤ N.P → U₂ ≤ N.P → IsFourSubgroup U₁ → IsFourSubgroup U₂ →
      ∃ g ∈ N.Pt, U₁.map (MulAut.conj g).toMonoidHom = U₂) ∧
    ∃ U : Subgroup (MulAut K), U ≤ N.P ∧ IsFourSubgroup U ∧
      (Nonempty (↥(normalizer (U : Set (MulAut K)) ⊓ innAut K) ≃* alternatingGroup (Fin 4)) ∨
        Nonempty (↥(normalizer (U : Set (MulAut K)) ⊓ innAut K) ≃* Equiv.Perm (Fin 4))) ∧
      centralizer (U : Set (MulAut K)) = U ⊔ fieldAutSub e ∧ U ⊓ fieldAutSub e = ⊥

theorem IVK_1_3f_of_parts (ha : IVK_1_3f_a) (hb : IVK_1_3f_b) (hc : IVK_1_3f_c) : IVK_1_3f := by
  intro F _ _ hF K _ _ e N
  refine ⟨ha F hF K e N, ?_⟩
  obtain ⟨U, hUP, hU4, hUC, hUF⟩ := hb F hF K e N
  exact ⟨U, hUP, hU4, hc F hF K e U (hUP.trans inf_le_right) hU4, hUC, hUF⟩

@[expose] def IVK_1_3g : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e), ∀ P₀ : Subgroup (MulAut K), P₀ ≤ N.P → (P₀.subgroupOf N.P).index = 2 →
      (∃ n : ℕ, IsDihedralTwoGroup ↥P₀ n) →
        normalizer (P₀ : Set (MulAut K)) ⊓ (N.T : Subgroup (MulAut K)) = N.P ⊔ N.R ∧
        ∀ f ∈ N.R, orderOf f = 2 →
          normalizer (P₀ : Set (MulAut K)) ⊓ (N.T : Subgroup (MulAut K)) =
            centralizer ({f} : Set (MulAut K)) ⊓ (N.T : Subgroup (MulAut K))

@[expose] def IVK_1_3abc : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ D : Subgroup (SL2 F), IsCyclic ↥D →
    Nat.card ↥D = Nat.card F - 1 →
      ∃ w : SL2 F, normalizer (D : Set (SL2 F)) = D ⊔ zpowers w ∧ w ∉ D ∧
        w ^ 2 ∈ center (SL2 F) ∧ w ^ 2 ≠ 1 ∧ ∀ x ∈ D, w * x * w⁻¹ = x⁻¹

@[expose] def IVK_1_4a : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (σ : F ≃+* F),
    HasSL2Model ↥(slFixed σ) (fun q₀ => q₀ ^ orderOf σ = Nat.card F) ∧
    (Odd (orderOf σ) →
      IsL2 ↥(fixedSubgroup K (fieldAutHom e σ)) (fun q₀ => q₀ ^ orderOf σ = Nat.card F) ∧
      ∀ N : L2Notation e, (N.T : Subgroup (MulAut K)) ≤
        centralizer ({fieldAutHom e σ} : Set (MulAut K))) ∧
    (Even (orderOf σ) →
      IsPGL2 ↥(fixedSubgroup K (fieldAutHom e σ)) (fun q₀ => q₀ ^ orderOf σ = Nat.card F))

@[expose] def IVK_1_4d : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (σ : F ≃+* F) (r : ℕ), r.Prime → Odd r → orderOf σ = r →
      ∀ R : Sylow r K, (∀ x ∈ (R : Subgroup K), fieldAutHom e σ x ∈ (R : Subgroup K)) →
        ∃ x ∈ (R : Subgroup K), fieldAutHom e σ x ≠ x

@[expose] def IVK_1_4e : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (σ : F ≃+* F), ∀ X : Subgroup K, X ≠ ⊥ → Odd (Nat.card ↥X) →
      ∃ c ∈ fixedSubgroup K (fieldAutHom e σ), ∃ x ∈ X, c * x * c⁻¹ ∉ X

@[expose] def IVK_1_4f : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (p n : ℕ), p.Prime → Nat.card F = p ^ n → ∀ W : Sylow p K,
      (∀ τ : F ≃+* F, ∀ x ∈ (W : Subgroup K), fieldAutHom e τ x ∈ (W : Subgroup K)) →
        ∀ σ : F ≃+* F, orderOf σ = p →
          (∃ x ∈ (W : Subgroup K), fieldAutHom e σ x ≠ x) ∧
          pRank p ↥(centralizer ({fieldAutHom e σ} : Set (MulAut K))) = 1 + n / p ∧ 1 + n / p < n

@[expose] def IVK_1_4g : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (p n : ℕ), p.Prime → Nat.card F = p ^ n → ∀ W : Sylow p K, ∀ W₀ : Subgroup K,
      W₀ ≤ (W : Subgroup K) → W₀ ≠ ⊥ →
        centralizer ((W₀.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) : Set (MulAut K)) ⊓
          innDiagSub e = (W : Subgroup K).map (MulAut.conj : K →* MulAut K) ∧
        ∃ D₀ : Subgroup K, IsCyclic ↥D₀ ∧ Nat.card ↥D₀ = (Nat.card F - 1) / 2 ∧
          IsFrobeniusSplit (W : Subgroup K) D₀ (normalizer ((W : Subgroup K) : Set K))

@[expose] def IVK_1_4h : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F)
    (I : Subgroup K), IsL2 ↥I (fun q₀ => Odd q₀ ∧ 3 ≤ q₀) →
      (∃ e' : K ≃* L2 F, IsCyclic ↥(centralizer ((I.map (MulAut.conj : K →* MulAut K) :
          Subgroup (MulAut K)) : Set (MulAut K))) ∧
        centralizer ((I.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) : Set (MulAut K)) ≤
          fieldAutSub e') ∧
      ∀ (e' : K ≃* L2 F), ∀ σ ∈ fieldAutSub e', orderOf σ = 2 →
        I = (oResidual 2 ↥(fixedSubgroup K σ)).map (fixedSubgroup K σ).subtype →
          centralizer ((I.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) :
            Set (MulAut K)) = zpowers σ

@[expose] def IVK_1_4j : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e), ∃ E : Subgroup (MulAut K), IsCyclic ↥E ∧ E ≤ fieldAutSub e ∧
      (∃ m : ℕ, Odd m ∧ (Nat.card ↥E = m ∨ Nat.card ↥E = 2 * m)) ∧
      centralizer (N.P : Set (MulAut K)) = (center ↥N.P).map N.P.subtype ⊔ E ∧
      (center ↥N.P).map N.P.subtype ⊓ E = ⊥ ∧ oPrimeResidual 2 (MulAut K) ⊔ E = ⊤

@[expose] def IVK_1_5a : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e), ∀ z ∈ N.P, orderOf z = 2 →
      (∀ x ∈ (N.T : Subgroup (MulAut K)), x * z = z * x) →
        Subgroup.closure ((xu N.t : Set K) ∪ (xu (N.t * z) : Set K)) = ⊤

@[expose] def IVK_1_5b : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F)
    (N : L2Notation e), ∀ z ∈ N.P, orderOf z = 2 →
      (∀ x ∈ (N.T : Subgroup (MulAut K)), x * z = z * x) →
        ∀ X : Subgroup K, X ≠ ⊥ → Odd (Nat.card ↥X) → (∀ p ∈ N.P, ∀ x ∈ X, p x ∈ X) →
          ∀ x ∈ X, z x = x

@[expose] def IVK_1_5c : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F)
    (p n : ℕ), p.Prime → Nat.card F = p ^ n → ∀ W : Sylow p K, ∀ x : K,
      x ∉ normalizer ((W : Subgroup K) : Set K) →
        Subgroup.closure (((W : Subgroup K) : Set K) ∪ {x}) = ⊤

@[expose] def IVK_1_5d : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F)
    (p n : ℕ), p.Prime → Nat.card F = p ^ n → ∀ W : Sylow p K, ∀ M : Subgroup K,
      (W : Subgroup K) ≤ M → Odd (Nat.card ↥M) → M ≤ normalizer ((W : Subgroup K) : Set K)

@[expose] def IVK_1_5e : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F)
    (p n : ℕ), p.Prime → Nat.card F = p ^ n → ∀ W : Sylow p K, ∀ D : Subgroup (MulAut K),
      D ≤ autNormalizer ⊤ (W : Subgroup K) → IsCyclic ↥D → Nat.card ↥D = Nat.card F - 1 →
        Nonempty (↥(innAut K ⊔ D) ≃* PGL2 F)

@[expose] def IVK_1_7a : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F)
    (p n : ℕ), p.Prime → Nat.card F = p ^ n → ∀ X M : Subgroup K, X ≠ ⊥ → Odd (Nat.card ↥X) →
      Nat.Coprime p (Nat.card ↥X) → X ≤ M → X ≤ centralizer (X : Set K) →
      centralizer (X : Set K) ⊓ M = normalizer (X : Set K) ⊓ M →
        ∀ Y : Subgroup K, Y ≤ centralizer (X : Set K) ⊓ M → Y ≠ ⊥ →
          normalizer (Y : Set K) ⊓ M = normalizer (X : Set K) ⊓ M

@[expose] def IVK_1_7b : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F)
    (p n : ℕ), p.Prime → Nat.card F = p ^ n → ∀ X M : Subgroup K, X ≠ ⊥ → Odd (Nat.card ↥X) →
      Nat.Coprime p (Nat.card ↥X) → X ≤ M → X ≤ centralizer (X : Set K) →
      centralizer (X : Set K) ⊓ M = normalizer (X : Set K) ⊓ M →
        ∃ I : Subgroup K, I ≤ M ∧ (I.subgroupOf M).Normal ∧
          I ⊓ (centralizer (X : Set K) ⊓ M) = ⊥ ∧ I ⊔ (centralizer (X : Set K) ⊓ M) = M ∧
          (Nat.card ↥I ∣ Nat.card F ∨ (Nat.card ↥I = 4 ∧ Nat.card ↥(centralizer (X : Set K)) = 3))

@[expose] def IVK_1_7c : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F)
    (p n : ℕ), p.Prime → Nat.card F = p ^ n → ∀ X : Subgroup K, X ≠ ⊥ → Odd (Nat.card ↥X) →
      Nat.Coprime p (Nat.card ↥X) → Nat.card ↥X ∣ Nat.card F - 1 →
        ∃ W₁ W₂ : Sylow p K, W₁ ≠ W₂ ∧
          (∀ W : Sylow p K, X ≤ normalizer ((W : Subgroup K) : Set K) ↔ W = W₁ ∨ W = W₂) ∧
          centralizer (X : Set K) ≤ normalizer ((W₁ : Subgroup K) : Set K) ∧
          centralizer (X : Set K) ≤ normalizer ((W₂ : Subgroup K) : Set K)

@[expose] def IVK_1_8 : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F),
    (∀ L : Subgroup K, ¬ Group.IsSolvable ↥L →
      (∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), ringChar F₀ = ringChar F ∧
        Nat.card F₀ ≤ Nat.card F ∧ (Nonempty (↥L ≃* L2 F₀) ∨ Nonempty (↥L ≃* PGL2 F₀))) ∨
      IsL2 ↥L (fun q₀ => q₀ = 5)) ∧
    (∀ n : ℕ, Nat.card F = 3 ^ n → Odd n → ∀ L : Subgroup K, ¬ Group.IsSolvable ↥L →
      ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), ringChar F₀ = 3 ∧
        Nonempty (↥(⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆) ≃* L2 F₀)) ∧
    ∀ y : K, y ≠ 1 → Odd (orderOf y) → ∃ g : K,
      ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), ringChar F₀ = ringChar F ∧
        Nat.card F₀ ≤ Nat.card F ∧
        Nonempty (↥(Subgroup.closure ({y, g * y * g⁻¹} : Set K)) ≃* L2 F₀)

@[expose] def IVK_1_9 : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (H : Type) [Group H] [Finite H]
    (Khat : Subgroup H) [Khat.Normal], centralizer (Khat : Set H) ≤ Khat →
      Nonempty (↥Khat ≃* SL2 F) →
      IsCyclic (H ⧸ Khat) ∧
      (Nonempty (↥(oPrimeResidual 2 (H ⧸ center H)) ≃* PGL2 F) ∨
        ∃ Fb : Subgroup (H ⧸ center H),
          Khat.map (QuotientGroup.mk' (center H)) ⊔ Fb = ⊤ ∧
          ∀ x ∈ Fb, orderOf x = 2 →
            IsFAutL2 (MulAut.conjNormal x : MulAut ↥(Khat.map (QuotientGroup.mk' (center H))))) ∧
      (Nonempty (↥(oPrimeResidual 2 (H ⧸ center H)) ≃* PGL2 F) →
        ∀ T : Sylow 2 H, (∃ n : ℕ, IsSemidihedralTwoGroup ↥T n) ∨ (∃ n : ℕ, IsQuaternionTwoGroup ↥T n))

@[expose] def IVK_1_9_a : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (H : Type) [Group H] [Finite H]
    (Khat : Subgroup H) [Khat.Normal], centralizer (Khat : Set H) ≤ Khat →
      Nonempty (↥Khat ≃* SL2 F) → IsCyclic (H ⧸ Khat)

@[expose] def IVK_1_9_b : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (H : Type) [Group H] [Finite H]
    (Khat : Subgroup H) [Khat.Normal], centralizer (Khat : Set H) ≤ Khat →
      Nonempty (↥Khat ≃* SL2 F) →
      (Nonempty (↥(oPrimeResidual 2 (H ⧸ center H)) ≃* PGL2 F) ∨
        ∃ Fb : Subgroup (H ⧸ center H),
          Khat.map (QuotientGroup.mk' (center H)) ⊔ Fb = ⊤ ∧
          ∀ x ∈ Fb, orderOf x = 2 →
            IsFAutL2 (MulAut.conjNormal x : MulAut ↥(Khat.map (QuotientGroup.mk' (center H)))))

@[expose] def IVK_1_9_c : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (H : Type) [Group H] [Finite H]
    (Khat : Subgroup H) [Khat.Normal], centralizer (Khat : Set H) ≤ Khat →
      Nonempty (↥Khat ≃* SL2 F) →
      (Nonempty (↥(oPrimeResidual 2 (H ⧸ center H)) ≃* PGL2 F) →
        ∀ T : Sylow 2 H, (∃ n : ℕ, IsSemidihedralTwoGroup ↥T n) ∨ (∃ n : ℕ, IsQuaternionTwoGroup ↥T n))

theorem IVK_1_9_of_parts (ha : IVK_1_9_a) (hb : IVK_1_9_b) (hc : IVK_1_9_c) : IVK_1_9 := by
  intro F _ _ hF H _ _ Khat _ hC hK
  exact ⟨ha F hF H Khat hC hK, hb F hF H Khat hC hK, hc F hF H Khat hC hK⟩

@[expose] def IVK_1_2_general : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (H : Type) [Group H] [Finite H]
    (K : Subgroup H) [K.Normal], Nonempty (↥K ≃* L2 F) → ∀ T : Sylow 2 H,
      ∃ (e' : ↥K ≃* L2 F) (N : L2Notation e'),
        (T : Subgroup H).map (MulAut.conjNormal : H →* MulAut ↥K) ≤ (N.T : Subgroup (MulAut ↥K)) ∧
        ((T : Subgroup H) ⊓ K).map (MulAut.conjNormal : H →* MulAut ↥K) = N.P

end CFSG.GH74.GLS.IVK
