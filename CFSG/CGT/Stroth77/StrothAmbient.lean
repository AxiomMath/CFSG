module

public import CFSG.CGT.Stroth77.AmbientSplit
public import CFSG.CGT.Stroth77.WeakType
public import CFSG.GroupTheory.HuppertProduct.Mho

public section

namespace CFSG.CGT.Stroth77

variable {G : Type*} [Group G] [Finite G]

abbrev omegaIn (i : ℕ) (D : Subgroup G) : Subgroup G :=
  (CFSG.omega ↥D (p := 2) i).map D.subtype

theorem omegaIn_le (i : ℕ) (D : Subgroup G) : omegaIn i D ≤ D := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

abbrev mhoOne (D : Subgroup G) : Subgroup G :=
  CFSG.GroupTheory.HuppertProduct.mho D 2

structure StrothAmbient (G : Type*) [Group G] [Finite G] where
  S : Sylow 2 G
  A : Subgroup G
  hAS : A ≤ (S : Subgroup G)
  dataA : StrothWeakTypeData A (StrothTypeIndex.t100 1)
  hS_uv : dataA.uv ∈ (S : Subgroup G)
  hS_t : dataA.t ∈ (S : Subgroup G)
  hS_u : dataA.u ∈ (S : Subgroup G)
  hH : NoInvolutionsCentralizing (S : Subgroup G) A

namespace StrothAmbient

variable (X : StrothAmbient G)

@[expose] def L : Subgroup G := X.dataA.L

theorem L_le_normalizer_A : X.L ≤ Subgroup.normalizer (X.A : Set G) :=
  X.dataA.L_le_normalizer

theorem card_A : Nat.card X.A = 32 := by
  have h := X.dataA.card
  rw [show (StrothTypeIndex.t100 1).k 0 = 1 from rfl,
    show (StrothTypeIndex.t100 1).k 1 = 2 from rfl,
    show (StrothTypeIndex.t100 1).k 2 = 2 from rfl] at h
  norm_num at h
  exact h

end StrothAmbient

structure StrothDatum (X : StrothAmbient G) where
  D : Subgroup G
  hAD : X.A ≤ D
  hDS : D ≤ (X.S : Subgroup G)
  τ : StrothTypeIndex
  dataD : StrothWeakTypeData D τ
  hL : dataD.L = X.L
  hcent : (X.S : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) = D

namespace StrothDatum

variable {X : StrothAmbient G} (Z : StrothDatum X)

@[expose] def centralizerIn : Subgroup G :=
  (X.S : Subgroup G) ⊓ Subgroup.centralizer (Z.D : Set G)

@[expose] def normalizerIn : Subgroup G :=
  (X.S : Subgroup G) ⊓ Subgroup.normalizer (Z.D : Set G)

@[expose] def centralizerInMho : Subgroup G :=
  Z.normalizerIn ⊓ Subgroup.centralizer ((mhoOne Z.D : Subgroup G) : Set G)

@[expose] def centralizerInOmegaOne : Subgroup G :=
  Z.normalizerIn ⊓ Subgroup.centralizer ((omegaIn 1 Z.D : Subgroup G) : Set G)

theorem centralizerIn_eq : Z.centralizerIn = Z.D := Z.hcent

theorem D_le_normalizerIn : Z.D ≤ Z.normalizerIn := by
  intro x hx
  rw [normalizerIn]
  exact ⟨Z.hDS hx, Subgroup.le_normalizer hx⟩

theorem L_le_normalizer : X.L ≤ Subgroup.normalizer (Z.D : Set G) := by
  rw [← Z.hL]
  exact Z.dataD.L_le_normalizer

theorem mem_of_mem_centralizer {x : G} (hxS : x ∈ (X.S : Subgroup G))
    (hx : x ∈ Subgroup.centralizer (Z.D : Set G)) : x ∈ Z.D := by
  have hx' : x ∈ Z.centralizerIn := by
    rw [centralizerIn]
    exact ⟨hxS, hx⟩
  rwa [Z.centralizerIn_eq] at hx'

theorem D_le_centralizerInMho : Z.D ≤ Z.centralizerInMho := by
  haveI : IsMulCommutative Z.D := Z.dataD.isMulCommutative
  intro x hx
  rw [centralizerInMho]
  exact ⟨Z.D_le_normalizerIn hx,
    Subgroup.centralizer_le (show ((mhoOne Z.D : Subgroup G) : Set G) ⊆ (Z.D : Set G) from
      CFSG.GroupTheory.HuppertProduct.mho_le Z.D 2) (Subgroup.le_centralizer Z.D hx)⟩

end StrothDatum

structure StrothSection2Input (X : StrothAmbient G) : Prop where
  induction_step :
    ∀ (B : Subgroup G) (τ : StrothTypeIndex) (Bdata : StrothWeakTypeData B τ),
      X.A ≤ B → B ≤ (X.S : Subgroup G) → Bdata.L = X.L →
      B < (X.S : Subgroup G) ⊓ Subgroup.centralizer (B : Set G) →
      ∃ (C : Subgroup G) (τ' : StrothTypeIndex) (Cdata : StrothWeakTypeData C τ'),
        B < C ∧ C ≤ (X.S : Subgroup G) ⊓ Subgroup.centralizer (B : Set G) ∧
          Cdata.L = X.L
  item224 :
    ∀ (Z : StrothDatum X),
      Z.τ.m + 1 = Z.τ.n →
      Nonempty (Additive ↥(omegaIn 2 Z.D) ≃+ Torus ![2, 2, 2]) →
      (∀ z : G, z ∈ Z.centralizerInMho → z * z = 1 → z ∈ omegaIn 1 Z.D) ∧
      (∀ (j : ℕ) (B : Subgroup G), j ≤ Z.τ.n - 1 → B ≤ Z.centralizerInMho →
        Nonempty (Additive ↥B ≃+
          (ZMod (2 ^ j) × ZMod (2 ^ (j + 1)) × ZMod (2 ^ (j + 1)))) →
        B ≤ Z.D) ∧
      ((Z.centralizerInMho ⊓
          Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G)) ≠ Z.D →
        ∃ s : G,
          s ∈ Z.centralizerInMho ⊓
              Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G) ∧
          s ∉ Z.D ∧ s * s = (Z.dataD.c : G) ∧
          (Z.centralizerInMho ⊓
              Subgroup.centralizer ((omegaIn (Z.τ.n - 1) Z.D : Subgroup G) : Set G)) =
            (Z.D ⊔ Subgroup.zpowers s) ∧
          ⁅Subgroup.zpowers s, Z.D⁆ =
            ⁅Subgroup.zpowers (Z.dataD.ρ : G), omegaIn 1 Z.D⁆)
  item225 :
    ∀ (Z : StrothDatum X),
      Z.τ.m + 2 = Z.τ.n →
      Nonempty (Additive ↥(omegaIn 2 Z.D) ≃+ Torus ![2, 2, 2]) →
      (∀ x : G, x ∈ Z.centralizerInMho → x * x ∈ Z.D) ∧
      (∀ x : G, x ∈ Z.centralizerInMho → ∀ y : G, y ∈ Z.centralizerInMho →
        x * y * x⁻¹ * y⁻¹ ∈ Z.D) ∧
      Nat.card Z.centralizerInMho ≤ 8 * Nat.card Z.D ∧
      (∀ (j : ℕ) (B : Subgroup G), j ≤ Z.τ.n - 2 → B ≤ Z.centralizerInMho →
        Nonempty (Additive ↥B ≃+
          (ZMod (2 ^ j) × ZMod (2 ^ (j + 2)) × ZMod (2 ^ (j - 2)))) →
        B ≤ Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) ∧
      ((Z.centralizerInMho ⊓
          Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) ≠ Z.D →
        ∃ s : G,
          s ∈ Z.centralizerInMho ⊓
              Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G) ∧
          s ∉ Z.D ∧ s * s = (Z.dataD.c : G) ∧
          (Z.centralizerInMho ⊓
              Subgroup.centralizer ((omegaIn (Z.τ.n - 2) Z.D : Subgroup G) : Set G)) =
            (Z.D ⊔ Subgroup.zpowers s) ∧
          ⁅Subgroup.zpowers s, Z.D⁆ =
            ⁅Subgroup.zpowers (Z.dataD.ρ : G), omegaIn 1 Z.D⁆)
  item226 :
    ∀ (Z : StrothDatum X) (B : Subgroup G),
      B ≤ Z.centralizerInOmegaOne →
      (∀ h : G, h ∈ Z.centralizerInOmegaOne → ∀ b : G, b ∈ B → h * b * h⁻¹ ∈ B) →
      B ≠ Z.D →
      (∃ g : G, B = Z.D.map (MulAut.conj g).toMonoidHom) →
      Z.τ.m = Z.τ.n
  item227 :
    ∀ (Z : StrothDatum X),
      (∀ x : G, x ∈ omegaIn 1 Z.D → orderOf x = 2 →
        ∀ y : G, y ∈ omegaIn 1 Z.D → orderOf y = 2 →
        ∃ g : G, y = g * x * g⁻¹) →
      Z.τ.m = Z.τ.n
  item228 :
    ∀ (Z : StrothDatum X),
      (∃ x : G, x ∈ omegaIn 1 Z.D ∧ orderOf x = 2 ∧
        ∃ y : G, y ∈ omegaIn 1 Z.D ∧ orderOf y = 2 ∧
          ∀ g : G, y ≠ g * x * g⁻¹) →
      (∃ m : ℕ, HasStrothWeakType Z.D (StrothTypeIndex.t200 m)) ∨
      (∃ m : ℕ, HasStrothWeakType Z.D (StrothTypeIndex.t201 m)) ∨
      (∃ m : ℕ, HasStrothWeakType Z.D (StrothTypeIndex.t100 m)) ∨
      (∃ s : ℕ, HasStrothWeakType Z.D (StrothTypeIndex.t101 s)) ∨
      (∃ n : ℕ, HasStrothWeakType Z.D (StrothTypeIndex.t300 n))

end CFSG.CGT.Stroth77
