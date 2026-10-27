module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25X03
public import CFSG.ClassicalInvolution.Asc77.AscC5O1C

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups
namespace C5O
open CFSG.ClassicalInvolution.Asc77.C5O
section Statements

structure Om5Data (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y)
    (z' a₀ b₀ : Y) : Prop where
  lie : ∃ D : LieSystemData 3 1 Y Φ, D.card = 1 ∧
    ∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i)
  twin : TwinSect0 Φ A A' z' a₀ b₀
  conj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ

@[expose] def HasBigFix {Y : Type} [Group Y] (β : Y ≃* Y) : Prop :=
  ∃ L : Subgroup Y, (∀ x ∈ L, β x = x) ∧ IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧
    Nat.card (SL(2, GaloisField 3 1)) ^ 2 < 4 * Nat.card L

@[expose] def Om5Centerless : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data Y Φ A A' z' a₀ b₀ → ∀ y : Y, (∀ x : Y, y * x = x * y) → y = 1

@[expose] def Om5InvFixFour : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data Y Φ A A' z' a₀ b₀ → ∀ y : Y, y * y = 1 → y ≠ 1 →
      ∃ J ∈ Φ, ∃ x ∈ J, x * x * x * x = 1 ∧ x * x ≠ 1 ∧ y * x = x * y

@[expose] def Om5Interchange : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data Y Φ A A' z' a₀ b₀ → ∀ (β : Y ≃* Y) (t' : Y), t' = β z' → t' ≠ z' →
      t' * z' = z' * t' →
        (∃ x : Y, x * z' * x⁻¹ = t' ∧ x * t' * x⁻¹ = z') ∧
          ∃ x : Y, x * (z' * t') * x⁻¹ = a₀ * b₀

@[expose] def Om5ZSwap : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data Y Φ A A' z' a₀ b₀ →
      ∃ s : Y, s * s = 1 ∧ conjSub s A = A' ∧ ∃ x : Y, x * z' * x⁻¹ = s

@[expose] def Om5USwapNotZ : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data Y Φ A A' z' a₀ b₀ → ∀ s : Y, conjSub s A = A' → (∃ x : Y, x * z' * x⁻¹ = s) →
      ∀ β : Y ≃* Y, β z' ≠ s * z'

@[expose] def Om5ExcClass : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om5Data Y Φ A A' z' a₀ b₀ → ∀ β₁ β₂ : Y ≃* Y,
      (∀ x : Y, β₁ (β₁ x) = x) → (∀ x : Y, β₂ (β₂ x) = x) →
      (∀ J ∈ Φ, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 → β₁ x ≠ x) →
      (∀ J ∈ Φ, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 → β₂ x ≠ x) →
      ¬ HasBigFix β₁ → ¬ HasBigFix β₂ →
        ∃ g : Y, ∀ x : Y, β₂ x = g * β₁ (g⁻¹ * x * g) * g⁻¹

structure ModelFacts : Prop where
  invFixFour : Om5InvFixFour
  interchange : Om5Interchange
  zSwap : Om5ZSwap
  uSwapNotZ : Om5USwapNotZ
  excClass : Om5ExcClass
  centerless : Om5Centerless
end Statements
end C5O
end Asc77

end

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
section Config
variable {G : Type} [Group G] [Finite G]

structure Ctx (Ω : Set (Subgroup G)) (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G)
    (z t u₁ u₂ a : G) : Prop where
  hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂
  haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
  ha2 : a * a = 1
  ha1 : a ≠ 1
  haz : a ≠ z
  hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z
  hA0 : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
    b = 1 ∨ b = a ∨ b = z ∨ b = a * z
  hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G))
  hbad' : z ∉ zStarOf (Subgroup.centralizer ({a * z} : Set G))
  h5 : LayerOrthType Ω a 5 true
  h5' : LayerOrthType Ω (a * z) 5 true
end Config
section Basic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.C5O.Ctx

theorem hz2 (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) : z * z = 1 := C.hyp.std.setting.hz.sq

theorem hz1 (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) : z ≠ 1 := C.hyp.std.setting.hz.ne_one

theorem comm (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) : a * z = z * a := C.hyp.hzS a C.haA.1

theorem mul_z_mul_z (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) : a * z * z = a := by
  rw [mul_assoc, C.hz2, mul_one]

theorem haR (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) : ∀ x ∈ R, a * x = x * a := fun x hx =>
  ((Subgroup.mem_centralizer_iff.mp C.haA.2) x (Subgroup.mem_sup_left hx)).symm

theorem haR' (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) : ∀ x ∈ R', a * x = x * a := fun x hx =>
  ((Subgroup.mem_centralizer_iff.mp C.haA.2) x (Subgroup.mem_sup_right hx)).symm

theorem swap [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    Ctx Ω K K' W S R R' z t u₁ u₂ (a * z) := by
  have hzA := T7T.z_mem_centralizer_of_hyp C.hyp
  have hz2 := C.hz2
  have haz' := C.comm
  have hazz' := C.mul_z_mul_z
  refine ⟨C.hyp, Subgroup.mul_mem _ C.haA hzA, ?_, ?_, ?_, ?_, ?_, C.hbad', ?_, C.h5', ?_⟩
  · calc a * z * (a * z) = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [haz']
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [C.ha2, hz2, one_mul]
  · intro h
    apply C.haz
    have : a = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right hz2]
  · intro h
    apply C.ha1
    calc a = (a * z) * z⁻¹ := by group
      _ = z * z⁻¹ := by rw [h]
      _ = 1 := by group
  · intro s hs
    have hszs : s * z * s⁻¹ = z := by
      calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [C.hyp.hzS s hs]
        _ = z := by group
    have hsa : s * (a * z) * s⁻¹ = (s * a * s⁻¹) * z := by
      calc s * (a * z) * s⁻¹ = (s * a * s⁻¹) * (s * z * s⁻¹) := by group
        _ = (s * a * s⁻¹) * z := by rw [hszs]
    rcases C.hconj s hs with h | h
    · left; rw [hsa, h]
    · right; rw [hsa, h, hazz']
  · intro b hb
    rcases C.hA0 b hb with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (by rw [hazz', h])))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  · rw [hazz']; exact C.hbad
  · rw [hazz']; exact C.h5

theorem om5 [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    ∃ (hzY : z ∈ ExactLayer.exactLayer Ω a) (hu₁Y : u₁ ∈ ExactLayer.exactLayer Ω a) (hu₂Y : u₂ ∈
        ExactLayer.exactLayer Ω a),
      K ∈ ExactLayer.tqMembers Ω a ∧ K' ∈ ExactLayer.tqMembers Ω a ∧
      Om5Data (↥(ExactLayer.exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω
          a))
        (oddQuotientFamily (ExactLayer.exactPair Ω a)) (T7H.exactImg Ω a K) (T7H.exactImg Ω a K')
        (T7H.toBar Ω a z hzY) (T7H.toBar Ω a u₁ hu₁Y) (T7H.toBar Ω a u₂ hu₂Y) := by
  classical
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', -, -, htw⟩ :=
    C25X.layer_a_frame C.hyp C.ha2 C.ha1 C.haR C.haR'
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := C.h5
  refine ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', ⟨D, hD1, i₀, ?_⟩, htw, ?_⟩
  · rw [hDt, hDn]; exact hT
  · intro J hJ yb
    obtain ⟨M, hMtq, rfl⟩ := T7H.exists_exactImg_of_mem hJ
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective yb
    rw [← C25Y.exactImg_conjSub_layer x]
    exact T7H.exactImg_mem (ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant
      (ExactLayer.exactLayer_le_centralizer Ω a x.2) hMtq)
end Ctx
end Basic
end Asc77.C5O

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
namespace C5O
open CFSG.ClassicalInvolution.Asc77.C5O
section Statements

structure TwinShare {Y₁ Y₂ : Type} [Group Y₁] [Finite Y₁] [Group Y₂] [Finite Y₂]
    (Φ₁ : Set (Subgroup Y₁)) (A₁ A₁' : Subgroup Y₁) (z₁ a₁ b₁ : Y₁)
    (Φ₂ : Set (Subgroup Y₂)) (A₂ A₂' : Subgroup Y₂) (z₂ a₂ b₂ : Y₂)
    {M : Type} [Group M] [Finite M] (π₁ : M →* Y₁) (π₂ : M →* Y₂) (L L' : Subgroup M) :
    Prop where
  data₁ : Om5Data Y₁ Φ₁ A₁ A₁' z₁ a₁ b₁
  data₂ : Om5Data Y₂ Φ₂ A₂ A₂' z₂ a₂ b₂
  range₁ : π₁.range = A₁ ⊔ A₁'
  range₂ : π₂.range = A₂ ⊔ A₂'
  odd₁ : Odd (Nat.card π₁.ker)
  odd₂ : Odd (Nat.card π₂.ker)
  map₁ : L.map π₁ = A₁ ∧ L'.map π₁ = A₁'
  map₂ : L.map π₂ = A₂ ∧ L'.map π₂ = A₂'
  swap : ∃ (τ : M → M) (τ₁ : Y₁ ≃* Y₁) (τ₂ : Y₂ ≃* Y₂),
    (∀ m ∈ L, τ m ∈ L') ∧ (∀ m ∈ L', τ m ∈ L) ∧
    (∀ m, π₁ (τ m) = τ₁ (π₁ m)) ∧ (∀ m, π₂ (τ m) = τ₂ (π₂ m)) ∧
    (∃ y : Y₂, ∀ x : Y₂, τ₂ x = y * x * y⁻¹) ∧ (∀ x : Y₁, τ₁ (τ₁ x) = x) ∧
    (∀ J ∈ Φ₁, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 → τ₁ x ≠ x) ∧ ¬ HasBigFix τ₁

@[expose] def Om5TwinComm : Prop :=
  ∀ (Y₁ Y₂ : Type) [Group Y₁] [Finite Y₁] [Group Y₂] [Finite Y₂]
    (Φ₁ : Set (Subgroup Y₁)) (A₁ A₁' : Subgroup Y₁) (z₁ a₁ b₁ : Y₁)
    (Φ₂ : Set (Subgroup Y₂)) (A₂ A₂' : Subgroup Y₂) (z₂ a₂ b₂ : Y₂)
    (M : Type) [Group M] [Finite M] (π₁ : M →* Y₁) (π₂ : M →* Y₂) (L L' : Subgroup M),
    TwinShare Φ₁ A₁ A₁' z₁ a₁ b₁ Φ₂ A₂ A₂' z₂ a₂ b₂ π₁ π₂ L L' →
    ∀ (γ₁ δ₁ : Y₁ ≃* Y₁) (γ₂ δ₂ : Y₂ ≃* Y₂),
      A₁.map γ₁.toMonoidHom = A₁ → A₁'.map γ₁.toMonoidHom = A₁' →
      A₂.map γ₂.toMonoidHom = A₂ → A₂'.map γ₂.toMonoidHom = A₂' →
      A₁.map δ₁.toMonoidHom = A₁ → A₁'.map δ₁.toMonoidHom = A₁' →
      A₂.map δ₂.toMonoidHom = A₂ → A₂'.map δ₂.toMonoidHom = A₂' →
      (∀ m : M, ∃ m' : M, π₁ m' = γ₁ (π₁ m) ∧ π₂ m' = γ₂ (π₂ m)) →
      (∀ m : M, ∃ m' : M, π₁ m' = δ₁ (π₁ m) ∧ π₂ m' = δ₂ (π₂ m)) →
        ∃ w : M, (∀ y : Y₁, γ₁ (δ₁ (γ₁.symm (δ₁.symm y))) = π₁ w * y * (π₁ w)⁻¹) ∧
          ∀ y : Y₂, γ₂ (δ₂ (γ₂.symm (δ₂.symm y))) = π₂ w * y * (π₂ w)⁻¹

@[expose] def Om5TwinCommSwap : Prop :=
  ∀ (Y₁ Y₂ : Type) [Group Y₁] [Finite Y₁] [Group Y₂] [Finite Y₂]
    (Φ₁ : Set (Subgroup Y₁)) (A₁ A₁' : Subgroup Y₁) (z₁ a₁ b₁ : Y₁)
    (Φ₂ : Set (Subgroup Y₂)) (A₂ A₂' : Subgroup Y₂) (z₂ a₂ b₂ : Y₂)
    (M : Type) [Group M] [Finite M] (π₁ : M →* Y₁) (π₂ : M →* Y₂) (L L' : Subgroup M),
    TwinShare Φ₁ A₁ A₁' z₁ a₁ b₁ Φ₂ A₂ A₂' z₂ a₂ b₂ π₁ π₂ L L' →
    ∀ (ψ : Y₁ ≃* Y₂) (ψ' : Y₂ ≃* Y₁) (δ₁ : Y₁ ≃* Y₁) (δ₂ : Y₂ ≃* Y₂),
      A₁.map ψ.toMonoidHom = A₂ → A₁'.map ψ.toMonoidHom = A₂' →
      A₂.map ψ'.toMonoidHom = A₁ → A₂'.map ψ'.toMonoidHom = A₁' →
      A₁.map δ₁.toMonoidHom = A₁ → A₁'.map δ₁.toMonoidHom = A₁' →
      A₂.map δ₂.toMonoidHom = A₂ → A₂'.map δ₂.toMonoidHom = A₂' →
      (∀ m : M, ∃ m' : M, π₂ m' = ψ (π₁ m) ∧ π₁ m' = ψ' (π₂ m)) →
      (∀ m : M, ∃ m' : M, π₁ m' = δ₁ (π₁ m) ∧ π₂ m' = δ₂ (π₂ m)) →
        ∃ w : M, (∀ y : Y₁, ψ' (δ₂ (ψ'.symm (δ₁.symm y))) = π₁ w * y * (π₁ w)⁻¹) ∧
          ∀ y : Y₂, ψ (δ₁ (ψ.symm (δ₂.symm y))) = π₂ w * y * (π₂ w)⁻¹

structure M8GFacts : Prop where
  comm : Om5TwinComm
  commSwap : Om5TwinCommSwap
end Statements
end C5O
end Asc77

end

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.C5O.Ctx

theorem not_conj_z (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) (y : G) : y * z * y⁻¹ ≠ a := by
  intro h
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hu₁K : u₁ ∈ K := C.hyp.hR.2.1 C.hyp.hu₁.1
  refine T7ER.not_commute_of_conj hs C.hyp.hW C.hyp.hE4 hs.stand.mem hs.hz
    (by rw [h]; exact C.haz) hu₁K C.hyp.hu₁.2.1 ?_
  rw [h]
  exact C.haR u₁ C.hyp.hu₁.1

theorem R_le [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    R ≤ ExactLayer.exactLayer Ω a := by
  obtain ⟨t', h⟩ := T7T.exists_hyp25T C.hyp
  obtain ⟨-, -, -, hK₂, -, -⟩ := C.om5
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one C.ha2
  have hRc : R ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (C.haR x hx).symm
  have hS₂ : IsSylow2In R (ExactLayer.exactCore a K) :=
    (ExactLayer.isSylow2In_exactCore_iff hs.stand.modU hcpg hs.stand.mem hK₂.2).mpr ⟨h.hRsyl, hRc⟩
  exact hS₂.1.trans (ExactLayer.exactCore_le_exactLayer hK₂)

theorem R'_le [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    R' ≤ ExactLayer.exactLayer Ω a := by
  obtain ⟨t', h⟩ := T7T.exists_hyp25T C.hyp
  obtain ⟨-, -, -, -, hK₂', -⟩ := C.om5
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one C.ha2
  have hRc : R' ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (C.haR' x hx).symm
  have hS₂ : IsSylow2In R' (ExactLayer.exactCore a K') :=
    (ExactLayer.isSylow2In_exactCore_iff hs.stand.modU hcpg hs.hK'.1 hK₂'.2).mpr ⟨h.hR'syl, hRc⟩
  exact hS₂.1.trans (ExactLayer.exactCore_le_exactLayer hK₂')

theorem z_not_triv [IsSimpleGroup G] (hM5 : Om5Centerless)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) : z ∉ trivialOnQuot (ExactLayer.exactLayer Ω a) := by
  intro hz
  obtain ⟨hzY, hu₁Y, hu₂Y, -, -, hD⟩ := C.om5
  have hb : conjSub z (ExactLayer.exactLayer Ω a) = ExactLayer.exactLayer Ω a :=
      conjSub_eq_self_of_mem hzY
  have hfix := (layerAut_eq_id_iff (ExactLayer.exactLayer Ω a) hb).mpr hz
  refine hD.twin.hzA.ne_one (hM5 _ _ _ _ _ _ _ hD _ fun x => ?_)
  induction x using QuotientGroup.induction_on with
  | H y =>
    have h1 := hfix (QuotientGroup.mk y)
    rw [C25Y.layerAut_mk] at h1
    have h2 : (QuotientGroup.mk (C25Y.conjOnSub (ExactLayer.exactLayer Ω a) hb y) :
        ↥(ExactLayer.exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a)) =
        T7H.toBar Ω a z hzY * QuotientGroup.mk y * (T7H.toBar Ω a z hzY)⁻¹ := by
      unfold T7H.toBar
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul]
      rfl
    rw [h2] at h1
    calc T7H.toBar Ω a z hzY * QuotientGroup.mk y
        = (T7H.toBar Ω a z hzY * QuotientGroup.mk y * (T7H.toBar Ω a z hzY)⁻¹) *
            T7H.toBar Ω a z hzY := by group
      _ = QuotientGroup.mk y * T7H.toBar Ω a z hzY := by rw [h1]

theorem a_triv (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    a ∈ trivialOnQuot (ExactLayer.exactLayer Ω a) := by
  have hΩ : HypOmegaModT Ω := C.hyp.std.setting.stand.modU
  refine ⟨mem_normalizer_of_conjSub_eq (ExactLayer.conjSub_exactLayer hΩ.conjInvariant
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl)), fun y hy => ?_⟩
  have hc : y * a = a * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (ExactLayer.exactLayer_le_centralizer Ω a hy)
  rw [(commutatorElement_eq_one_iff_mul_comm).mpr hc.symm]
  exact one_mem _

theorem mem_S_triv [IsSimpleGroup G] (hM5 : Om5Centerless)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {w : G} (hwS : w ∈ (S : Subgroup G))
    (hw : w ∈ trivialOnQuot (ExactLayer.exactLayer Ω a)) : w = 1 ∨ w = a := by
  have hO := odd_card_oddCoreIn (ExactLayer.exactLayer Ω a)
  have key : ∀ r ∈ ExactLayer.exactLayer Ω a, r ∈ (S : Subgroup G) →
      r ∈ Subgroup.centralizer ({w} : Set G) := by
    intro r hrX hrS
    have h1 : ⁅w, r⁆ ∈ oddCoreIn (ExactLayer.exactLayer Ω a) := hw.2 r hrX
    have h2 : ⁅w, r⁆ ∈ (S : Subgroup G) := by
      rw [commutatorElement_def]
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem
        ((S : Subgroup G).mul_mem hwS hrS) ((S : Subgroup G).inv_mem hwS))
        ((S : Subgroup G).inv_mem hrS)
    have h3 := eq_one_of_isPGroup_of_odd S.isPGroup' hO h2 h1
    rw [commutatorElement_eq_one_iff_mul_comm] at h3
    exact Subgroup.mem_centralizer_singleton_iff.mpr h3.symm
  have hle : R ⊔ R' ≤ Subgroup.centralizer ({w} : Set G) :=
    sup_le (fun r hr => key r (C.R_le hr) (C.hyp.hR.2.2 hr))
      (fun r hr => key r (C.R'_le hr) (C.hyp.hR'.2.2 hr))
  have hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
    refine ⟨hwS, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  rcases C.hA0 w hwA with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (h ▸ hw) (C.z_not_triv hM5)
  · exfalso
    apply C.z_not_triv hM5
    have := (trivialOnQuot (ExactLayer.exactLayer Ω a)).mul_mem
      ((trivialOnQuot (ExactLayer.exactLayer Ω a)).inv_mem C.a_triv) (h ▸ hw)
    simpa using this

theorem twoElt_triv [IsSimpleGroup G] (hM5 : Om5Centerless)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {w : G} (hwa : w * a = a * w)
    (hw : w ∈ trivialOnQuot (ExactLayer.exactLayer Ω a)) (h2 : IsPGroup 2 (Subgroup.zpowers w)) :
    w = 1 ∨ w = a := by
  classical
  set X := ExactLayer.exactLayer Ω a with hX
  have hΩ : HypOmegaModT Ω := C.hyp.std.setting.stand.modU
  have hz2 : z * z = 1 := C.hz2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  obtain ⟨hzY, -, -, -, -, -⟩ := C.om5
  have hwT : Subgroup.zpowers w ≤ trivialOnQuot X := Subgroup.zpowers_le.mpr hw
  obtain ⟨n, hn, hfix⟩ := exists_conj_fixed_of_isPGroup (A := Subgroup.zpowers w)
    (N := oddCoreIn X) h2 (odd_card_oddCoreIn X)
    (fun x hx m hm => conj_mem_oddCoreIn_of_mem_normalizer (hwT hx).1 hm) hz2
    (fun m hm => conj_mem_oddCoreIn hzY hm) (by
      intro x hx
      have h1 : ⁅x, z⁆ ∈ oddCoreIn X := (hwT hx).2 z hzY
      have h3 := conj_mem_oddCoreIn hzY h1
      have e : z * ⁅x, z⁆ * z⁻¹ = z * (x * z * x⁻¹) := by
        rw [commutatorElement_def, hzi]
        calc z * (x * z * x⁻¹ * z) * z = z * (x * z * x⁻¹) * (z * z) := by group
          _ = z * (x * z * x⁻¹) := by rw [hz2, mul_one]
      rwa [e] at h3)
  have hnX : n ∈ X := oddCoreIn_le X hn
  have hna : n * a = a * n :=
    Subgroup.mem_centralizer_singleton_iff.mp (ExactLayer.exactLayer_le_centralizer Ω a hnX)
  set w₁ := n⁻¹ * w * n with hw₁
  have hw₁z : w₁ * z * w₁⁻¹ = z := by
    have h := hfix w (Subgroup.mem_zpowers w)
    calc w₁ * z * w₁⁻¹ = n⁻¹ * (w * (n * z * n⁻¹) * w⁻¹) * n := by rw [hw₁]; group
      _ = z := by rw [h]; group
  have hw₁a : w₁ * a * w₁⁻¹ = a := by
    calc w₁ * a * w₁⁻¹ = n⁻¹ * w * (n * a * n⁻¹) * w⁻¹ * n := by rw [hw₁]; group
      _ = n⁻¹ * (w * a * w⁻¹) * n := by
          rw [show n * a * n⁻¹ = a by rw [hna]; group]; group
      _ = n⁻¹ * a * n := by rw [show w * a * w⁻¹ = a by rw [hwa]; group]
      _ = a := by rw [mul_assoc, ← hna]; group
  have hw₁T : w₁ ∈ trivialOnQuot X := by
    have hOT : ∀ m ∈ oddCoreIn X, m ∈ trivialOnQuot X := by
      intro m hm
      have hmX : m ∈ X := oddCoreIn_le X hm
      refine ⟨mem_normalizer_of_conjSub_eq (conjSub_eq_self_of_mem hmX), fun y hy => ?_⟩
      rw [commutatorElement_def]
      have h1 : y * m⁻¹ * y⁻¹ ∈ oddCoreIn X := conj_mem_oddCoreIn hy ((oddCoreIn X).inv_mem hm)
      have := (oddCoreIn X).mul_mem hm h1
      simpa [mul_assoc] using this
    rw [hw₁]
    exact (trivialOnQuot X).mul_mem ((trivialOnQuot X).mul_mem
      ((trivialOnQuot X).inv_mem (hOT n hn)) hw) (hOT n hn)
  have h2₁ : IsPGroup 2 (Subgroup.zpowers w₁) := by
    have e : Subgroup.zpowers w₁ = (Subgroup.zpowers w).map (MulAut.conj n⁻¹).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      congr 1
      simp [hw₁]
    rw [e]
    exact h2.map _
  set A₀ := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA₀
  have hzA₀ : z ∈ A₀ := T7T.z_mem_centralizer_of_hyp C.hyp
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (A₀ : Set G) := fun s hs =>
    mem_normalizer_of_conjSub_eq (T7T.conjSub_centralizer_of_hyp C.hyp hs)
  have hSsyl : IsSylow2In (S : Subgroup G) (Subgroup.normalizer (A₀ : Set G)) :=
    ⟨hSN, S.isPGroup', fun V' _ hV' hle => S.is_maximal' hV' hle⟩
  have hfixA : ∀ h ∈ A₀, w₁ * h * w₁⁻¹ = h := by
    intro h hh
    rcases C.hA0 h hh with rfl | rfl | rfl | rfl
    · group
    · exact hw₁a
    · exact hw₁z
    · calc w₁ * (a * z) * w₁⁻¹ = (w₁ * a * w₁⁻¹) * (w₁ * z * w₁⁻¹) := by group
        _ = a * z := by rw [hw₁a, hw₁z]
  have hw₁N : Subgroup.zpowers w₁ ≤ Subgroup.normalizer (A₀ : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_,
      fun hh => ?_⟩)
    · rw [hfixA h hh]; exact hh
    · have e1 := hfixA _ hh
      have e2 : h = w₁ * h * w₁⁻¹ := by
        calc h = w₁⁻¹ * (w₁ * h * w₁⁻¹) * w₁ := by group
          _ = w₁⁻¹ * (w₁ * (w₁ * h * w₁⁻¹) * w₁⁻¹) * w₁ := by rw [e1]
          _ = w₁ * h * w₁⁻¹ := by group
      rw [e2]; exact hh
  obtain ⟨V, hV, hVle⟩ := IsSylow2In.exists_ge h2₁ hw₁N
  obtain ⟨g, hg, hVeq⟩ := IsSylow2Of.exists_conj (show IsSylow2Of _ _ from hSsyl)
    (show IsSylow2Of _ _ from hV)
  have hw₂S : g⁻¹ * w₁ * g ∈ (S : Subgroup G) := by
    have h := hVle (Subgroup.mem_zpowers w₁)
    rw [hVeq] at h
    exact mem_conjSubgroup_iff.mp h
  have hginv : g⁻¹ ∈ Subgroup.normalizer (A₀ : Set G) := Subgroup.inv_mem _ hg
  have hb : g⁻¹ * a * g⁻¹⁻¹ ∈ A₀ := (Subgroup.mem_normalizer_iff.mp hginv a).mp C.haA
  rw [inv_inv] at hb
  have hbcases : g⁻¹ * a * g = a ∨ g⁻¹ * a * g = a * z := by
    rcases C.hA0 _ hb with h | h | h | h
    · exfalso; apply C.ha1
      calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · exact Or.inl h
    · exfalso; apply C.not_conj_z g
      calc g * z * g⁻¹ = g * (g⁻¹ * a * g) * g⁻¹ := by rw [h]
        _ = a := by group
    · exact Or.inr h
  have hw₂T : g⁻¹ * w₁ * g ∈ trivialOnQuot (ExactLayer.exactLayer Ω (g⁻¹ * a * g)) := by
    have h := trivialOnQuot_conjSub hw₁T g⁻¹
    rw [inv_inv] at h
    have e := ExactLayer.exactLayer_conj hΩ.conjInvariant g⁻¹ a
    rw [inv_inv] at e
    rw [e]
    exact h
  have hw₂ : g⁻¹ * w₁ * g = 1 ∨ g⁻¹ * w₁ * g = g⁻¹ * a * g := by
    rcases hbcases with hb' | hb'
    · rw [hb'] at hw₂T ⊢
      exact C.mem_S_triv hM5 hw₂S hw₂T
    · rw [hb'] at hw₂T ⊢
      exact C.swap.mem_S_triv hM5 hw₂S hw₂T
  have hw₁' : w₁ = 1 ∨ w₁ = a := by
    rcases hw₂ with h | h
    · left
      calc w₁ = g * (g⁻¹ * w₁ * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · right
      calc w₁ = g * (g⁻¹ * w₁ * g) * g⁻¹ := by group
        _ = a := by rw [h]; group
  rcases hw₁' with h | h
  · left
    calc w = n * w₁ * n⁻¹ := by rw [hw₁]; group
      _ = 1 := by rw [h]; group
  · right
    calc w = n * w₁ * n⁻¹ := by rw [hw₁]; group
      _ = n * a * n⁻¹ := by rw [h]
      _ = a := by rw [hna]; group
end Ctx
end Asc77.C5O

end

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.C5O.Ctx

theorem cOne_conj [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {c y : G}
    (hc : c * z * c⁻¹ = z)
    (hy : y ∈ cOne z K K') : c * y * c⁻¹ ∈ cOne z K K' := by
  obtain ⟨⟨hyz, hyK⟩, hyK'⟩ := hy
  obtain ⟨h1, h2⟩ := C25Y.trivialOnQuot_pair_conj C.hyp.std.setting hyK hyK' hc
  refine ⟨⟨?_, h1⟩, h2⟩
  have hyz' : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyz
  have hc' : c⁻¹ * z * c = z := by
    calc c⁻¹ * z * c = c⁻¹ * (c * z * c⁻¹) * c := by rw [hc]
      _ = z := by group
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc c * y * c⁻¹ * z = c * (y * (c⁻¹ * z * c)) * c⁻¹ := by group
    _ = c * (y * z) * c⁻¹ := by rw [hc']
    _ = c * (z * y) * c⁻¹ := by rw [hyz']
    _ = (c * z * c⁻¹) * (c * y * c⁻¹) := by group
    _ = z * (c * y * c⁻¹) := by rw [hc]

theorem z_mem_cOne (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) : z ∈ cOne z K K' := by
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  exact ⟨⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
    mem_trivialOnQuot_of_isUniqueInvolution hs.hz⟩,
    mem_trivialOnQuot_of_isUniqueInvolution (isUniqueInvolution_of_mem_twinSet hs.hz hs.hK')⟩

theorem a_mem_cOne [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    a ∈ cOne z K K' := by
  obtain ⟨-, -, -, hK₂, hK₂', -⟩ := C.om5
  exact ⟨⟨Subgroup.mem_centralizer_singleton_iff.mpr C.comm, hK₂.2⟩, hK₂'.2⟩

theorem mem_A_of_mem_cOne (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hs : s ∈ cOne z K K') :
    s ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
  have key : ∀ J : Subgroup G, s ∈ trivialOnQuot J → ∀ r ∈ J, r ∈ (S : Subgroup G) →
      r ∈ Subgroup.centralizer ({s} : Set G) := by
    intro J hsJ r hrJ hrS
    have h1 : ⁅s, r⁆ ∈ oddCoreIn J := hsJ.2 r hrJ
    have h2 : ⁅s, r⁆ ∈ (S : Subgroup G) := by
      rw [commutatorElement_def]
      exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem
        ((S : Subgroup G).mul_mem hsS hrS) ((S : Subgroup G).inv_mem hsS))
        ((S : Subgroup G).inv_mem hrS)
    have h3 := eq_one_of_isPGroup_of_odd S.isPGroup' (odd_card_oddCoreIn J) h2 h1
    rw [commutatorElement_eq_one_iff_mul_comm] at h3
    exact Subgroup.mem_centralizer_singleton_iff.mpr h3.symm
  have hle : R ⊔ R' ≤ Subgroup.centralizer ({s} : Set G) :=
    sup_le (fun r hr => key K hs.1.2 r (C.hyp.hR.2.1 hr) (C.hyp.hR.2.2 hr))
      (fun r hr => key K' hs.2 r (C.hyp.hR'.2.1 hr) (C.hyp.hR'.2.2 hr))
  exact ⟨hsS, Subgroup.mem_centralizer_iff.mpr fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hh)⟩

theorem A_le_cOne [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ≤ cOne z K K' := by
  intro b hb
  rcases C.hA0 b hb with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact C.a_mem_cOne
  · exact C.z_mem_cOne
  · exact mul_mem C.a_mem_cOne C.z_mem_cOne

theorem isSylow2In_cOne [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
      (cOne z K K') := by
  set A₀ := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA₀
  refine ⟨C.A_le_cOne, S.isPGroup'.to_le inf_le_left, fun V' hV'C hV' hle => ?_⟩
  have hSz : IsSylow2In (S : Subgroup G) (Subgroup.centralizer ({z} : Set G)) :=
    ⟨fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (C.hyp.hzS s hs), S.isPGroup',
      fun V'' _ hV'' hle' => S.is_maximal' hV'' hle'⟩
  have hV'z : V' ≤ Subgroup.centralizer ({z} : Set G) := fun v hv => (hV'C hv).1.1
  obtain ⟨V, hV, hV'V⟩ := IsSylow2In.exists_ge hV' hV'z
  obtain ⟨c, hc, hVeq⟩ := IsSylow2Of.exists_conj (show IsSylow2Of _ _ from hSz)
    (show IsSylow2Of _ _ from hV)
  have hcz : c⁻¹ * z * c⁻¹⁻¹ = z := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c⁻¹ * z * c⁻¹⁻¹ = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [h]
      _ = z := by group
  have hmap : ∀ v ∈ V', c⁻¹ * v * c ∈ A₀ := by
    intro v hv
    have h1 : c⁻¹ * v * c ∈ (S : Subgroup G) := by
      have := hV'V hv
      rw [hVeq] at this
      exact mem_conjSubgroup_iff.mp this
    have h2 : c⁻¹ * v * c ∈ cOne z K K' := by
      have := C.cOne_conj hcz (hV'C hv)
      rwa [inv_inv] at this
    exact C.mem_A_of_mem_cOne h1 h2
  have hcard : Nat.card V' ≤ Nat.card A₀ := by
    refine Nat.card_le_card_of_injective (fun v : V' => (⟨c⁻¹ * v * c, hmap v v.2⟩ : A₀)) ?_
    intro v w hvw
    have h := congrArg Subtype.val hvw
    simp only [mul_left_inj, mul_right_inj] at h
    exact Subtype.ext h
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem conjSub_cOne [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {c : G}
    (hc : c * z * c⁻¹ = z) : conjSub c (cOne z K K') = cOne z K K' := by
  have hc' : c⁻¹ * z * c⁻¹⁻¹ = z := by
    calc c⁻¹ * z * c⁻¹⁻¹ = c⁻¹ * (c * z * c⁻¹) * c := by rw [hc]; group
      _ = z := by group
  ext y
  rw [mem_conjSub_iff]
  constructor
  · intro hy
    have := C.cOne_conj hc hy
    simpa [mul_assoc] using this
  · intro hy
    have := C.cOne_conj hc' hy
    simpa using this

theorem oddCore_cOne_le [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    oddCoreIn (cOne z K K') ≤ oddCoreIn (Subgroup.centralizer ({z} : Set G)) := by
  refine le_oddCoreIn_of_normalizes ((oddCoreIn_le _).trans fun x hx => hx.1.1) ?_
    (odd_card_oddCoreIn _)
  intro c hc
  have hcz : c * z * c⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc]; group
  have h := oddCoreIn_conjSub_eq c (cOne z K K')
  rw [C.conjSub_cOne hcz] at h
  exact mem_normalizer_of_conjSub_eq h.symm

theorem cOne_normalizer_le [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    ∀ g ∈ cOne z K K', (∀ x : G, x ∈ (S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ↔ g * x * g⁻¹ ∈ (S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) →
      ∀ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        g * x = x * g := by
  set A₀ := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA₀
  intro g hg hgn x hx
  have hgz : g * z * g⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hg.1.1]; group
  have hgN : g ∈ Subgroup.normalizer (A₀ : Set G) := Subgroup.mem_normalizer_iff.mpr hgn
  have hcommA : ∀ y ∈ A₀, y * a = a * y := by
    intro y hy
    rcases C.hA0 y hy with h | h | h | h <;> rw [h]
    · group
    · exact C.comm.symm
    · calc a * z * a = a * (z * a) := by group
        _ = a * (a * z) := by rw [C.comm]
  have hga : g * a * g⁻¹ = a := by
    have hm : g * a * g⁻¹ ∈ A₀ := (hgn a).mp C.haA
    rcases C.hA0 _ hm with h | h | h | h
    · exfalso
      apply C.ha1
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · exact h
    · exact absurd (show g⁻¹ * z * g⁻¹⁻¹ = a by rw [← h]; group) (C.not_conj_z g⁻¹)
    · exfalso
      have hstep : ∀ (n : ℕ) (y : G), g ^ (n + 1) * y * (g ^ (n + 1))⁻¹ =
          g * (g ^ n * y * (g ^ n)⁻¹) * g⁻¹ := by
        intro n y; rw [pow_succ']; group
      have hazz : g * (a * z) * g⁻¹ = a := by
        calc g * (a * z) * g⁻¹ = (g * a * g⁻¹) * (g * z * g⁻¹) := by group
          _ = a := by rw [h, hgz, C.mul_z_mul_z]
      have hpar : ∀ j : ℕ, g ^ (2 * j) * a * (g ^ (2 * j))⁻¹ = a ∧
          g ^ (2 * j + 1) * a * (g ^ (2 * j + 1))⁻¹ = a * z := by
        intro j
        induction j with
        | zero => exact ⟨by simp, by simpa using h⟩
        | succ j ih =>
          have e1 : g ^ (2 * (j + 1)) * a * (g ^ (2 * (j + 1)))⁻¹ = a := by
            rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, hstep, ih.2, hazz]
          exact ⟨e1, by rw [hstep, e1, h]⟩
      have hn0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
      obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hn0
      obtain ⟨j, rfl⟩ := hm
      have hm0 : 2 * j + 1 ≠ 0 := by omega
      have hord : orderOf (g ^ (2 * j + 1)) = 2 ^ k := by
        rw [orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hn.symm), hn,
          Nat.mul_div_cancel _ (by omega)]
      have h2 : IsPGroup 2 (Subgroup.zpowers (g ^ (2 * j + 1))) :=
        IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hord])
      have hle : Subgroup.zpowers (g ^ (2 * j + 1)) ≤ Subgroup.normalizer (A₀ : Set G) :=
        Subgroup.zpowers_le.mpr (pow_mem hgN _)
      have hp := IsPGroup.to_sup_of_normal_right' h2 (S.isPGroup'.to_le inf_le_left) hle
      have hle' : Subgroup.zpowers (g ^ (2 * j + 1)) ⊔ A₀ ≤ cOne z K K' :=
        sup_le (Subgroup.zpowers_le.mpr (pow_mem hg _)) C.A_le_cOne
      have heq := C.isSylow2In_cOne.2.2 _ hle' hp le_sup_right
      have hgA : g ^ (2 * j + 1) ∈ A₀ := by
        have h4 := le_sup_left (a := Subgroup.zpowers (g ^ (2 * j + 1))) (b := A₀)
          (Subgroup.mem_zpowers (g ^ (2 * j + 1)))
        rw [heq] at h4
        exact h4
      have h3 := (hpar j).2
      rw [show g ^ (2 * j + 1) * a * (g ^ (2 * j + 1))⁻¹ = a by
        rw [hcommA _ hgA]; group] at h3
      apply C.hz1
      calc z = a⁻¹ * (a * z) := by group
        _ = 1 := by rw [← h3]; group
  rcases C.hA0 x hx with h | h | h | h <;> rw [h]
  · group
  · calc g * a = (g * a * g⁻¹) * g := by group
      _ = a * g := by rw [hga]
  · calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hgz]
  · calc g * (a * z) = (g * a * g⁻¹) * (g * z * g⁻¹) * g := by group
      _ = a * z * g := by rw [hga, hgz]

theorem cOne_eq_mul [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    ∀ c ∈ cOne z K K', ∃ o ∈ oddCoreIn (cOne z K K'), ∃ b ∈ (S : Subgroup G) ⊓
      Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G), c = o * b :=
  exists_oddCore_mul_of_normalizer_le C.isSylow2In_cOne C.cOne_normalizer_le

theorem conj_a_mem [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {c : G}
    (hc : c * z * c⁻¹ = z) :
    ∃ o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)),
      c * a * c⁻¹ = a * o ∨ c * a * c⁻¹ = a * z * o := by
  have hm : c * a * c⁻¹ ∈ cOne z K K' := C.cOne_conj hc C.a_mem_cOne
  obtain ⟨o, ho, b, hb, hob⟩ := C.cOne_eq_mul _ hm
  have hO := C.oddCore_cOne_le
  have hinv : (c * a * c⁻¹) * (c * a * c⁻¹) = 1 := by
    calc (c * a * c⁻¹) * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
      _ = 1 := by rw [C.ha2]; group
  rcases C.hA0 b hb with h | h | h | h
  · exfalso
    have hp : IsPGroup 2 (Subgroup.zpowers (c * a * c⁻¹)) := isPGroup_zpowers_of_sq_eq_one hinv
    have h1 : c * a * c⁻¹ ∈ oddCoreIn (cOne z K K') := by rw [hob, h, mul_one]; exact ho
    have h2 := eq_one_of_isPGroup_of_odd hp (odd_card_oddCoreIn _) (Subgroup.mem_zpowers _) h1
    apply C.ha1
    calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
      _ = 1 := by rw [h2]; group
  · have hai : a⁻¹ ∈ cOne z K K' := Subgroup.inv_mem _ C.a_mem_cOne
    have h1 := conj_mem_oddCoreIn hai ho
    rw [inv_inv] at h1
    refine ⟨a⁻¹ * o * a, hO h1, Or.inl ?_⟩
    rw [hob, h]; group
  · exfalso
    have hzo : z * (c * a * c⁻¹) ∈ oddCoreIn (cOne z K K') := by
      rw [hob, h]
      have h1 := conj_mem_oddCoreIn C.z_mem_cOne ho
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right C.hz2
      rw [hzi] at h1
      simpa [mul_assoc] using h1
    obtain ⟨n, -, hn⟩ := C25Y.exists_conj_of_involutions_odd (odd_card_oddCoreIn _) C.hz2 hinv hzo
    exact C.not_conj_z (c⁻¹ * n) (by
      calc c⁻¹ * n * z * (c⁻¹ * n)⁻¹ = c⁻¹ * (n * z * n⁻¹) * c := by group
        _ = a := by rw [← hn]; group)
  · have hazi : (a * z)⁻¹ ∈ cOne z K K' :=
      Subgroup.inv_mem _ (mul_mem C.a_mem_cOne C.z_mem_cOne)
    have h1 := conj_mem_oddCoreIn hazi ho
    rw [inv_inv] at h1
    refine ⟨(a * z)⁻¹ * o * (a * z), hO h1, Or.inr ?_⟩
    rw [hob, h]; group

theorem frattini [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {c : G}
    (hc : c * z * c⁻¹ = z) :
    ∃ o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)), o⁻¹ * c ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) : Subgroup G) :
        Set G) := by
  set A₀ := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA₀
  have hsyl := C.isSylow2In_cOne
  have hsyl' : IsSylow2In (conjSub c A₀) (cOne z K K') := by
    have := hsyl.conj c
    rwa [C.conjSub_cOne hc] at this
  obtain ⟨m, hm, hmeq⟩ := IsSylow2Of.exists_conj (show IsSylow2Of _ _ from hsyl)
    (show IsSylow2Of _ _ from hsyl')
  obtain ⟨o, ho, b, hb, hmob⟩ := C.cOne_eq_mul m hm
  refine ⟨o, C.oddCore_cOne_le ho, Subgroup.mem_normalizer_iff.mpr fun x => ?_⟩
  have key : ∀ y : G, y ∈ conjSub c A₀ ↔ b⁻¹ * (o⁻¹ * y * o) * b ∈ A₀ := by
    intro y
    rw [hmeq, mem_conjSubgroup_iff, hmob]
    have e : (o * b)⁻¹ * y * (o * b) = b⁻¹ * (o⁻¹ * y * o) * b := by group
    rw [e]
  have hbA : ∀ y : G, b⁻¹ * y * b ∈ A₀ ↔ y ∈ A₀ := by
    intro y
    constructor
    · intro hy
      have h1 := A₀.mul_mem (A₀.mul_mem hb hy) (A₀.inv_mem hb)
      have e : b * (b⁻¹ * y * b) * b⁻¹ = y := by group
      rwa [e] at h1
    · intro hy
      exact A₀.mul_mem (A₀.mul_mem (A₀.inv_mem hb) hy) hb
  constructor
  · intro hx
    have h1 : c * x * c⁻¹ ∈ conjSub c A₀ := by
      rw [mem_conjSub_iff]
      have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
      rw [e]; exact hx
    have h2 := (hbA _).mp ((key _).mp h1)
    have e : o⁻¹ * (c * x * c⁻¹) * o = o⁻¹ * c * x * (o⁻¹ * c)⁻¹ := by group
    rwa [e] at h2
  · intro hx
    have e : o⁻¹ * (c * x * c⁻¹) * o = o⁻¹ * c * x * (o⁻¹ * c)⁻¹ := by group
    have h2 : b⁻¹ * (o⁻¹ * (c * x * c⁻¹) * o) * b ∈ A₀ := (hbA _).mpr (by rw [e]; exact hx)
    have h1 := mem_conjSub_iff.mp ((key _).mpr h2)
    have e' : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    rwa [e'] at h1
end Ctx
end Asc77.C5O

end

end CFSG.ClassicalInvolution.Q3.Q3T8
