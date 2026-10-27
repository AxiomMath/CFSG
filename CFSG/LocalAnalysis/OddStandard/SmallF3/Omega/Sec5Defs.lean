module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def IsOm6Z2 {G : Type} [Group G] (L : Subgroup G) : Prop :=
  IsQuasisimple L ∧ IsTwoU43 (L ⧸ oddCore L)

structure Sec5Setting (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) : Prop
    extends Sec3SettingLB G t L where
  twoU43 : IsTwoU43 (L ⧸ oddCore L)

structure Sec5Ctx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) : Prop
    extends Sec5Setting G t L, Asc82Notation t L S z

structure Sec5RCtx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A : Subgroup G) : Prop extends Sec5Ctx G t L S z where
  conj_r : ∃ g : G, g⁻¹ * t * g = r
  type_r : ∃ α : ℤˣ, InducesTypeSome L r 6 (-1) 1 α
  B_le : B ≤ L ⊓ centralizer ({r} : Set G)
  B_E32 : IsElemAb2 B 5
  B_split : t ∈ B ∧ zpowers t ⊓ layerCent L r = ⊥ ∧ B = zpowers t ⊔ (B ⊓ layerCent L r)
  A_eq : A = zpowers r ⊔ B
  A_le : A ≤ S

structure Sec5KCtx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) : Prop extends Sec5RCtx G t L S z r B A where
  centre : centerIn L = zpowers t
  pocket₁ : Sl23PocketIn L z K₁
  pocket₂ : Sl23PocketIn L z K₂
  ne : K₁ ≠ K₂
  comm : ⁅K₁, K₂⁆ = ⊥
  iso₁ : Nonempty (↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
  iso₂ : Nonempty (↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
  prod : K₁ ⊔ K₂ = twoRes (L ⊓ centralizer ({z} : Set G))

structure Sec5HCtx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G) : Prop extends Sec5KCtx G t L S z r B A K₁ K₂ where
  h_mem : h ∈ normalizer (A : Set G)
  h_t : h⁻¹ * t * h ∈ K₁ ⊔ K₂
  h_sq : h * h ∈ centralizer ({t} : Set G)
  h_z : h ∈ centralizer ({z} : Set G)

variable {G : Type} [Group G]

@[expose] def IsHeartA8 (A H : Subgroup G) (Alt : Subgroup (Equiv.Perm (Fin 8))) : Prop :=
  ∃ φ : (Fin 8 → ZMod 2) → G,
    IsPermModuleMod (n := 8) IsEvenVec ({0, fun _ => 1} : Set (Fin 8 → ZMod 2)) φ A ⊥ H Alt

@[expose] def Case59Two (t z : G) (A : Subgroup G) : Prop :=
  conjClassIn ⊤ t ∩ (A : Set G) =
      ((A : Set G) \ {1}) \ conjClassIn (normalizer (A : Set G)) z ∧
    conjClassIn ⊤ t ∩ (A : Set G) = conjClassIn (normalizer (A : Set G)) t ∧
    Set.ncard (conjClassIn ⊤ t ∩ (A : Set G)) = 28 ∧
    ∃ Alt : Subgroup (Equiv.Perm (Fin 8)), (Alt = alternatingGroup (Fin 8) ∨ Alt = ⊤) ∧
      IsHeartA8 A (normalizer (A : Set G)) Alt

@[expose] def layerC5 (d : G) : Subgroup G :=
  CFSG.inSubgroup CFSG.layer (centralizer ({d} : Set G))

@[expose] def Gamma5 (K₁ K₂ : Subgroup G) (h : G) : Set (Subgroup G) :=
  {K₁, K₂, CFSG.conjugate K₁ h, CFSG.conjugate K₂ h}

@[expose] def Kfam5 (K₁ K₂ : Subgroup G) (h : G) : Fin 4 → Subgroup G :=
  ![K₁, K₂, CFSG.conjugate K₁ h, CFSG.conjugate K₂ h]

@[expose] def Delta5 (z : G) (Γ : Set (Subgroup G)) : Set G :=
  {d | orderOf d = 2 ∧ d ≠ z ∧ ∃ P ∈ Γ, ∃ P' ∈ Γ, P ≠ P' ∧ d ∈ P ⊔ P'}

@[expose] def DeltaT5 (z : G) (K₃ K₄ : Subgroup G) : Set G :=
  {d | orderOf d = 2 ∧ d ≠ z ∧ d ∈ K₃ ⊔ K₄}

@[expose] def IsKOf (Γ : Set (Subgroup G)) (d : G) (P : Subgroup G) : Prop :=
  ∃ P₁ ∈ Γ, ∃ P₂ ∈ Γ, P₁ ≠ P₂ ∧ P = P₁ ⊔ P₂ ∧ P ≤ centralizer ({d} : Set G)

@[expose] def Qsub (K₁ K₂ : Subgroup G) (h : G) : Subgroup G :=
  twoCoreIn (K₁ ⊔ K₂ ⊔ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h)

@[expose] def centralizerMod (z : G) (N E : Subgroup G) : Subgroup G where
  carrier := {n | n ∈ N ∧ n ∈ centralizer ({z} : Set G) ∧ n ∈ normalizer (E : Set G) ∧
    ∀ q ∈ E, n * q * n⁻¹ * q⁻¹ ∈ zpowers z}
  one_mem' := ⟨one_mem N, one_mem _, one_mem _, fun q _ => by simpa using one_mem (zpowers z)⟩
  mul_mem' := by
    rintro a b ⟨haN, haz, haE, ha⟩ ⟨hbN, hbz, hbE, hb⟩
    refine ⟨mul_mem haN hbN, mul_mem haz hbz, mul_mem haE hbE, fun q hq => ?_⟩
    have hac : Commute a z := (Subgroup.mem_centralizer_iff.mp haz z (Set.mem_singleton z)).symm
    obtain ⟨k, hk⟩ := hb q hq
    have hak : a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ = b * q * b⁻¹ * q⁻¹ := by
      rw [← hk]
      exact (hac.zpow_right k).mul_inv_cancel
    have key : a * b * q * (a * b)⁻¹ * q⁻¹ =
        (a * (b * q * b⁻¹ * q⁻¹) * a⁻¹) * (a * q * a⁻¹ * q⁻¹) := by group
    rw [key, hak]
    exact mul_mem ⟨k, hk⟩ (ha q hq)
  inv_mem' := by
    rintro a ⟨haN, haz, haE, ha⟩
    refine ⟨inv_mem haN, inv_mem haz, inv_mem haE, fun q hq => ?_⟩
    have hq' : a⁻¹ * q * a ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem haE) q).mp hq
      simpa using this
    have h1 := ha (a⁻¹ * q * a) hq'
    have key : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = (a * (a⁻¹ * q * a) * a⁻¹ * (a⁻¹ * q * a)⁻¹)⁻¹ := by
      group
    rw [key]
    exact inv_mem h1

@[expose] def IsElemAbelianModSub (C U : Subgroup G) : Prop :=
  ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ C ∧ a * a ∈ C

end CFSG.OddStandard.SmallF3.Omega
