module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Final
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6ShapesDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma810K : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper Catalog G →
    ∀ (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
      Sec8E G t L S z g B E → ∃ X1 X2 : Subgroup G, Sec8X G t E X1 X2

@[expose] def Asc82Lemma811K : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper Catalog G →
    ∀ (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
      Sec8E G t L S z g B E → ∃ Y1 Y2 : Subgroup G, Sec8XO G t E Y1 Y2

@[expose] def Asc82Step84IK : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper Catalog G →
    ∀ (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
      Sec8Ctx G t L S z g B → ∃ γ ∈ S, InducesOutsideGStar L 6 (-1) γ ∧
        S = zpowers t ⊔ zpowers γ ⊔ (S ⊓ L)

@[expose] def Asc82Step84TK : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper Catalog G →
    ∀ (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
      Sec8E G t L S z g B E → S ⊓ L ≤ normalizer (E : Set G) →
        ∀ T : Subgroup G, IsSylow2Of T (normalizer (E : Set G)) →
          S ⊓ normalizer (E : Set G) ≤ T → ¬ IsSylow2Of T ⊤

@[expose] def Asc82Step84GamK : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper Catalog G →
    ∀ (t : G) (L S : Subgroup G) (z g : G) (B E : Subgroup G),
      Sec8E G t L S z g B E → ∃ (γ : G) (K U : Subgroup G), Sec8Gamma G t L S z g B γ K U

@[expose] def Asc82Thm84K : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.KProper Catalog G →
    ∀ (t : G) (L : Subgroup G), Sec3SettingLB G t L →
      IsOmega6Minus L → ∃ s : G, orderOf s = 2 ∧ s ∈ centralizer ({t} : Set G) ∧
        ∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α

structure Sec8T84Base : Prop where
  h36 : Asc82Lemma36
  h37 : Asc82Lemma37
  h63 : Asc82Lemma63
  h68 : Asc82Lemma68
  h82 : Asc82Lemma82
  h83 : Asc82Lemma83
  hM : Asc82Tab6M
  h84z : Asc82Lemma84Z
  h85 : Asc82Lemma85
  h86 : Asc82Lemma86
  h87 : Asc82Lemma87
  h8A : Asc82Lemma8A
  h8B : Asc82Lemma8B
  h88a : Asc82Lemma88a
  h88b : Asc82Lemma88b
  hSyl : Asc82FinkSylow
  hCE : Asc82FinkCE
  hCX : Asc82FinkCX
  hAut : Asc82FinkAut
  hN : Asc82NormA6
  hH62 : ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    Asc82Hyp62 G
  hShapes : Asc82Shapes
  hAutF : Asc82AutFacts
  h6p : ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    LieModel (L ⧸ oddCore L) .PSL 4 3 1 → False
  h64 : Asc82Lemma64

structure Sec8T84K (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
    (B K : Subgroup G) : Prop where
  ctx : Sec8Ctx G t L S z g B
  le_C : K ≤ Nsub8 t B ⊓ centralizer (B : Set G)
  syl : IsSylow2Of K (Nsub8 t B ⊓ centralizer (B : Set G))
  A_le : Asub8 t B ≤ K
  card : Nat.card K = 2 ^ 9
  cent_t : K ⊓ centralizer ({t} : Set G) = Asub8 t B
  tau : ∀ b ∈ B, ∃ k ∈ K, k * t * k⁻¹ * t⁻¹ = b
  comm_le : ∀ k ∈ K, ∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ B
  sq_le : ∀ k ∈ K, k * k ∈ B
  center : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) ↔ k ∈ B

@[expose] def Sec8T84KEx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec8Ctx G t L S z g B → ∃ K : Subgroup G, Sec8T84K G t L S z g B K

structure Sec8T84L1 (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
    (B K L1 : Subgroup G) : Prop where
  K_data : Sec8T84K G t L S z g B K
  le : L1 ≤ K
  B_le : B ≤ L1
  card : Nat.card L1 = 2 ^ 8
  t_not : t ∉ L1
  sup : K = zpowers t ⊔ L1
  inv : ∀ n ∈ Nsub8 t B, ∀ x ∈ L1, n * x * n⁻¹ ∈ L1 ⊔ oddCoreIn (Nsub8 t B)

@[expose] def Sec8T84KL1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec8Ctx G t L S z g B → ∃ K L1 : Subgroup G, Sec8T84L1 G t L S z g B K L1

@[expose] def Asc82OutCosets : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S B : Subgroup G), IsOm6M L →
    IsSylow2Of S (normalizer (L : Set G)) → IsNormalE16In (S ⊓ L) B →
    (∀ y ∈ S, ∀ α : ℤˣ, ¬ InducesTypeSome L y 6 (-1) 1 α ∧ ¬ InducesTypeSome L y 6 (-1) 3 α) →
    autIn S B ≤ autIn L B →
      S ≤ (S ⊓ L) ⊔ centralizer (L : Set G) ∨
        ∃ γ ∈ S, InducesOutsideGStar L 6 (-1) γ ∧
          S ≤ zpowers γ ⊔ (S ⊓ L) ⊔ centralizer (L : Set G)

structure Sec8T84PFacts (Y : Type) [Group Y] [Finite Y] (E P F : Subgroup Y) : Prop where
  E_le : E ≤ P
  F_le : F ≤ P
  F_e16 : IsElemAb2 F 4
  F_ne : F ≠ E
  F_norm : (F.subgroupOf P).Normal
  only : ∀ F' : Subgroup Y, F' ≤ P → IsElemAb2 F' 4 → F' = E ∨ F' = F
  no32 : ∀ F' : Subgroup Y, F' ≤ P → ¬ IsElemAb2 F' 5
  J_card : Nat.card ↥(E ⊔ F) = 64
  EF_card : Nat.card ↥(E ⊓ F) = 4
  rank_cent : ∀ s : Y, orderOf s = 2 → CFSG.Open.pRank 2 (centralizer ({s} : Set Y)) = 4
  cent_E : P ⊓ centralizer (E : Set Y) = E
  cent_F : P ⊓ centralizer (F : Set Y) = F
  y_exists : ∃ y : Y, orderOf y = 3 ∧ y ∈ normalizer ((E ⊔ F : Subgroup Y) : Set Y) ∧
    (∀ u ∈ E ⊔ F, y * u = u * y → u = 1) ∧
      ∃ s ∈ P, s ∉ E ⊔ F ∧ orderOf s = 2 ∧ s * y * s⁻¹ = y⁻¹ ∧ P = zpowers s ⊔ (E ⊔ F)

@[expose] def Sec8T84FactP : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (E H P : Subgroup Y), IsElemAb2 E 4 → E.Normal →
    Nonempty (↥H ≃* alternatingGroup (Fin 6)) → E ⊓ H = ⊥ → E ⊔ H = ⊤ →
    (∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 → ∃ h ∈ H, h * a * h⁻¹ = b) → IsSylow2Of P ⊤ →
      ∃ F : Subgroup Y, Sec8T84PFacts Y E P F

@[expose] def Sec8T84FactQuad : Prop :=
  ∀ (G : Type) [Group G] (B : Subgroup G), IsElemAb2 B 4 → ∀ H : Subgroup (MulAut ↥B),
    Nonempty (↥H ≃* alternatingGroup (Fin 6)) → ∀ q : ↥B → ↥B, q 1 = 1 →
      (∀ h ∈ H, ∀ x : ↥B, q (h x) = h (q x)) →
      (∀ x y z : ↥B, q (x * y * z) * q x * q y * q z = q (x * y) * q (x * z) * q (y * z)) →
        q = (fun _ => 1) ∨ q = id

@[expose] def Sec8T84FactLift : Prop :=
  ∀ (G : Type) [Group G] (U : Subgroup G), (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) →
    Nat.card U = 256 → (∀ x ∈ U, x ^ 4 = 1) →
    Nat.card ↥(Subgroup.closure {u : G | ∃ x ∈ U, u = x * x}) = 16 →
    ∀ H : Subgroup (MulAut ↥U), Nonempty (↥H ≃* alternatingGroup (Fin 5)) →
      (∀ (x : ↥U), (x : G) * x = 1 → x ≠ 1 → ∀ (y : ↥U), (y : G) * y = 1 → y ≠ 1 →
        ∃ h ∈ H, h x = y) → False

end CFSG.OddStandard.SmallF3.Omega
