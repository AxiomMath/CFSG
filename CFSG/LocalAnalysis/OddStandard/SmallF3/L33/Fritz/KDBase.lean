module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKDSkeleton
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDData

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv GorensteinWalter Blueprint

structure KDBase {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (A : SDData t L)
    (C : A.CaseKD) where
  x : X
  y : X
  x_mem : x ∈ A.R
  y_mem : y ∈ A.R
  orderOf_x : orderOf x = 4
  y_sq : y ^ 2 = 1
  y_inv : y * x * y⁻¹ = x⁻¹
  d_y : ∃ g ∈ centralizer ({t} : Set X),
    g ∈ normalizer (closure {x ^ 2, y, t, C.k} : Set X) ∧ g * x ^ 2 * g⁻¹ = y ∧
      g * y * g⁻¹ = x ^ 2 * y ∧ g * C.k * g⁻¹ = C.k
  d_xy : ∃ g ∈ centralizer ({t} : Set X),
    g ∈ normalizer (closure {x ^ 2, x * y, t, C.k} : Set X) ∧ g * x ^ 2 * g⁻¹ = x * y ∧
      g * (x * y) * g⁻¹ = x ^ 2 * (x * y) ∧ g * (x ^ 2 * C.k) * g⁻¹ = x ^ 2 * C.k
  k_fixed : ∀ n ∈ normalizer (closure {x ^ 2, y, t, C.k} : Set X) ⊓ centralizer ({t} : Set X),
    n * C.k * n⁻¹ = C.k
  zk_fixed : ∀ n ∈ normalizer (closure {x ^ 2, x * y, t, C.k} : Set X) ⊓
      centralizer ({t} : Set X), n * (x ^ 2 * C.k) * n⁻¹ = x ^ 2 * C.k
  card_conj_z : (∀ g ∈ centralizer ({t} : Set X), g * x ^ 2 * g⁻¹ ≠ t * x ^ 2) →
    {b | ∃ g ∈ centralizer ({t} : Set X), g * x ^ 2 * g⁻¹ = b}.ncard ≡ 1 [MOD 4]
  card_conj_k : {b | ∃ g ∈ centralizer ({t} : Set X), g * C.k * g⁻¹ = b}.ncard ≡ 2 [MOD 4]
  not_conj_k_tk : ∀ g ∈ centralizer ({t} : Set X), g * C.k * g⁻¹ ≠ t * C.k
  inv_classes : ∀ i ∈ centralizer ({t} : Set X), i ^ 2 = 1 → i ≠ 1 →
    ∃ g ∈ centralizer ({t} : Set X), g * i * g⁻¹ = t ∨ g * i * g⁻¹ = x ^ 2 ∨
      g * i * g⁻¹ = t * x ^ 2 ∨ g * i * g⁻¹ = C.k ∨ g * i * g⁻¹ = t * C.k

namespace KDBase

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} (S : KDBase A C)

@[expose] def z : X := S.x ^ 2

@[expose] def k (_ : KDBase A C) : X := C.k

@[expose] def d (_ : KDBase A C) : X := C.d

@[expose] noncomputable def B : Subgroup X := closure {S.z, t, S.k}

@[expose] noncomputable def E (yi : X) : Subgroup X := closure {S.z, yi, t, S.k}

@[expose] noncomputable def E0 (yi ki : X) : Subgroup X := closure {S.z, yi, ki}

@[expose] noncomputable def TE : Subgroup X := A.T ⊓ centralizer (S.B : Set X)

structure Sec4 (T₁ : Subgroup X) : Prop where
  isPGroup : IsPGroup 2 T₁
  le : A.T ≤ T₁
  le_normalizer : T₁ ≤ normalizer (S.TE : Set X)
  maximal : ∀ Q : Subgroup X, IsPGroup 2 Q → T₁ ≤ Q → Q ≤ normalizer (S.TE : Set X) →
    Q = T₁
  card : Nat.card T₁ = 4 * Nat.card A.T
  fusion : ∀ b ∈ S.B, ConjTo t b ↔ b = t ∨ b = t * S.z ∨ b = t * S.k ∨ b = t * S.z * S.k

@[expose] def ActHolds (yi ki : X) (v w₁ w₂ : X) : ActType → Prop
  | .one => (∀ e ∈ S.E0 yi ki, v * e * v⁻¹ = e ∧ w₁ * e * w₁⁻¹ = e ∧ w₂ * e * w₂⁻¹ = e) ∧
      v * t * v⁻¹ = t * ki ∧ w₁ * t * w₁⁻¹ = t * S.z ∧ w₂ * t * w₂⁻¹ = t * yi
  | .two => (∀ e ∈ S.E0 yi ki, v * e * v⁻¹ = e) ∧ v * t * v⁻¹ = t * ki ∧
      w₁ * t * w₁⁻¹ = t * S.z * ki ∧ w₂ * t * w₂⁻¹ = t * yi * ki ∧
      w₁ * S.z * w₁⁻¹ = S.z ∧ w₂ * yi * w₂⁻¹ = yi ∧ w₂ * S.z * w₂⁻¹ = S.z * ki ∧
      w₁ * yi * w₁⁻¹ = yi * ki ∧ w₁ * ki * w₁⁻¹ = ki ∧ w₂ * ki * w₂⁻¹ = ki

@[expose] noncomputable def Q0 (yi ki w₁ w₂ : X) : Subgroup X :=
  S.E0 yi ki ⊔ zpowers w₁ ⊔ zpowers w₂

@[expose] def Q0Holds (yi ki v w₁ w₂ : X) : Q0Type → Prop
  | .elem => (∀ a ∈ S.Q0 yi ki w₁ w₂, ∀ b ∈ S.Q0 yi ki w₁ w₂, a * b = b * a) ∧
      (∀ a ∈ S.Q0 yi ki w₁ w₂, a ^ 2 = 1) ∧ Nat.card (S.Q0 yi ki w₁ w₂) = 32
  | .homocyclic => w₁ ^ 2 = S.z ∧ w₂ ^ 2 = yi ∧
      (∀ a ∈ S.Q0 yi ki w₁ w₂, ∀ b ∈ S.Q0 yi ki w₁ w₂, a * b = b * a) ∧
      Nat.card (S.Q0 yi ki w₁ w₂) = 32
  | .e4q8 => w₁ ^ 2 = ki ∧ w₂ ^ 2 = ki ∧ CenterEq (S.Q0 yi ki w₁ w₂) (S.E0 yi ki) ∧
      Nat.card (S.Q0 yi ki w₁ w₂) = 32
  | .exceptional => w₁ ^ 2 = S.z * ki ∧ w₂ ^ 2 = yi * ki ∧ w₁ * w₂ * w₁⁻¹ * w₂⁻¹ = ki ∧
      CenterEq (S.Q0 yi ki w₁ w₂) (S.E0 yi ki) ∧ Nat.card (S.Q0 yi ki w₁ w₂) = 32
  | .extraspecial => w₁ ^ 2 = 1 ∧ w₂ ^ 2 = 1 ∧ S.ActHolds yi ki v w₁ w₂ .two ∧
      CenterEq (S.Q0 yi ki w₁ w₂) (closure {ki}) ∧ Nat.card (S.Q0 yi ki w₁ w₂) = 32

structure Sec6 (T₁ : Subgroup X) (yi ki ui : X) where
  S₁ : Subgroup X
  Q₁ : Subgroup X
  D₁₁ : Subgroup X
  C₁ : Subgroup X
  v : X
  w₁ : X
  w₂ : X
  u : X
  d₃ : X
  act : ActType
  q0 : Q0Type
  automizer : Nonempty (normalizer (S.E yi : Set X) ⧸
    (centralizer (S.E yi : Set X)).subgroupOf (normalizer (S.E yi : Set X)) ≃*
      Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))
  controls : ∀ e ∈ S.E yi, ConjTo t e → ∃ n ∈ normalizer (S.E yi : Set X), n * t * n⁻¹ = e
  card_conj : Nat.card {e : S.E yi // ConjTo t e} = 8
  isPGroup_S₁ : IsPGroup 2 S₁
  S₁_le : S₁ ≤ normalizer (S.E yi : Set X)
  S₁_maximal : ∀ Q : Subgroup X, IsPGroup 2 Q → S₁ ≤ Q → Q ≤ normalizer (S.E yi : Set X) →
    Q = S₁
  S₁_eq : S₁ = S.E yi ⊔ zpowers v ⊔ zpowers w₁ ⊔ zpowers w₂ ⊔ zpowers u
  v_central : ∀ n ∈ normalizer (S.E yi : Set X), n * v * n⁻¹ * v⁻¹ ∈
    centralizer (S.E yi : Set X)
  d₃_mem : d₃ ∈ normalizer (S.E yi : Set X) ⊓ centralizer ({t} : Set X)
  d₃_cube : d₃ ^ 3 ∈ centralizer (S.E yi : Set X)
  d₃_not_mem : d₃ ∉ centralizer (S.E yi : Set X)
  u_inv_d₃ : u * d₃ * u⁻¹ * d₃ ∈ centralizer (S.E yi : Set X)
  u_comm_w₁ : u * w₁ * u⁻¹ * w₁⁻¹ ∈ centralizer (S.E yi : Set X)
  normalizer_inf_centralizer : normalizer (S.E yi : Set X) ⊓ centralizer ({t} : Set X) =
    centralizer (S.E yi : Set X) ⊔ zpowers d₃ ⊔ zpowers u
  act_holds : S.ActHolds yi ki v w₁ w₂ act
  k_fixed : ∀ n ∈ normalizer (S.E yi : Set X), n * ki * n⁻¹ = ki
  T₁_eq : T₁ = A.T ⊔ zpowers v ⊔ zpowers w₁
  R₁_le : T₁ ⊓ normalizer (S.E yi : Set X) ≤ S₁
  Q₁_eq : Q₁ = S₁ ⊓ A7Base.oddTwoCoreIn (normalizer (S.E yi : Set X))
  Q0_le : S.Q0 yi ki w₁ w₂ ≤ Q₁
  Q0_invariant : ∀ n ∈ normalizer (S.E yi : Set X) ⊓ normalizer (Q₁ : Set X),
    (S.Q0 yi ki w₁ w₂).map (MulAut.conj n).toMonoidHom = S.Q0 yi ki w₁ w₂
  q0_holds : S.Q0Holds yi ki v w₁ w₂ q0
  isPGroup_D₁₁ : IsPGroup 3 D₁₁
  D₁₁_le : D₁₁ ≤ normalizer (S.E yi : Set X) ⊓ normalizer (Q₁ : Set X) ⊓
    centralizer ({t} : Set X)
  C_eq : Q₁ ⊓ centralizer (D₁₁ : Set X) = closure {t, ki, v}
  w₁_comm_C : ∀ c ∈ Q₁ ⊓ centralizer (D₁₁ : Set X), w₁ * c * w₁⁻¹ * c⁻¹ ∈
    (match act with
      | .one => closure {S.z}
      | .two => closure {S.z * ki})
  w₁_comm_t : w₁ * t * w₁⁻¹ * t⁻¹ ≠ 1
  C₁_le : C₁ ≤ Q₁ ⊓ centralizer (D₁₁ : Set X)
  C₁_sup : C₁ ⊔ zpowers t = Q₁ ⊓ centralizer (D₁₁ : Set X)
  card_C₁ : Nat.card C₁ = 4
  card_C : Nat.card (Q₁ ⊓ centralizer (D₁₁ : Set X) : Subgroup X) = 8
  C₁_comm : ∀ c ∈ C₁, ∀ q ∈ S.Q0 yi ki w₁ w₂, c * q = q * c
  u_eq : u = ui ∨ u = t * ui
  u_comm_C : ∀ c ∈ Q₁ ⊓ centralizer (D₁₁ : Set X), u * c = c * u
  u_inv_D₁₁ : ∀ δ ∈ D₁₁, u * δ * u⁻¹ * δ ∈
    A7Base.oddCoreIn (centralizer (S.E yi : Set X))
  S₁_commutator_mem : ∀ a ∈ S₁, ∀ b ∈ S₁, a * b * a⁻¹ * b⁻¹ ∈ S.E0 yi ki ⊔ zpowers w₁
  Q₁_char : (q0 = .homocyclic ∨ q0 = .e4q8 ∨ q0 = .exceptional) →
    ∀ n ∈ normalizer (S₁ : Set X), Q₁.map (MulAut.conj n).toMonoidHom = Q₁
  no_conj_of : (q0 = .elem ∨ q0 = .homocyclic) → ∀ q ∈ S.Q0 yi ki w₁ w₂ ⊔ C₁, ¬ ConjTo t q

end KDBase

@[expose] def FritzKDSection4 : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (t : X) (L : Subgroup X) (A : SDData t L) (C : A.CaseKD),
      KDBase A C → ∃ (C' : A.CaseKD) (S : KDBase A C') (T₁ : Subgroup X), S.Sec4 T₁

@[expose] def FritzKDSection6 : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (t : X) (L : Subgroup X) (A : SDData t L) (C : A.CaseKD)
      (S : KDBase A C) (T₁ : Subgroup X), S.Sec4 T₁ →
      Nonempty (S.Sec6 T₁ S.y S.k (S.x * S.y)) ∧
        Nonempty (S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y))

@[expose] def FritzKDSection7 : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (t : X) (L : Subgroup X) (A : SDData t L) (C : A.CaseKD)
      (S : KDBase A C) (T₁ : Subgroup X), S.Sec4 T₁ →
      ∀ (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y)) (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)),
      (D₁.q0 = .e4q8 ∨ D₁.q0 = .exceptional ∨ D₂.q0 = .e4q8 ∨ D₂.q0 = .exceptional) → False

@[expose] def FritzKDSection8ab : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (t : X) (L : Subgroup X) (A : SDData t L) (C : A.CaseKD)
      (S : KDBase A C) (T₁ : Subgroup X), S.Sec4 T₁ →
      ∀ (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y)) (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)),
      (D₁.q0 = .elem ∨ D₁.q0 = .homocyclic ∨ D₁.q0 = .extraspecial) →
      (D₂.q0 = .elem ∨ D₂.q0 = .homocyclic ∨ D₂.q0 = .extraspecial) →
      ¬ (D₁.q0 = .extraspecial ∧ D₂.q0 = .extraspecial) → False

@[expose] def FritzKDSection8c : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (t : X) (L : Subgroup X) (A : SDData t L) (C : A.CaseKD)
      (S : KDBase A C) (T₁ : Subgroup X), S.Sec4 T₁ →
      ∀ (D₁ : S.Sec6 T₁ S.y S.k (S.x * S.y)) (D₂ : S.Sec6 T₁ (S.x * S.y) (S.z * S.k) (S.z * S.y)),
      D₁.q0 = .extraspecial → D₂.q0 = .extraspecial →
        ∃ (P : Sylow 2 X) (z l α₁ α₂ α₃ α₄ x y a : X), GHRel z l α₁ α₂ α₃ α₄ x y a ∧
          Subgroup.closure ({z, l, α₁, α₂, α₃, α₄, x, y, a} : Set X) = P ∧
          Nat.card (P : Subgroup X) = 512

end CFSG.OddStandard.SmallF3.L33.KD
