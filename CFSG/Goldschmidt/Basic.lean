module

public import CFSG.Goldschmidt.OddCore

public section

namespace CFSG.Goldschmidt

open CFSG.Open

section Subgroups

variable {G : Type*} [Group G]

@[expose] def Omega1 (T : Subgroup G) : Subgroup G :=
  Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1}

@[expose] def oddCoreOf (H : Subgroup G) : Subgroup G :=
  (goldschmidtOddCore H).map H.subtype

@[expose] def normalClosureIn (X A : Subgroup G) : Subgroup G :=
  (Subgroup.normalClosure ((A.subgroupOf X : Subgroup X) : Set X)).map X.subtype

@[expose] def barOf (M B : Subgroup G) : Subgroup (M ⧸ goldschmidtOddCore M) :=
  (B.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M))

@[expose] def preOf (M : Subgroup G) (L : Subgroup (M ⧸ goldschmidtOddCore M)) : Subgroup G :=
  (L.comap (QuotientGroup.mk' (goldschmidtOddCore M))).map M.subtype

@[expose] def IsMinStronglyClosed (S U : Subgroup G) : Prop :=
  U ≤ S ∧ U ≠ ⊥ ∧ fusionStronglyClosed (U : Set G) S ∧
    ∀ V : Subgroup G, V ≤ U → V ≠ ⊥ → fusionStronglyClosed (V : Set G) S → V = U

@[expose] def InducesOmega1 (A K T : Subgroup G) : Prop :=
  (∀ a ∈ A, ∃ t ∈ T ⊓ K, t ^ 2 ∈ Subgroup.centralizer (K : Set G) ∧
      ∀ x ∈ K, a⁻¹ * x * a = t⁻¹ * x * t) ∧
    ∀ t ∈ T ⊓ K, t ^ 2 ∈ Subgroup.centralizer (K : Set G) →
      ∃ a ∈ A, ∀ x ∈ K, a⁻¹ * x * a = t⁻¹ * x * t

theorem oddCoreOf_eq_fusionOddCoreOf (H : Subgroup G) : oddCoreOf H = fusionOddCoreOf H := rfl

end Subgroups

@[expose] def CoreConclusion (Z : Type) [Group Z] (S : Sylow 2 Z) (A : Subgroup Z) : Prop :=
  CFSG.Open.pCore 2 Z ⊔ goldschmidtLayer Z = ⊤ ∧
    A = CFSG.Open.pCore 2 Z ⊔
      Subgroup.closure {t | t ∈ (S : Subgroup Z) ⊓ goldschmidtLayer Z ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup Z, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K)

@[expose] def CoreFor (Z : Type) [Group Z] [Finite Z] : Prop :=
  ∀ (S : Sylow 2 Z) (A : Subgroup Z), A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set Z) (S : Subgroup Z) → Subgroup.normalClosure (A : Set Z) = ⊤ →
    goldschmidtOddCore Z = ⊥ → CoreConclusion Z S A

theorem coreStatement_iff :
    CoreStatement ↔ ∀ (Z : Type) [Group Z] [Finite Z], CoreFor Z := Iff.rfl

structure CoreHyp (G : Type) [Group G] (S : Sylow 2 G) (A : Subgroup G) : Prop where
  le : A ≤ (S : Subgroup G)
  comm : IsMulCommutative A
  closed : fusionStronglyClosed (A : Set G) (S : Subgroup G)
  gen : Subgroup.normalClosure (A : Set G) = ⊤
  oddCore : goldschmidtOddCore G = ⊥

theorem coreFor_iff (Z : Type) [Group Z] [Finite Z] :
    CoreFor Z ↔ ∀ (S : Sylow 2 Z) (A : Subgroup Z), CoreHyp Z S A → CoreConclusion Z S A :=
  ⟨fun h S A hA => h S A hA.le hA.comm hA.closed hA.gen hA.oddCore,
    fun h S A h1 h2 h3 h4 h5 => h S A ⟨h1, h2, h3, h4, h5⟩⟩

@[expose] def IH (n : ℕ) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z], Nat.card Z < n → CoreFor Z

theorem IH.mono {m n : ℕ} (h : IH n) (hmn : m ≤ n) : IH m :=
  fun Z _ _ hZ => h Z (lt_of_lt_of_le hZ hmn)

theorem coreStatement_of_step
    (h : ∀ (G : Type) [Group G] [Finite G], IH (Nat.card G) → CoreFor G) : CoreStatement := by
  have key : ∀ n, IH n := by
    intro n
    induction n with
    | zero => exact fun Z _ _ hZ => absurd hZ (Nat.not_lt_zero _)
    | succ n ih =>
      intro Z _ _ hZ
      rcases Nat.lt_succ_iff_lt_or_eq.mp hZ with hlt | heq
      · exact ih Z hlt
      · exact h Z (by rw [heq]; exact ih)
  intro Z _ _
  exact key (Nat.card Z + 1) Z (Nat.lt_succ_self _)

@[expose] def TopFor (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ (S : Sylow 2 Y) (A : Subgroup Y), A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set Y) (S : Subgroup Y) → Subgroup.normalClosure (A : Set Y) = ⊤ →
    Conclusion Y S A

theorem topStatement_iff :
    TopStatement ↔ ∀ (Y : Type) [Group Y] [Finite Y], TopFor Y := Iff.rfl

@[expose] def GoldFor (X : Type) [Group X] [Finite X] : Prop :=
  ∀ (S : Sylow 2 X) (A : Subgroup X), A ≤ S → IsMulCommutative A →
    fusionStronglyClosed (A : Set X) (S : Subgroup X) →
    Conclusion (Subgroup.normalClosure (A : Set X))
      ((S : Subgroup X).subgroupOf (Subgroup.normalClosure (A : Set X)))
      (A.subgroupOf (Subgroup.normalClosure (A : Set X)))

end CFSG.Goldschmidt
