module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0StructBase
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModIsoPerm

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup Matrix

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

@[expose] def epsV (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (v : Fin 3 → ZMod 2) : G :=
  N0.eps θ hn (ModIso.bits.symm v)

@[expose] def liftE (k : ℕ) (v : Fin 3 → ZMod 2) : Fin 3 → ZMod (2 ^ k) :=
  fun i => 2 ^ (k - 1) * ((v i).val : ZMod (2 ^ k))

@[expose] def Lfree (L : Subgroup G) (z : G) : Subgroup G :=
  L ⊔ AltStdBal.oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G))

@[expose] def KA (L : Subgroup G) (z : G) (A : Subgroup G) : Subgroup G :=
  normalizer (A : Set G) ⊓ centralizer ({z} : Set G) ⊓ Lfree L z

@[expose] def RA (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z : G) (A : Subgroup G) :
    Subgroup G :=
  normalizer ((A ⊔ zpowers z : Subgroup G) : Set G) ⊓ centralizer (E θ hn : Set G)

@[expose] def betaHat (k : ℕ) (z r : G) : G := (r * z * r⁻¹ * z⁻¹) ^ 2 ^ (k - 1)

structure LevelDatum (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z : G) (k : ℕ)
    (A : Subgroup G) : Prop where
  two_le : 2 ≤ k
  E_le : E θ hn ≤ A
  coords : ∃ ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k)),
    ∀ (v : Fin 3 → ZMod 2) (h : epsV θ hn v ∈ A),
      Multiplicative.toAdd (ι ⟨epsV θ hn v, h⟩) = liftE k v
  zact : (∀ a ∈ A, z * a * z⁻¹ = a⁻¹) ∨
    (3 ≤ k ∧ ∀ a ∈ A, z * a * z⁻¹ = a⁻¹ * a ^ 2 ^ (k - 1))
  cover : ∀ M : GL (Fin 3) (ZMod 2), ∃ g ∈ KA L z A, ∀ v : Fin 3 → ZMod 2,
    g * epsV θ hn v * g⁻¹ = epsV θ hn ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)

@[expose] def Terminal (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (A : Subgroup G) : Prop :=
  ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer (E θ hn : Set G) →
    Nat.card P ≤ 2 * Nat.card A

structure StepData (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z : G) (k : ℕ)
    (A P A' : Subgroup G) : Prop where
  datum : LevelDatum θ hn z k A
  P_le : P ≤ RA θ hn z A
  P_two : IsPGroup 2 P
  le_P : A ⊔ zpowers z ≤ P
  A'_eq : A' = P ⊓ centralizer (A : Set G)
  split : ∀ p ∈ P, p ∈ A' ∨ p * z ∈ A'
  card_A' : Nat.card A' = 8 * Nat.card A
  onto : ∀ e ∈ E θ hn, ∃ x ∈ A', betaHat k z x = e
  ker : ∀ x ∈ A', betaHat k z x = 1 → x ∈ A
  scalar : ∀ r ∈ RA θ hn z A,
    (∀ a ∈ A, r * a * r⁻¹ = a) ∨ (∀ a ∈ A, r * a * r⁻¹ = z * a * z⁻¹)

structure TermData (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (z : G) (m : ℕ)
    (A D : Subgroup G) : Prop where
  datum : LevelDatum θ hn z m A
  term : Terminal θ hn A
  D_le_L : D ≤ L
  D_norm : D ≤ normalizer (A : Set G)
  D_card : Nat.card D = 8
  D_faith : ∀ d ∈ D, (∀ e ∈ E θ hn, d * e * d⁻¹ = e) → d = 1

@[expose] def G2Start : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G),
      N0Data θ c.hn8 z T → Nonempty (T ≃* Multiplicative (Fin 3 → ZMod 4)) →
        LevelDatum θ c.hn8 z 2 T

@[expose] def G2Step : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (k : ℕ)
    (A : Subgroup G), LevelDatum θ c.hn8 z k A → ¬ Terminal θ c.hn8 A →
      ∃ A' : Subgroup G, LevelDatum θ c.hn8 z (k + 1) A' ∧ Nat.card A < Nat.card A'

@[expose] def G2Terminal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (m : ℕ)
    (A : Subgroup G), LevelDatum θ c.hn8 z m A → Terminal θ c.hn8 A → False

theorem sq_eq_one_of_elem {T : Subgroup G} (φ : T ≃* Multiplicative (Fin 6 → ZMod 2))
    {x : G} (hx : x ∈ T) : x ^ 2 = 1 := by
  have h2 : (φ ⟨x, hx⟩) ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    have hadd : ∀ a : ZMod 2, a + a = 0 := by decide
    simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, two_nsmul]
    exact hadd _
  have h3 : (⟨x, hx⟩ : T) ^ 2 = 1 := φ.injective (by rw [map_pow, h2, map_one])
  simpa using congrArg Subtype.val h3

theorem sec4N0Elementary_of_parts (h1 : G2Start) (h2 : G2Step) (h3 : G2Terminal) :
    Sec4N0Elementary := by
  intro G _ _ L Q n θ z c T hT
  rcases hT.homo with hφ | hφ
  · obtain ⟨φ⟩ := hφ
    exact fun x hx => sq_eq_one_of_elem φ hx
  · exfalso
    obtain ⟨φ⟩ := hφ
    obtain ⟨A, ⟨k, hk⟩, hmax⟩ := Set.exists_max_image
      {A : Subgroup G | ∃ k, LevelDatum θ c.hn8 z k A} (fun A => Nat.card A) (Set.toFinite _)
      ⟨T, 2, h1 G L Q n θ z c T hT ⟨φ⟩⟩
    by_cases hterm : Terminal θ c.hn8 A
    · exact h3 G L Q n θ z c k A hk hterm
    · obtain ⟨A', hA', hlt⟩ := h2 G L Q n θ z c k A hk hterm
      have := hmax A' ⟨k + 1, hA'⟩
      omega

end CFSG.OddStandard.AltStdSmall4.G2
