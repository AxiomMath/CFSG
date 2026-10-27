module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open

variable {G : Type} [Group G]

@[expose] noncomputable def twoAdic {X : Type*} [Group X] (H : Subgroup X) : ℕ :=
  (Nat.card H).factorization 2

@[expose] noncomputable def componentProduct (K : Subgroup G) (u : G) : Subgroup G :=
  sSup {N : Subgroup G | N ≤ centralizer ({u} : Set G) ∧
    (N.subgroupOf (centralizer ({u} : Set G))).Normal ∧ Nonempty (N ≃* K)}

@[expose] def autCentralizer (L K : Subgroup G) : Subgroup (MulAut L) where
  carrier := {α | ∀ k : L, (k : G) ∈ K → α k = k}
  mul_mem' := by
    intro a b ha hb k hk
    show a (b k) = k
    rw [hb k hk, ha k hk]
  one_mem' := fun _ _ => rfl
  inv_mem' := by
    intro a ha k hk
    show a.symm k = k
    calc a.symm k = a.symm (a k) := by rw [ha k hk]
      _ = k := a.symm_apply_apply k

@[expose] def vCandidates (K : Subgroup G) (u : G) : Set G :=
  {v | v ∈ K ⊔ zpowers u ∧ v ∉ (center K).map K.subtype ∧ orderOf v = 2}

@[expose] def vMaximal (K : Subgroup G) (u : G) : Set G :=
  {v | v ∈ vCandidates K u ∧ ∀ v' ∈ vCandidates K u,
    twoAdic (K ⊓ centralizer ({v'} : Set G)) ≤ twoAdic (K ⊓ centralizer ({v} : Set G))}

@[expose] def vPairs (L K : Subgroup G) (u : G) : Set G :=
  {w | ∃ v ∈ vMaximal K u, w = u * v ∧ ∃ l ∈ L, l * u * l⁻¹ = w}

structure SolomonSetting (G : Type) [Group G] [Finite G] (L K : Subgroup G) (t u : G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  simpleL : IsSimpleGroup L
  nonabelianL : ∃ a b : L, a * b ≠ b * a
  t_order : orderOf t = 2
  t_mem : t ∈ centralizer (L : Set G)
  u_order : orderOf u = 2
  u_mem : u ∈ L
  K_le : K ≤ L
  u_comm_t : u * t = t * u
  u_mem_centralizer_K : u ∈ centralizer (K : Set G)
  standard_in_L : standardComponentIsStandard (K.subgroupOf L)
  autCentralizer_two : twoAdic (autCentralizer L K) ≤ 2
  hyp35 : K = componentProduct K u

structure SolomonHyp (G : Type) [Group G] [Finite G] (L K : Subgroup G) (t u : G) : Prop
    extends SolomonSetting G L K t u where
  hyp38_1 : ∀ g ∈ centralizer ({u} : Set G), ∀ w ∈ vPairs L K u, g * w * g⁻¹ ∈ vPairs L K u
  hyp38_2 : centralizer ({u} : Set G) ≤ normalizer (L : Set G)

end CFSG.EvenSporadicStandard.Solomon78
