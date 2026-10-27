module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PairAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup Wreath

variable {G : Type*} [Group G]

abbrev conjSub (t : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj t).toMonoidHom

structure InnerD8Config (L : Subgroup G) (t : G) where
  u : G
  u₁ : G
  L₁ : Subgroup G
  x : G
  eL₁ : ↥L₁ ≃* alternatingGroup (Fin 6)
  u_mem : u ∈ L
  u_ord : orderOf u = 2
  card_centralizer_u : Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = 2880
  pair : PairData (centralizer ({u} : Set G)) L₁ t
  u₁_mem : u₁ ∈ centralizer ({u} : Set G) ⊓ centralizer (L₁ : Set G) ⊓
    centralizer ((conjSub t L₁ : Subgroup G) : Set G)
  u₁_ord : orderOf u₁ = 2
  u₁_conj : t * u₁ * t⁻¹ = u * u₁
  card_F : Nat.card ↥(centralizer ({u} : Set G) ⊓ centralizer (L₁ : Set G) ⊓
    centralizer ((conjSub t L₁ : Subgroup G) : Set G)) = 4
  t_conj_tu : IsConj t (t * u)
  diag : ∀ a : MulAut ↥L₁, a * a = 1 → a ≠ 1 → ∃ x ∈ L, x ∈ centralizer ({u} : Set G) ∧
    x * x = 1 ∧ ((∃ hx : x ∈ normalizer (L₁ : Set G), conjAutOf L₁ hx = a) ∨
      ∃ hx : x * t ∈ normalizer (L₁ : Set G), conjAutOf L₁ hx = a)
  x_mem : x ∈ L₁
  x_ord : orderOf x = 3
  card_centralizer_y : Nat.card (centralizer ({x * (t * x * t⁻¹)} : Set G)) = 259200

namespace InnerD8Config

variable {L : Subgroup G} {t : G} (c : InnerD8Config L t)

abbrev P : Subgroup G := centralizer ({c.u} : Set G)

abbrev F : Subgroup G := centralizer ({c.u} : Set G) ⊓ centralizer (c.L₁ : Set G) ⊓
  centralizer ((conjSub t c.L₁ : Subgroup G) : Set G)

theorem t_mem_P : t ∈ c.P := c.pair.t_mem

@[expose] noncomputable def rho : ↥c.P →* Wr2 (MulAut (alternatingGroup (Fin 6))) :=
  (mapEquiv (MulAut.congr c.eL₁)).toMonoidHom.comp c.pair.rho

theorem rho_apply (w : ↥c.P) : c.rho w = mapEquiv (MulAut.congr c.eL₁) (c.pair.rho w) := rfl

theorem rho_t : c.rho ⟨t, c.t_mem_P⟩ = tau := by
  simp [rho, c.pair.rho_t, mapEquiv_tau]

theorem ker_rho : c.rho.ker = c.pair.rho.ker := by
  ext p
  simp [rho, MonoidHom.mem_ker]

theorem card_ker_rho : Nat.card c.rho.ker = 4 := by
  rw [ker_rho, c.pair.ker_rho, ← c.card_F,
    ← Subgroup.card_map_of_injective (centralizer ({c.u} : Set G)).subtype_injective,
    Subgroup.subgroupOf_map_subtype]
  congr 2
  ext g
  simp only [mem_inf]
  tauto

end InnerD8Config

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
