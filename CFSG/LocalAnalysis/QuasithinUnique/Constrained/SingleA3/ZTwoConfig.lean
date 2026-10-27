module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin

structure ZTwoConfig {G : Type} [Group G] [Finite G] (T S U R : Subgroup G) (y x c : G) :
    Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  sylowT : IsSylowTwoOf T ⊤
  S_le : S ≤ T
  card_S : Nat.card S = 16
  x_mem : x ∈ T
  x_not_mem : x ∉ S
  x_normalizes : x ∈ Subgroup.normalizer (S : Set G)
  x_sq_mem : x ^ 2 ∈ S
  U_le : U ≤ S
  card_U : Nat.card U = 4
  U_exp : ∀ u ∈ U, u ^ 2 = 1
  S_normalizes_U : S ≤ Subgroup.normalizer (U : Set G)
  R_eq : R = U ⊔ conjSubgroup U x
  R_le : R ≤ S
  card_R : Nat.card R = 8
  R_nonabelian : ∃ r ∈ R, ∃ s ∈ R, r * s ≠ s * r
  y_mem : y ∈ S
  y_order : orderOf y = 2
  y_comm : ∀ s ∈ S, s * y = y * s
  y_not_mem_R : y ∉ R
  S_eq : S = R ⊔ Subgroup.zpowers y
  c_order : orderOf c = 3
  c_normalizes : c ∈ Subgroup.normalizer (U : Set G)
  c_fpf : ∀ u ∈ U, u ≠ 1 → c * u * c⁻¹ ≠ u
  c_comm : c * y = y * c
  N_y : ∀ t ∈ T, t ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) → t ∈ S
  N_U : ∀ t ∈ T, t ∈ Subgroup.normalizer (U : Set G) → t ∈ S
  N_Q : ∀ t ∈ T, t ∈ Subgroup.normalizer ((U ⊔ Subgroup.zpowers y : Subgroup G) : Set G) → t ∈ S
  sylow_Cy : IsSylowTwoOf S (Subgroup.centralizer ({y} : Set G))

end CFSG.QuasithinUnique
