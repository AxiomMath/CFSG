module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

structure GomiU42SetupG (G : Type) [Group G] [Finite G] (Bs : Subgroup G) (e t : G)
    (J₀ E₂ : Subgroup G) : Prop where
  e_mem : e ∈ Bs
  t_mem : t ∈ Bs
  kGroup : CFSG.SectionRank.IsKGroupCat ↥Bs
  e_central : ∀ y ∈ Bs, y * e = e * y
  orderOf_e : orderOf e = 3
  t_sq : t * t = 1
  t_ne_one : t ≠ 1
  J₀_le : J₀ ≤ Bs
  lieModel : CFSG.Blueprint.LieModel ↥J₀ .PSU 4 2 1
  le_centralizer : J₀ ≤ centralizer ({t} : Set G)
  inf_e : zpowers e ⊓ J₀ = ⊥
  centralizer_eq : Bs ⊓ centralizer ({t} : Set G) = zpowers t ⊔ (zpowers e ⊔ J₀)
  inf_t : zpowers t ⊓ (zpowers e ⊔ J₀) = ⊥
  two_pow_dvd : 2 ^ 9 ∣ Nat.card ↥Bs
  E₂_le : E₂ ≤ Bs
  elementary : CFSG.IsElementaryAbelian 2 ↥E₂
  card_E₂ : Nat.card ↥E₂ = 2 ^ 8
  mem_normalizer : t ∈ normalizer (E₂ : Set G)
  isPGroup_sup : IsPGroup 2 ↥(E₂ ⊔ zpowers t)
  card_inf : Nat.card ↥(E₂ ⊓ centralizer ({t} : Set G)) = 2 ^ 4
  inf_le : E₂ ⊓ centralizer ({t} : Set G) ≤ J₀

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
