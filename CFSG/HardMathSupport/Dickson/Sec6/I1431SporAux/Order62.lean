module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Sylow
public import CFSG.Monster.GMS.Facts.BabyTables
public import CFSG.Sporadic.Th.Setup

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Blueprint

theorem noOrder186_of_involution_centralizers {G : Type*} [Group G]
    (h : ∀ t : G, orderOf t = 2 → ¬ 31 ∣ Nat.card ↥(Subgroup.centralizer ({t} : Set G))) :
    NoOrder 186 G := by
  have h62 : NoOrder (2 * 31) G := noOrder_two_mul_of_involution_centralizer (by norm_num) h
  have := noOrder_mul_of_noOrder (k := 3) (by norm_num) h62
  simpa using this

theorem noOrder186_Th_of_card
    (h : ∀ w : ↥CFSG.Sporadic.Th.J, orderOf w = 2 →
      Nat.card ↥(Subgroup.centralizer ({w} : Set ↥CFSG.Sporadic.Th.J)) = 92897280) :
    NoOrder 186 NativeSporadic.Th := by
  have hJ : NoOrder 186 ↥CFSG.Sporadic.Th.J :=
    noOrder186_of_involution_centralizers fun t ht => by rw [h t ht]; norm_num
  exact fun g hg => hJ (CFSG.Sporadic.Th.thEquivJ g) (by rw [MulEquiv.orderOf_eq]; exact hg)

theorem noOrder186_B_of_table (h : CFSG.Monster.GMS.BabyTableIII) : NoOrder 186 NativeSporadic.B :=
  noOrder186_of_involution_centralizers fun t ht => by
    obtain ⟨k, -, hk⟩ := h.1 t ht
    rw [hk]
    fin_cases k <;> simp [CFSG.Monster.GMS.babyCentOrder] <;> norm_num

theorem card_centralizer_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G)) = Nat.card ↥(Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨u, hu⟩ := isConj_iff.1 h
  have e : (Subgroup.centralizer ({b} : Set G) : Subgroup G) =
      (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj u).toMonoidHom := by
    ext g
    simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [← hu]
    constructor
    · intro hg
      refine ⟨u⁻¹ * g * u, ?_, by group⟩
      calc u⁻¹ * g * u * a = u⁻¹ * (g * (u * a * u⁻¹)) * u := by group
        _ = u⁻¹ * ((u * a * u⁻¹) * g) * u := by rw [hg]
        _ = a * (u⁻¹ * g * u) := by group
    · rintro ⟨y, hy, rfl⟩
      calc u * y * u⁻¹ * (u * a * u⁻¹) = u * (y * a) * u⁻¹ := by group
        _ = u * (a * y) * u⁻¹ := by rw [hy]
        _ = u * a * u⁻¹ * (u * y * u⁻¹) := by group
  rw [e, Subgroup.card_map_of_injective (MulAut.conj u).injective]

end CFSG.HardMathSupport.Dickson.Sec6.I1431
