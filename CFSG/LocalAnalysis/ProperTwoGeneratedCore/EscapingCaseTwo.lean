module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwoQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOne

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

section CaseTwo

variable {S : Sylow 2 G} {H : Subgroup G} {z u : G} (hset : CoreSetting G S H)
  (hz : IsCentralInvolution (S : Subgroup G) z) (hzC : Subgroup.centralizer ({z} : Set G) ≤ H)
  (hu : orderOf u = 2) (huS : u ∈ (S : Subgroup G))
  (hesc : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
include hset hz hzC hu huS hesc

theorem escapingMk_central_facts {w : Subgroup.centralizer ({u} : Set G)} (hw : (w : G) = z) :
    orderOf (escapingMk u w) = 2 ∧ escapingMk u w ∈ escapingSylowImage S u ∧
      escapingMk u w ∈
        Subgroup.centralizer (escapingSylowImage S u : Set (EscapingQuotient u)) ∧
      escapingMk u w ≠ escapingBar u := by
  have hw2 : orderOf w = 2 := by rw [← Subgroup.orderOf_coe, hw]; exact hz.2.1
  refine ⟨escaping_orderOf_mk u hw2, ⟨w, show (w : G) ∈ (S : Subgroup G) from hw ▸ hz.1, rfl⟩,
    mk_mem_centralizer_escapingSylowImage fun s hs => by rw [hw]; exact hz.2.2 s hs, ?_⟩
  intro h
  have hwu : (w : G) = u := escaping_eq_of_mk_eq_bar (mul_self_eq_one_of_orderOf_eq_two hu)
    (mul_self_eq_one_of_orderOf_eq_two hw2) h
  have hzu : z = u := hw.symm.trans hwu
  exact not_isConj_of_centralizer_le hset (hset.sylow_le hz.1) hz.2.1 hzC (hset.sylow_le huS)
    hesc (hzu ▸ IsConj.refl z)

variable (hsyl : ∀ P : Subgroup G, P ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 P →
  Nat.card P ≤ Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G))
include hsyl

end CaseTwo

end CFSG.ProperTwoGeneratedCore.Assembly
