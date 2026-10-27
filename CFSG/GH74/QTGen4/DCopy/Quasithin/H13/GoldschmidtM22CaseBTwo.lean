module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBInv
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBWeak
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBTwoS331

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace BCtx_F4

variable {T M L V : Subgroup G} {g : G} {D : Subgroup G} (c : BCtx_F4 T M L V g D)

include c in
theorem caseB_two (h2 : V.relIndex (Subgroup.centralizer (V : Set G)) = 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hrQ, hrV, hr2, hQ⟩ := c.exists_r h2
  obtain ⟨a, haV1, haN, has, ha2⟩ := c.exists_a₁
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  have hr1 : r ≠ 1 := fun h => hrV (h ▸ V.one_mem)
  refine false_of_index_two_F4 c.h.simple c.h.nonabelian c.h.sylow.1 c.h.sylow.2
    (inf_le_left : T ⊓ (L ⊔ Subgroup.zpowers a) ≤ T)
    (c.relIndex_T0 haN has haa hrQ hr2 hQ hrV)
    (orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1) ?_
  intro g' hconj
  obtain ⟨-, hNB⟩ := Subgroup.mem_inf.mp hconj
  have hx2 : (g'⁻¹ * r * g') * (g'⁻¹ * r * g') = 1 := by
    calc g'⁻¹ * r * g' * (g'⁻¹ * r * g') = g'⁻¹ * (r * r) * g' := by group
      _ = 1 := by rw [hr2]; group
  have hx1 : g'⁻¹ * r * g' ≠ 1 := fun h => hr1 (by
    calc r = g' * (g'⁻¹ * r * g') * g'⁻¹ := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨h, v, hv, -, hhx⟩ := c.conj_into_V haV1 haN has haa hNB hx2 hx1
  refine c.not_conj_V h2 hrQ hrV (g' * h⁻¹) v hv ?_
  rw [← hhx]
  group

end BCtx_F4

theorem m22CaseBTwo_holds_F4 : M22CaseBTwo_F4 := by
  intro G _ _ T M L V g D hl h hk _ h2
  obtain ⟨c⟩ := nonempty_bCtx_F4 hl h hk
  exact c.caseB_two h2

end CFSG.Quasithin.H13.GM22
