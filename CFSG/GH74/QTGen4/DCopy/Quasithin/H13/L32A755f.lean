module

public import CFSG.Quasithin.H13.L32A755f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A755d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Orbit

namespace Ctx753

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G}

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem exists_coord_F4
    (C : Ctx753 T L V K) (h38 : Lemma14_7_38_F4) :
    ∃ e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ, Coord C e := by
  obtain ⟨e, h1, h2, h3, h4⟩ := C.exists_coord755_F4 h38
  refine ⟨e, ⟨h1, h2, h3, h4, (C.natural_sec_F4 h38).2.2.2, fun x hx w hw => ?_⟩⟩
  rcases C.lemma14_7_54_F4 h38 with ⟨h0, -⟩ | ⟨h2, -, hW⟩
  · rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at hw
    exact hw
  · exact M755.weyl_eq_of_mem_fixV hW h2
      (fun l => Subgroup.mem_normalizer_iff.mp (C.autH_le_normalizer hx) l) hw

end Ctx753

end CFSG.Quasithin.H13.L32A
