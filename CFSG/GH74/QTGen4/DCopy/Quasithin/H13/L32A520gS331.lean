module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32A520g

public section
namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem mem_normalizer_kY_F4 {T V Y : Subgroup G} {g : G} (hgX : g ∈ L32NSet14.nX T V)
    (hgY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((kY T V Y : Subgroup G) : Set G) :=
  Subgroup.mem_normalizer_fintype fun k hk =>
    ⟨(Subgroup.mem_normalizer_iff.mp hgY k).mp hk.1,
      L32NSet14.conj_mem_trivSub hgX.1 hgX.2 hk.2⟩

end CFSG.Quasithin.H13.L32A
