module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367d
public import CFSG.Quasithin.Background.B15P4Layer2Final

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem autOn_thompsonJ_le_normalizer_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup (MulAut ↥S.Uv)}
    (hK : IsComponentOf K (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)) :
    autOn (thompsonJ S.Tv) S.Uv ≤ Subgroup.normalizer (K : Set (MulAut ↥S.Uv)) := by
  have hUe := S.elemAbelian_Uv_F4 h1222 h517 hF
  have : IsMulCommutative ↥S.Uv := hUe.1
  have hV : ∀ v : ↥S.Uv, v ^ 2 = 1 := fun v =>
    Subtype.ext (by rw [Subgroup.coe_pow, hUe.2 _ v.2, Subgroup.coe_one])
  set P : Subgroup G := ((Subgroup.normalizer (K : Set (MulAut ↥S.Uv))).comap
    (conjAct S.Uv)).map (Subgroup.normalizer (S.Uv : Set G)).subtype with hP
  have hJP : thompsonJ S.Tv ≤ P := by
    refine iSup₂_le fun A hA => ?_
    intro a ha
    have haN : a ∈ Subgroup.normalizer (S.Uv : Set G) :=
      (hA.1.trans (S.Tv_le_Gv.trans S.Gv_le_normalizer_Uv)) ha
    refine ⟨⟨a, haN⟩, ?_, rfl⟩
    show conjAct S.Uv ⟨a, haN⟩ ∈ Subgroup.normalizer (K : Set (MulAut ↥S.Uv))
    by_cases hAc : A ≤ Subgroup.centralizer (S.Uv : Set G)
    · rw [S.conjAct_Uv_eq_one haN (hAc ha)]
      exact Subgroup.one_mem _
    · have hoff := S.isFFStarOffender_of_mem_F4 h1222 h517 hF ⟨hA, hAc⟩
      exact B15P4.asB15Part4 ↥S.Uv hV _ _ hoff K hK
        ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  intro x hx
  obtain ⟨⟨g, hgN⟩, hg, rfl⟩ := hx
  obtain ⟨⟨g', hg'N⟩, hg'P, hg'g⟩ := hJP (Subgroup.mem_subgroupOf.mp hg)
  have : (⟨g', hg'N⟩ : ↥(Subgroup.normalizer (S.Uv : Set G))) = ⟨g, hgN⟩ := Subtype.ext hg'g
  rw [← this]
  exact hg'P

end Setting

end CFSG.Quasithin.H13.A5
