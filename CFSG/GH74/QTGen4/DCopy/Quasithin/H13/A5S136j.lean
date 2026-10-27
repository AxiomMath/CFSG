module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Final

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem omegaOneCenter_inf_centralizer_L_F4 (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4) :
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  by_contra hC
  set C := quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) with hCdef

  have hZT : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) := by
    rw [quasithinOmegaOneCenter, Subgroup.closure_le]
    exact fun x hx => hx.1
  have hCT : C ≤ T := inf_le_left.trans (hZT.trans inf_le_left)
  have hCp : IsPGroup 2 C := S.isPGroup_T.to_le hCT
  have hLC : L ≤ Subgroup.normalizer (C : Set G) := by
    intro l hl
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · have hxl : l * x = x * l :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 l hl)
      have e : l * x * l⁻¹ = x := by rw [hxl]; group
      rw [e]
      exact hx
    · have hxl : l * x = x * l :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 l hl)
      have e : l⁻¹ * x * l = x := by
        calc l⁻¹ * x * l = l⁻¹ * (x * l) := by group
          _ = l⁻¹ * (l * x) := by rw [hxl]
          _ = x := by group
      rw [e]
      exact hx
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := by
    intro t ht
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · have hxt : t * x = x * t :=
        (Subgroup.mem_centralizer_iff.mp (hZT (Subgroup.mem_inf.mp hx).1).2 t ht)
      have e : t * x * t⁻¹ = x := by rw [hxt]; group
      rw [e]
      exact hx
    · have hxt : t * x = x * t :=
        (Subgroup.mem_centralizer_iff.mp (hZT (Subgroup.mem_inf.mp hx).1).2 t ht)
      have e : t⁻¹ * x * t = x := by
        calc t⁻¹ * x * t = t⁻¹ * (x * t) := by group
          _ = t⁻¹ * (t * x) := by rw [hxt]
          _ = x := by group
      rw [e]
      exact hx

  have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) := ⟨C, hC, hCp, rfl⟩
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge hloc
  have hM'eq := S.uniqueM.2 M' ⟨hM', (sup_le hLC hTC).trans hM'le⟩
  have hNM : Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    hM'eq ▸ hM'le

  obtain ⟨-, -, ⟨H, hH⟩, -, -⟩ := (h331 G T S.h13.simple S.h13.nonabelian S.h13.qtke
    S.h13.sylow).2 L S.maximal S.isQuasisimple_L
  rw [S.conjClosure_L_T] at hH
  have hHZ := h1327 G T L V S H hH
  apply hH.2.1
  refine le_trans ?_ hNM
  intro h hh
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  exact (Subgroup.mem_centralizer_iff.mp (hHZ hh) c (Subgroup.mem_inf.mp hc).1)

end Setting

end CFSG.Quasithin.H13.A5
