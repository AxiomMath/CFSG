module

public import CFSG.GH74.QTGen4.Leaves.Ru14775
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AStatements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems143
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsFSU

public section

namespace CFSG.GH74.QTGen4.Ru14775

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

theorem relIndex_eq_sixteen_of_isL24Section {G : Type} [Group G] {K X Y : Subgroup G}
    (h : L32A.IsL24Section K X Y) : Y.relIndex X = 16 := by
  obtain ⟨-, π, β, -, -, hβs, hβk, -⟩ := h
  rw [Subgroup.relIndex, ← hβk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hβs,
    Subgroup.card_top, Nat.card_eq_fintype_card]
  decide

theorem two_pow_five_le_card_fsuU_F4 (h63 : Thm14_7_63_F4) (hMod : StmtL32NModule_F4)
    {G : Type} [Group G] [Finite4 G] {T L V : Subgroup G} (h : Hyp147 G T L V) :
    2 ^ 5 ≤ Nat.card ↥(fsuU T V) := by
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  obtain ⟨-, -, -, -, -, -, U₀, hU₀, hL24⟩ := h63 G T L V h
  have hle : fsuV1 T V ≤ U₀ := by
    intro u hu
    rw [hU₀]
    refine ⟨le_conjClosure V _ (Subgroup.mem_inf.mp hu).1, fun k hk => ?_⟩
    have hkH : k ∈ L32A.hz T V := oTwoUpper_le _ hk
    rw [← Subgroup.mem_centralizer_iff.mp hkH u hu, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hV1U : fsuV1 T V ≤ fsuU T V := fun x hx => le_conjClosure V _ (Subgroup.mem_inf.mp hx).1
  have h1 := relIndex_eq_sixteen_of_isL24Section hL24
  have h2 := Subgroup.relIndex_mul_card U₀ (fsuU T V)
  have h3 : Nat.card ↥(fsuV1 T V) ≤ Nat.card ↥(U₀ ⊓ fsuU T V) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion (le_inf hle hV1U))
      (Subgroup.inclusion_injective _)
  rw [h1] at h2
  omega

theorem false_of_hyp147_F4 (h63 : Thm14_7_63_F4) (hMod : StmtL32NModule_F4)
    {G : Type} [Group G] [Finite4 G] {T L V : Subgroup G} (h : Hyp147 G T L V) : False := by
  obtain ⟨hVe, -⟩ := hMod G T L V h.hyp h.fsu
  have h5 := two_pow_five_le_card_fsuU_F4 h63 hMod h
  have h4 := card_fsuU_le_of_gen4 (Finite4.gen4 (G := G)) T V (fun v hv => hVe.2 v hv) h.abelian
  omega

theorem stmt14_7_75_F4_of_h63 (h63 : Thm14_7_63_F4) (hMod : StmtL32NModule_F4) :
    Stmt14_7_75_F4 := fun G _ _ T L V hyp hF hU =>
  (false_of_hyp147_F4 h63 hMod (⟨hyp, hF, hU⟩ : Hyp147 G T L V)).elim

end CFSG.GH74.QTGen4.Ru14775
