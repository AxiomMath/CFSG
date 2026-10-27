module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSyl
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalOrdRows
public import CFSG.Sporadic.Co2Cert.Order
public import CFSG.Sporadic.Fi22.Simple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint Subgroup

theorem orderOf_M11_b :
    orderOf (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8] : Equiv.Perm (Fin 11)) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hm0
  interval_cases m <;> decide

@[expose] def m24a : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] *
    List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] * List.formPerm [10, 17] *
    List.formPerm [11, 20] * List.formPerm [13, 15] * List.formPerm [19, 23] *
    List.formPerm [21, 22]

@[expose] def m24b : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
    List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]

theorem m24a_mem : m24a ∈ NativeSporadic.M24 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem m24b_mem : m24b ∈ NativeSporadic.M24 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem orderOf_M24_g : orderOf ((m24a * m24b * m24a * m24b⁻¹) ^ 3) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hm0
  interval_cases m <;> decide +kernel

theorem row_M11_5 :
    KFactSporLocalRow .M11 5 := by
  intro A _ _ L K₀ z hL _ _ hp _ _ hz hK₀L hzK _ _ _ hy _
  have hcard := hcard_M11 A L hL
  obtain ⟨e⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have hσ : (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8] : Equiv.Perm (Fin 11)) ∈
      NativeSporadic.M11 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  set g' : ↥L := (b.trans e.symm) ⟨_, hσ⟩ with hg'def
  have hg' : orderOf g' = 4 := by
    rw [hg'def, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact orderOf_M11_b
  have hord : orderOf (2 : ZMod 5) = 4 :=
    orderOf_two_zmod_eq 5 4 (by norm_num) (by decide) (by decide)
  exact (false_of_elemAbelian_sylow L K₀ hp (by norm_num) hz hK₀L hzK hy (d := 4) (m := 495) hord
    (by rw [hcard]; norm_num) (by decide) (g := (g' : A)) g'.2
    (by rw [Subgroup.orderOf_coe]; exact hg')).elim

theorem row_M24_11 :
    KFactSporLocalRow .M24 11 := by
  intro A _ _ L K₀ z hL _ _ hp _ _ hz hK₀L hzK _ _ _ hy _
  have hcard := hcard_M24 A L hL
  obtain ⟨e⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have hσ : (m24a * m24b * m24a * m24b⁻¹) ^ 3 ∈ NativeSporadic.M24 :=
    pow_mem (mul_mem (mul_mem (mul_mem m24a_mem m24b_mem) m24a_mem) (inv_mem m24b_mem)) 3
  set g' : ↥L := (b.trans e.symm) ⟨_, hσ⟩ with hg'def
  have hg' : orderOf g' = 4 := by
    rw [hg'def, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact orderOf_M24_g
  have hord : orderOf (2 : ZMod 11) = 10 :=
    orderOf_two_zmod_eq 11 10 (by norm_num) (by decide) (by decide)
  exact (false_of_elemAbelian_sylow L K₀ hp (by norm_num) hz hK₀L hzK hy (d := 10) (m := 239085)
    hord (by rw [hcard]; norm_num) (by decide) (g := (g' : A)) g'.2
    (by rw [Subgroup.orderOf_coe]; exact hg')).elim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
