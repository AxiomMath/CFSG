module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Wr
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

section TData

variable {t : G} {E T T1 T2 V1 V2 F1 F2 : Subgroup G}

private lemma sec8t84_inv_t (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right D.t_sq

private lemma sec8t84_T1_le_T (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : T1 ≤ T := by
  rw [D.T_eq]
  exact (le_sup_left : T1 ≤ T1 ⊔ T2).trans le_sup_right

private lemma sec8t84_T2_le_T (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : T2 ≤ T := by
  rw [D.T_eq]
  exact (le_sup_right : T2 ≤ T1 ⊔ T2).trans le_sup_right

private lemma sec8t84_V2_le_T2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : V2 ≤ T2 := by
  rw [D.V2_eq]
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨v, hv, rfl⟩ := hx
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using D.swap1 v (D.mod1.V_le hv)

private lemma sec8t84_F2_le_T2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : F2 ≤ T2 := by
  rw [D.F2_eq]
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨f, hf, rfl⟩ := hx
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using D.swap1 f (D.mod1.F_le hf)

private lemma sec8t84_V2_isElemAb2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    IsElemAb2 V2 4 := by
  have hcard : Nat.card V2 = 2 ^ 4 := by
    rw [D.V2_eq, Subgroup.card_map_of_injective (MulAut.conj t).injective, D.mod1.V_e16.2]
  refine ⟨?_, hcard⟩
  rw [D.V2_eq]
  exact D.mod1.V_e16.1.map (MulAut.conj t).toMonoidHom

private lemma sec8t84_F2_isElemAb2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    IsElemAb2 F2 4 := by
  have hcard : Nat.card F2 = 2 ^ 4 := by
    rw [D.F2_eq, Subgroup.card_map_of_injective (MulAut.conj t).injective, D.mod1.F_e16.2]
  refine ⟨?_, hcard⟩
  rw [D.F2_eq]
  exact D.mod1.F_e16.1.map (MulAut.conj t).toMonoidHom

private lemma sec8t84_conj_comp (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id G := by
  ext x
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  rw [sec8t84_inv_t D]
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
    _ = x := by simp [D.t_sq]

private lemma sec8t84_map_conj_inv (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2)
    (H : Subgroup G) :
    (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = H := by
  rw [Subgroup.map_map, sec8t84_conj_comp D, Subgroup.map_id]

private lemma sec8t84_F2_map_conj_t (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    F2.map (MulAut.conj t).toMonoidHom = F1 := by
  rw [D.F2_eq, Subgroup.map_map, sec8t84_conj_comp D, Subgroup.map_id]

private lemma sec8t84_decomp (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) {A1 A2 : Subgroup G}
    (hA1 : A1 ≤ T1) (hA2 : A2 ≤ T2) {x : G} (hx : x ∈ A1 ⊔ A2) :
    ∃ a ∈ A1, ∃ b ∈ A2, a * b = x := by
  have hcomm : ∀ a ∈ A1, ∀ b ∈ A2, a * b = b * a :=
    fun a ha b hb => D.comm a (hA1 ha) b (hA2 hb)
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun z _ => ∃ a ∈ A1, ∃ b ∈ A2, a * b = z)
    ?_ ?_ ?_ ?_ hx
  · rintro z (hz | hz)
    · exact ⟨z, hz, 1, A2.one_mem, by simp⟩
    · exact ⟨1, A1.one_mem, z, hz, by simp⟩
  · exact ⟨1, A1.one_mem, 1, A2.one_mem, by simp⟩
  · rintro a b _ _ ⟨v1, hv1, v2, hv2, rfl⟩ ⟨v1', hv1', v2', hv2', rfl⟩
    refine ⟨v1 * v1', A1.mul_mem hv1 hv1', v2 * v2', A2.mul_mem hv2 hv2', ?_⟩
    calc (v1 * v1') * (v2 * v2') = v1 * (v1' * (v2 * v2')) := by group
      _ = v1 * ((v1' * v2) * v2') := by group
      _ = v1 * ((v2 * v1') * v2') := by rw [hcomm v1' hv1' v2 hv2]
      _ = (v1 * v2) * (v1' * v2') := by group
  · rintro a _ ⟨v1, hv1, v2, hv2, rfl⟩
    refine ⟨v1⁻¹, A1.inv_mem hv1, v2⁻¹, A2.inv_mem hv2, ?_⟩
    rw [mul_inv_rev]
    exact hcomm v1⁻¹ (A1.inv_mem hv1) v2⁻¹ (A2.inv_mem hv2)

private lemma sec8t84_sup_factors (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2)
    {A1 B1 A2 B2 : Subgroup G} (hA1 : A1 ≤ T1) (hB1 : B1 ≤ T1)
    (hA2 : A2 ≤ T2) (hB2 : B2 ≤ T2) (h : A1 ⊔ A2 = B1 ⊔ B2) :
    A1 = B1 ∧ A2 = B2 := by
  have hleft : ∀ {A B C D' : Subgroup G}, A ≤ T1 → B ≤ T1 → C ≤ T2 → D' ≤ T2 →
      A ⊔ C = B ⊔ D' → A ≤ B := by
    intro A B C D' hA hB hC hD hsup x hx
    have hx' : x ∈ B ⊔ D' := hsup ▸ Subgroup.mem_sup_left hx
    obtain ⟨b, hb, d, hd, hbd⟩ := sec8t84_decomp D hB hD hx'
    have huniq := sec8t84_wr_unique D.wr (hA hx) (hB hb) T2.one_mem (hD hd)
      (by rw [mul_one, ← hbd])
    exact huniq.1.symm ▸ hb
  have hright : ∀ {A B C D' : Subgroup G}, A ≤ T1 → B ≤ T1 → C ≤ T2 → D' ≤ T2 →
      A ⊔ C = B ⊔ D' → C ≤ D' := by
    intro A B C D' hA hB hC hD hsup x hx
    have hx' : x ∈ B ⊔ D' := hsup ▸ Subgroup.mem_sup_right hx
    obtain ⟨b, hb, d, hd, hbd⟩ := sec8t84_decomp D hB hD hx'
    have huniq := sec8t84_wr_unique D.wr T1.one_mem (hB hb) (hC hx) (hD hd)
      (by rw [one_mul, ← hbd])
    exact huniq.2.symm ▸ hd
  exact ⟨le_antisymm (hleft hA1 hB1 hA2 hB2 h) (hleft hB1 hA1 hB2 hA2 h.symm),
    le_antisymm (hright hA1 hB1 hA2 hB2 h) (hright hB1 hA1 hB2 hA2 h.symm)⟩

theorem sec8t84_VF2_isElemAb2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    IsElemAb2 (V1 ⊔ F2) 8 := by
  have hF2 := sec8t84_F2_isElemAb2 D
  have hcomm : ∀ a ∈ V1, ∀ b ∈ F2, a * b = b * a :=
    fun a ha b hb => D.comm a (D.mod1.V_le ha) b (sec8t84_F2_le_T2 D hb)
  have hinf : V1 ⊓ F2 = ⊥ := by
    apply bot_unique
    rw [← D.inf]
    exact le_inf (inf_le_left.trans D.mod1.V_le) (inf_le_right.trans (sec8t84_F2_le_T2 D))
  refine ⟨?_, ?_⟩
  · exact D.mod1.V_e16.1.sup_of_commute hF2.1 hcomm
  · rw [sec124_card_sup hcomm hinf, D.mod1.V_e16.2, hF2.2]
    norm_num

theorem sec8t84_FV2_isElemAb2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    IsElemAb2 (F1 ⊔ V2) 8 := by
  have hV2 := sec8t84_V2_isElemAb2 D
  have hcomm : ∀ a ∈ F1, ∀ b ∈ V2, a * b = b * a :=
    fun a ha b hb => D.comm a (D.mod1.F_le ha) b (sec8t84_V2_le_T2 D hb)
  have hinf : F1 ⊓ V2 = ⊥ := by
    apply bot_unique
    rw [← D.inf]
    exact le_inf (inf_le_left.trans D.mod1.F_le) (inf_le_right.trans (sec8t84_V2_le_T2 D))
  refine ⟨?_, ?_⟩
  · exact D.mod1.F_e16.1.sup_of_commute hV2.1 hcomm
  · rw [sec124_card_sup hcomm hinf, D.mod1.F_e16.2, hV2.2]
    norm_num

theorem sec8t84_VF2_le_T (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : V1 ⊔ F2 ≤ T :=
  sup_le (D.mod1.V_le.trans (sec8t84_T1_le_T D))
    ((sec8t84_F2_le_T2 D).trans (sec8t84_T2_le_T D))

theorem sec8t84_FV2_le_T (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : F1 ⊔ V2 ≤ T :=
  sup_le (D.mod1.F_le.trans (sec8t84_T1_le_T D))
    ((sec8t84_V2_le_T2 D).trans (sec8t84_T2_le_T D))

theorem sec8t84_four_distinct (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    E ≠ V1 ⊔ F2 ∧ E ≠ F1 ⊔ V2 ∧ F1 ⊔ F2 ≠ V1 ⊔ F2 ∧ F1 ⊔ F2 ≠ F1 ⊔ V2 ∧
      V1 ⊔ F2 ≠ F1 ⊔ V2 := by
  have hV2F2 : V2 ≠ F2 := by
    intro h
    apply D.mod1.F_ne
    calc F1 = F2.map (MulAut.conj t).toMonoidHom := (sec8t84_F2_map_conj_t D).symm
      _ = V2.map (MulAut.conj t).toMonoidHom := by rw [h]
      _ = (V1.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
            rw [D.V2_eq]
      _ = V1 := sec8t84_map_conj_inv D V1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : V1 ⊔ V2 = V1 ⊔ F2 := by rw [← D.E_eq]; exact h
    exact hV2F2 (sec8t84_sup_factors D D.mod1.V_le D.mod1.V_le (sec8t84_V2_le_T2 D)
      (sec8t84_F2_le_T2 D) h').2
  · intro h
    have h' : V1 ⊔ V2 = F1 ⊔ V2 := by rw [← D.E_eq]; exact h
    exact D.mod1.F_ne (sec8t84_sup_factors D D.mod1.V_le D.mod1.F_le
      (sec8t84_V2_le_T2 D) (sec8t84_V2_le_T2 D) h').1.symm
  · intro h
    exact D.mod1.F_ne (sec8t84_sup_factors D D.mod1.F_le D.mod1.V_le
      (sec8t84_F2_le_T2 D) (sec8t84_F2_le_T2 D) h).1
  · intro h
    exact hV2F2 (sec8t84_sup_factors D D.mod1.F_le D.mod1.F_le
      (sec8t84_F2_le_T2 D) (sec8t84_V2_le_T2 D) h).2.symm
  · intro h
    exact D.mod1.F_ne (sec8t84_sup_factors D D.mod1.V_le D.mod1.F_le
      (sec8t84_F2_le_T2 D) (sec8t84_V2_le_T2 D) h).1.symm

theorem sec8t84_VF2_conj (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    (V1 ⊔ F2).map (MulAut.conj t).toMonoidHom = F1 ⊔ V2 := by
  rw [Subgroup.map_sup, ← D.V2_eq, sec8t84_F2_map_conj_t D]
  exact sup_comm V2 F1

theorem sec8t84_FV2_conj (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    (F1 ⊔ V2).map (MulAut.conj t).toMonoidHom = V1 ⊔ F2 := by
  rw [Subgroup.map_sup, D.F2_eq.symm, D.V2_eq, sec8t84_map_conj_inv D V1]
  exact sup_comm F2 V1

end TData

end CFSG.OddStandard.SmallF3.Omega
