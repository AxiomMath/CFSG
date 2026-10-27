module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Prod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Defs

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

private lemma sec8t84_V_decomp (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) {x : G}
    (hx : x ∈ V1 ⊔ V2) : ∃ v1 ∈ V1, ∃ v2 ∈ V2, v1 * v2 = x := by
  have hcomm : ∀ a ∈ V1, ∀ b ∈ V2, a * b = b * a :=
    fun a ha b hb => D.comm a (D.mod1.V_le ha) b (sec8t84_V2_le_T2 D hb)
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun z _ => ∃ v1 ∈ V1, ∃ v2 ∈ V2, v1 * v2 = z)
    ?_ ?_ ?_ ?_ hx
  · rintro z (hz | hz)
    · exact ⟨z, hz, 1, V2.one_mem, by simp⟩
    · exact ⟨1, V1.one_mem, z, hz, by simp⟩
  · exact ⟨1, V1.one_mem, 1, V2.one_mem, by simp⟩
  · rintro a b _ _ ⟨v1, hv1, v2, hv2, rfl⟩ ⟨v1', hv1', v2', hv2', rfl⟩
    refine ⟨v1 * v1', V1.mul_mem hv1 hv1', v2 * v2', V2.mul_mem hv2 hv2', ?_⟩
    calc (v1 * v1') * (v2 * v2') = v1 * (v1' * (v2 * v2')) := by group
      _ = v1 * ((v1' * v2) * v2') := by group
      _ = v1 * ((v2 * v1') * v2') := by rw [hcomm v1' hv1' v2 hv2]
      _ = (v1 * v2) * (v1' * v2') := by group
  · rintro a _ ⟨v1, hv1, v2, hv2, rfl⟩
    refine ⟨v1⁻¹, V1.inv_mem hv1, v2⁻¹, V2.inv_mem hv2, ?_⟩
    rw [mul_inv_rev]
    exact hcomm v1⁻¹ (V1.inv_mem hv1) v2⁻¹ (V2.inv_mem hv2)

private lemma sec8t84_F2_isElemAb2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    IsElemAb2 F2 4 := by
  have hcard : Nat.card F2 = 2 ^ 4 := by
    rw [D.F2_eq, Subgroup.card_map_of_injective (MulAut.conj t).injective, D.mod1.F_e16.2]
  refine ⟨?_, hcard⟩
  rw [D.F2_eq]
  exact D.mod1.F_e16.1.map (MulAut.conj t).toMonoidHom

private lemma sec8t84_T1_le_normalizer_F1 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    T1 ≤ normalizer F1 :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer D.mod1.F_le).mp D.mod1.F_norm

private lemma sec8t84_T1_le_normalizer_F2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    T1 ≤ normalizer F2 := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha b hb
  rw [D.comm a ha b (sec8t84_F2_le_T2 D hb), mul_assoc, mul_inv_cancel, mul_one]
  exact hb

private lemma sec8t84_T2_le_normalizer_F1 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    T2 ≤ normalizer F1 := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb a ha
  rw [(D.comm a (D.mod1.F_le ha) b hb).symm, mul_assoc, mul_inv_cancel, mul_one]
  exact ha

private lemma sec8t84_T2_le_normalizer_F2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    T2 ≤ normalizer F2 := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb x hx
  rw [D.F2_eq, Subgroup.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  rw [D.F2_eq, Subgroup.mem_map]
  refine ⟨(t⁻¹ * b * t) * a * (t⁻¹ * b * t)⁻¹, ?_, ?_⟩
  · have hb1 : t⁻¹ * b * t ∈ T1 := by
      simpa [sec8t84_inv_t D] using D.swap2 b hb
    exact (Subgroup.le_normalizer_iff.mp (sec8t84_T1_le_normalizer_F1 D)) _ hb1 _ ha
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private lemma sec8t84_T1_le_normalizer_F1F2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    T1 ≤ normalizer (F1 ⊔ F2 : Subgroup G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (sec8t84_T1_le_normalizer_F1 D ha)),
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (sec8t84_T1_le_normalizer_F2 D ha))]

private lemma sec8t84_T2_le_normalizer_F1F2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    T2 ≤ normalizer (F1 ⊔ F2 : Subgroup G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (sec8t84_T2_le_normalizer_F1 D hb)),
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (sec8t84_T2_le_normalizer_F2 D hb))]

private lemma sec8t84_F2_map_conj_t (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    F2.map (MulAut.conj t).toMonoidHom = F1 := by
  rw [D.F2_eq, Subgroup.map_map]
  have hcomp : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [sec8t84_inv_t D]
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by simp [D.t_sq]
  rw [hcomp, Subgroup.map_id]

private lemma sec8t84_unique (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) {a a' b b' : G}
    (ha : a ∈ T1) (ha' : a' ∈ T1) (hb : b ∈ T2) (hb' : b' ∈ T2) (h : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have hmem : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h1 : a'⁻¹ * a = 1 := by
    have hmem' : a'⁻¹ * a ∈ T1 ⊓ T2 :=
      Subgroup.mem_inf.mpr ⟨T1.mul_mem (T1.inv_mem ha') ha, by
        rw [hmem]
        exact T2.mul_mem hb' (T2.inv_mem hb)⟩
    rw [D.inf] at hmem'
    exact Subgroup.mem_bot.mp hmem'
  have h2 : b' * b⁻¹ = 1 := by rw [← hmem]; exact h1
  exact ⟨(inv_mul_eq_one.mp h1).symm, (mul_inv_eq_one.mp h2).symm⟩

theorem sec8t84_E_le_T (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : E ≤ T := by
  rw [D.E_eq]
  exact sup_le (D.mod1.V_le.trans (sec8t84_T1_le_T D))
    ((sec8t84_V2_le_T2 D).trans (sec8t84_T2_le_T D))

theorem sec8t84_E0_le_T (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : F1 ⊔ F2 ≤ T := by
  exact sup_le (D.mod1.F_le.trans (sec8t84_T1_le_T D))
    ((sec8t84_F2_le_T2 D).trans (sec8t84_T2_le_T D))

theorem sec8t84_E0_isElemAb2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    IsElemAb2 (F1 ⊔ F2) 8 := by
  have hF2 := sec8t84_F2_isElemAb2 D
  have hcomm : ∀ a ∈ F1, ∀ b ∈ F2, a * b = b * a :=
    fun a ha b hb => D.comm a (D.mod1.F_le ha) b (sec8t84_F2_le_T2 D hb)
  have hinf : F1 ⊓ F2 = ⊥ := by
    apply bot_unique
    rw [← D.inf]
    exact le_inf (inf_le_left.trans D.mod1.F_le) (inf_le_right.trans (sec8t84_F2_le_T2 D))
  refine ⟨?_, ?_⟩
  · exact D.mod1.F_e16.1.sup_of_commute hF2.1 hcomm
  · rw [sec124_card_sup hcomm hinf, D.mod1.F_e16.2, hF2.2]
    norm_num

theorem sec8t84_E0_normal (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    ((F1 ⊔ F2).subgroupOf T).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (sec8t84_E0_le_T D)]
  rw [D.T_eq]
  apply sup_le
  · rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup]
    erw [D.F2_eq.symm, sec8t84_F2_map_conj_t D]
    exact sup_comm F2 F1
  · exact sup_le (sec8t84_T1_le_normalizer_F1F2 D) (sec8t84_T2_le_normalizer_F1F2 D)

theorem sec8t84_E0_ne (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : F1 ⊔ F2 ≠ E := by
  intro h
  apply D.mod1.F_ne
  have hF1leV1 : F1 ≤ V1 := by
    intro x hx
    have hxE : x ∈ E := h ▸ (le_sup_left : F1 ≤ F1 ⊔ F2) hx
    rw [D.E_eq] at hxE
    obtain ⟨v1, hv1, v2, hv2, hv1v2⟩ := sec8t84_V_decomp D hxE
    have huniq := sec8t84_unique D (D.mod1.V_le hv1) (D.mod1.F_le hx)
      (sec8t84_V2_le_T2 D hv2) T2.one_mem (by rw [hv1v2, mul_one])
    exact huniq.1 ▸ hv1
  exact Subgroup.eq_of_le_of_card_ge hF1leV1 (by
    rw [D.mod1.V_e16.2, D.mod1.F_e16.2])

end TData

end CFSG.OddStandard.SmallF3.Omega
