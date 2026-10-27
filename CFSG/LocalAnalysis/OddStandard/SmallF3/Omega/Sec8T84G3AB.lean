module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {E T T1 T2 V1 V2 F1 F2 : Subgroup G}

private lemma sec8t84g3a_ab_inv_t (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right D.t_sq

private lemma sec8t84g3a_ab_conj_comp (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id G := by
  ext x
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  rw [sec8t84g3a_ab_inv_t D]
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
    _ = x := by simp [D.t_sq]

private lemma sec8t84g3a_ab_map_conj_inv (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2)
    (H : Subgroup G) :
    (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = H := by
  rw [Subgroup.map_map, sec8t84g3a_ab_conj_comp D, Subgroup.map_id]

private lemma sec8t84g3a_ab_F2_map_conj_t (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    F2.map (MulAut.conj t).toMonoidHom = F1 := by
  rw [D.F2_eq, Subgroup.map_map, sec8t84g3a_ab_conj_comp D, Subgroup.map_id]

private lemma sec8t84g3a_ab_decomp (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) {A B : Subgroup G}
    (hA : A ≤ T1) (hB : B ≤ T2) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a :=
    fun a ha b hb => D.comm a (hA ha) b (hB hb)
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun z _ => ∃ a ∈ A, ∃ b ∈ B, a * b = z)
    ?_ ?_ ?_ ?_ hx
  · rintro z (hz | hz)
    · exact ⟨z, hz, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, z, hz, by simp⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  · rintro a b _ _ ⟨v1, hv1, v2, hv2, rfl⟩ ⟨v1', hv1', v2', hv2', rfl⟩
    refine ⟨v1 * v1', A.mul_mem hv1 hv1', v2 * v2', B.mul_mem hv2 hv2', ?_⟩
    calc (v1 * v1') * (v2 * v2') = v1 * (v1' * (v2 * v2')) := by group
      _ = v1 * ((v1' * v2) * v2') := by group
      _ = v1 * ((v2 * v1') * v2') := by rw [hcomm v1' hv1' v2 hv2]
      _ = (v1 * v2) * (v1' * v2') := by group
  · rintro a _ ⟨v1, hv1, v2, hv2, rfl⟩
    refine ⟨v1⁻¹, A.inv_mem hv1, v2⁻¹, B.inv_mem hv2, ?_⟩
    rw [mul_inv_rev]
    exact hcomm v1⁻¹ (A.inv_mem hv1) v2⁻¹ (B.inv_mem hv2)

private lemma sec8t84g3a_ab_unique (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) {a a' b b' : G}
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

theorem sec8t84g3a_V2_le_T2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : V2 ≤ T2 := by
  rw [D.V2_eq]
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨v, hv, rfl⟩ := hx
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using D.swap1 v (D.mod1.V_le hv)

theorem sec8t84g3a_F2_le_T2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : F2 ≤ T2 := by
  rw [D.F2_eq]
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨f, hf, rfl⟩ := hx
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using D.swap1 f (D.mod1.F_le hf)

theorem sec8t84g3a_prod_inf (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) {A A' B B' : Subgroup G}
    (hA : A ≤ T1) (hA' : A' ≤ T1) (hB : B ≤ T2) (hB' : B' ≤ T2) :
    (A ⊔ B) ⊓ (A' ⊔ B') = (A ⊓ A') ⊔ (B ⊓ B') := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨a, ha, b, hb, hab⟩ := sec8t84g3a_ab_decomp D hA hB hx1
    obtain ⟨a', ha', b', hb', ha'b'⟩ := sec8t84g3a_ab_decomp D hA' hB' hx2
    have hxab : a * b = a' * b' := by rw [hab, ha'b']
    obtain ⟨rfl, rfl⟩ := sec8t84g3a_ab_unique D (hA ha) (hA' ha') (hB hb) (hB' hb') hxab
    rw [← hab]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨ha, ha'⟩) (Subgroup.mem_inf.mpr ⟨hb, hb'⟩)
  · apply le_inf
    · exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
    · exact sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right)

theorem sec8t84g3a_F2_ne_V2 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : F2 ≠ V2 := by
  intro h
  apply D.mod1.F_ne
  calc F1 = F2.map (MulAut.conj t).toMonoidHom := (sec8t84g3a_ab_F2_map_conj_t D).symm
    _ = V2.map (MulAut.conj t).toMonoidHom := by rw [h]
    _ = (V1.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom := by rw [D.V2_eq]
    _ = V1 := sec8t84g3a_ab_map_conj_inv D V1

theorem sec8t84g3a_U_inf (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    (V1 ⊔ F1) ⊓ (V2 ⊔ F2) = ⊥ := by
  have hA : V1 ⊔ F1 ≤ T1 := sup_le D.mod1.V_le D.mod1.F_le
  have hB' : V2 ⊔ F2 ≤ T2 := sup_le (sec8t84g3a_V2_le_T2 D) (sec8t84g3a_F2_le_T2 D)
  have h := sec8t84g3a_prod_inf D (A := V1 ⊔ F1) (A' := ⊥) (B := ⊥) (B' := V2 ⊔ F2)
    hA bot_le bot_le hB'
  simpa using h

theorem sec8t84g3a_W_eq (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    E ⊔ (F1 ⊔ F2) = (V1 ⊔ F1) ⊔ (V2 ⊔ F2) := by
  rw [D.E_eq, sup_sup_sup_comm]

theorem sec8t84g3a_U_card (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    Nat.card ↥(V1 ⊔ F1) = 64 ∧ Nat.card ↥(V2 ⊔ F2) = 64 := by
  refine ⟨D.mod1.J_card, ?_⟩
  have hmap : V2 ⊔ F2 = (V1 ⊔ F1).map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_sup, ← D.V2_eq, ← D.F2_eq]
  rw [hmap, Subgroup.card_map_of_injective (MulAut.conj t).injective, D.mod1.J_card]

theorem sec8t84g3a_U1_inf (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    (V1 ⊔ F1) ⊓ E = V1 ∧ (V1 ⊔ F1) ⊓ (F1 ⊔ F2) = F1 ∧ (V1 ⊔ F1) ⊓ (V1 ⊔ F2) = V1 := by
  have hA : V1 ⊔ F1 ≤ T1 := sup_le D.mod1.V_le D.mod1.F_le
  refine ⟨?_, ?_, ?_⟩
  · have h := sec8t84g3a_prod_inf D (A := V1 ⊔ F1) (A' := V1) (B := ⊥) (B' := V2)
      hA D.mod1.V_le bot_le (sec8t84g3a_V2_le_T2 D)
    rw [D.E_eq]
    simpa using h
  · have h := sec8t84g3a_prod_inf D (A := V1 ⊔ F1) (A' := F1) (B := ⊥) (B' := F2)
      hA D.mod1.F_le bot_le (sec8t84g3a_F2_le_T2 D)
    simpa using h
  · have h := sec8t84g3a_prod_inf D (A := V1 ⊔ F1) (A' := V1) (B := ⊥) (B' := F2)
      hA D.mod1.V_le bot_le (sec8t84g3a_F2_le_T2 D)
    simpa using h

theorem sec8t84g3a_U2_inf (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    (V2 ⊔ F2) ⊓ E = V2 ∧ (V2 ⊔ F2) ⊓ (F1 ⊔ F2) = F2 ∧ (V2 ⊔ F2) ⊓ (F1 ⊔ V2) = V2 := by
  have hB : V2 ⊔ F2 ≤ T2 := sup_le (sec8t84g3a_V2_le_T2 D) (sec8t84g3a_F2_le_T2 D)
  refine ⟨?_, ?_, ?_⟩
  · have h := sec8t84g3a_prod_inf D (A := ⊥) (A' := V1) (B := V2 ⊔ F2) (B' := V2)
      bot_le D.mod1.V_le hB (sec8t84g3a_V2_le_T2 D)
    rw [D.E_eq]
    simpa using h
  · have h := sec8t84g3a_prod_inf D (A := ⊥) (A' := F1) (B := V2 ⊔ F2) (B' := F2)
      bot_le D.mod1.F_le hB (sec8t84g3a_F2_le_T2 D)
    simpa using h
  · have h := sec8t84g3a_prod_inf D (A := ⊥) (A' := F1) (B := V2 ⊔ F2) (B' := V2)
      bot_le D.mod1.F_le hB (sec8t84g3a_V2_le_T2 D)
    simpa using h

end CFSG.OddStandard.SmallF3.Omega
