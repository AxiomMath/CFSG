module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5Skeleton
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Basic
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5EModel

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec5E

open Sec7 Sec8 T2M

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

structure Ctx (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X) where
  h4 : S.Sec4 F T₁
  hF : F.Normal
  D : S.Sec5 F T₁
  hE : D.case = .E

omit [Finite X] in
theorem conj_eq {a b : X} (h : a * b = b * a) : a * b * a⁻¹ = b := by
  rw [h, mul_inv_cancel_right]

theorem t_mul_t (S : A7Base X) : S.t * S.t = 1 := by rw [← pow_two, S.t_sq]

theorem z_mul_z (S : A7Base X) : S.z * S.z = 1 := by rw [← pow_two, z_sq]

theorem xF_mul_xF (F : S.Frame) : F.xF * F.xF = S.z := by rw [← pow_two, F.xF_sq]

theorem t_comm {a : X} (ha : a ∈ S.data.T) : a * S.t = S.t * a := S.data.commute_t ha

theorem z_comm {a : X} (ha : a ∈ S.data.T) : S.z * a = a * S.z := S.central_of_mem_B z_mem_B ha

theorem k_comm (F : S.Frame) {a : X} (ha : a ∈ S.data.T) : F.kF * a = a * F.kF :=
  Sec7.kF_comm F ha

namespace Ctx

variable (C : Ctx S F T₁)

theorem w₁_eq : C.D.w₁ = C.D.w := by
  rcases C.D.w₁_eq with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd (C.hE.symm.trans h) Sec5Case.noConfusion

theorem w_mul_w : C.D.w * C.D.w = 1 := by rw [← pow_two, C.D.w_sq]

theorem w₂_mul_w₂ : C.D.w₂ * C.D.w₂ = 1 := by
  rcases C.D.sq_cases with ⟨-, -, h⟩ | ⟨h, -, -⟩
  · rw [← pow_two, h]
  · exact absurd (C.hE.symm.trans h) Sec5Case.noConfusion

theorem w₂_comm_w : C.D.w₂ * C.D.w = C.D.w * C.D.w₂ := by
  have := C.D.w₂_w₁; rwa [C.w₁_eq] at this

include C in
theorem kF_eq : F.kF = S.k := C.hF.2.2

theorem w_comm_z : C.D.w * S.z = S.z * C.D.w := by
  rw [← F.xF_sq, pow_two, ← mul_assoc, C.D.w_x, mul_assoc, C.D.w_x, ← mul_assoc]

theorem pcX : T2M.PcX F.xF C.D.w S.z F.yF S.t F.kF where
  x_sq := xF_mul_xF F
  x_w := conj_eq C.D.w_x.symm
  x_z := by rw [← xF_mul_xF F]; group
  x_y := xF_conj_yF F
  x_t := conj_eq (t_comm (xF_mem_T F))
  x_k := conj_eq (k_comm F (xF_mem_T F)).symm
  w_sq := C.w_mul_w
  w_z := conj_eq C.w_comm_z
  w_y := conj_eq C.D.w_y
  w_t := by rw [C.D.w_t]; exact (z_comm S.data.t_mem_T).symm
  w_k := conj_eq C.D.w_k
  z_sq := z_mul_z S
  z_y := conj_eq (z_comm (yF_mem_T F))
  z_t := conj_eq (z_comm S.data.t_mem_T)
  z_k := conj_eq (z_comm F.kF_mem)
  y_sq := by rw [← pow_two, F.yF_sq]
  y_t := conj_eq (t_comm (yF_mem_T F))
  y_k := conj_eq (k_comm F (yF_mem_T F)).symm
  t_sq := t_mul_t S
  t_k := conj_eq (k_comm F S.data.t_mem_T).symm
  k_sq := by rw [← pow_two, F.kF_sq]

noncomputable def ι : T2M →* X := Classical.choose (T2M.exists_hom C.pcX)

theorem ι_spec : C.ι T2M.x = F.xF ∧ C.ι T2M.w = C.D.w ∧ C.ι T2M.z = S.z ∧ C.ι T2M.y = F.yF ∧
    C.ι T2M.t = S.t ∧ C.ι T2M.k = F.kF :=
  Classical.choose_spec (T2M.exists_hom C.pcX)

theorem ι_x : C.ι T2M.x = F.xF := C.ι_spec.1

theorem ι_w : C.ι T2M.w = C.D.w := C.ι_spec.2.1

theorem ι_z : C.ι T2M.z = S.z := C.ι_spec.2.2.1

theorem ι_y : C.ι T2M.y = F.yF := C.ι_spec.2.2.2.1

theorem ι_t : C.ι T2M.t = S.t := C.ι_spec.2.2.2.2.1

theorem ι_k : C.ι T2M.k = F.kF := C.ι_spec.2.2.2.2.2

theorem ι_injective : Function.Injective C.ι :=
  T2M.injective_of C.ι (by rw [C.ι_z]; exact S.z_ne_one) (by rw [C.ι_k]; exact (isK_kF F).ne_one)
    (by rw [C.ι_z, C.ι_k]; exact (isK_zkF F).ne_one)

theorem T_le_T₂ : S.data.T ≤ C.D.T₂ := by rw [C.D.T₂_eq_sup]; exact le_sup_left

theorem w_mem_T₂ : C.D.w ∈ C.D.T₂ := by rw [C.D.T₂_eq_sup]; exact mem_sup_right (mem_zpowers _)

theorem ι_mem_of_gens {K : Subgroup X} (h : ∀ g ∈ T2M.gens, C.ι g ∈ K) (a : T2M) : C.ι a ∈ K := by
  rw [T2M.nf_spec a]
  exact map_mem_of_inSpan C.ι
    ⟨nfBits a, by simpa [nfBits, gens] using mem_allBits (nfBits a), rfl⟩ h

theorem ι_mem_T₂ (a : T2M) : C.ι a ∈ C.D.T₂ := by
  refine C.ι_mem_of_gens (fun g hg => ?_) a
  simp only [T2M.gens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [C.ι_x]; exact C.T_le_T₂ (xF_mem_T F)
  · rw [C.ι_w]; exact C.w_mem_T₂
  · rw [C.ι_z]; exact C.T_le_T₂ z_mem_T
  · rw [C.ι_y]; exact C.T_le_T₂ (yF_mem_T F)
  · rw [C.ι_t]; exact C.T_le_T₂ S.data.t_mem_T
  · rw [C.ι_k]; exact C.T_le_T₂ F.kF_mem

theorem range_ι : C.ι.range = C.D.T₂ := by
  refine Subgroup.eq_of_le_of_card_ge (fun _ ⟨a, ha⟩ => ha ▸ C.ι_mem_T₂ a) ?_
  rw [C.D.card_T₂, ← Nat.card_congr (MonoidHom.ofInjective C.ι_injective).toEquiv,
    T2M.card_eq]
  norm_num

theorem exists_ι {b : X} (hb : b ∈ C.D.T₂) : ∃ a : T2M, C.ι a = b := by
  rw [← C.range_ι] at hb; exact hb

noncomputable def ιinv (b : X) : T2M := Classical.epsilon fun a => C.ι a = b

theorem ι_ιinv {b : X} (hb : b ∈ C.D.T₂) : C.ι (C.ιinv b) = b :=
  Classical.epsilon_spec (C.exists_ι hb)

theorem ι_mem_of_span {P : T2M → Prop} {gs : List T2M} (hspan : ∀ a, P a → InSpan gs a)
    {K : Subgroup X} (hK : ∀ g ∈ gs, C.ι g ∈ K) {a : T2M} (ha : P a) : C.ι a ∈ K :=
  map_mem_of_inSpan C.ι (hspan a ha) hK

theorem ι_mem_iff {P : T2M → Prop} [DecidablePred P] {K : Subgroup X} (hKT : K ≤ C.D.T₂)
    (hPK : ∀ a, P a → C.ι a ∈ K) (hcard : Nat.card K ≤ (Finset.univ.filter P).card) (a : T2M) :
    C.ι a ∈ K ↔ P a := by
  classical
  refine ⟨fun ha => ?_, hPK a⟩
  by_contra hPa
  set K' := K.comap C.ι with hK'
  have hcardK' : Nat.card K' = Nat.card K := by
    have hmap : K'.map C.ι = K := by
      rw [hK', Subgroup.map_comap_eq, C.range_ι, inf_eq_right.mpr hKT]
    rw [← hmap, Subgroup.card_map_of_injective C.ι_injective]
  have hsub : insert a (Finset.univ.filter P) ⊆ Finset.univ.filter (· ∈ K') := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rcases hb with rfl | hb
    · exact ha
    · exact hPK b hb
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simpa using hPa)] at h1
  have h2 : (Finset.univ.filter (· ∈ K')).card = Nat.card K' := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega

theorem card_T_filter : (Finset.univ.filter T2M.InT).card = 32 := by decide +kernel

theorem card_E1_filter : (Finset.univ.filter T2M.InE1).card = 16 := by decide +kernel

theorem card_E2_filter : (Finset.univ.filter (· ∈ T2M.E2l)).card = 16 := by decide +kernel

theorem span_T : ∀ a : T2M, T2M.InT a → InSpan [T2M.x, T2M.z, T2M.y, T2M.t, T2M.k] a := by
  decide +kernel

theorem span_E1 : ∀ a : T2M, T2M.InE1 a → InSpan [T2M.z, T2M.y, T2M.t, T2M.k] a := by
  decide +kernel

theorem span_E2 : ∀ a ∈ T2M.E2l, InSpan [T2M.z, T2M.x * T2M.y, T2M.t, T2M.k] a := by
  decide +kernel

theorem ι_mem_T_iff (a : T2M) : C.ι a ∈ S.data.T ↔ T2M.InT a := by
  refine C.ι_mem_iff C.T_le_T₂ (fun b hb => C.ι_mem_of_span span_T (fun g hg => ?_) hb)
    (by rw [S.card_T, card_T_filter]) a
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · rw [C.ι_x]; exact xF_mem_T F
  · rw [C.ι_z]; exact z_mem_T
  · rw [C.ι_y]; exact yF_mem_T F
  · rw [C.ι_t]; exact S.data.t_mem_T
  · rw [C.ι_k]; exact F.kF_mem

include C in
theorem E₁_eq : F.E₁ = closure {S.z, F.yF, S.t, F.kF} := by
  rw [A7Base.Frame.E₁, A7Base.E, C.kF_eq]

include C in
theorem E₂_eq : F.E₂ = closure {S.z, F.xF * F.yF, S.t, F.kF} := by
  rw [A7Base.Frame.E₂, A7Base.E, C.kF_eq]

theorem E₁_le_T : F.E₁ ≤ S.data.T := (isRefl_yF F).E_le_T

theorem E₂_le_T : F.E₂ ≤ S.data.T := (isRefl_xyF F).E_le_T

theorem card_E₁ : Nat.card F.E₁ = 16 := (isRefl_yF F).card_E

theorem card_E₂ : Nat.card F.E₂ = 16 := (isRefl_xyF F).card_E

theorem ι_mem_E₁_iff (a : T2M) : C.ι a ∈ F.E₁ ↔ T2M.InE1 a := by
  refine C.ι_mem_iff (E₁_le_T.trans C.T_le_T₂)
    (fun b hb => C.ι_mem_of_span span_E1 (fun g hg => ?_) hb)
    (by rw [card_E₁, card_E1_filter]) a
  rw [C.E₁_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · rw [C.ι_z]; exact subset_closure (by simp)
  · rw [C.ι_y]; exact subset_closure (by simp)
  · rw [C.ι_t]; exact subset_closure (by simp)
  · rw [C.ι_k]; exact subset_closure (by simp)

theorem ι_mem_E₂_iff (a : T2M) : C.ι a ∈ F.E₂ ↔ a ∈ T2M.E2l := by
  refine C.ι_mem_iff (E₂_le_T.trans C.T_le_T₂)
    (fun b hb => C.ι_mem_of_span span_E2 (fun g hg => ?_) hb)
    (by rw [card_E₂, card_E2_filter]) a
  rw [C.E₂_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · rw [C.ι_z]; exact subset_closure (by simp)
  · rw [map_mul, C.ι_x, C.ι_y]; exact subset_closure (by simp)
  · rw [C.ι_t]; exact subset_closure (by simp)
  · rw [C.ι_k]; exact subset_closure (by simp)

theorem w_inv : C.D.w⁻¹ = C.D.w := inv_eq_of_mul_eq_one_right C.w_mul_w

theorem w₂_inv : C.D.w₂⁻¹ = C.D.w₂ := inv_eq_of_mul_eq_one_right C.w₂_mul_w₂

theorem x_w₂ : F.xF * C.D.w₂ * F.xF⁻¹ = C.D.w * C.D.w₂ := by
  have h := C.D.u_w₂
  rw [C.w₁_eq] at h
  have h2 : (C.D.w₂ * C.D.w)⁻¹ = C.D.w * C.D.w₂ := by rw [mul_inv_rev, C.w_inv, C.w₂_inv]
  rw [h2] at h
  have hy : F.yF * C.D.w₂ * F.yF⁻¹ = C.D.w₂ := conj_eq C.D.w₂_y.symm
  calc F.xF * C.D.w₂ * F.xF⁻¹ = F.xF * (F.yF * C.D.w₂ * F.yF⁻¹) * F.xF⁻¹ := by rw [hy]
    _ = F.xF * F.yF * C.D.w₂ * (F.xF * F.yF)⁻¹ := by group
    _ = C.D.w * C.D.w₂ := h

theorem w₂_x : C.D.w₂ * F.xF * C.D.w₂⁻¹ = F.xF * C.D.w := by
  have h : F.xF * C.D.w₂ = C.D.w * C.D.w₂ * F.xF := by
    rw [← C.x_w₂]; group
  calc C.D.w₂ * F.xF * C.D.w₂⁻¹ = C.D.w₂ * (F.xF * C.D.w₂) := by rw [C.w₂_inv, mul_assoc]
    _ = C.D.w₂ * (C.D.w * C.D.w₂ * F.xF) := by rw [h]
    _ = (C.D.w₂ * C.D.w) * C.D.w₂ * F.xF := by group
    _ = C.D.w * (C.D.w₂ * C.D.w₂) * F.xF := by rw [C.w₂_comm_w]; group
    _ = F.xF * C.D.w := by rw [C.w₂_mul_w₂, mul_one, C.D.w_x]

theorem w₂_conj (a : T2M) : C.D.w₂ * C.ι a * C.D.w₂⁻¹ = C.ι (T2M.sw2 a) := by
  have h := T2M.map_eq_homOf ((MulAut.conj C.D.w₂).toMonoidHom.comp C.ι) C.ι
    (ix := T2M.x * T2M.w) (iy := T2M.y) (iw := T2M.w) (it := T2M.y * T2M.t) (ik := T2M.k)
    (by simp [C.ι_x, C.ι_w, C.w₂_x]) (by simp [C.ι_y, conj_eq C.D.w₂_y])
    (by simp [C.ι_w, conj_eq C.w₂_comm_w])
    (by simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, C.ι_t,
      map_mul, C.ι_y]; rw [C.D.w₂_t]; exact (t_comm (yF_mem_T F)).symm)
    (by simp [C.ι_k, conj_eq C.D.w₂_k]) a
  simpa [T2M.sw2] using h

end Ctx

end Sec5E

end CFSG.ComponentClassification.HSFLit
