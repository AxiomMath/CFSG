module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5HFacts
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5Skeleton
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7E

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Sec8

namespace Sec5H

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

section Rel

variable (D : S.Sec5 F T₁)

theorem w₁_eq_H (hH : D.case = .H) : D.w₁ = D.w * S.t := by
  rcases D.w₁_eq with ⟨h, -⟩ | ⟨-, h⟩
  · rw [hH] at h; cases h
  · exact h

theorem w₂_sq_H (hH : D.case = .H) : D.w₂ * D.w₂ = F.yF := by
  rcases D.sq_cases with ⟨h, -⟩ | ⟨-, -, h⟩
  · rw [hH] at h; cases h
  · rw [← pow_two, h]

theorem w_mul_w : D.w * D.w = 1 := by rw [← pow_two, D.w_sq]

omit [Finite X] in
theorem conj_of_comm {a b : X} (h : a * b = b * a) : a * b * a⁻¹ = b := by
  rw [h, mul_inv_cancel_right]

omit [Finite X] in
theorem inv_eq_self {a : X} (h : a * a = 1) : a⁻¹ = a := inv_eq_of_mul_eq_one_right h

theorem t_mul_t : S.t * S.t = 1 := by rw [← pow_two, S.t_sq]

theorem z_mul_z : S.z * S.z = 1 := by
  rw [← pow_two, A7Base.z, ← pow_mul, S.x_pow_four]

theorem x_mem_T : F.xF ∈ S.data.T := F.xF_mem.1

theorem y_mem_T : F.yF ∈ S.data.T := F.yF_mem.1

theorem x_mul_x : F.xF * F.xF = S.z := by rw [← pow_two, F.xF_sq]

theorem y_mul_y : F.yF * F.yF = 1 := by rw [← pow_two, F.yF_sq]

theorem k_mul_k : F.kF * F.kF = 1 := by rw [← pow_two, F.kF_sq]

theorem x_y_x : F.xF * F.yF * F.xF⁻¹ = S.z * F.yF := by
  calc F.xF * F.yF * F.xF⁻¹ = F.xF * (F.yF * F.xF * F.yF⁻¹)⁻¹ * F.yF := by group
    _ = S.z * F.yF := by rw [F.yF_inv, inv_inv, x_mul_x]

omit [Finite X] in
theorem rearr {t z x y : X} (htz : t * z = z * t) (htx : t * x = x * t) (hty : t * y = y * t)
    (hzx : z * x = x * z) : t * z * x * y = x * (z * (y * t)) := by
  calc t * z * x * y = z * (t * x) * y := by rw [htz]; group
    _ = z * x * (t * y) := by rw [htx]; group
    _ = x * (z * (y * t)) := by rw [hty, hzx]; group

theorem pcX_of (hH : D.case = .H) : RH.PcX D.w₂ D.w F.xF S.z F.yF S.t F.kF := by
  have hT := S.data.t_mem_T
  have hxT : F.xF ∈ S.data.T := x_mem_T
  have hyT : F.yF ∈ S.data.T := y_mem_T
  have hkT : F.kF ∈ S.data.T := F.kF_mem
  have htx : S.t * F.xF = F.xF * S.t := (S.data.commute_t hxT).symm
  have hty : S.t * F.yF = F.yF * S.t := (S.data.commute_t hyT).symm
  have htk : S.t * F.kF = F.kF * S.t := (S.data.commute_t hkT).symm
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T hT
  have hzx : S.z * F.xF = F.xF * S.z := S.z_comm_of_mem_T hxT
  have hzy : S.z * F.yF = F.yF * S.z := S.z_comm_of_mem_T hyT
  have hzk : S.z * F.kF = F.kF * S.z := S.z_comm_of_mem_T hkT
  have hkx : F.kF * F.xF = F.xF * F.kF := F.kF_comm _ F.xF_mem
  have hky : F.kF * F.yF = F.yF * F.kF := F.kF_comm _ F.yF_mem
  have hwz : D.w * S.z = S.z * D.w := by
    rw [← x_mul_x, ← mul_assoc, D.w_x, mul_assoc, D.w_x, mul_assoc]
  have hw₁ := w₁_eq_H D hH
  have hw₂ := w₂_sq_H D hH
  have hww := w_mul_w D
  have htt : S.t * S.t = 1 := t_mul_t
  have hw₂x : D.w₂ * F.xF * D.w₂⁻¹ = D.w * (F.xF * (S.z * (F.yF * S.t))) := by
    have h1 : D.w₂ * F.xF * D.w₂⁻¹ = D.w₂ * (F.xF * F.yF * D.w₂ * (F.xF * F.yF)⁻¹) *
        (F.xF * F.yF) * (D.w₂ * F.yF * D.w₂)⁻¹ := by group
    have h2 : D.w₂ * F.yF * D.w₂ = 1 := by
      rw [D.w₂_y, mul_assoc, hw₂, y_mul_y]
    have h3 : D.w₂ * (D.w₂ * D.w₁)⁻¹ = D.w₁⁻¹ := by
      rw [D.w₂_w₁]; group
    have h4 : D.w₁⁻¹ = S.t * D.w := by
      rw [hw₁, mul_inv_rev, inv_eq_self htt, inv_eq_self hww]
    have h5 : S.t * D.w = D.w * S.t * S.z := by
      have := D.w_t
      calc S.t * D.w = D.w * (D.w⁻¹ * S.t * D.w) := by group
        _ = D.w * (D.w * S.t * D.w⁻¹) := by rw [inv_eq_self hww]
        _ = D.w * S.t * S.z := by rw [this, mul_assoc]
    rw [h1, D.u_w₂, h2, inv_one, mul_one, h3, h4, h5]
    calc D.w * S.t * S.z * (F.xF * F.yF) = D.w * (S.t * S.z * F.xF * F.yF) := by group
      _ = D.w * (F.xF * (S.z * (F.yF * S.t))) := by
        rw [rearr (hzt.symm) htx hty hzx]
  refine ⟨hw₂, ?_, hw₂x, conj_of_comm D.w₂_z, conj_of_comm D.w₂_y, ?_, conj_of_comm D.w₂_k,
    hww, conj_of_comm D.w_x, conj_of_comm hwz, conj_of_comm D.w_y, ?_, conj_of_comm D.w_k,
    x_mul_x, conj_of_comm hzx.symm, x_y_x, conj_of_comm htx.symm, conj_of_comm hkx.symm,
    z_mul_z, conj_of_comm hzy, conj_of_comm hzt, conj_of_comm hzk, y_mul_y,
    conj_of_comm hty.symm, conj_of_comm hky.symm, htt, conj_of_comm htk, k_mul_k⟩
  ·
    have hc : D.w₂ * D.w₁ * D.w₂⁻¹ = D.w₁ := conj_of_comm D.w₂_w₁
    have hw : D.w = D.w₁ * S.t := by rw [hw₁, mul_assoc, htt, mul_one]
    calc D.w₂ * D.w * D.w₂⁻¹ = (D.w₂ * D.w₁ * D.w₂⁻¹) * (D.w₂ * S.t * D.w₂⁻¹) := by
          rw [hw]; group
      _ = D.w * F.yF := by rw [hc, D.w₂_t, ← mul_assoc, ← hw]
  ·
    rw [D.w₂_t, hty]
  ·
    rw [D.w_t, hzt]

end Rel

section Conj

variable {G : Type*} [Group G]

abbrev conjSub (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {g f : G} {H : Subgroup G} : f ∈ conjSub g H ↔ g⁻¹ * f * g ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hf
    exact ⟨g⁻¹ * f * g, hf, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conj_mem_conjSub {g h : G} {H : Subgroup G} (hh : h ∈ H) :
    g * h * g⁻¹ ∈ conjSub g H :=
  ⟨h, hh, rfl⟩

theorem conjSub_le_iff {g : G} {H K : Subgroup G} :
    conjSub g H ≤ K ↔ ∀ h ∈ H, g * h * g⁻¹ ∈ K := by
  constructor
  · intro hle h hh
    exact hle (conj_mem_conjSub hh)
  · rintro hK _ ⟨h, hh, rfl⟩
    exact hK h hh

theorem conjSub_mul (g h : G) (H : Subgroup G) :
    conjSub (g * h) H = conjSub g (conjSub h H) := by
  rw [conjSub, conjSub, conjSub, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem conjSub_one (H : Subgroup G) : conjSub 1 H = H := by
  ext x
  rw [mem_conjSub]
  simp

theorem conjSub_inv_conjSub (g : G) (H : Subgroup G) : conjSub g⁻¹ (conjSub g H) = H := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_injective (g : G) {H K : Subgroup G} (h : conjSub g H = conjSub g K) : H = K := by
  rw [← conjSub_inv_conjSub g H, h, conjSub_inv_conjSub]

theorem conjSub_eq_self_iff {g : G} {H : Subgroup G} : conjSub g H = H ↔ g ∈ normalizer H :=
  (Subgroup.mem_normalizer_iff_map_conj_eq).symm

theorem conjSub_inf (g : G) (H K : Subgroup G) :
    conjSub g (H ⊓ K) = conjSub g H ⊓ conjSub g K :=
  Subgroup.map_inf_eq _ _ _ (MulEquiv.injective _)

theorem conjSub_mono (g : G) {H K : Subgroup G} (h : H ≤ K) : conjSub g H ≤ conjSub g K :=
  Subgroup.map_mono h

theorem card_conjSub [Finite G] (g : G) (H : Subgroup G) :
    Nat.card (conjSub g H) = Nat.card H :=
  card_map_of_injective (MulEquiv.injective _)

theorem conjSub_eq_of_le [Finite G] {g : G} {H K : Subgroup G} (hle : conjSub g H ≤ K)
    (hcard : Nat.card K ≤ Nat.card H) : conjSub g H = K :=
  Subgroup.eq_of_le_of_card_ge hle (by rwa [card_conjSub])

end Conj

theorem kF_ne_one : F.kF ≠ 1 := fun h => F.kF_not_mem (h ▸ one_mem _)

theorem z_mul_kF_ne_one : S.z * F.kF ≠ 1 := by
  intro h
  have hk : F.kF = S.z⁻¹ := eq_inv_of_mul_eq_one_right h
  exact F.kF_not_mem (hk ▸ mem_sup_left (inv_mem S.z_mem))

structure Setup (D : S.Sec5 F T₁) where
  hH : D.case = .H
  h4 : S.Sec4 F T₁
  hF : F.Normal
  ι : RH →* X
  ι_w₂ : ι RH.w₂ = D.w₂
  ι_w : ι RH.w = D.w
  ι_x : ι RH.x = F.xF
  ι_z : ι RH.z = S.z
  ι_y : ι RH.y = F.yF
  ι_t : ι RH.t = S.t
  ι_k : ι RH.k = F.kF
  inj : Function.Injective ι

theorem exists_setup (D : S.Sec5 F T₁) (hH : D.case = .H) (h4 : S.Sec4 F T₁)
    (hF : F.Normal) : Nonempty (Setup D) := by
  obtain ⟨ι, h1, h2, h3, h4', h5, h6, h7⟩ := RH.exists_hom (pcX_of D hH)
  refine ⟨⟨hH, h4, hF, ι, h1, h2, h3, h4', h5, h6, h7, RH.injective_of ι ?_ ?_ ?_⟩⟩
  · rw [h4']; exact S.z_ne_one
  · rw [h7]; exact kF_ne_one
  · rw [map_mul, h4', h7]; exact z_mul_kF_ne_one

omit [Finite X] in
theorem map_span (ι : RH →* X) (gs : List RH) :
    (RH.span gs).map ι = closure {x | x ∈ gs.map ι} := by
  rw [RH.span, MonoidHom.map_closure]
  congr 1
  ext x
  simp

section T₂

variable (D : S.Sec5 F T₁)

theorem T_le_T₂ : S.data.T ≤ D.T₂ := by rw [D.T₂_eq_sup]; exact le_sup_left

theorem w_mem_T₂ : D.w ∈ D.T₂ := by rw [D.T₂_eq_sup]; exact mem_sup_right (mem_zpowers _)

theorem w₂_mem_R : D.w₂ ∈ D.R := by rw [D.R_eq]; exact mem_sup_right (mem_zpowers _)

theorem t_mem_T₂ : S.t ∈ D.T₂ := T_le_T₂ D S.data.t_mem_T

theorem x_mem_T₂ : F.xF ∈ D.T₂ := T_le_T₂ D x_mem_T

theorem y_mem_T₂ : F.yF ∈ D.T₂ := T_le_T₂ D y_mem_T

theorem z_mem_T₂ : S.z ∈ D.T₂ := T_le_T₂ D S.z_mem.1

theorem k_mem_T₂ : F.kF ∈ D.T₂ := T_le_T₂ D F.kF_mem

end T₂

namespace Setup

variable {D : S.Sec5 F T₁} (C : Setup D)

theorem ι_u : C.ι RH.u = F.xF * F.yF := by rw [RH.u, map_mul, C.ι_x, C.ι_y]

theorem ι_w₁ : C.ι RH.w₁ = D.w₁ := by rw [RH.w₁, map_mul, C.ι_w, C.ι_t, w₁_eq_H D C.hH]

include C in
theorem kF_eq : F.kF = S.k := C.hF.2.2

theorem gens_mem_R : ∀ g ∈ RH.gens, C.ι g ∈ D.R := by
  intro g hg
  simp only [RH.gens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [C.ι_w₂]; exact (w₂_mem_R D)
  · rw [C.ι_w]; exact D.T₂_le (w_mem_T₂ D)
  · rw [C.ι_x]; exact D.T₂_le (x_mem_T₂ D)
  · rw [C.ι_z]; exact D.T₂_le (z_mem_T₂ D)
  · rw [C.ι_y]; exact D.T₂_le (y_mem_T₂ D)
  · rw [C.ι_t]; exact D.T₂_le (t_mem_T₂ D)
  · rw [C.ι_k]; exact D.T₂_le (k_mem_T₂ D)

theorem range_eq : C.ι.range = D.R := by
  refine Subgroup.eq_of_le_of_card_ge (RH.range_le C.ι C.gens_mem_R) ?_
  rw [D.card_R, ← Nat.card_congr (MonoidHom.ofInjective C.inj).toEquiv, RH.card_eq]
  norm_num

theorem mem_R {r : X} : r ∈ D.R ↔ ∃ c, C.ι c = r := by
  rw [← C.range_eq]; rfl

theorem ι_mem_R (c : RH) : C.ι c ∈ D.R := C.mem_R.mpr ⟨c, rfl⟩

theorem map_T2 : RH.T2.map C.ι = D.T₂ := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [RH.T2, map_span, closure_le]
    intro g hg
    simp only [RH.T2gens, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false, Set.mem_ofPred_eq] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [C.ι_w]; exact (w_mem_T₂ D)
    · rw [C.ι_x]; exact (x_mem_T₂ D)
    · rw [C.ι_z]; exact (z_mem_T₂ D)
    · rw [C.ι_y]; exact (y_mem_T₂ D)
    · rw [C.ι_t]; exact (t_mem_T₂ D)
    · rw [C.ι_k]; exact (k_mem_T₂ D)
  · rw [D.card_T₂, card_map_of_injective C.inj, RH.card_T2]

theorem mem_T₂ {τ : X} : τ ∈ D.T₂ ↔ ∃ c, RH.pT2 c = true ∧ C.ι c = τ := by
  rw [← C.map_T2, Subgroup.mem_map]
  simp only [RH.mem_T2]

theorem ι_mem_T₂ {c : RH} : C.ι c ∈ D.T₂ ↔ RH.pT2 c = true := by
  rw [← C.map_T2, Subgroup.mem_map_iff_mem C.inj, RH.mem_T2]

theorem map_Q : RH.Q.map C.ι = D.Q := by
  have hQ := D.Q_eq_sup
  have hE : F.E₁ ≤ RH.Q.map C.ι := by
    rw [A7Base.Frame.E₁, A7Base.E, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · rw [← C.ι_z]; exact mem_map_of_mem _ ((RH.mem_Q _).mpr (by decide +kernel))
    · rw [← C.ι_y]; exact mem_map_of_mem _ ((RH.mem_Q _).mpr (by decide +kernel))
    · rw [← C.ι_t]; exact mem_map_of_mem _ ((RH.mem_Q _).mpr (by decide +kernel))
    · rw [← C.kF_eq, ← C.ι_k]; exact mem_map_of_mem _ ((RH.mem_Q _).mpr (by decide +kernel))
  refine le_antisymm ?_ ?_
  · rw [RH.Q, map_span, closure_le, hQ]
    intro g hg
    simp only [RH.Qgens, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false, Set.mem_ofPred_eq] at hg
    have hE₁ : ∀ e ∈ F.E₁, e ∈ F.E₁ ⊔ zpowers D.w₁ ⊔ zpowers D.w₂ :=
      fun e he => mem_sup_left (mem_sup_left he)
    have hgen : ∀ e ∈ ({S.z, F.yF, S.t, S.k} : Set X), e ∈ F.E₁ :=
      fun e he => subset_closure he
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [C.ι_z]; exact hE₁ _ (hgen _ (by simp))
    · rw [C.ι_y]; exact hE₁ _ (hgen _ (by simp))
    · rw [C.ι_t]; exact hE₁ _ (hgen _ (by simp))
    · rw [C.ι_k, C.kF_eq]; exact hE₁ _ (hgen _ (by simp))
    · rw [C.ι_w₁]; exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · rw [C.ι_w₂]; exact mem_sup_right (mem_zpowers _)
  · rw [hQ]
    refine sup_le (sup_le hE ?_) ?_
    · rw [zpowers_le, ← C.ι_w₁]; exact mem_map_of_mem _ ((RH.mem_Q _).mpr (by decide +kernel))
    · rw [zpowers_le, ← C.ι_w₂]; exact mem_map_of_mem _ ((RH.mem_Q _).mpr (by decide +kernel))

theorem ι_mem_Q {c : RH} : C.ι c ∈ D.Q ↔ RH.pQ c = true := by
  rw [← C.map_Q, Subgroup.mem_map_iff_mem C.inj, RH.mem_Q]

@[expose] noncomputable def Fs (i : Fin 8) : Subgroup X := (RH.G i).map C.ι

theorem ι_mem_Fs {i : Fin 8} {c : RH} : C.ι c ∈ C.Fs i ↔ RH.pG i c = true := by
  rw [Fs, Subgroup.mem_map_iff_mem C.inj, RH.mem_G]

theorem mem_Fs {i : Fin 8} {f : X} : f ∈ C.Fs i ↔ ∃ c, RH.pG i c = true ∧ C.ι c = f := by
  rw [Fs, Subgroup.mem_map]
  simp only [RH.mem_G]

theorem card_Fs (i : Fin 8) : Nat.card (C.Fs i) = 16 := by
  rw [Fs, card_map_of_injective C.inj, RH.card_G]

theorem Fs_le_R (i : Fin 8) : C.Fs i ≤ D.R := by
  rw [← C.range_eq]; exact map_le_range _ _

theorem sq_of_mem_Fs {i : Fin 8} {f : X} (hf : f ∈ C.Fs i) : f * f = 1 := by
  obtain ⟨c, hc, rfl⟩ := C.mem_Fs.mp hf
  rw [← map_mul, RH.pG_sq i c hc, map_one]

theorem Fs_zero : C.Fs 0 = F.E₁ := by
  rw [Fs, RH.G, map_span, A7Base.Frame.E₁, A7Base.E]
  congr 1
  ext g
  simp only [RH.Ggens, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, C.ι_z, C.ι_k, C.ι_t, C.ι_y,
    C.kF_eq]
  tauto

theorem Fs_one : C.Fs 1 = F.E₂ := by
  rw [Fs, RH.G, map_span, A7Base.Frame.E₂, A7Base.E]
  congr 1
  ext g
  simp only [RH.Ggens, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, C.ι_z, C.ι_k, C.ι_t, C.ι_u,
    C.kF_eq]
  tauto

theorem le_Fs_of_elem (A : Subgroup X) (hAR : A ≤ D.R) (hA : ∀ a ∈ A, a * a = 1)
    (hcard : 16 ≤ Nat.card A) : ∃ i, A ≤ C.Fs i := by
  set Â := A.comap C.ι with hÂ
  have hmap : Â.map C.ι = A := map_comap_eq_self (C.range_eq ▸ hAR)
  have hcardÂ : Nat.card Â = Nat.card A := by
    conv_rhs => rw [← hmap]
    rw [card_map_of_injective C.inj]
  obtain ⟨i, hi⟩ := RH.le_G_of_elem Â (fun a ha => C.inj (by
      rw [map_mul, map_one]; exact hA _ ha)) (hcardÂ ▸ hcard)
  exact ⟨i, hmap ▸ map_mono hi⟩

theorem eq_Fs_of_elem (A : Subgroup X) (hAR : A ≤ D.R) (hA : ∀ a ∈ A, a * a = 1)
    (hcard : Nat.card A = 16) : ∃ i, A = C.Fs i := by
  obtain ⟨i, hi⟩ := C.le_Fs_of_elem A hAR hA hcard.ge
  exact ⟨i, Subgroup.eq_of_le_of_card_ge hi (by rw [hcard, C.card_Fs])⟩

theorem Fs_ne {i j : Fin 8} (hij : i ≠ j) : C.Fs i ≠ C.Fs j := by
  intro h
  obtain ⟨c, hc⟩ := RH.G_distinct i j hij
  have h1 : C.ι c ∈ C.Fs i ↔ C.ι c ∈ C.Fs j := by rw [h]
  rw [C.ι_mem_Fs, C.ι_mem_Fs] at h1
  exact hc (by cases h2 : RH.pG i c <;> cases h3 : RH.pG j c <;> simp_all)

theorem Fs_injective {i j : Fin 8} (h : C.Fs i = C.Fs j) : i = j := by
  by_contra hij
  exact C.Fs_ne hij h

@[expose] noncomputable def Zs : Subgroup X := RH.Zs.map C.ι

theorem mem_Zs {f : X} : f ∈ C.Zs ↔ f = 1 ∨ f = S.z ∨ f = F.kF ∨ f = S.z * F.kF := by
  rw [Zs, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rcases (RH.pZ_iff c).mp ((RH.mem_Zs c).mp hc) with rfl | rfl | rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr (Or.inl C.ι_z)
    · exact Or.inr (Or.inr (Or.inl C.ι_k))
    · exact Or.inr (Or.inr (Or.inr (by rw [map_mul, C.ι_z, C.ι_k])))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, one_mem _, map_one _⟩
    · exact ⟨RH.z, (RH.mem_Zs _).mpr (by decide +kernel), C.ι_z⟩
    · exact ⟨RH.k, (RH.mem_Zs _).mpr (by decide +kernel), C.ι_k⟩
    · exact ⟨RH.z * RH.k, (RH.mem_Zs _).mpr (by decide +kernel), by rw [map_mul, C.ι_z, C.ι_k]⟩

theorem ι_mem_Zs {c : RH} : C.ι c ∈ C.Zs ↔ RH.pZ c = true := by
  rw [Zs, Subgroup.mem_map_iff_mem C.inj, RH.mem_Zs]

theorem normal_cases {i : Fin 8} (hn : ∀ r ∈ D.R, ∀ f ∈ C.Fs i, r * f * r⁻¹ ∈ C.Fs i) :
    i = 0 ∨ i = 2 := by
  apply RH.normal_cases i
  intro g _ c hc
  have h := hn (C.ι g) (C.ι_mem_R g) (C.ι c) (C.ι_mem_Fs.mpr hc)
  rw [← map_inv, ← map_mul, ← map_mul, C.ι_mem_Fs] at h
  exact h

theorem conjSub_w₂ (i : Fin 8) : conjSub D.w₂ (C.Fs i) = C.Fs (RH.wtau i) := by
  refine conjSub_eq_of_le (conjSub_le_iff.mpr fun f hf => ?_) (by rw [C.card_Fs, C.card_Fs])
  obtain ⟨c, hc, rfl⟩ := C.mem_Fs.mp hf
  rw [← C.ι_w₂, ← map_inv, ← map_mul, ← map_mul, C.ι_mem_Fs]
  exact RH.w2_conj i c hc

theorem conjSub_T₂ {i : Fin 8} (hi : i.val < 6) {τ : X} (hτ : τ ∈ D.T₂) :
    conjSub τ (C.Fs i) = C.Fs i := by
  obtain ⟨τ', hτ', rfl⟩ := C.mem_T₂.mp hτ
  refine conjSub_eq_of_le (conjSub_le_iff.mpr fun f hf => ?_) le_rfl
  obtain ⟨c, hc, rfl⟩ := C.mem_Fs.mp hf
  rw [← map_inv, ← map_mul, ← map_mul, C.ι_mem_Fs]
  exact RH.T2_norm i hi τ' hτ' c hc

theorem Fs_le_T₂ {i : Fin 8} (hi : i.val < 6) : C.Fs i ≤ D.T₂ := by
  intro f hf
  obtain ⟨c, hc, rfl⟩ := C.mem_Fs.mp hf
  exact C.ι_mem_T₂.mpr (RH.G_T2 i hi c hc)

theorem card_Fs_inf_T₂ {i : Fin 8} (hi : 6 ≤ i.val) :
    Nat.card (C.Fs i ⊓ D.T₂ : Subgroup X) ≤ 8 := by
  have hle : C.Fs i ⊓ D.T₂ ≤ RH.E0.map C.ι := by
    rintro f ⟨hf, hfT⟩
    obtain ⟨c, hc, rfl⟩ := C.mem_Fs.mp hf
    exact (Subgroup.mem_map_iff_mem C.inj).mpr
      ((RH.mem_E0 c).mpr (RH.G_inf_T2 i hi c hc (C.ι_mem_T₂.mp hfT)))
  calc Nat.card (C.Fs i ⊓ D.T₂ : Subgroup X) ≤ Nat.card (RH.E0.map C.ι) :=
        Subgroup.card_le_of_le hle
    _ = 8 := by rw [card_map_of_injective C.inj, RH.card_E0]

theorem card_Fs_inf_Q {i : Fin 8} (hi : i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 5) :
    Nat.card (C.Fs i ⊓ D.Q : Subgroup X) ≤ 8 := by
  classical
  set A : Subgroup RH := (C.Fs i ⊓ D.Q).comap C.ι with hA
  have hmap : A.map C.ι = C.Fs i ⊓ D.Q :=
    map_comap_eq_self (C.range_eq ▸ inf_le_left.trans (C.Fs_le_R i))
  have hmem : ∀ c, c ∈ A ↔ (RH.pG i c = true ∧ RH.pQ c = true) := by
    intro c
    rw [hA, Subgroup.mem_comap, Subgroup.mem_inf, C.ι_mem_Fs, C.ι_mem_Q]
  rw [← hmap, card_map_of_injective C.inj, RH.card_of_mem_iff (p := fun c =>
    RH.pG i c && RH.pQ c) (fun c => by rw [hmem]; simp)]
  have := RH.G_inf_Q i hi
  simpa using this

theorem Fs_le_Q {i : Fin 8} (hi : i = 0 ∨ i = 2 ∨ i = 6 ∨ i = 7) : C.Fs i ≤ D.Q := by
  intro f hf
  obtain ⟨c, hc, rfl⟩ := C.mem_Fs.mp hf
  exact C.ι_mem_Q.mpr (RH.G_Q i hi c hc)

theorem inter_Z {f : X} :
    (f ∈ C.Fs 1 → f ∈ C.Fs 2 → f ∈ C.Zs) ∧ (f ∈ C.Fs 1 → f ∈ C.Fs 4 → f ∈ C.Zs) ∧
      (f ∈ C.Fs 0 → f ∈ C.Fs 3 → f ∈ C.Zs) ∧ (f ∈ C.Fs 0 → f ∈ C.Fs 5 → f ∈ C.Zs) := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩ <;>
  · obtain ⟨c, hc, rfl⟩ := C.mem_Fs.mp h1
    rw [C.ι_mem_Fs] at h2
    rw [C.ι_mem_Zs]
    have := RH.inter_Z c
    tauto

theorem inter_big :
    (∃ f ∈ C.Fs 0, f ∈ C.Fs 2 ∧ f ∉ C.Zs) ∧ (∃ f ∈ C.Fs 0, f ∈ C.Fs 4 ∧ f ∉ C.Zs) ∧
      (∃ f ∈ C.Fs 1, f ∈ C.Fs 3 ∧ f ∉ C.Zs) ∧ (∃ f ∈ C.Fs 1, f ∈ C.Fs 5 ∧ f ∉ C.Zs) := by
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩, ⟨h7, h8, h9⟩, ⟨h10, h11, h12⟩⟩ := RH.inter_big
  refine ⟨⟨_, C.ι_mem_Fs.mpr h1, C.ι_mem_Fs.mpr h2, fun h => by
      rw [C.ι_mem_Zs, h3] at h; exact absurd h (by decide)⟩,
    ⟨_, C.ι_mem_Fs.mpr h4, C.ι_mem_Fs.mpr h5, fun h => by
      rw [C.ι_mem_Zs, h6] at h; exact absurd h (by decide)⟩,
    ⟨_, C.ι_mem_Fs.mpr h7, C.ι_mem_Fs.mpr h8, fun h => by
      rw [C.ι_mem_Zs, h9] at h; exact absurd h (by decide)⟩,
    ⟨_, C.ι_mem_Fs.mpr h10, C.ι_mem_Fs.mpr h11, fun h => by
      rw [C.ι_mem_Zs, h12] at h; exact absurd h (by decide)⟩⟩

include C in
theorem T₂_orbit {τ : X} (hτ : τ ∈ D.T₂) :
    (τ * S.t * τ⁻¹ = S.t ∨ τ * S.t * τ⁻¹ = S.z * S.t) ∧
      (τ * F.yF * τ⁻¹ = F.yF ∨ τ * F.yF * τ⁻¹ = S.z * F.yF) := by
  obtain ⟨c, hc, rfl⟩ := C.mem_T₂.mp hτ
  obtain ⟨h1, h2⟩ := RH.T2_orbit c hc
  rw [← C.ι_t, ← C.ι_y, ← C.ι_z, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
    ← map_mul, ← map_mul]
  exact ⟨h1.imp (congrArg C.ι) (congrArg C.ι), h2.imp (congrArg C.ι) (congrArg C.ι)⟩

include C in
theorem mem_Q_of_comm_y {r : X} (hr : r ∈ D.R) (hry : r * F.yF = F.yF * r) : r ∈ D.Q := by
  obtain ⟨c, rfl⟩ := C.mem_R.mp hr
  rw [← C.ι_y, ← map_mul, ← map_mul] at hry
  exact C.ι_mem_Q.mpr (RH.cent_y c (C.inj hry))

@[expose] noncomputable def E0 : Subgroup X := RH.E0.map C.ι

theorem E0_eq : C.E0 = closure {S.z, F.yF, F.kF} := by
  rw [E0, RH.E0, map_span]
  congr 1
  ext g
  simp [C.ι_z, C.ι_y, C.ι_k]

theorem inf_le_E0 : C.Fs 0 ⊓ C.Fs 2 ≤ C.E0 := by
  rintro f ⟨h1, h2⟩
  obtain ⟨c, hc, rfl⟩ := C.mem_Fs.mp h1
  exact (Subgroup.mem_map_iff_mem C.inj).mpr
    ((RH.mem_E0 c).mpr (RH.inter_E0 c hc (C.ι_mem_Fs.mp h2)))

theorem E0_le_Fs {i : Fin 8} (hi : i = 0 ∨ i = 2 ∨ i = 6 ∨ i = 7) : C.E0 ≤ C.Fs i := by
  rw [E0, Fs]
  refine Subgroup.map_mono fun c hc => (RH.mem_G i c).mpr ?_
  rw [RH.mem_E0] at hc
  revert c
  revert i
  decide +kernel

include C in
theorem comm_z_k {r : X} (hr : r ∈ D.R) : r * S.z = S.z * r ∧ r * F.kF = F.kF * r := by
  obtain ⟨c, rfl⟩ := C.mem_R.mp hr
  obtain ⟨h1, h2⟩ := RH.z_k_comm c
  rw [← C.ι_z, ← C.ι_k, ← map_mul, ← map_mul, ← map_mul, ← map_mul, h1, h2]
  exact ⟨rfl, rfl⟩

end Setup

end Sec5H

end CFSG.ComponentClassification.HSFLit
