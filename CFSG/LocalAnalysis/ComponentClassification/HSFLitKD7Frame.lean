module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD7Basic
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Basic

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv

namespace KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD}

omit [Finite X] in
theorem elemAbelianTwo_zpowers {g : X} (hg : g ^ 2 = 1) : ElemAbelianTwo (zpowers g) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
    rw [← zpow_add, ← zpow_add, add_comm]
  · rcases eq_one_or_eq_of_mem_zpowers hg ha with rfl | rfl
    · exact one_pow 2
    · exact hg

structure Frame (S : KDBase A C) where
  xF : X
  yF : X
  kF : X
  xF_mem : xF ∈ A.R
  yF_mem : yF ∈ A.R
  xF_sq : xF ^ 2 = S.z
  yF_sq : yF ^ 2 = 1
  yF_inv : yF * xF * yF⁻¹ = xF⁻¹
  kF_eq : kF = S.k ∨ kF = S.z * S.k

variable {S : KDBase A C}

section

variable (S)

theorem elemAbelianTwo_z : ElemAbelianTwo (zpowers S.z) := elemAbelianTwo_zpowers (z_sq S)

theorem comm_zpowers_z {g : X} (hg : g ∈ A.T) {a : X} (ha : a ∈ zpowers S.z) :
    g * a = a * g := by
  rcases eq_one_or_eq_of_mem_zpowers (z_sq S) ha with rfl | rfl
  · rw [mul_one, one_mul]
  · exact z_comm_T S hg

end

namespace Frame

variable (F : Frame S)

theorem xF_mem_T : F.xF ∈ A.T := F.xF_mem.1

theorem yF_mem_T : F.yF ∈ A.T := F.yF_mem.1

theorem yF_mem_L : F.yF ∈ L := F.yF_mem.2

theorem kF_mem_T : F.kF ∈ A.T := by
  rcases F.kF_eq with h | h <;> rw [h]
  · exact C.k_mem
  · exact mul_mem (z_mem_T S) C.k_mem

theorem kF_comm {r : X} (hr : r ∈ A.R) : F.kF * r = r * F.kF := by
  have hk : S.k * r = r * S.k := L2KD.commute_k C hr
  rcases F.kF_eq with h | h <;> rw [h]
  · exact hk
  · rw [mul_assoc, hk, ← mul_assoc, ← z_comm_T S hr.1, mul_assoc]

theorem kF_comm_t : F.kF * t = t * F.kF := A.commute_t F.kF_mem_T

theorem kF_comm_z : F.kF * S.z = S.z * F.kF := F.kF_comm (z_mem_R S)

theorem kF_sq : F.kF ^ 2 = 1 := by
  have hk : S.k ^ 2 = 1 := C.k_sq
  rcases F.kF_eq with h | h <;> rw [h]
  · exact hk
  · show (S.z * C.k) ^ 2 = 1
    rw [(Commute.mul_pow (z_comm_T S C.k_mem).symm 2), z_sq S]
    exact (one_mul _).trans hk

theorem kF_kF : F.kF * F.kF = 1 := by rw [← pow_two, F.kF_sq]

theorem kF_inv : F.kF⁻¹ = F.kF := inv_eq_of_mul_eq_one_right F.kF_kF

theorem kF_not_mem_L : F.kF ∉ L := by
  rcases F.kF_eq with h | h <;> rw [h]
  · exact k_not_mem_L (C := C)
  · exact zk_not_mem_L S

theorem t_kF_not_mem_L : t * F.kF ∉ L := t_mul_not_mem_L S F.kF_eq

theorem kF_ne_one : F.kF ≠ 1 := fun h => F.kF_not_mem_L (h ▸ one_mem L)

theorem k_eq : S.k = F.kF ∨ S.k = S.z * F.kF := by
  rcases F.kF_eq with h | h
  · exact Or.inl h.symm
  · right
    rw [h, ← mul_assoc, zz S, one_mul]

theorem z_mem_B : S.z ∈ S.B := subset_closure (by simp)

theorem t_mem_B : t ∈ S.B := subset_closure (by simp)

theorem k_mem_B : S.k ∈ S.B := subset_closure (by simp)

theorem kF_mem_B : F.kF ∈ S.B := by
  rcases F.kF_eq with h | h <;> rw [h]
  · exact k_mem_B
  · exact mul_mem z_mem_B k_mem_B

theorem xF_ne_inv : F.xF ≠ F.xF⁻¹ := by
  intro h
  apply z_ne_one S
  rw [← F.xF_sq, pow_two]
  nth_rewrite 2 [h]
  exact mul_inv_cancel _

theorem yF_ne_one : F.yF ≠ 1 := by
  intro h
  apply F.xF_ne_inv
  rw [← F.yF_inv, h]
  group

theorem yF_ne_z : F.yF ≠ S.z := by
  intro h
  apply F.xF_ne_inv
  rw [← F.yF_inv, h, ← z_comm_T S F.xF_mem_T, mul_inv_cancel_right]

theorem yF_yF : F.yF * F.yF = 1 := by rw [← pow_two, F.yF_sq]

theorem yF_inv' : F.yF⁻¹ = F.yF := inv_eq_of_mul_eq_one_right F.yF_yF

theorem z_comm_yF : S.z * F.yF = F.yF * S.z := (z_comm_T S F.yF_mem_T).symm

theorem xF_conj_yF : F.xF * F.yF * F.xF⁻¹ = S.z * F.yF := by
  have h : F.yF * F.xF⁻¹ = F.xF * F.yF := by
    have h1 := congrArg (·⁻¹) F.yF_inv
    simp only [mul_inv_rev, inv_inv, F.yF_inv'] at h1
    calc F.yF * F.xF⁻¹ = F.yF * F.xF⁻¹ * F.yF * F.yF := by
          rw [mul_assoc _ F.yF F.yF, F.yF_yF, mul_one]
      _ = F.xF * F.yF := by rw [show F.yF * F.xF⁻¹ * F.yF = F.xF by
            rw [← mul_assoc] at h1; exact h1]
  rw [mul_assoc, h, ← mul_assoc, ← pow_two, F.xF_sq]

theorem xyF_mem_R : F.xF * F.yF ∈ A.R := mul_mem F.xF_mem F.yF_mem

theorem xyF_sq : (F.xF * F.yF) ^ 2 = 1 := by
  have h : F.yF * F.xF = F.xF⁻¹ * F.yF := by rw [← F.yF_inv]; group
  calc (F.xF * F.yF) ^ 2 = F.xF * (F.yF * F.xF) * F.yF := by rw [pow_two]; group
    _ = F.yF * F.yF := by rw [h]; group
    _ = 1 := F.yF_yF

theorem z_mem_E0 : S.z ∈ S.E0 F.yF F.kF := subset_closure (by simp)

theorem yF_mem_E0 : F.yF ∈ S.E0 F.yF F.kF := subset_closure (by simp)

theorem kF_mem_E0 : F.kF ∈ S.E0 F.yF F.kF := subset_closure (by simp)

theorem k_mem_E0 : S.k ∈ S.E0 F.yF F.kF := by
  rcases F.k_eq with h | h <;> rw [h]
  · exact F.kF_mem_E0
  · exact mul_mem F.z_mem_E0 F.kF_mem_E0

theorem E0_eq : S.E0 F.yF F.kF = zpowers S.z ⊔ zpowers F.yF ⊔ zpowers F.kF :=
  Sec7.closure_triple_eq _ _ _

theorem E0_eq' : S.E0 F.yF F.kF = zpowers S.z ⊔ zpowers F.kF ⊔ zpowers F.yF := by
  rw [E0_eq, sup_right_comm]

theorem elemAbelianTwo_zk : ElemAbelianTwo (zpowers S.z ⊔ zpowers F.kF) :=
  Sec7.elemAbelianTwo_sup (elemAbelianTwo_z S) F.kF_sq fun _ ha =>
    comm_zpowers_z S F.kF_mem_T ha

theorem zk_le_E0 : (zpowers S.z ⊔ zpowers F.kF : Subgroup X) ≤ S.E0 F.yF F.kF :=
  sup_le (zpowers_le.mpr F.z_mem_E0) (zpowers_le.mpr F.kF_mem_E0)

theorem kF_not_mem_z : F.kF ∉ zpowers S.z := fun h =>
  F.kF_not_mem_L (zpowers_le.mpr (z_mem_L S) h)

theorem card_zk : Nat.card (zpowers S.z ⊔ zpowers F.kF : Subgroup X) = 4 := by
  rw [Sec7.card_sup_of_not_mem (elemAbelianTwo_z S) F.kF_sq F.kF_not_mem_z
    (fun _ ha => comm_zpowers_z S F.kF_mem_T ha), Nat.card_zpowers,
    orderOf_eq_prime (z_sq S) (z_ne_one S)]

theorem yF_comm_zk {a : X} (ha : a ∈ zpowers S.z ⊔ zpowers F.kF) : F.yF * a = a * F.yF := by
  have hle : (zpowers S.z ⊔ zpowers F.kF : Subgroup X) ≤ centralizer ({F.yF} : Set X) := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_) <;> rw [mem_centralizer_singleton_iff]
    · exact F.z_comm_yF
    · exact F.kF_comm F.yF_mem
  exact (mem_centralizer_singleton_iff.mp (hle ha)).symm

theorem yF_not_mem_zk : F.yF ∉ zpowers S.z ⊔ zpowers F.kF := by
  intro h
  rcases Sec7.mem_or_of_mem_sup (elemAbelianTwo_z S) F.kF_sq
    (fun _ ha => comm_zpowers_z S F.kF_mem_T ha) h with h1 | h1
  · rcases eq_one_or_eq_of_mem_zpowers (z_sq S) h1 with h2 | h2
    · exact F.yF_ne_one h2
    · exact F.yF_ne_z h2
  · apply F.kF_not_mem_L
    have := mul_mem (inv_mem F.yF_mem_L) (zpowers_le.mpr (z_mem_L S) h1)
    rwa [inv_mul_cancel_left] at this

theorem elemAbelianTwo_E0 : ElemAbelianTwo (S.E0 F.yF F.kF) := by
  rw [E0_eq']
  exact Sec7.elemAbelianTwo_sup F.elemAbelianTwo_zk F.yF_sq fun _ ha => F.yF_comm_zk ha

theorem card_E0 : Nat.card (S.E0 F.yF F.kF) = 8 := by
  rw [E0_eq', Sec7.card_sup_of_not_mem F.elemAbelianTwo_zk F.yF_sq F.yF_not_mem_zk
    (fun _ ha => F.yF_comm_zk ha), F.card_zk]

theorem E0_le_T : S.E0 F.yF F.kF ≤ A.T := by
  rw [E0_eq]
  exact sup_le (sup_le (zpowers_le.mpr (z_mem_T S)) (zpowers_le.mpr F.yF_mem_T))
    (zpowers_le.mpr F.kF_mem_T)

theorem t_comm_E0 {e : X} (he : e ∈ S.E0 F.yF F.kF) : t * e = e * t :=
  (A.commute_t (F.E0_le_T he)).symm

theorem comm_E0 {a b : X} (ha : a ∈ S.E0 F.yF F.kF) (hb : b ∈ S.E0 F.yF F.kF) :
    a * b = b * a :=
  F.elemAbelianTwo_E0.comm a ha b hb

theorem V_le_L : (zpowers S.z ⊔ zpowers F.yF : Subgroup X) ≤ L :=
  sup_le (zpowers_le.mpr (z_mem_L S)) (zpowers_le.mpr F.yF_mem_L)

theorem mem_V_or {e : X} (he : e ∈ S.E0 F.yF F.kF) :
    e ∈ (zpowers S.z ⊔ zpowers F.yF : Subgroup X) ∨
      e * F.kF ∈ (zpowers S.z ⊔ zpowers F.yF : Subgroup X) := by
  rw [E0_eq] at he
  have hV : ElemAbelianTwo (zpowers S.z ⊔ zpowers F.yF : Subgroup X) :=
    Sec7.elemAbelianTwo_sup (elemAbelianTwo_z S) F.yF_sq
      fun _ ha => comm_zpowers_z S F.yF_mem_T ha
  refine Sec7.mem_or_of_mem_sup hV F.kF_sq (fun a ha => ?_) he
  have hle : (zpowers S.z ⊔ zpowers F.yF : Subgroup X) ≤ A.R :=
    sup_le (zpowers_le.mpr (z_mem_R S)) (zpowers_le.mpr F.yF_mem)
  exact F.kF_comm (hle ha)

theorem t_not_mem_E0 : t ∉ S.E0 F.yF F.kF := by
  intro h
  rcases F.mem_V_or h with h1 | h1
  · exact t_not_mem_L (A := A) (F.V_le_L h1)
  · exact F.t_kF_not_mem_L (F.V_le_L h1)

theorem z_mem_E (yi : X) : S.z ∈ S.E yi := subset_closure (by simp)

theorem yi_mem_E (yi : X) : yi ∈ S.E yi := subset_closure (by simp)

theorem t_mem_E (yi : X) : t ∈ S.E yi := subset_closure (by simp)

theorem k_mem_E (yi : X) : S.k ∈ S.E yi := subset_closure (by simp)

theorem kF_mem_E (yi : X) : F.kF ∈ S.E yi := by
  rcases F.kF_eq with h | h <;> rw [h]
  · exact k_mem_E yi
  · exact mul_mem (z_mem_E yi) (k_mem_E yi)

theorem E0_le_E : S.E0 F.yF F.kF ≤ S.E F.yF := by
  rw [E0_eq]
  exact sup_le (sup_le (zpowers_le.mpr (z_mem_E _)) (zpowers_le.mpr (yi_mem_E _)))
    (zpowers_le.mpr (F.kF_mem_E _))

theorem E_eq : S.E F.yF = S.E0 F.yF F.kF ⊔ zpowers t := by
  apply le_antisymm
  · refine (closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_sup_left F.z_mem_E0
    · exact mem_sup_left F.yF_mem_E0
    · exact mem_sup_right (mem_zpowers _)
    · exact mem_sup_left F.k_mem_E0
  · exact sup_le F.E0_le_E (zpowers_le.mpr (t_mem_E _))

theorem elemAbelianTwo_E : ElemAbelianTwo (S.E F.yF) := by
  rw [E_eq]
  exact Sec7.elemAbelianTwo_sup F.elemAbelianTwo_E0 (L2K.t_sq (A := A)) fun _ ha =>
    F.t_comm_E0 ha

theorem mem_E0_or {e : X} (he : e ∈ S.E F.yF) :
    e ∈ S.E0 F.yF F.kF ∨ e * t ∈ S.E0 F.yF F.kF := by
  rw [E_eq] at he
  exact Sec7.mem_or_of_mem_sup F.elemAbelianTwo_E0 (L2K.t_sq (A := A))
    (fun _ ha => F.t_comm_E0 ha) he

theorem mem_E0_of_mem_L {e : X} (he : e ∈ S.E F.yF) (heL : e ∈ L) : e ∈ S.E0 F.yF F.kF := by
  rcases F.mem_E0_or he with h | h
  · exact h
  · exfalso
    rcases F.mem_V_or h with h1 | h1
    · apply t_not_mem_L (A := A)
      have := mul_mem (inv_mem heL) (F.V_le_L h1)
      rwa [inv_mul_cancel_left] at this
    · apply F.t_kF_not_mem_L
      have := mul_mem (inv_mem heL) (F.V_le_L h1)
      rwa [mul_assoc, inv_mul_cancel_left] at this

end Frame

variable (S)

@[expose] def frame₁ : Frame S where
  xF := S.x
  yF := S.y
  kF := S.k
  xF_mem := S.x_mem
  yF_mem := S.y_mem
  xF_sq := rfl
  yF_sq := S.y_sq
  yF_inv := S.y_inv
  kF_eq := Or.inl rfl

theorem x_inv_eq : S.x⁻¹ = S.z * S.x := by
  rw [inv_eq_of_mul_eq_one_right (a := S.x) (b := S.x ^ 3)]
  · show S.x ^ 3 = S.x ^ 2 * S.x
    rw [← pow_succ]
  · rw [← pow_succ', x_pow_four S]

@[expose] def frame₂ : Frame S where
  xF := S.x⁻¹
  yF := S.x * S.y
  kF := S.z * S.k
  xF_mem := inv_mem S.x_mem
  yF_mem := mul_mem S.x_mem S.y_mem
  xF_sq := by rw [inv_pow]; exact z_inv S
  yF_sq := (isRefl_xy S).sq
  yF_inv := by
    rw [inv_inv]
    calc S.x * S.y * S.x⁻¹ * (S.x * S.y)⁻¹ = S.x * (S.y * S.x * S.y⁻¹)⁻¹ * S.x⁻¹ := by group
      _ = S.x := by rw [S.y_inv]; group
  kF_eq := Or.inr rfl

theorem conj_mem_E_of_ψ {g : X} (hg : g ∈ A.T) (hψ : L2K.ψX A g = d8) {r r' : X}
    (hr : g * r * g⁻¹ ∈ S.E r') {e : X} (he : e ∈ S.E r) : g * e * g⁻¹ ∈ S.E r' := by
  have hle : S.E r ≤ (S.E r').comap (MulAut.conj g).toMonoidHom := by
    refine (closure_le _).mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    show g * a * g⁻¹ ∈ S.E r'
    rcases ha with rfl | rfl | rfl | rfl
    · rw [conj_z S hg]; exact Frame.z_mem_E r'
    · exact hr
    · rw [mem_centralizer_singleton_iff.mp (A.T_le_centralizer hg), mul_inv_cancel_right]
      exact Frame.t_mem_E r'
    · rcases conj_k_of_ψ S hg hψ with h | h
      · show g * C.k * g⁻¹ ∈ S.E r'
        rw [h]; exact mul_mem (Frame.z_mem_E r') (Frame.k_mem_E r')
      · show g * C.k * g⁻¹ ∈ S.E r'
        rw [h]
        exact mul_mem (mul_mem (Frame.z_mem_E r') (Frame.k_mem_E r')) (Frame.t_mem_E r')
  exact hle he

theorem conj_E₁_of_ψ {g : X} (hg : g ∈ A.T) (hψ : L2K.ψX A g = d8) {e : X}
    (he : e ∈ S.E S.y) : g * e * g⁻¹ ∈ S.E (S.x * S.y) := by
  refine conj_mem_E_of_ψ S hg hψ ?_ he
  rcases conj_refl_of_ψ hg hψ (isRefl_y S) with h | h <;> rw [h]
  · exact Frame.yi_mem_E _
  · rw [x_inv_eq S, mul_assoc]
    exact mul_mem (Frame.z_mem_E _) (Frame.yi_mem_E _)

theorem conj_E₂_of_ψ {g : X} (hg : g ∈ A.T) (hψ : L2K.ψX A g = d8) {e : X}
    (he : e ∈ S.E (S.x * S.y)) : g * e * g⁻¹ ∈ S.E S.y := by
  refine conj_mem_E_of_ψ S hg hψ ?_ he
  rcases conj_refl_of_ψ hg hψ (isRefl_xy S) with h | h <;> rw [h]
  · rw [← mul_assoc, show S.x * S.x = S.z from (pow_two S.x).symm]
    exact mul_mem (Frame.z_mem_E _) (Frame.yi_mem_E _)
  · rw [inv_mul_cancel_left]
    exact Frame.yi_mem_E _

theorem d_conj_E₁ {e : X} (he : e ∈ S.E S.y) : C.d * e * C.d⁻¹ ∈ S.E (S.x * S.y) :=
  conj_E₁_of_ψ S C.d_mem (L2KD.ψX_d C) he

theorem d_inv_conj_E₂ {e : X} (he : e ∈ S.E (S.x * S.y)) : C.d⁻¹ * e * C.d ∈ S.E S.y := by
  have := conj_E₂_of_ψ S (inv_mem C.d_mem) (ψX_d_inv (C := C)) he
  rwa [inv_inv] at this

end KD7

end CFSG.ComponentClassification.HSFLit
